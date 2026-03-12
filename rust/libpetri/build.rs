use libpetri_docgen::*;
use libpetri_docgen::export::mapper::DotConfig;
use libpetri_docgen::export::graph::RankDir;
use std::collections::HashSet;

fn main() {
    generate_svg("basic_chain", &basic_chain());

    SvgGenerator::new()
        .config(DotConfig {
            direction: RankDir::LeftToRight,
            environment_places: HashSet::from([
                "KeyboardEvent".to_string(),
                "UserMessage".to_string(),
                "TopicChange".to_string(),
            ]),
            ..DotConfig::default()
        })
        .generate("showcase", &showcase());
}

/// p1 -> t1 -> p2 -> t2 -> p3
fn basic_chain() -> PetriNet {
    let p1 = Place::<i32>::new("p1");
    let p2 = Place::<i32>::new("p2");
    let p3 = Place::<i32>::new("p3");

    let t1 = Transition::builder("t1")
        .input(one(&p1))
        .output(out_place(&p2))
        .action(fork())
        .build();

    let t2 = Transition::builder("t2")
        .input(one(&p2))
        .output(out_place(&p3))
        .action(fork())
        .build();

    PetriNet::builder("basic_chain")
        .transition(t1)
        .transition(t2)
        .build()
}

/// Racing LLM agent pipeline showcasing all arc types, timing modes, and patterns.
///
/// Three environment places model real chat UX: KeyboardEvent (raw keystroke activity),
/// UserMessage (fully composed submitted message), and TopicChange (tool-call-initiated
/// summarization trigger). Coloured tokens (`String` messages + `()` control signals)
/// flow through an agent pipeline.
///
/// **Racing pattern (deep vs quick):**
/// Receive AND-forks into Pending + Processing + Conversation. GatherContext or
/// GatherFresh (standard Petri net optional-dependency pattern) consumes Pending, reads
/// Conversation (guaranteed non-empty — Receive just added a token), reads Summary if
/// present → ContextReady. DeepAgent consumes ContextReady and produces Thinking.
/// Meanwhile, Timeout fires at exactly 5s (inhibited by Response and Composing) to
/// produce Urgency. QuickAgent consumes Processing + Urgency, reads Conversation → Response.
///
/// **Race resolution:**
/// - Deep wins (finishes before 5s): Complete consumes Thinking + Processing → Response.
///   Timeout can't fire (Processing consumed + Response inhibits).
/// - Quick wins (5s passes): QuickAgent consumes Processing + Urgency → Response.
///   Deep eventually produces Thinking → Dump fires (consumes Thinking, reads Response
///   to confirm quick already answered, produces nothing). Clean state.
///
/// **Summarization (two triggers):**
/// AutoSummarize: conversation reaches ≥3 messages → at_least(3) input + reset
/// remainder → Summarizing → SummaryDone → Summary.
/// ToolSummarize: external TopicChange signal + reads Conversation → Summarizing.
///
/// Arc types: input (incl. at_least threshold), output (incl. AND-fork, sink),
/// read, inhibitor, reset.
/// Timing: immediate, window, exact, delayed, deadline.
fn showcase() -> PetriNet {
    // Coloured places — String messages, () control signals
    let keyboard       = Place::<()>::new("KeyboardEvent");      // env: raw keystroke activity
    let user_message   = Place::<String>::new("UserMessage");    // env: submitted full message
    let topic_change   = Place::<()>::new("TopicChange");        // env: tool-call summarization trigger
    let composing      = Place::<()>::new("Composing");          // user is currently typing
    let pending        = Place::<String>::new("Pending");        // raw message, not yet context-enriched
    let processing     = Place::<()>::new("Processing");         // active request flag
    let context_ready  = Place::<String>::new("ContextReady");   // message enriched with context
    let conversation   = Place::<String>::new("Conversation");   // message history (accumulates)
    let summary        = Place::<String>::new("Summary");        // compressed history
    let summarizing    = Place::<()>::new("Summarizing");        // summarization in progress
    let thinking       = Place::<String>::new("Thinking");       // deep result awaiting delivery
    let urgency        = Place::<()>::new("Urgency");            // timeout signal
    let response       = Place::<String>::new("Response");       // delivered response

    // 1. Typing: keystroke activity → user is composing; resets urgency (user is engaged)
    let typing = Transition::builder("Typing")
        .input(one(&keyboard))
        .reset(reset(&urgency))
        .output(out_place(&composing))
        .timing(immediate())
        .priority(20)
        .action(fork())
        .build();

    // 2. Receive: submitted message → AND-fork into Pending + Processing + Conversation
    //    resets Composing (user finished typing)
    let receive = Transition::builder("Receive")
        .input(one(&user_message))
        .reset(reset(&composing))
        .output(and(vec![
            out_place(&pending),
            out_place(&processing),
            out_place(&conversation),
        ]))
        .timing(immediate())
        .priority(10)
        .action(fork())
        .build();

    // 3. GatherContext: reads both Conversation + Summary → fires when Summary exists
    let gather_context = Transition::builder("GatherContext")
        .input(one(&pending))
        .read(read(&conversation))
        .read(read(&summary))
        .output(out_place(&context_ready))
        .timing(immediate())
        .action(fork())
        .build();

    // 4. GatherFresh: reads Conversation, inhibited by Summary → fires when Summary absent
    let gather_fresh = Transition::builder("GatherFresh")
        .input(one(&pending))
        .read(read(&conversation))
        .inhibitor(inhibitor(&summary))
        .output(out_place(&context_ready))
        .timing(immediate())
        .action(fork())
        .build();

    // 5. DeepAgent: thorough analysis — consumes ContextReady, produces Thinking
    let deep_agent = Transition::builder("DeepAgent")
        .input(one(&context_ready))
        .output(out_place(&thinking))
        .timing(window(500, 10000))
        .action(fork())
        .build();

    // 6. Timeout: fires at exactly 5s; inhibited by Response (already answered) and Composing
    let timeout = Transition::builder("Timeout")
        .read(read(&processing))
        .inhibitor(inhibitor(&response))
        .inhibitor(inhibitor(&composing))
        .output(out_place(&urgency))
        .timing(exact(5000))
        .action(fork())
        .build();

    // 7. QuickAgent: fast fallback — consumes Processing + Urgency, reads Conversation
    let quick_agent = Transition::builder("QuickAgent")
        .input(one(&processing))
        .input(one(&urgency))
        .read(read(&conversation))
        .output(out_place(&response))
        .timing(immediate())
        .action(fork())
        .build();

    // 8. Complete: deep wins the race — consumes Thinking + Processing, inhibited by Response
    let complete = Transition::builder("Complete")
        .input(one(&thinking))
        .input(one(&processing))
        .inhibitor(inhibitor(&response))
        .reset(reset(&urgency))
        .output(out_place(&response))
        .timing(deadline(3000))
        .action(fork())
        .build();

    // 9. Dump: deep loses the race — consumes Thinking, reads Response (confirms quick answered)
    //    no output: acts as a sink (discards the late deep result)
    let dump = Transition::builder("Dump")
        .input(one(&thinking))
        .read(read(&response))
        .timing(immediate())
        .action(fork())
        .build();

    // 10. AutoSummarize: conversation reaches ≥3 messages; resets remainder
    let auto_summarize = Transition::builder("AutoSummarize")
        .input(at_least(3, &conversation))
        .inhibitor(inhibitor(&summarizing))
        .reset(reset(&conversation))
        .output(out_place(&summarizing))
        .timing(delayed(2000))
        .action(fork())
        .build();

    // 11. ToolSummarize: external TopicChange trigger; reads Conversation, resets it
    let tool_summarize = Transition::builder("ToolSummarize")
        .input(one(&topic_change))
        .read(read(&conversation))
        .inhibitor(inhibitor(&summarizing))
        .reset(reset(&conversation))
        .output(out_place(&summarizing))
        .timing(immediate())
        .action(fork())
        .build();

    // 12. SummaryDone: summarization completes — replaces old Summary
    let summary_done = Transition::builder("SummaryDone")
        .input(one(&summarizing))
        .reset(reset(&summary))
        .output(out_place(&summary))
        .timing(deadline(2000))
        .action(fork())
        .build();

    PetriNet::builder("AgentPipeline")
        .transition(typing)
        .transition(receive)
        .transition(gather_context)
        .transition(gather_fresh)
        .transition(deep_agent)
        .transition(timeout)
        .transition(quick_agent)
        .transition(complete)
        .transition(dump)
        .transition(auto_summarize)
        .transition(tool_summarize)
        .transition(summary_done)
        .build()
}
