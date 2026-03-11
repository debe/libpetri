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
                "UserInput".to_string(),
                "SummarizeCmd".to_string(),
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

/// LLM agent orchestration pipeline showcasing all arc types, timing modes, and patterns.
///
/// Coloured tokens flow through an agent pipeline: user messages (String) are routed
/// to either a deep-analysis agent or a quick-reply agent based on an urgency control
/// place. Conversation history accumulates via AND-fork. External keyboard events
/// trigger summarization. A watchdog produces urgency after inactivity.
///
/// Arc types: input, output, read (Conversation context), inhibitor (Urgency blocks
/// deep path), reset (Complete clears stale Urgency).
/// Timing: immediate, window, deadline, delayed, exact.
fn showcase() -> PetriNet {
    // Coloured places — String messages, () control signals
    let user_input   = Place::<String>::new("UserInput");     // env: keyboard events
    let pending      = Place::<String>::new("Pending");       // message awaiting agent
    let conversation = Place::<String>::new("Conversation");  // history (accumulates)
    let urgency      = Place::<()>::new("Urgency");           // urgency control signal
    let thinking     = Place::<String>::new("Thinking");      // deep analysis in progress
    let response     = Place::<String>::new("Response");      // agent output
    let summarize_cmd = Place::<()>::new("SummarizeCmd");     // env: "summarize" trigger
    let summary      = Place::<String>::new("Summary");       // conversation summary

    // Receive: keyboard input → AND-fork into processing queue + conversation history
    let receive = Transition::builder("Receive")
        .input(one(&user_input))
        .output(and(vec![out_place(&pending), out_place(&conversation)]))
        .timing(immediate())
        .priority(10)
        .action(fork())
        .build();

    // DeepAgent: slow, thorough analysis — blocked when urgent
    let deep_agent = Transition::builder("DeepAgent")
        .input(one(&pending))
        .read(read(&conversation))
        .inhibitor(inhibitor(&urgency))
        .output(out_place(&thinking))
        .timing(window(500, 5000))
        .action(fork())
        .build();

    // QuickAgent: fast reply — fires only when urgency is present (consumes it)
    let quick_agent = Transition::builder("QuickAgent")
        .input(one(&pending))
        .input(one(&urgency))
        .read(read(&conversation))
        .output(out_place(&response))
        .timing(immediate())
        .action(fork())
        .build();

    // Complete: deep analysis finishes — clears any stale urgency via reset arc
    let complete = Transition::builder("Complete")
        .input(one(&thinking))
        .reset(reset(&urgency))
        .output(out_place(&response))
        .timing(deadline(3000))
        .action(fork())
        .build();

    // Summarize: external "summarize" command — reads full conversation context
    let summarize = Transition::builder("Summarize")
        .input(one(&summarize_cmd))
        .read(read(&conversation))
        .output(out_place(&summary))
        .timing(delayed(1000))
        .action(fork())
        .build();

    // Watchdog: produces urgency after 10s inactivity — self-inhibits (fires at most once)
    let watchdog = Transition::builder("Watchdog")
        .read(read(&conversation))
        .inhibitor(inhibitor(&urgency))
        .output(out_place(&urgency))
        .timing(exact(10000))
        .action(fork())
        .build();

    PetriNet::builder("AgentPipeline")
        .transition(receive)
        .transition(deep_agent)
        .transition(quick_agent)
        .transition(complete)
        .transition(summarize)
        .transition(watchdog)
        .build()
}
