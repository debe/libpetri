//! Racing LLM agent pipeline demonstrating async dispatch with the libpetri API.
//!
//! 13 typed places, 12 transitions with timing, environment places, DOT export,
//! async execution via Tokio.

use libpetri::core::token::ErasedToken;
use libpetri::runtime::environment::ExternalEvent;
use libpetri::*;

#[tokio::main]
async fn main() {
    // Coloured places — String messages, () control signals
    let keyboard = EnvironmentPlace::<()>::new("KeyboardEvent");
    let user_message = EnvironmentPlace::<String>::new("UserMessage");
    let topic_change = EnvironmentPlace::<()>::new("TopicChange");
    let composing = Place::<()>::new("Composing");
    let pending = Place::<String>::new("Pending");
    let processing = Place::<()>::new("Processing");
    let context_ready = Place::<String>::new("ContextReady");
    let conversation = Place::<String>::new("Conversation");
    let summary = Place::<String>::new("Summary");
    let summarizing = Place::<()>::new("Summarizing");
    let thinking = Place::<String>::new("Thinking");
    let urgency = Place::<()>::new("Urgency");
    let response = Place::<String>::new("Response");

    // 1. Typing: keystroke → user is composing; resets urgency
    let typing = Transition::builder("Typing")
        .input(one(keyboard.place()))
        .reset(reset(&urgency))
        .output(out_place(&composing))
        .timing(immediate())
        .priority(20)
        .action(fork())
        .build();

    // 2. Receive: submitted message → AND-fork into Pending + Processing + Conversation
    let receive = Transition::builder("Receive")
        .input(one(user_message.place()))
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

    // 3. GatherContext: reads Conversation + Summary → fires when Summary exists
    let gather_context = Transition::builder("GatherContext")
        .input(one(&pending))
        .read(read(&conversation))
        .read(read(&summary))
        .output(out_place(&context_ready))
        .timing(immediate())
        .action(async_action(|mut ctx| async move {
            let msg: std::sync::Arc<String> = ctx.input("Pending")?;
            let conv: std::sync::Arc<String> = ctx.read("Conversation")?;
            let sum: std::sync::Arc<String> = ctx.read("Summary")?;
            ctx.output(
                "ContextReady",
                format!("[ctx: {sum} | {conv}] {msg}"),
            )?;
            Ok(ctx)
        }))
        .build();

    // 4. GatherFresh: reads Conversation, inhibited by Summary → fires when no summary
    let gather_fresh = Transition::builder("GatherFresh")
        .input(one(&pending))
        .read(read(&conversation))
        .inhibitor(inhibitor(&summary))
        .output(out_place(&context_ready))
        .timing(immediate())
        .action(async_action(|mut ctx| async move {
            let msg: std::sync::Arc<String> = ctx.input("Pending")?;
            let conv: std::sync::Arc<String> = ctx.read("Conversation")?;
            ctx.output("ContextReady", format!("[ctx: {conv}] {msg}"))?;
            Ok(ctx)
        }))
        .build();

    // 5. DeepAgent: thorough analysis — consumes ContextReady, produces Thinking
    let deep_agent = Transition::builder("DeepAgent")
        .input(one(&context_ready))
        .output(out_place(&thinking))
        .timing(window(500, 10000))
        .action(async_action(|mut ctx| async move {
            let msg: std::sync::Arc<String> = ctx.input("ContextReady")?;
            tokio::task::yield_now().await;
            ctx.output("Thinking", format!("{msg} [deep analysis]"))?;
            Ok(ctx)
        }))
        .build();

    // 6. Timeout: fires at exactly 5s; inhibited by Response and Composing
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
        .action(async_action(|mut ctx| async move {
            let conv: std::sync::Arc<String> = ctx.read("Conversation")?;
            tokio::task::yield_now().await;
            ctx.output("Response", format!("{conv} [quick reply]"))?;
            Ok(ctx)
        }))
        .build();

    // 8. Complete: deep wins — consumes Thinking + Processing, inhibited by Response
    let complete = Transition::builder("Complete")
        .input(one(&thinking))
        .input(one(&processing))
        .inhibitor(inhibitor(&response))
        .reset(reset(&urgency))
        .output(out_place(&response))
        .timing(deadline(3000))
        .action(async_action(|mut ctx| async move {
            let thought: std::sync::Arc<String> = ctx.input("Thinking")?;
            tokio::task::yield_now().await;
            ctx.output("Response", format!("{thought} [completed]"))?;
            Ok(ctx)
        }))
        .build();

    // 9. Dump: deep loses — consumes Thinking, reads Response (confirms quick answered)
    let dump = Transition::builder("Dump")
        .input(one(&thinking))
        .read(read(&response))
        .timing(immediate())
        .action(fork())
        .build();

    // 10. AutoSummarize: ≥3 messages → summarize; resets remainder
    let auto_summarize = Transition::builder("AutoSummarize")
        .input(at_least(3, &conversation))
        .inhibitor(inhibitor(&summarizing))
        .reset(reset(&conversation))
        .output(out_place(&summarizing))
        .timing(delayed(2000))
        .action(fork())
        .build();

    // 11. ToolSummarize: external TopicChange trigger
    let tool_summarize = Transition::builder("ToolSummarize")
        .input(one(topic_change.place()))
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

    // Build the net
    let net = PetriNet::builder("AgentPipeline")
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
        .build();

    // Export to DOT
    println!("=== DOT Export ===\n");
    println!("{}", dot_export(&net, None));

    // Set up initial marking: seed with a conversation message,
    // then inject a user message via the environment place.
    // No Summary token → GatherFresh fires (not GatherContext).
    let mut marking = Marking::new();
    marking.add(
        &conversation,
        Token::at("User: Hello, can you help?".to_string(), 0),
    );

    let mut executor =
        BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());

    let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExternalEvent>();

    // Inject a user message into the environment place
    tx.send(ExternalEvent {
        place_name: user_message.name().into(),
        token: ErasedToken::from_typed(&Token::at("User: What is a Petri net?".to_string(), 0)),
    })
    .unwrap();

    // Drop sender so the executor knows no more events are coming
    drop(tx);

    executor.run_async(rx).await;

    // Inspect result
    println!("\n=== Result ===\n");
    match executor.marking().peek(&response) {
        Some(value) => println!("Response: {value}"),
        None => println!("No token in 'Response'"),
    }
}
