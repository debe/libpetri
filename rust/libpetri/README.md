# libpetri — Coloured Time Petri Net Engine

A high-performance [Coloured Time Petri Net](https://en.wikipedia.org/wiki/Petri_net) engine with formal verification support.

## Example: Racing LLM Agent Pipeline

An agent orchestration net with coloured tokens (`String` messages + `()` control
signals), three environment inputs (keystroke activity, submitted messages,
topic-change triggers), a racing pattern (deep vs quick agent with dump semantics),
explicit context assembly (optional-dependency pattern), and two-trigger
background summarization:

```rust
use libpetri::*;

// Coloured places — String messages, () control signals
let keyboard      = EnvironmentPlace::<()>::new("KeyboardEvent");      // raw keystroke activity
let user_message  = EnvironmentPlace::<String>::new("UserMessage");    // submitted full message
let topic_change  = EnvironmentPlace::<()>::new("TopicChange");        // tool-call summarization trigger
let composing     = Place::<()>::new("Composing");          // user is currently typing
let pending       = Place::<String>::new("Pending");        // raw message, not yet context-enriched
let processing    = Place::<()>::new("Processing");         // active request flag
let context_ready = Place::<String>::new("ContextReady");   // message enriched with context
let conversation  = Place::<String>::new("Conversation");   // message history (accumulates)
let summary       = Place::<String>::new("Summary");        // compressed history
let summarizing   = Place::<()>::new("Summarizing");        // summarization in progress
let thinking      = Place::<String>::new("Thinking");       // deep result awaiting delivery
let urgency       = Place::<()>::new("Urgency");            // timeout signal
let response      = Place::<String>::new("Response");       // delivered response

// Typing: keystroke → user is composing; resets urgency (user is engaged)
let typing = Transition::builder("Typing")
    .input(one(keyboard.place()))
    .reset(reset(&urgency))
    .output(out_place(&composing))
    .timing(immediate())
    .priority(20)
    .action(fork())
    .build();

// Receive: submitted message → AND-fork into Pending + Processing + Conversation
//   resets Composing (user finished typing)
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

// GatherContext: reads both Conversation + Summary → fires when Summary exists (full context)
let gather_context = Transition::builder("GatherContext")
    .input(one(&pending))
    .read(read(&conversation))
    .read(read(&summary))
    .output(out_place(&context_ready))
    .timing(immediate())
    .action(fork())
    .build();

// GatherFresh: reads Conversation, inhibited by Summary → fires when Summary absent
//   Standard Petri net optional-dependency pattern — exactly one fires for any marking
let gather_fresh = Transition::builder("GatherFresh")
    .input(one(&pending))
    .read(read(&conversation))
    .inhibitor(inhibitor(&summary))
    .output(out_place(&context_ready))
    .timing(immediate())
    .action(fork())
    .build();

// DeepAgent: thorough analysis — consumes ContextReady, produces Thinking
let deep_agent = Transition::builder("DeepAgent")
    .input(one(&context_ready))
    .output(out_place(&thinking))
    .timing(window(500, 10000))              // window: fires between 500ms and 10s
    .action(async_action(|mut ctx| async move {
        let msg: std::sync::Arc<String> = ctx.input("ContextReady")?;
        // ... deep analysis
        ctx.output("Thinking", format!("{msg} [analyzed]"))?;
        Ok(ctx)
    }))
    .build();

// Timeout: fires at exactly 5s — inhibited by Response (already answered) and Composing
let timeout = Transition::builder("Timeout")
    .read(read(&processing))
    .inhibitor(inhibitor(&response))
    .inhibitor(inhibitor(&composing))
    .output(out_place(&urgency))
    .timing(exact(5000))                     // exact: fires at precisely 5s
    .action(fork())
    .build();

// QuickAgent: fast fallback — consumes Processing + Urgency, reads Conversation
let quick_agent = Transition::builder("QuickAgent")
    .input(one(&processing))
    .input(one(&urgency))
    .read(read(&conversation))
    .output(out_place(&response))
    .timing(immediate())
    .action(fork())
    .build();

// Complete: deep wins the race — consumes Thinking + Processing, inhibited by Response
let complete = Transition::builder("Complete")
    .input(one(&thinking))
    .input(one(&processing))
    .inhibitor(inhibitor(&response))         // inhibitor: can't fire if quick already answered
    .reset(reset(&urgency))                  // reset arc: clears any pending urgency
    .output(out_place(&response))
    .timing(deadline(3000))                  // deadline: must complete within 3s of enablement
    .action(fork())
    .build();

// Dump: deep loses the race — consumes Thinking, reads Response (confirms quick answered)
//   no output: acts as a sink (discards the late deep result)
let dump = Transition::builder("Dump")
    .input(one(&thinking))
    .read(read(&response))                   // read: verifies quick already answered
    .timing(immediate())
    .action(fork())
    .build();

// AutoSummarize: fires when conversation reaches ≥3 messages (at_least input)
//   consumes threshold messages + resets remainder; delayed cooldown prevents churn
let auto_summarize = Transition::builder("AutoSummarize")
    .input(at_least(3, &conversation))       // at_least: need ≥3 messages
    .inhibitor(inhibitor(&summarizing))
    .reset(reset(&conversation))             // reset arc: clear remaining messages
    .output(out_place(&summarizing))
    .timing(delayed(2000))                   // delayed: 2s cooldown
    .action(fork())
    .build();

// ToolSummarize: external TopicChange trigger; reads Conversation, resets it
let tool_summarize = Transition::builder("ToolSummarize")
    .input(one(topic_change.place()))
    .read(read(&conversation))
    .inhibitor(inhibitor(&summarizing))
    .reset(reset(&conversation))
    .output(out_place(&summarizing))
    .timing(immediate())
    .action(fork())
    .build();

// SummaryDone: summarization completes — replaces old Summary
let summary_done = Transition::builder("SummaryDone")
    .input(one(&summarizing))
    .reset(reset(&summary))                  // reset arc: replace old summary
    .output(out_place(&summary))
    .timing(deadline(2000))
    .action(fork())
    .build();

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
```

<p align="center">
  <img src="https://raw.githubusercontent.com/debe/libpetri/main/rust/libpetri/doc/showcase.svg" alt="Racing LLM Agent Pipeline Petri Net">
</p>

All five arc types (input, output, **read**, **inhibitor**, **reset**), all five timing
modes (immediate, window, deadline, delayed, exact), environment places, priority
scheduling, AND-fork, dump semantics, and coloured tokens.

## Crate Structure

| Crate | Description |
|-------|-------------|
| **libpetri-core** | Places, tokens, transitions, timing, arc types, actions |
| **libpetri-event** | Event store for recording execution events |
| **libpetri-runtime** | Bitmap-based executor (sync + async via `tokio` feature) |
| **libpetri-export** | DOT/Graphviz export pipeline |
| **libpetri-verification** | Formal verification (P-invariants, state class graphs, SMT) |
| **libpetri-debug** | WebSocket debug protocol for live net inspection |
| **libpetri-docgen** | Build-script helper for generating Petri net SVGs in rustdoc |

## Executors

- **BitmapNetExecutor** — General-purpose, bitmap-based enablement checks
- **PrecompiledNetExecutor** — High-performance alternative with ring buffers, opcode dispatch, and two-level summary bitmaps (~3.8x faster on large nets)

## Feature Flags

| Feature | Effect |
|---------|--------|
| `tokio` | Enables `run_async()` on both executors |
| `z3` | Enables SMT-based IC3/PDR model checking |
| `debug` | Enables the WebSocket debug protocol module |

## License

Apache-2.0
