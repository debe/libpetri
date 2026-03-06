//! Order processing pipeline demonstrating async dispatch with the libpetri API.
//!
//! 3 typed places, 2 transitions with real actions and timing, DOT export,
//! async execution via Tokio.

use libpetri::*;
use libpetri::runtime::environment::ExternalEvent;

#[tokio::main]
async fn main() {
    // Define typed places
    let order = Place::<String>::new("order");
    let validated = Place::<String>::new("validated");
    let fulfilled = Place::<String>::new("fulfilled");

    // Validate: read the order, check it, produce a validated result (5s deadline)
    let validate = Transition::builder("validate")
        .input(one(&order))
        .output(out_place(&validated))
        .timing(deadline(5000))
        .action(async_action(|mut ctx| async move {
            let order_id: std::sync::Arc<String> = ctx.input("order")?;
            // simulate async validation work
            tokio::task::yield_now().await;
            ctx.output("validated", format!("{order_id} [valid]"))?;
            Ok(ctx)
        }))
        .build();

    // Fulfill: consume validated order, produce fulfillment confirmation
    let fulfill = Transition::builder("fulfill")
        .input(one(&validated))
        .output(out_place(&fulfilled))
        .action(async_action(|mut ctx| async move {
            let validated_order: std::sync::Arc<String> = ctx.input("validated")?;
            tokio::task::yield_now().await;
            ctx.output("fulfilled", format!("{validated_order} -> shipped"))?;
            Ok(ctx)
        }))
        .build();

    // Build the net
    let net = PetriNet::builder("OrderProcessing")
        .transition(validate)
        .transition(fulfill)
        .build();

    // Export to DOT
    println!("=== DOT Export ===\n");
    println!("{}", dot_export(&net, None));

    // Set up initial marking and run async
    let mut marking = Marking::new();
    marking.add(&order, Token::at("ORD-001".to_string(), 0));

    let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
        &net,
        marking,
        ExecutorOptions::default(),
    );
    let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExternalEvent>();
    executor.run_async(rx).await;

    // Inspect result
    println!("=== Result ===\n");
    match executor.marking().peek(&fulfilled) {
        Some(value) => println!("Fulfilled: {value}"),
        None => println!("No token in 'fulfilled'"),
    }
}
