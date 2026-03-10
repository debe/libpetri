use libpetri_docgen::*;
use libpetri_docgen::export::mapper::DotConfig;
use libpetri_docgen::export::graph::RankDir;
use std::collections::HashSet;

fn main() {
    generate_svg("basic_chain", &basic_chain());

    SvgGenerator::new()
        .config(DotConfig {
            direction: RankDir::LeftToRight,
            environment_places: HashSet::from(["CancelRequest".to_string()]),
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

/// Order processing pipeline showcasing all arc types, timing modes, and patterns.
fn showcase() -> PetriNet {
    let order = Place::<String>::new("Order");
    let active = Place::<String>::new("Active");
    let validating = Place::<String>::new("Validating");
    let in_stock = Place::<String>::new("InStock");
    let payment_ok = Place::<String>::new("PaymentOk");
    let payment_failed = Place::<String>::new("PaymentFailed");
    let ready = Place::<String>::new("Ready");
    let shipped = Place::<String>::new("Shipped");
    let rejected = Place::<String>::new("Rejected");
    let cancelled = Place::<String>::new("Cancelled");
    let overdue = Place::<String>::new("Overdue");
    let cancel_request = Place::<String>::new("CancelRequest");

    let receive = Transition::builder("Receive")
        .input(one(&order))
        .output(and(vec![out_place(&active), out_place(&validating), out_place(&in_stock)]))
        .timing(immediate())
        .priority(10)
        .action(fork())
        .build();

    let authorize = Transition::builder("Authorize")
        .input(one(&validating))
        .output(xor_places(&[&payment_ok, &payment_failed]))
        .timing(window(200, 5000))
        .action(fork())
        .build();

    let retry_payment = Transition::builder("RetryPayment")
        .input(one(&payment_failed))
        .output(xor_places(&[&payment_ok, &payment_failed]))
        .inhibitor(inhibitor(&overdue))
        .timing(delayed(1000))
        .action(fork())
        .build();

    let approve = Transition::builder("Approve")
        .input(one(&payment_ok))
        .input(one(&in_stock))
        .output(out_place(&ready))
        .timing(deadline(2000))
        .action(fork())
        .build();

    let ship = Transition::builder("Ship")
        .input(one(&ready))
        .read(read(&active))
        .inhibitor(inhibitor(&cancelled))
        .output(out_place(&shipped))
        .timing(immediate())
        .action(fork())
        .build();

    let reject = Transition::builder("Reject")
        .input(one(&payment_failed))
        .input(one(&overdue))
        .reset(reset(&in_stock))
        .output(out_place(&rejected))
        .timing(immediate())
        .action(fork())
        .build();

    let cancel = Transition::builder("Cancel")
        .input(one(&cancel_request))
        .inhibitor(inhibitor(&shipped))
        .inhibitor(inhibitor(&rejected))
        .output(out_place(&cancelled))
        .timing(immediate())
        .action(fork())
        .build();

    let monitor = Transition::builder("Monitor")
        .read(read(&active))
        .inhibitor(inhibitor(&shipped))
        .inhibitor(inhibitor(&rejected))
        .inhibitor(inhibitor(&cancelled))
        .inhibitor(inhibitor(&overdue))
        .output(out_place(&overdue))
        .timing(exact(10000))
        .action(fork())
        .build();

    PetriNet::builder("OrderProcessingPipeline")
        .transition(receive)
        .transition(authorize)
        .transition(retry_payment)
        .transition(approve)
        .transition(ship)
        .transition(reject)
        .transition(cancel)
        .transition(monitor)
        .build()
}
