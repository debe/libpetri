use std::env;
use std::fs;
use std::path::Path;
use std::process::Command;

fn main() {
    let out_dir = env::var("OUT_DIR").unwrap();
    let out_path = Path::new(&out_dir);

    // Check if `dot` is available
    let dot_available = Command::new("dot")
        .arg("-V")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false);

    // Basic chain: p1 -> t1 -> p2 -> t2 -> p3
    let basic_chain_dot = r##"digraph basic_chain {
  rankdir=LR;
  bgcolor="transparent";
  node [fontname="Helvetica" fontsize=10];
  edge [fontname="Helvetica" fontsize=9];

  p_p1 [label="p1" shape=circle style=filled fillcolor="#E8F5E9" color="#388E3C" penwidth=1.5];
  p_p2 [label="p2" shape=circle style=filled fillcolor="#FFFFFF" color="#1565C0" penwidth=1.5];
  p_p3 [label="p3" shape=circle style=filled fillcolor="#FFF3E0" color="#E65100" penwidth=1.5];
  t_t1 [label="t1" shape=box style=filled fillcolor="#E3F2FD" color="#1565C0" penwidth=1.5 width=0.3 height=0.6];
  t_t2 [label="t2" shape=box style=filled fillcolor="#E3F2FD" color="#1565C0" penwidth=1.5 width=0.3 height=0.6];

  p_p1 -> t_t1;
  t_t1 -> p_p2;
  p_p2 -> t_t2;
  t_t2 -> p_p3;
}"##;

    // Order processing pipeline (showcase)
    let showcase_dot = r##"digraph OrderProcessingPipeline {
  rankdir=LR;
  bgcolor="transparent";
  node [fontname="Helvetica" fontsize=10];
  edge [fontname="Helvetica" fontsize=9];

  p_Order [label="Order" shape=circle style=filled fillcolor="#E8F5E9" color="#388E3C" penwidth=1.5];
  p_Active [label="Active" shape=circle style=filled fillcolor="#FFFFFF" color="#1565C0" penwidth=1.5];
  p_Validating [label="Validating" shape=circle style=filled fillcolor="#FFFFFF" color="#1565C0" penwidth=1.5];
  p_InStock [label="InStock" shape=circle style=filled fillcolor="#FFFFFF" color="#1565C0" penwidth=1.5];
  p_PaymentOk [label="PaymentOk" shape=circle style=filled fillcolor="#FFFFFF" color="#1565C0" penwidth=1.5];
  p_PaymentFailed [label="PaymentFailed" shape=circle style=filled fillcolor="#FFFFFF" color="#1565C0" penwidth=1.5];
  p_Ready [label="Ready" shape=circle style=filled fillcolor="#FFFFFF" color="#1565C0" penwidth=1.5];
  p_Shipped [label="Shipped" shape=circle style=filled fillcolor="#FFF3E0" color="#E65100" penwidth=1.5];
  p_Rejected [label="Rejected" shape=circle style=filled fillcolor="#FFF3E0" color="#E65100" penwidth=1.5];
  p_Cancelled [label="Cancelled" shape=circle style=filled fillcolor="#FFF3E0" color="#E65100" penwidth=1.5];
  p_Overdue [label="Overdue" shape=circle style=filled fillcolor="#FFFFFF" color="#1565C0" penwidth=1.5];
  p_CancelRequest [label="CancelRequest" shape=circle style="filled,dashed" fillcolor="#F3E5F5" color="#7B1FA2" penwidth=1.5];

  t_Receive [label="Receive\nimmediate\npri=10" shape=box style=filled fillcolor="#E3F2FD" color="#1565C0" penwidth=1.5 width=0.3 height=0.6];
  t_Authorize [label="Authorize\n[200ms,5s]" shape=box style=filled fillcolor="#E3F2FD" color="#1565C0" penwidth=1.5 width=0.3 height=0.6];
  t_RetryPayment [label="RetryPayment\ndelayed 1s" shape=box style=filled fillcolor="#E3F2FD" color="#1565C0" penwidth=1.5 width=0.3 height=0.6];
  t_Approve [label="Approve\ndeadline 2s" shape=box style=filled fillcolor="#E3F2FD" color="#1565C0" penwidth=1.5 width=0.3 height=0.6];
  t_Ship [label="Ship\nimmediate" shape=box style=filled fillcolor="#E3F2FD" color="#1565C0" penwidth=1.5 width=0.3 height=0.6];
  t_Reject [label="Reject\nimmediate" shape=box style=filled fillcolor="#E3F2FD" color="#1565C0" penwidth=1.5 width=0.3 height=0.6];
  t_Cancel [label="Cancel\nimmediate" shape=box style=filled fillcolor="#E3F2FD" color="#1565C0" penwidth=1.5 width=0.3 height=0.6];
  t_Monitor [label="Monitor\nexact 10s" shape=box style=filled fillcolor="#E3F2FD" color="#1565C0" penwidth=1.5 width=0.3 height=0.6];

  p_Order -> t_Receive;
  t_Receive -> p_Active;
  t_Receive -> p_Validating;
  t_Receive -> p_InStock;
  p_Validating -> t_Authorize;
  t_Authorize -> p_PaymentOk [label="XOR"];
  t_Authorize -> p_PaymentFailed [label="XOR"];
  p_PaymentFailed -> t_RetryPayment;
  p_Overdue -> t_RetryPayment [style=dotted arrowhead=odot label="inhibitor"];
  t_RetryPayment -> p_PaymentOk [label="XOR"];
  t_RetryPayment -> p_PaymentFailed [label="XOR"];
  p_PaymentOk -> t_Approve;
  p_InStock -> t_Approve;
  t_Approve -> p_Ready;
  p_Ready -> t_Ship;
  p_Active -> t_Ship [style=dashed label="read"];
  p_Cancelled -> t_Ship [style=dotted arrowhead=odot label="inhibitor"];
  t_Ship -> p_Shipped;
  p_PaymentFailed -> t_Reject;
  p_Overdue -> t_Reject;
  p_InStock -> t_Reject [style=bold color="#D32F2F" label="reset"];
  t_Reject -> p_Rejected;
  p_CancelRequest -> t_Cancel;
  p_Shipped -> t_Cancel [style=dotted arrowhead=odot label="inhibitor"];
  p_Rejected -> t_Cancel [style=dotted arrowhead=odot label="inhibitor"];
  t_Cancel -> p_Cancelled;
  p_Active -> t_Monitor [style=dashed label="read"];
  p_Shipped -> t_Monitor [style=dotted arrowhead=odot label="inhibitor"];
  p_Rejected -> t_Monitor [style=dotted arrowhead=odot label="inhibitor"];
  p_Cancelled -> t_Monitor [style=dotted arrowhead=odot label="inhibitor"];
  p_Overdue -> t_Monitor [style=dotted arrowhead=odot label="inhibitor"];
  t_Monitor -> p_Overdue;
}"##;

    generate_svg(dot_available, out_path, "basic_chain", basic_chain_dot);
    generate_svg(dot_available, out_path, "showcase", showcase_dot);

    println!("cargo::rerun-if-changed=build.rs");
}

fn generate_svg(dot_available: bool, out_path: &Path, name: &str, dot_source: &str) {
    let dot_file = out_path.join(format!("{name}.dot"));
    let svg_file = out_path.join(format!("{name}.svg"));

    fs::write(&dot_file, dot_source).unwrap();

    if dot_available {
        let output = Command::new("dot")
            .args(["-Tsvg", dot_file.to_str().unwrap()])
            .output()
            .expect("failed to run dot");

        if output.status.success() {
            fs::write(&svg_file, output.stdout).unwrap();
            return;
        }
    }

    // Fallback: embed DOT source as HTML pre block
    let fallback = format!(
        "<pre><code>{}</code></pre>",
        dot_source.replace('<', "&lt;").replace('>', "&gt;")
    );
    fs::write(&svg_file, fallback).unwrap();
}
