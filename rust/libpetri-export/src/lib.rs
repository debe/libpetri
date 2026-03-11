//! # libpetri-export — DOT/Graphviz Export Pipeline
//!
//! Converts a [`PetriNet`](libpetri_core::petri_net::PetriNet) into a
//! DOT string for Graphviz rendering.
//!
//! ## Architecture
//!
//! The pipeline has four layers, separating concerns cleanly:
//!
//! ```text
//! PetriNet ──► map_to_graph() ──► Graph ──► render_dot() ──► DOT string
//!              (knows Petri nets)           (format-agnostic)
//! ```
//!
//! 1. **Styles** ([`styles`]) — Color/shape constants from the shared spec
//! 2. **Graph model** ([`graph`]) — Format-agnostic typed graph (nodes, edges, clusters)
//! 3. **Mapper** ([`mapper`]) — Petri net → Graph (place classification, arc styling)
//! 4. **Renderer** ([`dot_renderer`]) — Graph → DOT string (no Petri net knowledge)
//!
//! ## Quick Start
//!
//! ```rust
//! use libpetri_core::place::Place;
//! use libpetri_core::transition::Transition;
//! use libpetri_core::petri_net::PetriNet;
//! use libpetri_core::input::one;
//! use libpetri_core::output::out_place;
//! use libpetri_core::action::fork;
//! use libpetri_export::dot_exporter::dot_export;
//!
//! let p1 = Place::<i32>::new("input");
//! let p2 = Place::<i32>::new("output");
//!
//! let t = Transition::builder("process")
//!     .input(one(&p1))
//!     .output(out_place(&p2))
//!     .action(fork())
//!     .build();
//!
//! let net = PetriNet::builder("example").transition(t).build();
//! let dot = dot_export(&net, None);
//!
//! assert!(dot.contains("digraph"));
//! ```
//!
//! ## Example Output
//!
#![doc = include_str!("../doc/export_example.svg")]
//!
//! ## Configuration
//!
//! [`DotConfig`](mapper::DotConfig) controls rendering:
//!
//! | Field | Default | Effect |
//! |-------|---------|--------|
//! | `direction` | `TopToBottom` | Graph layout direction |
//! | `show_types` | `true` | Display place token types |
//! | `show_intervals` | `true` | Display timing intervals on transitions |
//! | `show_priority` | `true` | Display priority values |
//! | `environment_places` | `{}` | Place names styled as external event sources |
//!
//! ## Visual Vocabulary
//!
//! - **Green** circles — start places (no incoming arcs)
//! - **Blue** circles — end places (no outgoing arcs)
//! - **Red** dashed circles — environment places (external event injection)
//! - **Solid** arrows — input/output arcs
//! - **Dashed** arrows — read arcs
//! - **Dot-headed** arrows — inhibitor arcs
//! - **Double** arrows — reset arcs

pub mod dot_exporter;
pub mod dot_renderer;
pub mod graph;
pub mod mapper;
pub mod styles;
