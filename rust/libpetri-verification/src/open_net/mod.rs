//! Open-net verification: a subnet checked in isolation against a contract, with its
//! ports played by the environment ([VER-022]). Entry point: [`verify_open_net`].
//!
//! A caller that builds its nets from a fixed vocabulary of subnets can prove each subnet
//! once. A proof then costs what the subnet costs rather than what the interleavings of
//! the composed net cost; the composition argument stays the caller's own.
//!
//! ```ignore
//! use libpetri_verification::open_net::{OpenNetContract, OpenNetOptions, verify_open_net};
//!
//! let contract = OpenNetContract::builder()
//!     .initial_tokens("X/idle", 1)
//!     .initial_tokens("_budget", 1)
//!     .arrive(1, ["X/in", "X/in_empty"])       // exactly one arrival on the input edge
//!     .arrive_at_most(1, ["_halt"])            // never or once
//!     .expect("e1", 1, ["e1/data", "e1/empty"])
//!     .expect("budget", 1, ["_budget"])
//!     .terminal("_halt", ["X/in", "X/in_empty"])
//!     .build();
//! let result = verify_open_net(&net, &contract, &OpenNetOptions::default());
//! println!("{}", result.report);
//! ```
//!
//! The module is split the way the TypeScript reference is, so the two can be read side
//! by side: the contract and its builder, the closure that turns the contract's
//! environment into net structure, the one predicate both routes judge a quiescent
//! marking by, the graph route, the SMT route, the result types and the report. Only the
//! contract, the closure, the options, the entry point and the result types are public;
//! the routes and the predicate are internal, because a second caller of them is exactly
//! how the two routes would stop judging the same sets.

mod closure;
mod contract;
mod graph_route;
mod predicate;
mod report;
mod result;
mod smt_route;
mod verify_open_net;

#[cfg(test)]
mod tests;

pub use closure::{ClosedNet, EnvironmentStep, EnvironmentStepKind, close_open_net};
pub use contract::{
    ArrivalGroup, CountClause, DesignedTerminal, OpenNetContract, OpenNetContractBuilder,
};
pub use result::{
    ContractViolation, ContractViolationKind, OpenNetResult, OpenNetRoute, PortChange, PortStep,
};
pub use verify_open_net::{OpenNetOptions, SmtConfigurator, verify_open_net};
