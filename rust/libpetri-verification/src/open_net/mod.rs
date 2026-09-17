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
//! Split as the TypeScript reference is: contract, closure, the one predicate both routes
//! judge quiescence by, graph route, SMT route, results and report. The routes and the
//! predicate stay private, so both routes keep judging the same sets.

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
