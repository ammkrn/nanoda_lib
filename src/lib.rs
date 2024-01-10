//! Placeholder:
//! ```ignore
//! Doc comment example
//! ```
#![allow(clippy::too_many_arguments)]

pub mod debug_printer;
pub mod env;
pub mod expr;
pub mod inductive;
pub mod level;
pub mod name;
pub mod parser;
pub mod pretty_printer;
pub mod quot;
pub mod tc;
#[cfg(test)]
mod tests;
pub mod union_find;
pub mod unique_hasher;
pub mod util;

pub(crate) const STACK_SIZE: usize = 16_777_216;
