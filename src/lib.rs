#![forbid(unsafe_code)]
#![allow(unused_parens)]
#![allow(non_snake_case)]

#[cfg(feature = "mimalloc")]
#[global_allocator]
static GLOBAL: mimallocator::Mimalloc = mimallocator::Mimalloc;

pub mod utils;
pub mod errors;
pub mod name;
pub mod level;
pub mod expr;
pub mod tc;
pub mod env;
pub mod quot;
pub mod inductive;
pub mod recursor;
pub mod serial_parser;
pub mod pp;

#[cfg(test)]
mod tests {
    //use super::*;
}
