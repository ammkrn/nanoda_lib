Basically what we're doing is putting all of the type checker's terms into arenas, and manipulating those terms as pointers into said arenas. The Rust part is that we use phantom data and phantom lifetimes to (for zero runtime cost) make sure that pointers into the backing arenas are type and memory safe. At compile time we know, modulo the correctness of Rust's type system, that an arena pointer always points to the right data, and that the backing storage cannot be dropped while there are still pointers into it, meaning we can never be stuck holding an invalid arena pointer. The insight is that we really only have two sets of Lean items with two unique lifetimes, one that holds the items needed to make the basic statements of 'theorem A : B := X' or 'inductive Q : R with constructors C1 .. Cn', and another set which holds the terms created in the process of checking that those terms are well-typed. This set of items is created and dropped with every new item checked/introduced, and is strictly less than the environment lifetime, since it's created after the environment is, and dropped before as well.

* Note to self about future work: when rust stabilizes the allocator api, the backing storage for all of the collections can be changed to use something like a bump allocator for the cost of one additional lifetime annotation. This should be a pretty big win since we'll no longer be allocating collections anew for every declaration and (more importantly) *all of the linked-list stuff can be replaced with `Vec<A, Bump>`*, which will remove all of the syntactic clutter (most prominent in `inductive.rs`) and make operations on sequences faster.

The benefits of using such a 'dumb' collection (dumb in the sense that does almost nothing to manage its memory) are that even though we're using arenas (which don't actively try to drop items that are no longer reachable) we have a smaller memory footprint than the other type checkers since our types are very small and our collections are defacto free of duplicates, and we get a pretty significant increase in speed (about 3-4x faster than the other reference checkers) for a variety of reasons. This arena based strategy also allows for working with expression graphs that contain cycles, though Lean doesn't need this. It also works very well in a parallel context, requiring no locks or atomics since the persistent environment is read-only by the time you start spawning threads, and the temporary storage for each new declaration is local.
The only real drawback is that pretty much every function needs to explicitly take a context as an argument, since you need the carry the arenas around, though this was already the case for all of the functions in the actual type checker module. Making the backing stores global to remove this requirement would start introducing locks and goofy wrappers and all that.

The underlying pointer type (utils::Ptr) consists of an enum discriminant (4 bytes) and a u32 showing its position in the arena (4 bytes), with two zero sized types which are essentially just for interfacing with the compiler's static analysis systems. Pretty much everything else is some combination of one or more of these pointers and an enum discriminant, so they range from 8 to 31 bytes. By far the most common item is an expression application node, which is 19 bytes.

In the course of checking a version of mathlib from August 2020 (06e1405), the export file produces a list of just over 12.5 million persistent items which need to be kept alive for the duration of the program. The largest temporary stores (the storage that's created, then dropped in the course of checking one declaration) are 10 million (polynomial.monic.next_coeff_mul) and ~1.6 million items (finset.sum_range_sub_of_monotone), but the average declaration produces under 100k temporary items (~3mb). 
The total number of attempted item allocations in mathlib is 1.2 billion, with duplicates outnumbering unique items 4:1 (~922 million rejections with duplicates, ~269 million unique items). 

The `basic.rs` example shows the basics of how to actually use the type checker; you can pass \
a number of threads, and an absolute path to an export file.\
An argument of zero threads will default to one thread.\
Example : 
```
cargo run --release --example basic 4 <path to your export file>
```

The `debug.rs` example only takes a file path argument; the checker will be run on 1 thread only, and the declaration names will be displayed as they're compiled and checked. It can be invoked as follows:
```
cargo run --release --example debug <path to export file>
```


