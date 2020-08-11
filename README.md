
As of 2/7/20 the master branch has been converted to (among other things)
use arenas as the primary means of storage in addition to having a generally
nicer implementation. In particular the inductive module is now simple recursive
functions over immutable lists, whereas before there were some pretty sketchy spots
involving a lot of mutable state.

The arena setup is fairly small and uses a combination
of phantom data and zero-sized types to ensure that all arena operations are memory and type safe.

The switch produced a type checker that's significantly (~3x) faster and uses much less memory compared to both its predecessor and the other reference typecheckers. I think arena based memory management is actually really strong for this kind of application.

I'm busy with some related work at the moment, but I'd eventually like to write some kind
of retrospective or paper on the implementation just to show that this as a viable 
if not preferrable solution for memory management in ITPs. If anyone would like to help 
or is working on something similar please contact me.

The executable example shows the basics of how to actually use the type checker; you can pass \
a number of threads, and an absolute path to an export file.\
An argument of zero threads will default to one thread.\
Example : 
```
cargo run --release --example basic 4 /home/computer/lean/core.out
```
