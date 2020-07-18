
Some notes :

If you want something changed, you can change the spec and file a PR and I'll make the corresponding changes in the Rust codebase.
If nothing else, I'm assuming there's going to be some refinement 
of what does and doesn't need to appear in the export file.

The stuff I was told can be handled natively by mm1/mm0 has been 
removed; the only list functions still handled by utils and printed
explicitly are noDupes, isSubset, and Pos since those deal with
object equality. You can remove those and PR it if you want those
taken out too.

Some steps have comments indicating some assertion where the list of hypotheses
is, IE `ASSERT : length a = length b`.
A proof/trace of these assertions will not be provided in the output file,
and its up to verifiers to enforce these properties, though they are enforced
in the source code of the type checker.
These only appear in places where the property should be easy for verifiers
to check, but would be really difficult and/or inefficient for the rust program
to export a proof of, like equality of two natural numbers.

I've tried my best to ensure that the number and order of items/fields 
match between the Lean spec and the actual output. For some inductive
in the Lean spec, all items should appear in the output file (from left
to right) as :

params
constructor args
any items in a `let .. in ..` block
hypotheses

In some cases (especially for smaller items) the `let .. in ..` patterns 
are a bit cumbersome, but I think it's far superior to the alternative
of the spec and the implementation just totally diverging.

In cases where an item is invariant, it won't be in the block of let bindings
and won't appear explicitly as an item in the printed step. For example,
in `Level.Leq`, the call to `leqCore` is always called
with height numbers of zero, so the zeroes are just placed in-line,
and aren't printed as literals in the export file.

** The actual source of truth you should consult for how things are going to be
printed is the `/nanoda_lib/src/trace/step.rs` since that's where function that
determines the formatting is actually derived. For some enum representing
an step in the spec, the fields will be printed (as they appear in the rust file)
top to bottom |-> left to right, with no field omitted.
There's no automation to enforce the two being exactly the same, so I'm sure there's
at least one place where I left out or swapped fields. I HIGHLY recommend you have
both the spec file and step.rs open side-by-side.

With respect to handling of the environment :

Whenever `env.getDeclar` appears as a hypothesis in the spec, what will 
actually appear in the output is a pointer to the `AdmitDeclar` step at 
which that declaration was added to the environment.
IE :
`env.getDeclar n (Definition n ups t v hint is_unsafe)`
will appear as
`<step_num> . AD . D . ..stuff..`

For steps that add declarations to the environment, which in some way step from 
some `env` to a new `env'`, the original `env` will be a pointer to the most recent `AdmitDeclar` step, indicating the most recent iteration of the environment.
