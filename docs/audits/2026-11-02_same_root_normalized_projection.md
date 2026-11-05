# Normalized projections into the same recursive root

The contribution is based on the checked source reconciliation
`18cb33218fcb2a31fee2da573463f3df461f55ce`. It adds the whole-interval
coordinate isometry and identifies viability on that interval with closeness
of its native image to the original full ground space.

For every unit ground vector, the actual native root projection is nonzero.
Its normalization lies in the same recursively constructed root, has squared
overlap at least 197/200 and squared distance at most 3/100. Its inner product
with the target is the nonnegative real norm of the unnormalized projection.
The entire recursive construction precedes this target vector. The witness
retains the native root's all-span bond bound, including its extra generator
count factor. No independent matrix product approximation replaces the root.

This is a constant-accuracy existential witness. The capped gap, block
leaves and one final trim remain explicit. It does not perform the source's
final filter-and-trim iteration or Ritz extraction and does not establish
adaptive joint probability or computational cost. Those obligations are
recorded in `docs/paper-gaps/alvv16_approximation_parameters.tex`.

## Verification

The two actual modules were checked separately against immutable warmed
TNLean 5fc343a57d and its own QICLean ba017 dependency, with explicit privately
checked tree objects and the normalized-projection leaf from QICLean
ca0aea30. Selected source, object and build-input hashes remained fixed.
The coordinate module passed in 7.295 seconds; the physical witness passed in
14.453 seconds over 740 selected source-object pairs.

The preserved uncompiled draft needed explicit coercion changes from a
linear-equivalence application to its isometry application, the current
Mathlib name `Finset.notMem_empty`, and removal of two unnecessary tactic
focus combinators. Its mathematical statements and hypotheses are unchanged.
The five imported public declarations, including the simp theorem, use only
`propext`, `Classical.choice` and `Quot.sound`; this audit passed in
9.085 seconds. Its temporary source was deleted.

The isolated source tree has no Lake directory. No provider or cache was
modified, no build artifacts were copied and Mathlib was not rebuilt.
Ordinary combined dependency, full-library, regression, compiled blueprint
and quiet timing checks remain required.
