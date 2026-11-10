# Normalized projections into the same recursive root

It adds the whole-interval coordinate isometry and identifies viability on
that interval with closeness of its native image to the original full ground
space.

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
