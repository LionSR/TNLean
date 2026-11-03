# Two actual regional soft residuals with derived reverse coercivity

The new physical theorem constructs exact regional minimum energies, normalized
attaining vectors and the original centered ground energy from the raw positive
unit nearest-neighbour interactions. These data precede the soft scale and order.
For each positive scale and order at least two, it constructs the same actual
soft replacement and an attained soft ground energy before every spectral width
and auxiliary tail cutoff. No physical residual, successful approximation,
spectral gap, simple ground space or soft-energy bound is supplied.

Positivity of the actual regional terms and crossing bonds gives positivity of
the soft Hamiltonian. Its order below the original centered Hamiltonian, tested
against the constructed original ground vector, gives 0 <= mu <= E <= 2. The
upper bound is relative to the derived sum of regional minima, not an assertion
that the uncentered original ground energy is at most two.

The source geometry supplies a crossing set of cardinality at most two. The
existing private counting proof is exposed unchanged. Regional support
commutation gives a commuting interior soft sum; the actual scalar high-energy
floor gives its original high-projection lower bound. Neither a boundary count,
commutation relation nor coercive projection order is assumed by the physical
theorem.

For reverse width eta >= 0, choose U = 2(eta+8). If the actual soft scale and the
auxiliary tail cutoff are at least U, the polynomial remainder at U is at most
U/2. The resulting floor is at least eta+8. Only after substituting the derived
mu <= 2 and actual crossing-cardinality <= 2 does the proof obtain a Sylvester
denominator at least two. The existing weighted restriction theorem is reused
with distinct floor and projection threshold; its map and its norm bound are
constructed from the original local boundary interactions. The hard-excess
factorization and the checked soft-hard norm comparison then give the reverse
residual 16 exp(-(T-U)/8) + (t/m)(T/t)^m on the actual soft low-energy space.
The same operator retains the original-side residual from the preceding
physical theorem. The scales and Taylor order are independent.

The auxiliary covers empty regions, coincident cuts, endpoint cuts, local
dimension one and the zero-site indexed chain. Its normalized ground vectors
are constructed from positive local dimension; no extra dimension or gap
premise is introduced. The low-energy spaces contain every eigenvector below
the closed cutoff, including all degeneracies.

The exact energy centers are a scope restriction relative to ALVV,
arXiv:1602.08828v2, Definition `def:soft-trunc`, lines 1178–1185, which permits
any estimate in the ten-unit interval below each minimum. The restriction and
a concrete shifted-energy elimination plan are recorded in
`docs/paper-gaps/alvv16_soft_regional_residuals.tex`. The new statement has its
own corrected auxiliary book label. It does not assert the printed uniform
energy estimate, its spectral enlargement, estimated-center uniformity,
several simultaneous replacements or the final GEN and running-time bounds.
The existing cluster counterexamples and their false-source status remain.

All checks read immutable fully built TNLean
`994a1963ab36a234e1b02689a13bf1da965573b2` and its own QICLean
`67a788fdb9660c16c70c97bf36be5da6bbbaa348`. The exposed existing counting
module passed strict checking in 8.395 seconds; its unchanged existing hard
importer passed in 7.136 seconds. The existing original-side module was freshly
checked after its scope documentation was added, in 6.618 seconds. The final
new physical module passed in 7.309 seconds with 122 selected source/object
pairs guarded. An imported audit of the newly exposed counting declaration,
the preceding original-side theorem and the new two-sided theorem passed in
4.531 seconds; each reports only propext, Classical.choice and Quot.sound.

Selected sources, objects, build inputs and the prebuilt Mathlib record were
guarded. All outputs and temporary foundation commands remain under /tmp.
The source worktree has no .lake directory. No shared provider, dependency
cache or Mathlib source was changed. The ordinary integrated full-library,
compiled-book and paper-gap-document checks remain pending. No permanent
Lean test fixture is added.
