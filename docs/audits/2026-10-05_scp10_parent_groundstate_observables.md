# SCP10 6.7–6.10: actual regular parent ground states

## Source and scope

The source is `Papers/1001.3807/paper_v3.tex`, arXiv:1001.3807v3:
Theorem 6.7 (lines 1995–2015), Corollary 6.8 (2017–2025),
Theorem 6.9 (2027–2072), and Corollary 6.10 (2074–2090).

The new capstones start with an arbitrary physical vector in the kernel of
`regionParentHamiltonian torusPlaquetteRegion P`. Each existing
`IsRegionParentInteraction` premise requires positivity and the genuine
regional-range kernel. The parent Hamiltonian and the region geometry are
unchanged. The regular native torus has both periods at least three, with one tensor
repeated at every site.
A region has a connected induced occupied nearest-neighbour graph and a
simply connected actual closed-cell realization. These are independent
conditions, as diagonal closed-cell contacts need not connect the occupied
graph. The two stripes are exactly the coordinate-zero row and column.

## Gap closed

The earlier entropy and local-equivalence theorems assumed a supplied
finite commuting-closure superposition. The full regular parent-kernel
classification already identified the actual kernel with that span, but
no observable/entropy capstone accepted an arbitrary kernel vector.
`IsGInjective.exists_torusGClosure_sum_of_mem_parentKernel` now extracts
coefficients using finite span membership. Restriction and reassembly prove
that the cut of any nonzero global vector is nonzero.

Consequently the existing closure-family theorems give, for every actual
nonzero parent ground vector in the stated scope:

- 6.7: a physical unitary on two width-one stripes between any two normalized
  vectors; more generally a complementary unitary for the stated region.
- 6.8: equality of every normalized local operator expectation.
- 6.9: one common positive normalized reduced density, rank `|G|^(b-1)`,
  the flat-spectrum identity `ρ² = |G|^(-(b-1)) ρ`, von Neumann entropy
  `(b-1) log |G|`, and every finite real nonnegative-order Rényi entropy
  with the same value. Here `b` is the actual crossing-bond count.
- 6.10: with only regular G-injectivity, the same reduced-density rank and
  zero-order Rényi entropy, without a flat-spectrum assertion.

No closure expansion, boundary rank, exterior loop, cut nonvanishing,
normalization constant, or parent-kernel identification is assumed anew.
Coefficient extraction also covers the zero ground vector; normalized
observables and entropy correctly require a nonzero vector.

## Remaining restrictions

This closes the arbitrary-parent-vector bridge only within the already
proved regular native-torus/region scope. It does not assert paper-wide
completion, smaller torus periods, arbitrary semi-regular observable
formulas, nonuniform/link-dependent tensors, disconnected occupied blocks,
negative or infinite Rényi orders, or MPU-gauging results. The broader
paper-gap note should retain those distinctions.

## Integration

All changes are new files. Add the production module to the generated root
imports, include
`chapter/ch24_peps_parent_ground_state_observables` in the PEPS blueprint,
and regenerate `blueprint/lean_decls` when integrating. The new blueprint
contains five public declaration tags and four mathematical entries.
The existing paper-gap note's closure-family discussion can now be updated
to include every nonzero actual regular parent ground vector, retaining the
scope above.

## Validation

The production module and its regression file are checked with pinned Lean
4.35.0-rc3, strict implicit arguments, Mathlib standard linters, and
warnings-as-errors. The final capstone and test builds took 3.96 s and
4.61 s in this workspace. Regressions start from the actual matrix equation
`H *ᵥ ψ = 0` for arbitrary physical vectors, plus a zero-vector expansion
case. Guarded dependency checks for all five public capstones permit only
`propext`, `Classical.choice`, and `Quot.sound`.

The final imported closure contains 230 TNLean/QICLean modules. There were
38 fresh private builds across dependency preparation and the two new files;
192 pre-existing artifacts were reused with checked provenance.
Dependencies are validated in a private overlay: actual TNLean and pinned
QICLean import sources are SHA-256 matched, reused artifacts are checked
against prior source-and-artifact provenance, and missing TNLean modules
are compiled afresh. Mathlib is reused at the pinned revision and is never
rebuilt. No aggregate/root build or full-repository CI pass is claimed.
