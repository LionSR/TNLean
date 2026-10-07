# One-species PVBS ground spaces

The model follows Bachmann and Nachtergaele, arXiv:1112.4097, Section II,
equations (1)–(8), with left-to-right word order and complex hopping
q = μ exp(iθ). The review arXiv:2011.12127 uses q = 1 + λ. The source
comparison and critical-value correction are in
[`cpgsv21_pvbs_threshold`](../paper-gaps/cpgsv21_pvbs_threshold.tex).

## Reuse and complete statements

- The vacuum is Mathlib `Pi.single`, and the raising matrix and critical W
  state reuse `Examples.WState`.
- The actual open parent Hamiltonian uses the existing Euclidean-space
  projector definition. Its kernel is exactly the vacuum-particle span and
  has dimension two for every length at least two, including q = 0 and q = 1.
- A model-specific restriction intersection lemma feeds the existing general
  contiguous-window induction. No parallel Hamiltonian or generic
  ground-space representation is introduced.
- Existing cyclic-translation covariance forces b = b q^N. Thus the actual
  periodic parent kernel is the one-dimensional vacuum span if q^N ≠ 1.
  The size-independent sufficient condition is ‖q‖ ≠ 1.
- A two-site W state is a concrete critical periodic counterexample.
- Mathlib convergence of geometric powers proves left localization and right
  localization relative to the final-site amplitude.

All statements allow complex hopping. The endpoint q = 0 extends the
primary source's positive hopping family algebraically. Fixed-size
nonresonance on the unit circle does not assert a uniform spectral gap.
The original multi-species construction and its spectral-gap estimates are
outside this one-species finite-chain result.
