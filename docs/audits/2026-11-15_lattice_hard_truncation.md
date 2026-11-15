# Hard truncation on a lattice of bounded interactions

Issue #9844 retained the general bounded-interaction statement of Arad,
Kuwahara and Landau (arXiv:1406.3898, Theorem 2.6, `thm:lowspec`,
`low70.tex` lines 719–748, truncation `def:Ht`, lines 684–697), which ALVV
(arXiv:1602.08828v2, Proposition 4.4 and Lemma 4.5, lines 894–968) quote and
apply only to chains. This note records its formalization with the same
explicit-cutoff conclusions as the chain theorem.

## Statement

`TNLean.Lattice.exists_region_hard_truncation_spectral_comparison` (with its
residual half `exists_region_hard_truncation_residuals`) takes:

- an arbitrary finite site set `ι` of local dimension `q ≥ 1`;
- a finite family of terms `h i` with `0 ≤ h i ≤ 1`, each supported on
  `D i ⊆ ι` with `|D i| ≤ k`;
- the degree bound: every site lies in at most `g` of the sets `D i`;
- `k, g ≥ 1` (no Hamiltonian is excluded: a family with degree at most `g`
  also has degree at most `g + 1`);
- a region `Λ ⊆ ι`.

The terms inside `Λ` form `H_in`, the terms disjoint from `Λ` form `H_out`,
and the `b` crossing terms form `Y`. The regional minima `e_in, e_out`, a
common regional ground vector, and the attained ground energies `E, E' ∈ [0, b]`
of `H = Σ h − (e_in + e_out)` and of
`F = min(H_in, e_in + t) + H_out + Y − (e_in + e_out)` are constructed. No
residual, minimum, eigenbasis, gap or decomposition is supplied.

For `η > 0` and `t ≥ η + 3b + 1`, with
`ξ = 4 g k (b + 1) exp(−(t − η − 3b − 1) / (2 g k))`:

- both restricted errors `‖(H − F)|_{T_H(E+η)}‖`, `‖(H − F)|_{T_F(E+η)}‖ ≤ ξ`;
- `λ_i(F) ≤ λ_i(H) ≤ λ_i(F) + ξ` whenever `λ_i(F) ≤ E + η`;
- `E' ≤ E ≤ E' + ξ`;
- for `δ > 0` and `η' = η + ξ + 2ξ √(⌈η/(2ξ)⌉/δ)`, the enlarged clipped space
  `T_F(E' + η')` is δ-close to `T_H(E + η)` and `T_H(E + η')` is δ-close to
  `T_F(E' + η)`.

For a nearest-neighbour chain `b ≤ 2`, `g = k = 2`, and the cutoff becomes
`η + 7`, matching `TNLean.MPS.AreaLaw.ALVV.exists_single_region_hard_truncation_spectral_comparison`.

## Deviations from the source

These are recorded as one **Local fix** marker on the module
`TNLean/Lattice/HardTruncation.lean`:

- **Cutoff.** The explicit sufficient `t ≥ η + 3b + 1` replaces the printed
  unrestricted `t > η`. The flat-sector chain of
  `TNLean.MPS.AreaLaw.HardTruncationCutoff` shows the truncated-side estimate
  fails under `t > η` alone; it is kept unchanged.
- **Constants.** The decay rate is `1/(2gk)` and the prefactor
  `4gk(b+1)`, from the commutator count below, rather than the printed
  `(6/λ^{3/2}) e^{−λ(Δτ − Δε − 3|L_∂|)}` and `33|L_∂|` constants. The sign of
  the exponent is the decaying one (ALVV's printed `e^{(t−η)/8+24}` grows).
- **Windows.** The closeness enlargement carries the ceiling window count and
  the ground shift, as in the QICLean-owned note
  https://sirui-lu.com/QICLean/paper-gaps/alvv16_hard_truncation_windows.pdf.

The source text of arXiv:1406.3898 was not available offline in this session;
the line ranges above are the ones recorded in the issue thread.

## Proof structure and shared core

- `TNLean/Lattice/BoundedDegreeImaginaryTime.lean`: `ad_H^m(O)` is a sum of at
  most `∏_{j<m} g(|S| + jk)` pieces of norm `≤ ‖O‖`, giving
  `‖ad_H^m O‖ ≤ (gk)^m m! ‖O‖` for `|S| ≤ k`, and the conjugation bound
  `‖e^{t(H−z)} O e^{−t(H−z)}‖ ≤ 2‖O‖` for `2gkt ≤ 1`
  (AKL `lem:Hadamard-bound`, lines 795–880).
- `TNLean/Algebra/ExpConjugation.lean`: the conjugation estimate with an
  arbitrary growth constant, derived from the existing rate-4 estimate by
  rescaling; the positive-contraction commutator bound moved here from the
  chain file.
- `TNLean/Algebra/WeightedLowRestriction.lean`: the weighted Sylvester
  restriction and the clipping-excess tail, stated from a conjugation bound on
  the boundary operator only. The chain theorems
  `exists_nearestNeighbour_weighted_low_restriction` and
  `norm_consecutive_regional_truncation_low_le` are now short instances of it,
  so the chain and lattice theorems share one proof of the spectral estimate.
- `TNLean/Lattice/DisjointRegionalGround.lean`: generalized from chain sites
  `Fin L` to an arbitrary finite site type; chain call sites are unchanged.

The chain theorem is not re-derived from the lattice one: its three-region
centring (`e : Fin 3`) and constant `32 e^{−(t−η)/8}` differ from the
two-region lattice form, and the translation would cost more than the shared
core already saves.
