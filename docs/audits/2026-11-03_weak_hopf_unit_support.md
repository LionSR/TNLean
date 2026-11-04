# Weak-Hopf unit support without the identity at the blocking length, 3 November 2026

## Change

The weak-Hopf average of GLM23 Appendix B (arXiv:2203.12563v3,
lines 2463--2466) fixed the support projection, `E_n(P_n) = P_n`, only for
a state tensor injective at one site. For a tensor injective after blocking
`L > 1` sites it also assumed `Q_L = I`, where `Q_n = ρ_n(1)` is the
represented unit. That identity can fail when `Δ(1) ≠ 1 ⊗ 1`. The finite-set
weak Hopf algebra is one example.

Removed declaration:

- `MPOTensor.WeakHopfRepresentation.weakHopfAverage_starProjection_of_rep_eq_one`
  (hypotheses: block injectivity at `L > 0` and `W.rep L 1 = 1`).

Replacement, in `TNLean/MPS/Symmetry/WeakHopfParentAverage.lean`:

- `MPOTensor.WeakHopfRepresentation.weakHopfAverage_starProjection` now
  takes `Kraus.IsNBlkInjective A L` for any `L`, with no hypothesis on
  `W.rep L 1`. It is built on the unit-support theorem
  `MPOTensor.WeakHopfRepresentation.rep_one_mulVec_mpvWithBoundary`
  (`Q_n ψ^n_{A,X} = ψ^n_{A,X}` for every `n > 0`) and on
  `MPOTensor.WeakHopfRepresentation.toEuclideanLin_rep_one_comp_starProjection`
  (`Q_n P_n = P_n`). Both of these now take block injectivity as well.
- The other consequences in that file (Hermiticity and trace, the literal
  parent average `Q_n - P_n`, the ambient complement, its nonvanishing, and
  its commutation with every boundary operator) now take block injectivity
  instead of one-site injectivity. The same holds for
  `MPOTensor.FiniteSetWeakHopf.sum_rep_single_mul_starProjection_mul`.

## Argument

Multiplicativity of `ρ_m` for `m > 0` gives
`(I ⊗ Q_m) Q_{m+1} = Q_{m+1} = (Q_m ⊗ I) Q_{m+1}`. The supporting lemmas
are `rep_one_mulVec_cons`, `rep_one_mulVec_snoc`, and
`MPOTensor.weakHopfRep_succ_apply_last`. Hence the state boundaries `Z` with
`Q_m Γ_m(Z) = Γ_m(Z)` for all `m > 0` form a space that is stable under
multiplication by each letter on either side. Block injectivity then makes
this space a two-sided ideal of the bond matrix algebra.

Compatibility with the unit boundary, together with `Q_m^2 = Q_m`, puts
into the ideal, for each `X`, a boundary that agrees with `X` at one site,
where `Q_1 = I`. If the ideal has a nonzero element, it is everything.
Otherwise every one-site vector vanishes, and then so does every vector of
positive length.

The general boundary criteria in `TNLean/MPS/Symmetry/BoundaryUnitSupport.lean`
and `TNLean/MPS/Symmetry/BoundaryProjectionAverage.lean` are unchanged. They
still apply to an arbitrary operator tensor that has a boundary equal to the
identity at one injective length.

The paper-gap note `docs/paper-gaps/glm23_wha_parent_completion.tex` records
this resolution. Its remaining open item is the formal Bell-pair instance.
