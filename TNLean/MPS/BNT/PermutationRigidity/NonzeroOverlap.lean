import TNLean.Analysis.ConvergenceHelpers
import TNLean.MPS.FundamentalTheorem.Proportional
import TNLean.MPS.FundamentalTheorem.OverlapConvergenceAux
import TNLean.MPS.BNT.Basic
import TNLean.Spectral.SpectralGapRect
import TNLean.Spectral.SpectralGapNT
import TNLean.MPS.Overlap.Basic
import TNLean.MPS.Overlap.CastLemmas
import TNLean.MPS.Overlap.CastDecay

/-!
# Permutation rigidity for basis-of-normal-tensors (BNT) decompositions — Theorem 4.4
(paper hypotheses, no span-equality)

This module replaces the extra span-equality hypothesis used in
`PermutationRigidityPrimitive.lean` with the **paper-style** hypotheses from Theorem 4.4
(arXiv:2011.12127 / 1606.00608, primitive branch): proportionality of the full MPV
families together with explicit decompositions into BNT families.

It contains both directions of the key nonvanishing-overlap step and the resulting
full permutation / gauge-phase matching theorems, in both the injective and
irreducible trace-preserving settings.

The overlap arguments follow the Appendix-A strategy: take overlaps of the
proportional full states with individual block states and use the asymptotic
orthogonality inside each BNT family.

In canonical-form applications one first normalizes by the dominant weights, so the relevant
coefficient arrays are `(μ j / μ 0)^N`; the discarded dominant factors are absorbed into the
proportionality constant.

## Paper-faithfulness note

Both directions of the key non-decay step take the full symmetric hypothesis
set: dominant-block normalization on each side,
uniform sub-dominant coefficient bounds, per-side asymptotic block-orthonormality
(diagonal overlaps tend to `1`, off-diagonal overlaps tend to `0`), per-length
nonzero proportionality, and the BNT decomposition identities. This matches
CPSV16's hypothesis "$A$ and $B$ in canonical form" (arXiv:1606.00608, statement
of Theorem thm1) — the paper's CF concept implicitly carries the
dominant-block normalization and the per-block primitivity that gives
asymptotic orthonormality. Thus the displayed hypotheses are the explicit
A-side and B-side components of the source's canonical-form assumption; no
hypothesis is added beyond what the paper provides.
-/

open scoped BigOperators InnerProductSpace Matrix
open Filter Finset

namespace MPSTensor

/-! ## Key paper step: some mixed overlap does not decay

The argument follows arXiv:1606.00608 lines 1170-1192. The proof uses inner-product
manipulation of the BNT decompositions, asymptotic block-orthonormality, and the
dominant-block normalization. The linear-independence corollary supplies eventual
linear independence from asymptotic orthonormality; the contradiction step applies
this after showing that the relevant joint family is asymptotically orthonormal. -/

/-- Eventual linear independence for the union of two asymptotically orthonormal
MPV families whose mixed overlaps vanish.

Source: arXiv:1606.00608, lines 1170--1192, where the linear-independence
corollary is applied after adjoining a single block from one BNT family to the
other family.  This is the symmetric two-family generalization of that
linear-independence input. -/
lemma eventually_linearIndependent_of_two_family_overlap_tendsto_orthonormal
    {d : ℕ} {gA gB : ℕ} {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (k : Fin gB) → MPSTensor d (dimB k))
    (hA_self : ∀ j,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A j) N) atTop (nhds (1 : ℂ)))
    (hA_off : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (d := d) (A i) (A j) N) atTop (nhds 0))
    (hB_self : ∀ k,
      Tendsto (fun N => mpvOverlap (d := d) (B k) (B k) N) atTop (nhds (1 : ℂ)))
    (hB_off : ∀ k₁ k₂, k₁ ≠ k₂ →
      Tendsto (fun N => mpvOverlap (d := d) (B k₁) (B k₂) N) atTop (nhds 0))
    (hAB : ∀ j k,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (B k) N) atTop (nhds 0)) :
    ∀ᶠ N in atTop,
      LinearIndependent ℂ (fun x : Sum (Fin gA) (Fin gB) =>
        match x with
        | Sum.inl j => mpvState (d := d) (A j) N
        | Sum.inr k => mpvState (d := d) (B k) N) := by
  classical
  let C : (x : Sum (Fin gA) (Fin gB)) → MPSTensor d (Sum.elim dimA dimB x)
    | Sum.inl j => A j
    | Sum.inr k => B k
  have h_self : ∀ x,
      Tendsto (fun N => mpvOverlap (d := d) (C x) (C x) N) atTop
        (nhds (1 : ℂ)) := by
    intro x
    cases x with
    | inl j => simpa [C] using hA_self j
    | inr k => simpa [C] using hB_self k
  have h_cross : ∀ x y, x ≠ y →
      Tendsto (fun N => mpvOverlap (d := d) (C x) (C y) N) atTop
        (nhds (0 : ℂ)) := by
    intro x y hxy
    cases x with
    | inl i =>
        cases y with
        | inl j =>
            have hij : i ≠ j := by
              intro hij
              apply hxy
              simp [hij]
            simpa [C] using hA_off i j hij
        | inr k =>
            simpa [C] using hAB i k
    | inr k =>
        cases y with
        | inl i =>
            simpa [C] using tendsto_mpvOverlap_zero_swap (A i) (B k) (hAB i k)
        | inr l =>
            have hkl : k ≠ l := by
              intro hkl
              apply hxy
              simp [hkl]
            simpa [C] using hB_off k l hkl
  have hLI :=
    MPSTensor.eventually_linearIndependent_of_fintype_overlap_tendsto_orthonormal C h_self h_cross
  refine hLI.mono ?_
  intro N hN
  convert hN with x
  cases x <;> rfl

/--
**Key step of Theorem 4.4 (paper route).**

Source: arXiv:1606.00608, lines 1170–1192 (proof of Theorem thm1).

Assume we have two families `A j` and `B k` whose within-family overlaps are
asymptotically orthonormal, and that the *full* tensors `A_total` and `B_total`
are proportional MPV families with explicit decompositions into the families.

Then for each `k`, it is impossible that `mpvOverlap (A j) (B k)` tends to `0`
for all `j`.

**Unfaithful:** The proof body is currently `sorry`. The earlier proof relied
on the convergence-to-nonzero-limit hypotheses (`aLim`, `bLim`, `cLim`,
`haCoeff`, `hbCoeff`, `hc`, `haLim_ne`, `hbLim_ne`, `hcLim_ne`) — these were
removed because they are uninstantiable on the source's intended canonical-form
class once `‖μ_1‖ = 1` is in force. Documented in
`docs/paper-gaps/cpsv16_cf_normalization_and_proportional_comparison.tex`.

The source proof applies the linear-independence corollary directly: if all
overlaps with a fixed block `B k` decayed to zero, the joint family consisting
of the `A`-blocks together with that `B k` would be asymptotically orthonormal,
hence eventually linearly independent, contradicting the proportionality of the
full states.

The formal gap is the coefficient nonvanishing consumed by that argument.  The
current `ProportionalDecompositionData` records dominant normalization and
uniform bounds, but it does not yet record or derive, for each surviving block,
the per-length nonvanishing of the coefficient multiplying that block.  The
proof must recover this either from the canonical-form nonzero-weight data
(for the source's direct argument) or by first matching a dominant block and
then applying the argument to the remaining family.

Elimination: supply the missing coefficient nonvanishing from the
canonical-form data, or implement the dominant-block residual argument; tracked
in #1559 Stage C. -/
theorem exists_nonzero_overlap_of_proportional_decomp
    {d : ℕ}
    {gA gB : ℕ}
    {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    {DtotA DtotB : ℕ}
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (k : Fin gB) → MPSTensor d (dimB k))
    (A_total : MPSTensor d DtotA)
    (B_total : MPSTensor d DtotB)
    (aCoeff : ℕ → Fin gA → ℂ) (bCoeff : ℕ → Fin gB → ℂ)
    (c : ℕ → ℂ)
    (hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = ∑ j : Fin gA, (aCoeff N j) * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv B_total σ = ∑ k : Fin gB, (bCoeff N k) * mpv (B k) σ)
    (hProp : ∀ N (σ : Fin N → Fin d), mpv A_total σ = c N * mpv B_total σ)
    (hc_ne : ∀ N, c N ≠ 0)
    (hA_top_norm_one : ∀ N (h : 0 < gA), ‖aCoeff N ⟨0, h⟩‖ = 1)
    (hB_top_norm_one : ∀ N (h : 0 < gB), ‖bCoeff N ⟨0, h⟩‖ = 1)
    (hA_norm_le_one : ∀ N j, ‖aCoeff N j‖ ≤ 1)
    (hB_norm_le_one : ∀ N k, ‖bCoeff N k‖ ≤ 1)
    (hA_self : ∀ j,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A j) N) atTop (nhds (1 : ℂ)))
    (hA_off : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (d := d) (A i) (A j) N) atTop (nhds 0))
    (hB_self : ∀ k,
      Tendsto (fun N => mpvOverlap (d := d) (B k) (B k) N) atTop (nhds (1 : ℂ)))
    (hB_off : ∀ k₁ k₂, k₁ ≠ k₂ →
      Tendsto (fun N => mpvOverlap (d := d) (B k₁) (B k₂) N) atTop (nhds 0)) :
    ∀ k : Fin gB,
      ∃ j : Fin gA,
        ¬ Tendsto (fun N => mpvOverlap (d := d) (A j) (B k) N) atTop (nhds 0) := by
  -- Paper-faithful proof pending. The CPSV16 lines 1170-1192 argument follows
  -- The linear-independence corollary for asymptotically orthonormal MPV states:
  -- assuming all `mpvOverlap (A j) (B k) → 0`, the joint family
  -- `{V^N(A_j)}_j ∪ {V^N(B_k)}` is asymptotically orthonormal hence eventually
  -- LI; proportionality `V^N(A_total) = c_N V^N(B_total)` then forces
  -- linearly-dependent coefficient relations contradicting LI.
  -- The missing formal input is coefficient nonvanishing for the fixed block:
  -- either derive it from the canonical-form nonzero-weight data, or match a
  -- dominant block first and apply the argument to the remaining family.
  -- See `docs/paper-gaps/cpsv16_cf_normalization_and_proportional_comparison.tex`.
  sorry


/-! ## Symmetric key step (A-indexed)

For the block-count equality we also need the converse direction: for each `A j`, some overlap
with a `B k` does not decay.
-/

/--
**Key step of Theorem 4.4 (paper route), opposite direction.**

Source: arXiv:1606.00608, lines 1170–1192 (proof of Theorem thm1,
symmetric to `exists_nonzero_overlap_of_proportional_decomp`).

Under the same proportionality + decomposition hypotheses as
`exists_nonzero_overlap_of_proportional_decomp`, if the `A`-family overlaps
are asymptotically orthonormal, then for each `j` it is impossible that
`mpvOverlap (A j) (B k) → 0` for all `k`.

**Unfaithful:** Same situation as the companion theorem — proof body is
`sorry`, the deleted limit hypotheses are documented in
`docs/paper-gaps/cpsv16_cf_normalization_and_proportional_comparison.tex`,
elimination tracked in #1559 Stage C.

The two nonzero-overlap conclusions are related by interchanging the two
decompositions and replacing the proportionality scalar $c_N$ by $c_N^{-1}$.
This direction remains a separate Stage C statement until that interchange is
formalized as a single symmetric argument; the planned elimination is to prove
the joint right- and left-indexed conclusion at once, or derive one side from
the other after this scalar inversion step is available. -/
theorem exists_nonzero_overlap_of_proportional_decomp_left
    {d : ℕ}
    {gA gB : ℕ}
    {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    {DtotA DtotB : ℕ}
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (k : Fin gB) → MPSTensor d (dimB k))
    (A_total : MPSTensor d DtotA)
    (B_total : MPSTensor d DtotB)
    (aCoeff : ℕ → Fin gA → ℂ) (bCoeff : ℕ → Fin gB → ℂ)
    (c : ℕ → ℂ)
    (hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = ∑ j : Fin gA, (aCoeff N j) * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv B_total σ = ∑ k : Fin gB, (bCoeff N k) * mpv (B k) σ)
    (hProp : ∀ N (σ : Fin N → Fin d), mpv A_total σ = c N * mpv B_total σ)
    (hc_ne : ∀ N, c N ≠ 0)
    (hA_top_norm_one : ∀ N (h : 0 < gA), ‖aCoeff N ⟨0, h⟩‖ = 1)
    (hB_top_norm_one : ∀ N (h : 0 < gB), ‖bCoeff N ⟨0, h⟩‖ = 1)
    (hA_norm_le_one : ∀ N j, ‖aCoeff N j‖ ≤ 1)
    (hB_norm_le_one : ∀ N k, ‖bCoeff N k‖ ≤ 1)
    (hA_self : ∀ j,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A j) N) atTop (nhds (1 : ℂ)))
    (hA_off : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (d := d) (A i) (A j) N) atTop (nhds 0))
    (hB_self : ∀ k,
      Tendsto (fun N => mpvOverlap (d := d) (B k) (B k) N) atTop (nhds (1 : ℂ)))
    (hB_off : ∀ k₁ k₂, k₁ ≠ k₂ →
      Tendsto (fun N => mpvOverlap (d := d) (B k₁) (B k₂) N) atTop (nhds 0)) :
    ∀ j : Fin gA,
      ∃ k : Fin gB,
        ¬ Tendsto (fun N => mpvOverlap (d := d) (A j) (B k) N) atTop (nhds 0) := by
  -- Paper-faithful proof pending. Mathematically this is the A/B-swapped
  -- direction, with the proportionality scalar inverted at each length.
  sorry

end MPSTensor
