import TNLean.MPS.FundamentalTheorem.Proportional
import TNLean.MPS.FundamentalTheorem.OverlapConvergenceAux
import TNLean.Algebra.GramMatrixLI
import TNLean.Spectral.SpectralGapRect
import TNLean.Spectral.SpectralGapNT
import TNLean.MPS.Overlap.Basic
import TNLean.MPS.Overlap.CastLemmas
import TNLean.MPS.Overlap.CastDecay

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

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

Both `exists_nonzero_overlap_of_proportional_decomp` and the `_left` companion take the
full symmetric hypothesis set: dominant-block normalization on each side,
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
dominant-block normalization. Lemma Lem1 supplies eventual linear independence
from asymptotic orthonormality; the contradiction step applies this after showing
that the relevant joint family is asymptotically orthonormal. -/

/-- Eventual linear independence for the union of two asymptotically orthonormal
MPV families whose mixed overlaps vanish.

Source: arXiv:1606.00608, lines 1170--1192, where Corollary Lem1 is applied
to the joint family obtained by adjoining a block from one BNT family to the
other side.  This is the direct joint-family form of that linear-independence
input. -/
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
  let V := lp (fun N : ℕ => MPVSpace d N) 2
  let v : Sum (Fin gA) (Fin gB) → ℕ → V := fun x N =>
    match x with
    | Sum.inl j => lp.single 2 N (mpvState (d := d) (A j) N)
    | Sum.inr k => lp.single 2 N (mpvState (d := d) (B k) N)
  have hGram : ∀ x y : Sum (Fin gA) (Fin gB),
      Tendsto (fun N => ⟪(v x N), (v y N)⟫_ℂ) atTop
        (nhds (if x = y then (1 : ℂ) else 0)) := by
    intro x y
    cases x with
    | inl i =>
        cases y with
        | inl j =>
            by_cases h : i = j
            · subst j
              have h1 :
                  Tendsto (fun N =>
                    ⟪mpvState (d := d) (A i) N, mpvState (d := d) (A i) N⟫_ℂ)
                    atTop (nhds (1 : ℂ)) := by
                simpa [mpvInner] using tendsto_inner_one (A i) (hA_self i)
              have h2 :
                  Tendsto (fun N => ⟪v (Sum.inl i) N, v (Sum.inl i) N⟫_ℂ)
                    atTop (nhds (1 : ℂ)) := by
                refine h1.congr fun N => ?_
                simp only [v]
                rw [lp.inner_single_left, lp.single_apply_self]
              simpa using h2
            · have h1 :
                  Tendsto (fun N =>
                    ⟪mpvState (d := d) (A i) N, mpvState (d := d) (A j) N⟫_ℂ)
                    atTop (nhds (0 : ℂ)) := by
                simpa [mpvInner] using tendsto_inner_zero (A i) (A j) (hA_off i j h)
              have h2 :
                  Tendsto (fun N => ⟪v (Sum.inl i) N, v (Sum.inl j) N⟫_ℂ)
                    atTop (nhds (0 : ℂ)) := by
                refine h1.congr fun N => ?_
                simp only [v]
                rw [lp.inner_single_left, lp.single_apply_self]
              simpa [h] using h2
        | inr k =>
            have h1 :
                Tendsto (fun N =>
                  ⟪mpvState (d := d) (A i) N, mpvState (d := d) (B k) N⟫_ℂ)
                  atTop (nhds (0 : ℂ)) := by
              have hinner : Tendsto (fun N => mpvInner (d := d) (A i) (B k) N)
                  atTop (nhds 0) :=
                tendsto_inner_zero (A i) (B k) (hAB i k)
              simpa [mpvInner] using hinner
            have h2 :
                Tendsto (fun N => ⟪v (Sum.inl i) N, v (Sum.inr k) N⟫_ℂ)
                  atTop (nhds (0 : ℂ)) := by
              refine h1.congr fun N => ?_
              simp only [v]
              rw [lp.inner_single_left, lp.single_apply_self]
            simpa using h2
    | inr k =>
        cases y with
        | inl i =>
            have hBA :
                Tendsto (fun N => mpvOverlap (d := d) (B k) (A i) N) atTop
                  (nhds 0) :=
              tendsto_mpvOverlap_zero_swap (A i) (B k) (hAB i k)
            have h1 :
                Tendsto (fun N =>
                  ⟪mpvState (d := d) (B k) N, mpvState (d := d) (A i) N⟫_ℂ)
                  atTop (nhds (0 : ℂ)) := by
              have hinner : Tendsto (fun N => mpvInner (d := d) (B k) (A i) N)
                  atTop (nhds 0) :=
                tendsto_inner_zero (B k) (A i) hBA
              simpa [mpvInner] using hinner
            have h2 :
                Tendsto (fun N => ⟪v (Sum.inr k) N, v (Sum.inl i) N⟫_ℂ)
                  atTop (nhds (0 : ℂ)) := by
              refine h1.congr fun N => ?_
              simp only [v]
              rw [lp.inner_single_left, lp.single_apply_self]
            simpa using h2
        | inr l =>
            by_cases h : k = l
            · subst l
              have h1 :
                  Tendsto (fun N =>
                    ⟪mpvState (d := d) (B k) N, mpvState (d := d) (B k) N⟫_ℂ)
                    atTop (nhds (1 : ℂ)) := by
                simpa [mpvInner] using tendsto_inner_one (B k) (hB_self k)
              have h2 :
                  Tendsto (fun N => ⟪v (Sum.inr k) N, v (Sum.inr k) N⟫_ℂ)
                    atTop (nhds (1 : ℂ)) := by
                refine h1.congr fun N => ?_
                simp only [v]
                rw [lp.inner_single_left, lp.single_apply_self]
              simpa using h2
            · have h1 :
                  Tendsto (fun N =>
                    ⟪mpvState (d := d) (B k) N, mpvState (d := d) (B l) N⟫_ℂ)
                    atTop (nhds (0 : ℂ)) := by
                simpa [mpvInner] using tendsto_inner_zero (B k) (B l) (hB_off k l h)
              have h2 :
                  Tendsto (fun N => ⟪v (Sum.inr k) N, v (Sum.inr l) N⟫_ℂ)
                    atTop (nhds (0 : ℂ)) := by
                refine h1.congr fun N => ?_
                simp only [v]
                rw [lp.inner_single_left, lp.single_apply_self]
              simpa [h] using h2
  have hLI_emb : ∀ᶠ N in atTop,
      LinearIndependent ℂ (fun x : Sum (Fin gA) (Fin gB) => v x N) :=
    MPSTensor.eventually_linearIndependent_of_gram_tendsto_id (v := v) hGram
  refine hLI_emb.mono ?_
  intro N hN
  let fN : MPVSpace d N →ₗ[ℂ] V :=
    lp.lsingle (𝕜 := ℂ) (E := fun N : ℕ => MPVSpace d N) 2 N
  have hN' : LinearIndependent ℂ (fun x : Sum (Fin gA) (Fin gB) =>
      fN (match x with
        | Sum.inl j => mpvState (d := d) (A j) N
        | Sum.inr k => mpvState (d := d) (B k) N)) := by
    have hfun :
        (fun x : Sum (Fin gA) (Fin gB) =>
          fN (match x with
            | Sum.inl j => mpvState (d := d) (A j) N
            | Sum.inr k => mpvState (d := d) (B k) N)) =
          (fun x : Sum (Fin gA) (Fin gB) => v x N) := by
      funext x
      cases x <;> simp only [fN, v] <;> rw [lp.lsingle_apply]
    simpa [hfun] using hN
  exact LinearIndependent.of_comp fN hN'

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

The CPSV16 proof (lines 1170-1192) gives the lower-bound argument cleanly only
for the dominant block `k = 0` (where `hB_top_norm_one` keeps
`‖bCoeff N 0‖ = 1` away from zero). For sub-dominant `k ≥ 1`, the source
matches blocks iteratively: after the dominant block is matched, peel it off
and re-apply the argument to the residual. The "∀ k, ∃ j" form of the
conclusion as stated bundles this iteration; the actual proof will need to
implement the residual-and-recurse step, since a literal one-shot lower
bound on `‖bCoeff N k‖` is not available for sub-dominant blocks under the
source normalization.

Elimination: rewrite using the source-faithful lower-bound + iterative
peeling with `hB_top_norm_one`, `hB_norm_le_one`, and `hc_ne` from the now
threaded-through `ProportionalDecompositionData` data; tracked in #1559
Stage C. -/
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
  -- Cor Lem1 (asymptotically orthonormal NMPVs are eventually LI):
  -- assuming all `mpvOverlap (A j) (B k) → 0`, the joint family
  -- `{V^N(A_j)}_j ∪ {V^N(B_k)}` is asymptotically orthonormal hence eventually
  -- LI; proportionality `V^N(A_total) = c_N V^N(B_total)` then forces
  -- linearly-dependent coefficient relations contradicting LI.
  -- The argument requires BOTH dominant-block normalizations (`hA_top_norm_one`
  -- and `hB_top_norm_one`) to derive the contradiction; iterative peeling
  -- handles sub-dominant blocks.
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
decompositions and replacing the proportionality scalar `c N` by `(c N)⁻¹`.
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
