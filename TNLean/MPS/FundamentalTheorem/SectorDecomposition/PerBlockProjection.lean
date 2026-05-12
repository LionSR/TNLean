/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.SectorDecomposition
import TNLean.MPS.FundamentalTheorem.Full.ProportionalExpansion

/-!
# Paper Step 1 on the `SectorDecomposition` surface

This module re-states and proves Step 1 of arXiv:1606.00608, Theorem `thm1`
(the per-block-projection cancellation argument) on the paper-faithful
`SectorDecomposition` surface introduced by issue #1641 / Plan C.

## Main statements

* `fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp`:
  fix a `Q`-block `k₀` and assume all overlaps from `P.basis j` to `Q.basis k₀`
  decay; the projected proportionality identity is then asymptotically
  contradictory.
* `fixed_left_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp`:
  the symmetric statement obtained by swapping the two families.
* `eventuallyNonzeroProportionalMPV₂_symm`: `EventuallyNonzeroProportionalMPV₂`
  is symmetric in its two arguments; used to reduce the left case to the
  right case.

## Scope and load-bearing hypothesis

The argument is decoupled from `IsCanonicalFormBNT`.  The hypotheses are the
paper's: every per-sector weight has unit modulus, so the BNT coefficient
`coeff N j = ∑_q (weight j q)^N` is bounded in modulus by the multiplicity
`copies j`.  The load-bearing non-cancellation hypothesis `hNoCancel` is
factored out: it asserts that the projected proportionality right-hand side
`c_N · ⟪V(Q.toTensor), V(Q.basis k₀)⟫_N` does not tend to zero for the scalar
witnesses `c` produced by `hProp`.  In the paper this non-cancellation
follows from almost-periodicity of finite `N`-th power sums of unit-modulus
complex numbers combined with the dominant-weight-adjusted scalar limit;
both ingredients live outside this module.

## References

* Cirac, Pérez-García, Schuch, Verstraete, *Matrix Product Density Operators:
  Renormalization Fixed Points and Boundary Theories*, arXiv:1606.00608 (2017),
  Theorem `thm1`, lines 1170--1192.
* `audits/2026-05-13_cpsv16_ft_definition_audit.md` §10 (the per-block
  projection algebra).
-/

open scoped Matrix BigOperators
open Filter

namespace MPSTensor

variable {d : ℕ}

section PerBlockProjection

/-- **Bounded BNT coefficient from unit-modulus sector weights.**

If every sector weight has unit modulus, then the coefficient
`coeff N j = ∑_q (μ_{j,q})^N` is bounded in modulus by the multiplicity
`copies j` uniformly in `N`.  This is the boundedness ingredient required for
the per-block projection argument. -/
lemma SectorDecomposition.norm_coeff_le_copies
    (P : SectorDecomposition d)
    (hP_unit : ∀ j q, ‖P.sectors.weight j q‖ = 1)
    (N : ℕ) (j : Fin P.basisCount) :
    ‖P.coeff N j‖ ≤ (P.copies j : ℝ) := by
  classical
  unfold SectorDecomposition.coeff SectorWeightData.coeff
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ q : Fin (P.copies j), ‖(P.weight j q) ^ N‖ = 1 := by
    intro q
    rw [norm_pow, hP_unit j q, one_pow]
  have hsum :
      (∑ q : Fin (P.copies j), ‖(P.weight j q) ^ N‖) = (P.copies j : ℝ) := by
    calc
      (∑ q : Fin (P.copies j), ‖(P.weight j q) ^ N‖)
          = ∑ q : Fin (P.copies j), (1 : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro q _
            exact hterm q
      _ = (P.copies j : ℝ) := by
            simp
  exact hsum.le

/-- **Symmetry of `EventuallyNonzeroProportionalMPV₂`.**

The eventual nonzero-proportionality predicate is symmetric in its two
arguments: inverting the per-length scalar swaps the two MPV families. -/
lemma eventuallyNonzeroProportionalMPV₂_symm
    {d D₁ D₂ : ℕ} {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (h : EventuallyNonzeroProportionalMPV₂ A B) :
    EventuallyNonzeroProportionalMPV₂ B A := by
  refine h.mono ?_
  intro N hN
  rcases hN with ⟨c, hc, hEq⟩
  refine ⟨c⁻¹, inv_ne_zero hc, fun σ => ?_⟩
  calc
    mpv B σ = c⁻¹ * (c * mpv B σ) := by
      rw [inv_mul_cancel_left₀ hc]
    _ = c⁻¹ * mpv A σ := by
      rw [← hEq σ]

/-- **Per-block projection contradiction (fixed right block).**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192.

Given two paper-faithful sector decompositions `P, Q` with unit-modulus
sector weights on `P`, eventual nonzero proportionality of the assembled
tensors, and a fixed `Q`-block index `k₀` such that all cross-overlaps from
`P.basis j` to `Q.basis k₀` decay to zero, the projected proportionality
forces the scalar-weighted projected sum to tend to zero.  Combined with the
non-cancellation hypothesis `hNoCancel`, this is contradictory.

This is Plan C on the `SectorDecomposition` surface (paper Step 1) for an
arbitrary fixed block, without any combined-family linear-independence input.

**Load-bearing hypothesis:** `hNoCancel` asserts that for every scalar
sequence `c` witnessing the eventual proportionality, the product
`c N · ⟪V(Q.toTensor), V(Q.basis k₀)⟫_N` does not tend to zero.  In the paper
this follows from (i) almost-periodicity giving `lim sup |coeff_Q N k₀| > 0`,
(ii) decay of off-diagonal `Q` cross-overlaps and bounded `|coeff_Q|` from
unit-modulus weights, and (iii) `|c_N|` bounded below via the dominant-weight
scaling lemma.  Folding (i)--(iii) into a single hypothesis decouples the
algebraic skeleton (here) from the analytic content (a future workstream). -/
lemma fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp
    (P Q : SectorDecomposition d)
    (hP_unit : ∀ j q, ‖P.sectors.weight j q‖ = 1)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor)
    (k₀ : Fin Q.basisCount)
    (hAllDecay : ∀ j : Fin P.basisCount,
      Tendsto (fun N => mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N)
        atTop (nhds 0))
    (hNoCancel : ∀ c : ℕ → ℂ,
      (∀ᶠ N in atTop, ∀ σ : Fin N → Fin d,
        mpv P.toTensor σ = c N * mpv Q.toTensor σ) →
      ¬ Tendsto
        (fun N => c N * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N)
        atTop (nhds 0)) :
    False := by
  classical
  -- Step 1: extract a scalar sequence `c` witnessing the eventual
  -- proportionality, in the same style as
  -- `exists_eventually_weighted_mpvState_eq_smul_sequence_of_eventuallyNonzeroProportionalMPV₂`.
  set Pprop : ℕ → Prop := fun N =>
    ∃ c : ℂ, c ≠ 0 ∧ ∀ σ : Fin N → Fin d,
      mpv P.toTensor σ = c * mpv Q.toTensor σ with hPprop_def
  have hEvent : ∀ᶠ N in atTop, Pprop N := hProp
  let c : ℕ → ℂ := fun N => if hN : Pprop N then Classical.choose hN else 1
  have hc_eq : ∀ᶠ N in atTop, ∀ σ : Fin N → Fin d,
      mpv P.toTensor σ = c N * mpv Q.toTensor σ := by
    refine hEvent.mono ?_
    intro N hN
    simp only [c]
    rw [dif_pos hN]
    exact (Classical.choose_spec hN).2
  -- Step 2: the projected proportionality identity holds eventually in `N`.
  --   `mpvOverlap P.toTensor (Q.basis k₀) N = c N * mpvOverlap Q.toTensor (Q.basis k₀) N`
  have hProj : ∀ᶠ N in atTop,
      mpvOverlap (d := d) P.toTensor (Q.basis k₀) N
        = c N * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N := by
    refine hc_eq.mono ?_
    intro N hN
    exact
      mpvOverlap_eq_mul_of_mpv_eq_mul (d := d) P.toTensor Q.toTensor
        (c N) hN (Q.basis k₀)
  -- Step 3: the LHS expands by the BNT decomposition for `P.toTensor`.
  have hLHS_decomp : ∀ N : ℕ,
      mpvOverlap (d := d) P.toTensor (Q.basis k₀) N
        = ∑ j : Fin P.basisCount,
            P.coeff N j * mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N := by
    intro N
    refine mpvOverlap_eq_sum_of_decomp_left
      (d := d) (g := P.basisCount) (dim := P.basisDim)
      P.toTensor P.basis (N := N)
      (fun j => P.coeff N j) ?_ (Q.basis k₀)
    intro σ
    exact P.mpv_toTensor_eq_sum_coeff (N := N) σ
  -- Step 4: each summand on the LHS tends to zero.
  -- Bounded coefficient × decaying overlap = decaying product.
  have hSummand : ∀ j : Fin P.basisCount,
      Tendsto
        (fun N => P.coeff N j * mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N)
        atTop (nhds 0) := by
    intro j
    -- `|coeff N j * overlap N| ≤ copies j * |overlap N|`.
    refine squeeze_zero_norm
      (f := fun N => P.coeff N j * mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N)
      (a := fun N => (P.copies j : ℝ)
                      * ‖mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N‖)
      ?_ ?_
    · intro N
      simp only [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (P.norm_coeff_le_copies hP_unit N j) (norm_nonneg _)
    · -- multiply the decay limit by the constant `(copies j : ℝ)`.
      have h0 : Tendsto
          (fun N => ‖mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N‖)
          atTop (nhds 0) :=
        (tendsto_zero_iff_norm_tendsto_zero.mp (hAllDecay j))
      have := h0.const_mul (P.copies j : ℝ)
      simpa using this
  -- Step 5: the LHS therefore tends to zero.
  have hLHS_tendsto : Tendsto
      (fun N => mpvOverlap (d := d) P.toTensor (Q.basis k₀) N)
      atTop (nhds 0) := by
    have hSum : Tendsto
        (fun N => ∑ j : Fin P.basisCount,
            P.coeff N j * mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N)
        atTop (nhds 0) := by
      have hTo : Tendsto
          (fun N => ∑ j : Fin P.basisCount,
              P.coeff N j * mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N)
          atTop (nhds (∑ _j : Fin P.basisCount, (0 : ℂ))) :=
        tendsto_finset_sum (Finset.univ : Finset (Fin P.basisCount))
          (fun j _ => hSummand j)
      simpa using hTo
    refine hSum.congr' ?_
    refine Filter.Eventually.of_forall ?_
    intro N
    exact (hLHS_decomp N).symm
  -- Step 6: combine with the projected proportionality identity to obtain the
  -- scalar limit `c N * mpvOverlap Q.toTensor (Q.basis k₀) N → 0`.
  have hRHS_tendsto : Tendsto
      (fun N => c N * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N)
      atTop (nhds 0) := by
    refine hLHS_tendsto.congr' ?_
    exact hProj
  -- Step 7: contradiction with `hNoCancel`.
  exact hNoCancel c hc_eq hRHS_tendsto

/-- **Per-block projection contradiction (fixed left block).**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1182--1185.

Symmetric counterpart of
`fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp`.
Fixing a `P`-block `j₀` instead of a `Q`-block, the projected proportionality
identity is contradictory with the per-block decay of all cross-overlaps to
`P.basis j₀`.

The proof reduces to the right-block version after swapping `P` and `Q`:
the swapped proportionality witness `c⁻¹` plays the role of `c`, and the
hypothesis `hAllDecay` is rephrased via `tendsto_mpvOverlap_zero_swap`. -/
lemma fixed_left_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp
    (P Q : SectorDecomposition d)
    (hQ_unit : ∀ k q, ‖Q.sectors.weight k q‖ = 1)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor)
    (j₀ : Fin P.basisCount)
    (hAllDecay : ∀ k : Fin Q.basisCount,
      Tendsto (fun N => mpvOverlap (d := d) (P.basis j₀) (Q.basis k) N)
        atTop (nhds 0))
    (hNoCancel : ∀ c : ℕ → ℂ,
      (∀ᶠ N in atTop, ∀ σ : Fin N → Fin d,
        mpv Q.toTensor σ = c N * mpv P.toTensor σ) →
      ¬ Tendsto
        (fun N => c N * mpvOverlap (d := d) P.toTensor (P.basis j₀) N)
        atTop (nhds 0)) :
    False := by
  -- Swap P and Q and apply the right-block version.
  refine
    fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp
      Q P hQ_unit (eventuallyNonzeroProportionalMPV₂_symm hProp) j₀ ?_ hNoCancel
  intro k
  exact tendsto_mpvOverlap_zero_swap (d := d) (P.basis j₀) (Q.basis k)
    (hAllDecay k)

end PerBlockProjection

end MPSTensor
