/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hamiltonian
import QICLean.Algebra.UnitaryTraceZero
import QICLean.Representation.RegionPowerSymbol

/-!
# An upper bound for the gap of a range-one chain

Changing a unit ground vector by a unitary on the first site gives an orthogonal trial vector.
Only the singleton and the adjacent edge can change their energy expectations.

This is an auxiliary estimate for the constant comparison in Landau–Vazirani–Vidick,
arXiv:1307.5143v1, `eq:def-ce` and `l:within` (`algo53.tex`, lines 291–293 and 509–515).
-/

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ} {J E₀ Δ : ℝ} {Ω : EuclideanSpace ℂ (Fin L → Fin q)}

/-- The full-system gap of a nonempty range-one chain with local dimension at least two is
at most four times the interaction norm bound. The Hamiltonian and gap inequalities are those
of the TNLean one-dimensional note, Section 1, `eq:ham` and `eq:gap`. -/
theorem ChainHamiltonian.gap_le_four_mul_of_range_one (h : ChainHamiltonian L q 1 J)
    (hL : 0 < L) (hq : 2 ≤ q) (hgs : Matrix.IsGappedGroundState h.operator E₀ Ω Δ) :
    Δ ≤ 4 * J := by
  classical
  let x : Fin L := ⟨0, hL⟩
  obtain ⟨U, hU⟩ := Matrix.IsHermitian.exists_unitary_trace_mul_eq_zero
    (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q) {x} Ω)
      (by simpa [Entropy.RegionConfig, Fintype.card_pi] using hq)
  let K := Entropy.localLift (n := fun _ : Fin L ↦ q) {x} (U : Matrix _ _ ℂ)
  have hUunit :
      (U : Matrix (Entropy.RegionConfig (fun _ : Fin L ↦ q) {x})
        (Entropy.RegionConfig (fun _ : Fin L ↦ q) {x}) ℂ)ᴴ * (U : Matrix _ _ ℂ) = 1 := by
    convert U.property.1 using 1
    ext i j
    simp only [Matrix.one_apply]
    split_ifs <;> rfl
  have hK : Kᴴ * K = 1 := by
    simpa only [K, Entropy.localLift_mul, Entropy.localLift_conjTranspose,
      Entropy.localLift_one] using
      congrArg (Entropy.localLift (n := fun _ : Fin L ↦ q) {x}) hUunit
  have hφ : ‖toEuclideanLin K Ω‖ = 1 :=
    (Entropy.norm_toEuclideanLin_of_conjTranspose_mul_self hK Ω).trans hgs.1
  have horth : ⟪Ω, toEuclideanLin K Ω⟫_ℂ = 0 := by
    simpa only [K, Entropy.inner_localLift] using hU
  have hgap : Δ ≤
      (⟪toEuclideanLin K Ω, toEuclideanLin h.operator (toEuclideanLin K Ω)⟫_ℂ).re - E₀ := by
    simpa [hφ, horth] using hgs.2.2.gap_le (toEuclideanLin K Ω)
  have hE : (⟪Ω, toEuclideanLin h.operator Ω⟫_ℂ).re = E₀ := by
    have heig : toEuclideanLin h.operator Ω = (E₀ : ℂ) • Ω := by
      rw [← coe_toEuclideanCLM_eq_toEuclideanLin]
      exact hgs.2.1
    rw [heig, inner_smul_right, inner_self_eq_norm_sq_to_K, hgs.1]
    simp
  have hnorm (X : ChainSupport L 1) (v : EuclideanSpace ℂ (Fin L → Fin q))
      (hv : ‖v‖ = 1) : |(⟪v, toEuclideanLin (h.term X) v⟫_ℂ).re| ≤ J := by
    calc
      |(⟪v, toEuclideanLin (h.term X) v⟫_ℂ).re|
          ≤ ‖⟪v, toEuclideanLin (h.term X) v⟫_ℂ‖ := Complex.abs_re_le_norm _
      _ ≤ ‖v‖ * ‖toEuclideanLin (h.term X) v‖ := norm_inner_le_norm _ _
      _ ≤ ‖v‖ * (‖h.term X‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (Entropy.norm_toEuclideanLin_le _ _) (norm_nonneg _)
      _ ≤ J := by simpa only [hv, mul_one, one_mul] using h.norm_le X
  have hsame (X : ChainSupport L 1) (hx : x ∉ X.1) :
      ⟪toEuclideanLin K Ω, toEuclideanLin (h.term X) (toEuclideanLin K Ω)⟫_ℂ =
        ⟪Ω, toEuclideanLin (h.term X) Ω⟫_ℂ := by
    have hc :=
      Entropy.commute_localLift_of_isSupportedOn (n := fun _ : Fin L ↦ q)
        (Q := {x}) (D := X.1) (c := h.term X)
        (Finset.disjoint_singleton_left.mpr hx) (U : Matrix _ _ ℂ) (h.supported X)
        (fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩)
    rw [← LinearMap.adjoint_inner_right, ← toEuclideanLin_conjTranspose_eq_adjoint,
      ← Entropy.toEuclideanLin_mul_apply, ← Entropy.toEuclideanLin_mul_apply, Matrix.mul_assoc,
      ← hc.eq, ← Matrix.mul_assoc, hK, Matrix.one_mul]
  have hdiff (X : ChainSupport L 1) :
      (⟪toEuclideanLin K Ω, toEuclideanLin (h.term X) (toEuclideanLin K Ω)⟫_ℂ).re -
        (⟪Ω, toEuclideanLin (h.term X) Ω⟫_ℂ).re ≤ if x ∈ X.1 then 2 * J else 0 := by
    split_ifs with hx
    · linarith [(abs_le.mp (hnorm X (toEuclideanLin K Ω) hφ)).2,
        (abs_le.mp (hnorm X Ω hgs.1)).1]
    · simp only [hsame X hx, sub_self, le_refl]
  have hcard : (Finset.univ.filter (fun X : ChainSupport L 1 ↦ x ∈ X.1)).card ≤ 2 := by
    let t := Finset.univ.filter (fun y : Fin L ↦ y.val = 1)
    have ht : t.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb ↦
      Fin.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
    have hbound : (Finset.univ.filter (fun X : ChainSupport L 1 ↦ x ∈ X.1)).card ≤
        t.powerset.card := by
      apply Finset.card_le_card_of_injOn (fun X : ChainSupport L 1 ↦ X.1.erase x)
      · refine fun X hX ↦ Finset.mem_powerset.mpr fun y hy ↦ ?_
        have hval := X.2.2 x (Finset.mem_filter.mp hX).2 y (Finset.mem_erase.mp hy).2
        have hy0 : y.val ≠ 0 := fun hy0 ↦ (Finset.mem_erase.mp hy).1 (Fin.ext hy0)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          Nat.le_antisymm hval (Nat.one_le_iff_ne_zero.mpr hy0)⟩
      · refine fun X hX Y hY hXY ↦ Subtype.ext ?_
        simpa only [Finset.insert_erase (Finset.mem_filter.mp hX).2,
          Finset.insert_erase (Finset.mem_filter.mp hY).2] using
          congrArg (fun s : Finset (Fin L) ↦ insert x s) hXY
    exact hbound.trans (by
      simpa only [Finset.card_powerset, pow_one] using
        Nat.pow_le_pow_right (by decide : 1 ≤ 2) ht)
  have hsum :
      (∑ X : ChainSupport L 1,
        ((⟪toEuclideanLin K Ω, toEuclideanLin (h.term X) (toEuclideanLin K Ω)⟫_ℂ).re -
          (⟪Ω, toEuclideanLin (h.term X) Ω⟫_ℂ).re)) ≤
        ((Finset.univ.filter (fun X : ChainSupport L 1 ↦ x ∈ X.1)).card : ℝ) * (2 * J) := by
    simpa only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun X _ ↦ hdiff X)
  have hmul : ((Finset.univ.filter (fun X : ChainSupport L 1 ↦ x ∈ X.1)).card : ℝ) *
      (2 * J) ≤ 4 * J := by
    calc
      _ ≤ 2 * (2 * J) := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (mul_nonneg (by norm_num) (h.norm_bound_nonneg x))
      _ = 4 * J := by ring
  have henergy :
      (⟪toEuclideanLin K Ω, toEuclideanLin h.operator (toEuclideanLin K Ω)⟫_ℂ).re - E₀ ≤
        4 * J := by
    rw [← hE]
    simpa only [ChainHamiltonian.operator, map_sum, LinearMap.sum_apply, inner_sum,
      Complex.re_sum, Finset.sum_sub_distrib] using hsum.trans hmul
  exact hgap.trans henergy

end TNLean.MPS.AreaLaw
