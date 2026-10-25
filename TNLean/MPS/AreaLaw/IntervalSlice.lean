/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.OpenMPSCutRank

/-!
# Fixing the exterior coordinates of an MPS

Fixing the configuration outside a contiguous interval gives a vector whose
internal coefficient matrices are submatrices of the corresponding full-chain
coefficient matrices. Its cut ranks, and hence its MPS bond bound, cannot increase.
A nonzero scalar rescaling preserves the same bond bound.

Source: Schuch, Wolf, Verstraete, and Cirac, arXiv:0705.0292v2,
`paper_v2.tex`, lines 436–470. This supplies the bond-bound step when product
replacement separates a chain into consecutive blocks.
-/

noncomputable section
namespace TNLean.MPS.AreaLaw

variable {T L q : ℕ}

/-- Replace one contiguous interval of a fixed full configuration. -/
def insertInterval (a : ℕ) (σ₀ : Fin T → Fin q) (x : Fin L → Fin q) : Fin T → Fin q :=
  fun i ↦ if h : a ≤ i.val ∧ i.val < a + L then x ⟨i.val - a, by omega⟩ else σ₀ i

/-- Fix every physical coordinate outside one interval. -/
def intervalSlice (ψ : EuclideanSpace ℂ (Fin T → Fin q)) (a : ℕ)
    (σ₀ : Fin T → Fin q) : EuclideanSpace ℂ (Fin L → Fin q) :=
  WithLp.toLp 2 fun x ↦ ψ (insertInterval a σ₀ x)

/-- Extend prefix coordinates by the fixed exterior configuration. -/
private def prefixMap (a j : ℕ) (hj : j ≤ L) (σ₀ : Fin T → Fin q)
    (x : (v : {v : Fin L // v ∈ leftBlock L j}) → Fin q) :
    (v : {v : Fin T // v ∈ leftBlock T (a + j)}) → Fin q :=
  fun v ↦ if ha : a ≤ v.1.val then
    x ⟨⟨v.1.val - a, by have := mem_leftBlock.mp v.2; omega⟩,
      mem_leftBlock.mpr (by dsimp only; have := mem_leftBlock.mp v.2; omega)⟩
  else σ₀ v.1

/-- Extend suffix coordinates by the fixed exterior configuration. -/
private def suffixMap (a j : ℕ) (σ₀ : Fin T → Fin q)
    (x : (v : {v : Fin L // v ∉ leftBlock L j}) → Fin q) :
    (v : {v : Fin T // v ∉ leftBlock T (a + j)}) → Fin q :=
  fun v ↦ if hb : v.1.val < a + L then
    x ⟨⟨v.1.val - a, by have := mt mem_leftBlock.mpr v.2; omega⟩,
      (by have := mt mem_leftBlock.mpr v.2; simp only [mem_leftBlock]; omega)⟩
  else σ₀ v.1

/-- An interval slice at a local cut is a submatrix at the corresponding full cut. -/
private theorem cutMatrix_intervalSlice (ψ : EuclideanSpace ℂ (Fin T → Fin q))
    (a j : ℕ) (hj : j ≤ L) (σ₀ : Fin T → Fin q) :
    cutMatrix (intervalSlice (L := L) ψ a σ₀) j =
      (cutMatrix ψ (a + j)).submatrix (prefixMap a j hj σ₀) (suffixMap a j σ₀) := by
  ext x y
  change ψ (insertInterval a σ₀
    ((Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L j)).symm (x, y))) =
      ψ ((Entropy.cutEquiv (fun _ : Fin T ↦ q) (leftBlock T (a + j))).symm
        (prefixMap a j hj σ₀ x, suffixMap a j σ₀ y))
  apply congrArg ψ
  funext i
  by_cases hi : i.val < a + j
  · rw [Entropy.cutEquiv_symm_apply_mem _ _ (mem_leftBlock.mpr hi)]
    by_cases ha : a ≤ i.val
    · have hb : i.val < a + L := lt_of_lt_of_le hi (Nat.add_le_add_left hj a)
      simp only [insertInterval,
        dite_eq_left (show a ≤ i.val ∧ i.val < a + L from ⟨ha, hb⟩),
        prefixMap, dite_eq_left ha]
      rw [Entropy.cutEquiv_symm_apply_mem _ _ (mem_leftBlock.mpr (by dsimp only; omega))]
    · simp [insertInterval, prefixMap, ha]
  · rw [Entropy.cutEquiv_symm_apply_not_mem _ _ (mt mem_leftBlock.mp hi)]
    by_cases hb : i.val < a + L
    · have ha : a ≤ i.val := by omega
      simp only [insertInterval,
        dite_eq_left (show a ≤ i.val ∧ i.val < a + L from ⟨ha, hb⟩),
        suffixMap, dite_eq_left hb]
      rw [Entropy.cutEquiv_symm_apply_not_mem _ _ (by simp only [mem_leftBlock]; omega)]
    · simp [insertInterval, suffixMap, hb]

/-- Fixing the coordinates outside an interval cannot increase its internal cut ranks. -/
theorem rank_cutMatrix_intervalSlice_le (ψ : EuclideanSpace ℂ (Fin T → Fin q))
    (a j : ℕ) (hj : j ≤ L) (σ₀ : Fin T → Fin q) :
    (cutMatrix (intervalSlice (L := L) ψ a σ₀) j).rank ≤ (cutMatrix ψ (a + j)).rank := by
  rw [cutMatrix_intervalSlice ψ a j hj σ₀]
  exact Matrix.rank_submatrix_le _ _ _

/-- The usual cut-rank bound for a full chain also bounds every interval slice. -/
theorem IsOpenMPS.intervalSlice {D : ℕ}
    {ψ : EuclideanSpace ℂ (Fin T → Fin q)}
    (hψ : IsOpenMPS T q D (fun x ↦ ψ x))
    (a : ℕ) (ha : a + L ≤ T) (σ₀ : Fin T → Fin q) :
    IsOpenMPS L q D (fun x ↦ intervalSlice (L := L) ψ a σ₀ x) := by
  apply isOpenMPS_of_internal_cutMatrix_rank_le
  intro j hj0 hjL
  exact (rank_cutMatrix_intervalSlice_le ψ a j hjL.le σ₀).trans
    (hψ.rank_cutMatrix_le (by omega) (by omega))

/-- A nonzero scalar multiple of an interval slice has the same MPS bond bound. -/
theorem IsOpenMPS.of_intervalSlice_eq_mul {D : ℕ}
    {ψ : EuclideanSpace ℂ (Fin T → Fin q)}
    (hψ : IsOpenMPS T q D (fun x ↦ ψ x))
    (a : ℕ) (ha : a + L ≤ T) (σ₀ : Fin T → Fin q)
    (φ : EuclideanSpace ℂ (Fin L → Fin q)) (c : ℂ) (hc : c ≠ 0)
    (hslice : ∀ x, TNLean.MPS.AreaLaw.intervalSlice ψ a σ₀ x = c * φ x) :
    IsOpenMPS L q D (fun x ↦ φ x) := by
  obtain ⟨A, z, hA, hcoeff⟩ := hψ.intervalSlice a ha σ₀
  refine ⟨A, c⁻¹ * z, hA, ?_⟩
  intro x
  apply mul_left_cancel₀ hc
  rw [← hslice]
  change (fun x ↦ TNLean.MPS.AreaLaw.intervalSlice ψ a σ₀ x) x = _
  rw [hcoeff]
  simp [← mul_assoc, hc]

end TNLean.MPS.AreaLaw
