/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixKroneckerContraction
import TNLean.Lattice.RegionSplit

/-!
# Swapping two copies of a system on a region

Two copies of a finite set `ι` of sites with local dimension `q` have the configurations
`(ι → Fin q) × (ι → Fin q)`. The unitary `F_S` exchanges the two copies at the sites of a region
`S` and fixes them elsewhere. It commutes with products of operators acting off `S`, and it
exchanges the two tensor factors of operators acting on `S`. Nothing here depends on a geometry
of the sites, so the one-dimensional chain and the square lattice both use it.

## Main definitions

* `TNLean.Lattice.sheetSwap`, `TNLean.Lattice.sheetSwapOp`: the unitary `F_S` swapping the two
  copies at the sites of `S`.

## Main results

* `TNLean.Lattice.sheetSwapOp_mul_sheetSwapOp`: `F_A F_Y = F_T` for `Y = T ⊔ A`.
* `TNLean.Lattice.commute_sheetSwapOp_kronecker`: `F_S` commutes with products of operators
  acting off `S`.
* `TNLean.Lattice.sheetSwapOp_mul_kronecker_of_mem_supportedOperators`: `F_S` exchanges two
  operators acting on `S`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), proof of Lemma 6.6 `lem:exchange`,
  `05-frames.tex`, lines 481–561, and `02-information.tex`, lines 416–424.

Source text: `openai/math` at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, file
`preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/`
`build/sections/05-frames.tex`. The statements and proofs here are formalized independently from
the manuscript; no upstream Lean proof text was reused.
-/

open Matrix QuantumCircuit
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.Lattice

section SheetSwap

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

/-- The bijection of two-sheet raw configurations exchanging the two sheets at the sites of
`S`. -/
def sheetSwap (q : ℕ) (S : Finset ι) : Equiv.Perm ((ι → Fin q) × (ι → Fin q)) where
  toFun r := (fun x => if x ∈ S then r.2 x else r.1 x, fun x => if x ∈ S then r.1 x else r.2 x)
  invFun r := (fun x => if x ∈ S then r.2 x else r.1 x, fun x => if x ∈ S then r.1 x else r.2 x)
  left_inv r := by
    ext x <;> by_cases hx : x ∈ S <;> simp [hx]
  right_inv r := by
    ext x <;> by_cases hx : x ∈ S <;> simp [hx]

/-- The unitary `F_S` swapping the two raw sheets at the positions in `S`.

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 483–484. -/
def sheetSwapOp (q : ℕ) (S : Finset ι) :
    Matrix ((ι → Fin q) × (ι → Fin q)) ((ι → Fin q) × (ι → Fin q)) ℂ :=
  (sheetSwap q S).toPEquiv.toMatrix

omit [Fintype ι] in
theorem sheetSwap_symm (S : Finset ι) : (sheetSwap q S).symm = sheetSwap q S := rfl

theorem norm_sheetSwapOp_le_one (S : Finset ι) : ‖sheetSwapOp q S‖ ≤ 1 :=
  l2_opNorm_toMatrix_toPEquiv_le _

/-- `F_A F_Y = F_T` when `Y` is the disjoint union of `T` and `A`
(`05-frames.tex`, lines 516–520). -/
theorem sheetSwapOp_mul_sheetSwapOp {A Y T : Finset ι} (hT : ∀ x, x ∈ T ↔ x ∈ Y ∧ x ∉ A)
    (hA : A ⊆ Y) : sheetSwapOp q A * sheetSwapOp q Y = sheetSwapOp q T := by
  rw [sheetSwapOp, sheetSwapOp, PEquiv.toMatrix_toPEquiv_mul]
  change ((sheetSwap q Y).toPEquiv.toMatrix : Matrix _ _ ℂ).submatrix (sheetSwap q A)
    (Equiv.refl _) = _
  rw [toMatrix_toPEquiv_submatrix, sheetSwapOp]
  congr 2
  ext r x
  · by_cases hxA : x ∈ A
    · simp [sheetSwap, hxA, hA hxA, (hT x).not.mpr (fun h => h.2 hxA)]
    · by_cases hxY : x ∈ Y <;> simp [sheetSwap, hxA, hxY, hT x]
  · by_cases hxA : x ∈ A
    · simp [sheetSwap, hxA, hA hxA, (hT x).not.mpr (fun h => h.2 hxA)]
    · by_cases hxY : x ∈ Y <;> simp [sheetSwap, hxA, hxY, hT x]

/-- In the coordinates of `sheetSplit S`, swapping the sheets at `S` swaps the `S`-parts. -/
theorem sheetSplit_sheetSwap_fst (S : Finset ι) (r : (ι → Fin q) × (ι → Fin q)) :
    sheetSplit q S (sheetSwap q S r).1 = ((sheetSplit q S r.2).1, (sheetSplit q S r.1).2) := by
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · simp [sheetSwap, v.2]
  · simp [sheetSwap, Finset.mem_compl.mp v.2]

theorem sheetSplit_sheetSwap_snd (S : Finset ι) (r : (ι → Fin q) × (ι → Fin q)) :
    sheetSplit q S (sheetSwap q S r).2 = ((sheetSplit q S r.1).1, (sheetSplit q S r.2).2) := by
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · simp [sheetSwap, v.2]
  · simp [sheetSwap, Finset.mem_compl.mp v.2]

/-- The product of an operator acting off `S` and an operator acting on `S`, in the coordinates
of `sheetSplit S`. -/
theorem mul_submatrix_sheetSplit {S : Finset ι} {O I : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    {O' : Matrix (↥Sᶜ → Fin q) (↥Sᶜ → Fin q) ℂ} {I' : Matrix (S → Fin q) (S → Fin q) ℂ}
    (hO : O.submatrix (sheetSplit q S).symm (sheetSplit q S).symm = 1 ⊗ₖ O')
    (hI : I.submatrix (sheetSplit q S).symm (sheetSplit q S).symm = I' ⊗ₖ 1) :
    (O * I).submatrix (sheetSplit q S).symm (sheetSplit q S).symm = I' ⊗ₖ O' := by
  rw [← submatrix_mul_equiv _ _ _ (sheetSplit q S).symm, hO, hI, ← mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one]

theorem apply_eq_submatrix_apply {m n : Type*} (M : Matrix m m ℂ) (e : m ≃ n) (x y : m) :
    M x y = M.submatrix e.symm e.symm (e x) (e y) := by
  simp

/-- The swap of the sheets at `S` commutes with every product `R₁ ⊗ R₂` of operators acting off
`S`. -/
theorem commute_sheetSwapOp_kronecker {S : Finset ι} {D : Set ι} (hD : Disjoint D (S : Set ι))
    {R₁ R₂ : Matrix (ι → Fin q) (ι → Fin q) ℂ} (h₁ : R₁ ∈ supportedOperators q D)
    (h₂ : R₂ ∈ supportedOperators q D) : Commute (sheetSwapOp q S) (R₁ ⊗ₖ R₂) := by
  obtain ⟨R₁', hR₁'⟩ := exists_one_kronecker_of_mem_supportedOperators hD h₁
  obtain ⟨R₂', hR₂'⟩ := exists_one_kronecker_of_mem_supportedOperators hD h₂
  change _ * _ = _ * _
  rw [sheetSwapOp, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, sheetSwap_symm]
  ext ⟨y₁, y₂⟩ ⟨r₁, r₂⟩
  simp only [submatrix_apply, kroneckerMap_apply, id]
  simp only [apply_eq_submatrix_apply R₁ (sheetSplit q S), apply_eq_submatrix_apply R₂
    (sheetSplit q S)]
  rw [hR₁', hR₂']
  simp only [kroneckerMap_apply, sheetSplit_sheetSwap_fst, sheetSplit_sheetSwap_snd]
  ring

end SheetSwap

/-- A sheet swap exchanges two operators supported on its region.

This is the local exchange identity used to cancel the two identical replica terms inside
the swapped region in the polynomial-PEPS manuscript, `02-information.tex`, lines 416–424. -/
theorem sheetSwapOp_mul_kronecker_of_mem_supportedOperators
    {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} {R : Finset ι}
    {A B : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hA : A ∈ supportedOperators q (R : Set ι))
    (hB : B ∈ supportedOperators q (R : Set ι)) :
    sheetSwapOp q R * (A ⊗ₖ B) = (B ⊗ₖ A) * sheetSwapOp q R := by
  obtain ⟨A', hA'⟩ := exists_kronecker_one_of_mem_supportedOperators hA
  obtain ⟨B', hB'⟩ := exists_kronecker_one_of_mem_supportedOperators hB
  rw [sheetSwapOp, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv, sheetSwap_symm]
  ext ⟨y₁, y₂⟩ ⟨r₁, r₂⟩
  simp only [submatrix_apply, kroneckerMap_apply, id]
  simp only [apply_eq_submatrix_apply A (sheetSplit q R),
    apply_eq_submatrix_apply B (sheetSplit q R)]
  rw [hA', hB']
  simp only [kroneckerMap_apply, sheetSplit_sheetSwap_fst, sheetSplit_sheetSwap_snd]
  ring

end TNLean.Lattice
