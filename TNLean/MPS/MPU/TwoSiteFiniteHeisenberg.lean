/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TwoSiteStandardFormCircuit
import TNLean.MPS.MPU.TwoSiteStandardFormOpenWord
import QICLean.Algebra.MatrixKroneckerEmbed
import Mathlib.Tactic.FinCases

/-!
# Actual finite Heisenberg action of a supplied two-site standard form

For every chain of at least three complete two-site blocks, the actual
periodic MPO conjugates an observable on the middle input block to the
four neighbouring output half-sites. The entire remaining chain is an
identity spectator in the result. The proof lifts the already established
open three-block intertwiner to the complete finite operator, then uses
the actual MPO's unitarity. The periodic seam remains in the word trace.

Source: arXiv:1703.09188, equations StandardForm and SF, lines 603--622,
and the finite conjugation underlying eq:appendix-1, lines 2300--2306.

**Scope restriction (complete blocks):** This result is for the supplied
blocked tensor itself and every length at least three in that alphabet.
It does not yet assemble arbitrary original-site residuals, arbitrary
interval embeddings, or a compatible quasi-local automorphism. The exact
remaining scope is recorded in
`docs/paper-gaps/mpu_qca_complete_block_heisenberg_scope.tex`.
-/

open scoped Matrix BigOperators Kronecker
open Matrix

namespace MPOTensor

private abbrev HalfPair (d : ℕ) := Fin d × Fin d
private abbrev FourHalves (d : ℕ) := HalfPair d × HalfPair d
private abbrev Tail (d n : ℕ) := Fin n → Fin (d * d)
private abbrev InputExterior (d n : ℕ) := (Fin (d * d) × Fin (d * d)) × Tail d n
private abbrev OutputExterior (d n : ℕ) := HalfPair d × Tail d n

private def windowInputHeadEquiv (d : ℕ) :
    ((Fin (d * d) × Fin (d * d)) × HalfPair d) ≃ (Fin 3 → Fin (d * d)) where
  toFun z := ![z.1.1, finProdFinEquiv z.2, z.1.2]
  invFun f := ((f 0, f 2), finProdFinEquiv.symm (f 1))
  left_inv z := by rcases z with ⟨⟨a, b⟩, c⟩; simp
  right_inv f := by funext i; fin_cases i <;> simp

private def windowOutputHeadEquiv (d : ℕ) :
    (HalfPair d × FourHalves d) ≃ (Fin 3 → Fin (d * d)) where
  toFun z := ![finProdFinEquiv (z.1.1, z.2.1.1),
    finProdFinEquiv (z.2.1.2, z.2.2.1), finProdFinEquiv (z.2.2.2, z.1.2)]
  invFun f :=
    (((finProdFinEquiv.symm (f 0)).1, (finProdFinEquiv.symm (f 2)).2),
      (((finProdFinEquiv.symm (f 0)).2, (finProdFinEquiv.symm (f 1)).1),
        ((finProdFinEquiv.symm (f 1)).2, (finProdFinEquiv.symm (f 2)).1)))
  left_inv z := by rcases z with ⟨⟨a, b⟩, ⟨⟨c, e⟩, ⟨f, g⟩⟩⟩; simp
  right_inv f := by funext i; fin_cases i <;> simp

private def switchMiddleEquiv (α β γ : Type*) : ((α × β) × γ) ≃ ((α × γ) × β) where
  toFun z := ((z.1.1, z.2), z.1.2)
  invFun z := ((z.1.1, z.2), z.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Complete input coordinates: the two exterior input blocks and the
arbitrary tail are separated from the middle input pair. These are a
bijection with all finite-chain configurations, not a restricted family.
Source: arXiv:1703.09188, StandardForm, lines 603--622. -/
def twoSiteHeisenbergInputEquiv (d n : ℕ) :
    (InputExterior d n × HalfPair d) ≃ (Fin (3 + n) → Fin (d * d)) :=
  (switchMiddleEquiv _ _ _).trans
    (((windowInputHeadEquiv d).prodCongr (Equiv.refl (Tail d n))).trans
      (Fin.appendEquiv 3 n))

/-- Complete output coordinates separate the four output half-sites
from the two exterior half-sites and arbitrary tail. Their ordering is
exactly that of the existing two-link output observable.
Source: arXiv:1703.09188, StandardForm, lines 603--622. -/
def twoSiteHeisenbergOutputEquiv (d n : ℕ) :
    (OutputExterior d n × FourHalves d) ≃ (Fin (3 + n) → Fin (d * d)) :=
  (switchMiddleEquiv _ _ _).trans
    (((windowOutputHeadEquiv d).prodCongr (Equiv.refl (Tail d n))).trans
      (Fin.appendEquiv 3 n))

/-- The actual full periodic MPO in the two complete coordinate systems.
Its row and column relabelings are bijective; no coefficient slice is
used as a substitute for the finite operator.
Source: arXiv:1703.09188, StandardForm and eq:appendix-1, lines 603--622
and 2300--2306. -/
noncomputable def twoSiteHeisenbergMatrix {d D : ℕ}
    (W : MPOTensor (d * d) D) (n : ℕ) :
    Matrix (OutputExterior d n × FourHalves d) (InputExterior d n × HalfPair d) ℂ :=
  Matrix.reindex (twoSiteHeisenbergOutputEquiv d n).symm
    (twoSiteHeisenbergInputEquiv d n).symm (mpo W (3 + n))

private theorem twoSiteHeisenbergMatrix_apply {d D ℓ r n : ℕ}
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (HalfPair d) ℂ}
    {v : Matrix (HalfPair d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v)
    (e : OutputExterior d n) (f : InputExterior d n) (x : FourHalves d) (j : HalfPair d) :
    twoSiteHeisenbergMatrix W n (e, x) (f, j) =
      twoSiteThreeBlockTrace S 1 (evalWord W (List.ofFn e.2) (List.ofFn f.2))
        e.1.1 e.1.2 f.1.1 f.1.2 x j := by
  change mpo W (3 + n)
    (Fin.append ![finProdFinEquiv (e.1.1, x.1.1),
      finProdFinEquiv (x.1.2, x.2.1), finProdFinEquiv (x.2.2, e.1.2)] e.2)
    (Fin.append ![f.1.1, finProdFinEquiv j, f.1.2] f.2) = _
  simp only [mpo_apply, mpoMatrixEntry, List.ofFn_fin_append]
  rw [evalWord_append W _ _ _ _ (by simp)]
  change Matrix.trace (evalWord W _ _ * evalWord W _ _) =
    Matrix.trace (1 * evalWord W _ _ * evalWord W _ _)
  rw [Matrix.one_mul]

/-- The full finite MPO intertwines the actual middle input observable
with the neighbouring four-half-site output observable, for every tail
length. This lifts the open contraction identity to complete finite
matrices; arXiv:1703.09188, StandardForm, lines 603--622. -/
theorem twoSiteHeisenbergMatrix_intertwiner {d D ℓ r : ℕ}
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (HalfPair d) ℂ}
    {v : Matrix (HalfPair d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (n : ℕ)
    (A : Matrix (HalfPair d) (HalfPair d) ℂ) :
    twoSiteHeisenbergMatrix W n * Matrix.rightKroneckerEmbed A =
      Matrix.rightKroneckerEmbed (twoLinkOutputObservable u v A) *
        twoSiteHeisenbergMatrix W n := by
  classical
  ext row col
  rcases row with ⟨e, x⟩
  rcases col with ⟨f, j⟩
  have h := congrArg (fun M ↦ M x j)
    (twoSite_threeBlock_trace_intertwiner_with_endpoints S
      (1 : Matrix (Fin D) (Fin D) ℂ)
      (evalWord W (List.ofFn e.2) (List.ofFn f.2))
      e.1.1 e.1.2 f.1.1 f.1.2 A)
  simp only [Matrix.mul_apply] at h
  simpa [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.rightKroneckerEmbed_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, twoSiteHeisenbergMatrix_apply S] using h

/-- The full finite MPO in these complete coordinates is unitary between
the indicated spaces, derived from the supplied standard form itself.
Source: arXiv:1703.09188, StandardForm and SF, lines 603--622. -/
theorem twoSiteHeisenbergMatrix_isUnitaryBetween {d D ℓ r : ℕ}
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (HalfPair d) ℂ}
    {v : Matrix (HalfPair d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (n : ℕ) :
    (twoSiteHeisenbergMatrix W n).IsUnitaryBetween := by
  let : NeZero (3 + n) := ⟨by omega⟩
  have h := (Matrix.isUnitaryBetween_iff_mem_unitaryGroup (mpo W (3 + n))).mpr
    (TwoSiteStandardFormData.mpo_mem_unitaryGroup W u v S)
  exact h.reindex _ (twoSiteHeisenbergOutputEquiv d n).symm
    (twoSiteHeisenbergInputEquiv d n).symm

/-- Actual finite Heisenberg conjugation is the same local two-link output
for every ambient tail length. Every exterior index, including the whole
tail, is an identity spectator in the result. This is a derived finite
locality identity, with no assumed compatibility or support equality.
Source: arXiv:1703.09188, StandardForm and eq:appendix-1, lines 603--622
and 2300--2306, in the complete-block domain stated above. -/
theorem twoSiteHeisenbergMatrix_conjugation {d D ℓ r : ℕ}
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (HalfPair d) ℂ}
    {v : Matrix (HalfPair d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (n : ℕ)
    (A : Matrix (HalfPair d) (HalfPair d) ℂ) :
    twoSiteHeisenbergMatrix W n * Matrix.rightKroneckerEmbed A *
        (twoSiteHeisenbergMatrix W n)ᴴ =
      Matrix.rightKroneckerEmbed (twoLinkOutputObservable u v A) := by
  rw [twoSiteHeisenbergMatrix_intertwiner S n A, Matrix.mul_assoc,
    (twoSiteHeisenbergMatrix_isUnitaryBetween S n).2, Matrix.mul_one]

end MPOTensor
