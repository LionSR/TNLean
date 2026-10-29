/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TwoSiteStandardFormCircuit
import TNLean.MPS.MPU.TwoSiteStandardFormOpenWord
import TNLean.MPS.MPU.TwoSiteStandardFormResidualWord
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

**Scope restriction (supplied standard form):** The conjugation and
buffering results use actual MPU unitarity and supplied two-site standard
form data, rather than constructing these data from a bare MPU. Canonical
interval compatibility is assembled in the accompanying buffered-action
module. The inverse family, source bond-dimension radius, and quasi-local
automorphism remain separate. See
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
  right_inv f := by
    funext i
    fin_cases i
    · rfl
    · exact finProdFinEquiv.apply_symm_apply (f 1)
    · rfl

private def windowOutputHeadEquiv (d : ℕ) :
    (HalfPair d × FourHalves d) ≃ (Fin 3 → Fin (d * d)) where
  toFun z := ![finProdFinEquiv (z.1.1, z.2.1.1),
    finProdFinEquiv (z.2.1.2, z.2.2.1), finProdFinEquiv (z.2.2.2, z.1.2)]
  invFun f :=
    (((finProdFinEquiv.symm (f 0)).1, (finProdFinEquiv.symm (f 2)).2),
      (((finProdFinEquiv.symm (f 0)).2, (finProdFinEquiv.symm (f 1)).1),
        ((finProdFinEquiv.symm (f 1)).2, (finProdFinEquiv.symm (f 2)).1)))
  left_inv z := by rcases z with ⟨⟨a, b⟩, ⟨⟨c, e⟩, ⟨f, g⟩⟩⟩; simp
  right_inv f := by
    funext i
    fin_cases i
    · exact finProdFinEquiv.apply_symm_apply (f 0)
    · exact finProdFinEquiv.apply_symm_apply (f 1)
    · exact finProdFinEquiv.apply_symm_apply (f 2)

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
  simp only [Matrix.one_mul, List.ofFn_succ, List.ofFn_zero]

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
    Matrix.mul (twoSiteHeisenbergMatrix W n) (Matrix.rightKroneckerEmbed A) =
      Matrix.mul (Matrix.rightKroneckerEmbed (twoLinkOutputObservable u v A))
        (twoSiteHeisenbergMatrix W n) := by
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
    Matrix.mul (Matrix.mul (twoSiteHeisenbergMatrix W n) (Matrix.rightKroneckerEmbed A))
        (twoSiteHeisenbergMatrix W n)ᴴ =
      Matrix.rightKroneckerEmbed (m := OutputExterior d n) (twoLinkOutputObservable u v A) := by
  rw [twoSiteHeisenbergMatrix_intertwiner S n A, Matrix.mul_assoc,
    (twoSiteHeisenbergMatrix_isUnitaryBetween S n).2, Matrix.mul_one]

private abbrev OriginalExterior (d p s : ℕ) (E : Type*) :=
  ((Fin p → Fin d) × (Fin s → Fin d)) × E

private def surroundWindowEquiv (α β γ δ : Type*) :
    (((α × δ) × β) × γ) ≃ (α × ((β × γ) × δ)) where
  toFun z := (z.1.1.1, ((z.1.2, z.2), z.1.1.2))
  invFun z := (((z.1, z.2.2), z.2.1.1), z.2.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def originalWindowMiddleEquiv (d k : ℕ) :
    (Fin 3 → Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k)) ≃
      (Fin (3 * (2 * k)) → Fin d) :=
  (Equiv.arrowCongr (Equiv.refl (Fin 3)) (twoSiteDirectBlockEquiv d k).symm).trans
    (MPSTensor.blockedConfigEquiv d 3 (2 * k))

private noncomputable def originalWindowConfigEquiv (d k p s : ℕ)
    {E C : Type*}
    (head : (E × C) ≃ (Fin 3 →
      Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k))) :
    (OriginalExterior d p s E × C) ≃ (Fin (p + (3 * (2 * k) + s)) → Fin d) :=
  (surroundWindowEquiv _ _ _ _).trans
    (((Equiv.refl (Fin p → Fin d)).prodCongr
      ((((head.trans (originalWindowMiddleEquiv d k)).prodCongr
        (Equiv.refl (Fin s → Fin d))).trans (Fin.appendEquiv (3 * (2 * k)) s)))).trans
          (Fin.appendEquiv p (3 * (2 * k) + s)))

/-- Complete original-chain input coordinates with arbitrary residual
prefix and suffix lengths. The middle observable is on two length-k
blocks; no divisibility condition on the whole chain is imposed.
Source: arXiv:1703.09188, finite conjugation, lines 2300--2306. -/
noncomputable def originalSiteHeisenbergInputEquiv (d k p s : ℕ) :
    (OriginalExterior d p s
      (Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k) ×
        Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k)) ×
          HalfPair (MPSTensor.blockPhysDim d k)) ≃
      (Fin (p + (3 * (2 * k) + s)) → Fin d) :=
  originalWindowConfigEquiv d k p s (windowInputHeadEquiv (MPSTensor.blockPhysDim d k))

/-- Complete original-chain output coordinates separate the four output
half-blocks from the arbitrary original residuals and exterior halves.
Source: arXiv:1703.09188, finite conjugation, lines 2300--2306. -/
noncomputable def originalSiteHeisenbergOutputEquiv (d k p s : ℕ) :
    (OriginalExterior d p s (HalfPair (MPSTensor.blockPhysDim d k)) ×
      FourHalves (MPSTensor.blockPhysDim d k)) ≃
        (Fin (p + (3 * (2 * k) + s)) → Fin d) :=
  originalWindowConfigEquiv d k p s (windowOutputHeadEquiv (MPSTensor.blockPhysDim d k))

/-- The actual original-site MPO, in complete window coordinates with
arbitrary original residual lengths. Source: arXiv:1703.09188,
StandardForm and eq:appendix-1, lines 603--622 and 2300--2306. -/
noncomputable def originalSiteHeisenbergMatrix {d D : ℕ}
    (U : MPOTensor d D) (k p s : ℕ) :
    Matrix (OriginalExterior d p s (HalfPair (MPSTensor.blockPhysDim d k)) ×
      FourHalves (MPSTensor.blockPhysDim d k))
      (OriginalExterior d p s
        (Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k) ×
          Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k)) ×
            HalfPair (MPSTensor.blockPhysDim d k)) ℂ :=
  Matrix.reindex (originalSiteHeisenbergOutputEquiv d k p s).symm
    (originalSiteHeisenbergInputEquiv d k p s).symm
      (mpo U (p + (3 * (2 * k) + s)))

private theorem originalSiteHeisenbergMatrix_apply {d D ℓ r k p s : ℕ}
    (U : MPOTensor d D)
    {u : Matrix (Fin ℓ × Fin r) (HalfPair (MPSTensor.blockPhysDim d k)) ℂ}
    {v : Matrix (HalfPair (MPSTensor.blockPhysDim d k)) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData (blockTwo (blockTensor U k)) u v)
    (e : OriginalExterior d p s (HalfPair (MPSTensor.blockPhysDim d k)))
    (f : OriginalExterior d p s
      (Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k) ×
        Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k)))
    (x : FourHalves (MPSTensor.blockPhysDim d k))
    (j : HalfPair (MPSTensor.blockPhysDim d k)) :
    originalSiteHeisenbergMatrix U k p s (e, x) (f, j) =
      twoSiteThreeBlockTrace S
        (evalWord U (List.ofFn e.1.1) (List.ofFn f.1.1))
        (evalWord U (List.ofFn e.1.2) (List.ofFn f.1.2))
        e.2.1 e.2.2 f.2.1 f.2.2 x j := by
  let midI := fun t : Fin 3 ↦ (twoSiteDirectBlockEquiv d k).symm
    (windowOutputHeadEquiv (MPSTensor.blockPhysDim d k) (e.2, x) t)
  let midJ := fun t : Fin 3 ↦ (twoSiteDirectBlockEquiv d k).symm
    (windowInputHeadEquiv (MPSTensor.blockPhysDim d k) (f.2, j) t)
  change mpo U (p + (3 * (2 * k) + s))
    (Fin.append e.1.1 (Fin.append
      (MPSTensor.blockedConfigEquiv d 3 (2 * k) midI) e.1.2))
    (Fin.append f.1.1 (Fin.append
      (MPSTensor.blockedConfigEquiv d 3 (2 * k) midJ) f.1.2)) = _
  apply originalSite_threeBlock_window_entry U k p s S
    e.1.1 f.1.1 e.1.2 f.1.2 midI midJ e.2.1 e.2.2 f.2.1 f.2.2 x j
  · funext t
    change (twoSiteDirectBlockEquiv d k)
      ((twoSiteDirectBlockEquiv d k).symm
        (windowOutputHeadEquiv (MPSTensor.blockPhysDim d k) (e.2, x) t)) = _
    exact (twoSiteDirectBlockEquiv d k).apply_symm_apply _
  · funext t
    change (twoSiteDirectBlockEquiv d k)
      ((twoSiteDirectBlockEquiv d k).symm
        (windowInputHeadEquiv (MPSTensor.blockPhysDim d k) (f.2, j) t)) = _
    exact (twoSiteDirectBlockEquiv d k).apply_symm_apply _

/-- Actual original-site finite MPO intertwining with arbitrary residual
prefix and suffix lengths. The whole chain need not be a multiple of the
simple-block length. Source: arXiv:1703.09188, StandardForm and
finite conjugation, lines 603--622 and 2300--2306. -/
theorem originalSiteHeisenbergMatrix_intertwiner {d D ℓ r : ℕ}
    (U : MPOTensor d D) (k p s : ℕ)
    {u : Matrix (Fin ℓ × Fin r) (HalfPair (MPSTensor.blockPhysDim d k)) ℂ}
    {v : Matrix (HalfPair (MPSTensor.blockPhysDim d k)) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData (blockTwo (blockTensor U k)) u v)
    (A : Matrix (HalfPair (MPSTensor.blockPhysDim d k))
      (HalfPair (MPSTensor.blockPhysDim d k)) ℂ) :
    Matrix.mul (originalSiteHeisenbergMatrix U k p s) (Matrix.rightKroneckerEmbed A) =
      Matrix.mul (Matrix.rightKroneckerEmbed (twoLinkOutputObservable u v A))
        (originalSiteHeisenbergMatrix U k p s) := by
  classical
  ext row col
  rcases row with ⟨e, x⟩
  rcases col with ⟨f, j⟩
  have h := congrArg (fun M ↦ M x j)
    (twoSite_threeBlock_trace_intertwiner_with_endpoints S
      (evalWord U (List.ofFn e.1.1) (List.ofFn f.1.1))
      (evalWord U (List.ofFn e.1.2) (List.ofFn f.1.2))
      e.2.1 e.2.2 f.2.1 f.2.2 A)
  simp only [Matrix.mul_apply] at h
  simpa [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.rightKroneckerEmbed_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, originalSiteHeisenbergMatrix_apply U S] using h

/-- The actual original finite MPO is unitary between the complete window
coordinate systems whenever its length is in the MPU convention.
Source: arXiv:1703.09188, UisUnitary and eq:appendix-1, lines 327--335
and 2300--2306. -/
theorem originalSiteHeisenbergMatrix_isUnitaryBetween {d D : ℕ}
    {U : MPOTensor d D} (hU : U.IsMPU) (k p s : ℕ)
    (hN : 1 < p + (3 * (2 * k) + s)) :
    (originalSiteHeisenbergMatrix U k p s).IsUnitaryBetween := by
  have h := (Matrix.isUnitaryBetween_iff_mem_unitaryGroup
    (mpo U (p + (3 * (2 * k) + s)))).mpr (hU.mpo_mem_unitaryGroup hN)
  exact h.reindex _ (originalSiteHeisenbergOutputEquiv d k p s).symm
    (originalSiteHeisenbergInputEquiv d k p s).symm

/-- The actual original-chain finite Heisenberg action of a middle
observable has the same local output for every residual prefix and suffix,
without a chain-length divisibility premise. This is a finite local
stabilization identity, not yet the arbitrary-region compatible action.
Source: arXiv:1703.09188, eq:appendix-1, lines 2300--2306. -/
theorem originalSiteHeisenbergMatrix_conjugation {d D ℓ r : ℕ}
    {U : MPOTensor d D} (hU : U.IsMPU) (k p s : ℕ)
    (hN : 1 < p + (3 * (2 * k) + s))
    {u : Matrix (Fin ℓ × Fin r) (HalfPair (MPSTensor.blockPhysDim d k)) ℂ}
    {v : Matrix (HalfPair (MPSTensor.blockPhysDim d k)) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData (blockTwo (blockTensor U k)) u v)
    (A : Matrix (HalfPair (MPSTensor.blockPhysDim d k))
      (HalfPair (MPSTensor.blockPhysDim d k)) ℂ) :
    Matrix.mul (Matrix.mul (originalSiteHeisenbergMatrix U k p s)
        (Matrix.rightKroneckerEmbed A)) (originalSiteHeisenbergMatrix U k p s)ᴴ =
      Matrix.rightKroneckerEmbed
        (m := OriginalExterior d p s (HalfPair (MPSTensor.blockPhysDim d k)))
        (twoLinkOutputObservable u v A) := by
  rw [originalSiteHeisenbergMatrix_intertwiner U k p s S A, Matrix.mul_assoc,
    (originalSiteHeisenbergMatrix_isUnitaryBetween hU k p s hN).2, Matrix.mul_one]


/-- Separate the complete exterior words from one consecutive finite window.
These coordinates keep the original site order inside all three words.
Source: arXiv:1703.09188, identity-tensor inclusion, lines 2292--2295. -/
def bufferedWindowConfigEquiv (d n p s : ℕ) :
    (((Fin p → Fin d) × (Fin s → Fin d)) × (Fin n → Fin d)) ≃
      (Fin (p + (n + s)) → Fin d) :=
  (switchMiddleEquiv _ _ _).trans
    ((Equiv.prodAssoc _ _ _).trans
      (((Equiv.refl (Fin p → Fin d)).prodCongr (Fin.appendEquiv n s)).trans
        (Fin.appendEquiv p (n + s))))

/-- Include a window matrix into original-site coordinates by adjoining
identity operators on arbitrary exterior words. Source: arXiv:1703.09188,
Appendix, identity-tensor inclusion in lines 2292--2295. -/
noncomputable def bufferedWindowMatrix (d n p s : ℕ)
    (A : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :
    Matrix (Fin (p + (n + s)) → Fin d) (Fin (p + (n + s)) → Fin d) ℂ :=
  Matrix.reindex (bufferedWindowConfigEquiv d n p s)
    (bufferedWindowConfigEquiv d n p s) (Matrix.rightKroneckerEmbed A)

private theorem originalWindowConfigEquiv_buffer {d k p s : ℕ} {E C : Type*}
    (head : (E × C) ≃ (Fin 3 →
      Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k)))
    (z : OriginalExterior d p s E × C) :
    originalWindowConfigEquiv d k p s head z =
      bufferedWindowConfigEquiv d (3 * (2 * k)) p s
        (z.1.1, (head.trans (originalWindowMiddleEquiv d k)) (z.1.2, z.2)) := rfl

private theorem originalWindowMatrix_eq_buffer {d k p s : ℕ} {E C : Type*}
    [Fintype E] [DecidableEq E] [Fintype C] [DecidableEq C]
    (head : (E × C) ≃ (Fin 3 →
      Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k)))
    (A : Matrix C C ℂ) :
    Matrix.reindex (originalWindowConfigEquiv d k p s head)
      (originalWindowConfigEquiv d k p s head) (Matrix.rightKroneckerEmbed A) =
    bufferedWindowMatrix d (3 * (2 * k)) p s
      (Matrix.reindex (head.trans (originalWindowMiddleEquiv d k))
        (head.trans (originalWindowMiddleEquiv d k)) (Matrix.rightKroneckerEmbed A)) := by
  classical
  ext row col
  obtain ⟨⟨⟨ex, e⟩, c⟩, rfl⟩ :=
    (originalWindowConfigEquiv d k p s head).surjective row
  obtain ⟨⟨⟨ex', e'⟩, c'⟩, rfl⟩ :=
    (originalWindowConfigEquiv d k p s head).surjective col
  simp only [Matrix.reindex_apply, Equiv.symm_apply_apply]
  rw [originalWindowConfigEquiv_buffer, originalWindowConfigEquiv_buffer]
  simp only [bufferedWindowMatrix, Matrix.reindex_apply, Equiv.symm_apply_apply,
    Matrix.rightKroneckerEmbed_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Prod.mk.injEq]
  by_cases he : ex = ex' <;> by_cases hh : e = e' <;> simp [he, hh]

/-- Full original-site configurations of the fixed window, separating
its central two-block input index from the two exterior block indices.
Source: arXiv:1703.09188, StandardForm, lines 603--622. -/
noncomputable def originalSiteHeisenbergInputWindowEquiv (d k : ℕ) :
    ((Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k) ×
      Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k)) ×
        HalfPair (MPSTensor.blockPhysDim d k)) ≃ (Fin (3 * (2 * k)) → Fin d) :=
  (windowInputHeadEquiv (MPSTensor.blockPhysDim d k)).trans (originalWindowMiddleEquiv d k)

/-- The input matrix on the fixed six-block window. Its central two
half-blocks carry the supplied observable and the other four half-blocks
carry identities. Source: arXiv:1703.09188, StandardForm and finite
conjugation, lines 603--622 and 2300--2306. -/
noncomputable def originalSiteHeisenbergInputWindow (d k : ℕ)
    (A : Matrix (HalfPair (MPSTensor.blockPhysDim d k))
      (HalfPair (MPSTensor.blockPhysDim d k)) ℂ) :
    Matrix (Fin (3 * (2 * k)) → Fin d) (Fin (3 * (2 * k)) → Fin d) ℂ :=
  Matrix.reindex
    (originalSiteHeisenbergInputWindowEquiv d k)
    (originalSiteHeisenbergInputWindowEquiv d k) (Matrix.rightKroneckerEmbed A)

/-- The actual output configuration order consists of two exterior half
blocks and the four consecutive output half blocks. Source: CPSV17,
StandardForm and eq:appendix-1, lines 603–622 and 2300–2306. -/
noncomputable def originalSiteHeisenbergOutputWindowEquiv (d k : ℕ) :
    (HalfPair (MPSTensor.blockPhysDim d k) ×
      FourHalves (MPSTensor.blockPhysDim d k)) ≃ (Fin (3 * (2 * k)) → Fin d) :=
  (windowOutputHeadEquiv (MPSTensor.blockPhysDim d k)).trans (originalWindowMiddleEquiv d k)

/-- The fixed six-block output matrix of the actual local action. Keeping
the two exterior half-blocks here makes adjoining original residual words
canonical without imposing divisibility on their lengths.
Source: arXiv:1703.09188, StandardForm and finite conjugation,
lines 603--622 and 2300--2306. -/
noncomputable def originalSiteHeisenbergOutputWindow {d ℓ r : ℕ} (k : ℕ)
    (u : Matrix (Fin ℓ × Fin r) (HalfPair (MPSTensor.blockPhysDim d k)) ℂ)
    (v : Matrix (HalfPair (MPSTensor.blockPhysDim d k)) (Fin r × Fin ℓ) ℂ)
    (A : Matrix (HalfPair (MPSTensor.blockPhysDim d k))
      (HalfPair (MPSTensor.blockPhysDim d k)) ℂ) :
    Matrix (Fin (3 * (2 * k)) → Fin d) (Fin (3 * (2 * k)) → Fin d) ℂ :=
  Matrix.reindex
    (originalSiteHeisenbergOutputWindowEquiv d k)
    (originalSiteHeisenbergOutputWindowEquiv d k)
    (Matrix.rightKroneckerEmbed (twoLinkOutputObservable u v A))

/-- The actual periodic MPO conjugates identity-tensor inclusions of the
same fixed input window to inclusions of the same fixed output window,
for every original-site prefix and suffix. No ambient-dependent output
matrix is chosen. Source: arXiv:1703.09188, eq:appendix-1, lines 2300--2306. -/
theorem mpo_bufferedWindow_conjugation {d D ℓ r : ℕ}
    {U : MPOTensor d D} (hU : U.IsMPU) (k p s : ℕ)
    (hN : 1 < p + (3 * (2 * k) + s))
    {u : Matrix (Fin ℓ × Fin r) (HalfPair (MPSTensor.blockPhysDim d k)) ℂ}
    {v : Matrix (HalfPair (MPSTensor.blockPhysDim d k)) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData (blockTwo (blockTensor U k)) u v)
    (A : Matrix (HalfPair (MPSTensor.blockPhysDim d k))
      (HalfPair (MPSTensor.blockPhysDim d k)) ℂ) :
    mpo U (p + (3 * (2 * k) + s)) *
        bufferedWindowMatrix d (3 * (2 * k)) p s
          (originalSiteHeisenbergInputWindow d k A) *
        (mpo U (p + (3 * (2 * k) + s)))ᴴ =
      bufferedWindowMatrix d (3 * (2 * k)) p s
        (originalSiteHeisenbergOutputWindow k u v A) := by
  let ei := originalSiteHeisenbergInputEquiv d k p s
  let eo := originalSiteHeisenbergOutputEquiv d k p s
  let M := originalSiteHeisenbergMatrix U k p s
  have hM : Matrix.reindex eo ei M = mpo U (p + (3 * (2 * k) + s)) := by
    ext row col
    simp [M, eo, ei, originalSiteHeisenbergMatrix, Matrix.reindex_apply]
  have hMH : Matrix.reindex ei eo Mᴴ = (mpo U (p + (3 * (2 * k) + s)))ᴴ := by
    rw [← Matrix.conjTranspose_reindex, hM]
  have h := congrArg (Matrix.reindexLinearEquiv ℂ ℂ eo eo)
    (originalSiteHeisenbergMatrix_conjugation hU k p s hN S A)
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ eo ei eo,
    ← Matrix.reindexLinearEquiv_mul ℂ ℂ eo ei ei] at h
  simp only [Matrix.coe_reindexLinearEquiv] at h
  rw [hM, hMH] at h
  simpa only [ei, eo, originalSiteHeisenbergInputEquiv,
    originalSiteHeisenbergOutputEquiv, originalWindowMatrix_eq_buffer,
    originalSiteHeisenbergInputWindow, originalSiteHeisenbergInputWindowEquiv,
    originalSiteHeisenbergOutputWindow] using h


/-- Original consecutive coordinates on the complete central two-block
input algebra. Source: arXiv:1703.09188, StandardForm and physical blocking,
lines 603--622. -/
noncomputable def originalSiteHeisenbergCentreEquiv (d k : ℕ) :
    HalfPair (MPSTensor.blockPhysDim d k) ≃ (Fin (2 * k) → Fin d) :=
  finProdFinEquiv.trans ((twoSiteDirectBlockEquiv d k).symm.trans
    (MPSTensor.decodeBlockEquiv d (2 * k)))

private theorem originalWindowMiddleEquiv_block (d k : ℕ)
    (w : Fin 3 → Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k))
    (i : Fin 3) (j : Fin (2 * k)) :
    originalWindowMiddleEquiv d k w (finProdFinEquiv (i, j)) =
      MPSTensor.decodeBlock d (2 * k) ((twoSiteDirectBlockEquiv d k).symm (w i)) j := by
  simp [originalWindowMiddleEquiv, MPSTensor.blockedConfigEquiv,
    Equiv.arrowCongr, Equiv.curry, Function.comp]

/-- The numbered middle interval reads exactly the complete central input
configuration; arXiv:1703.09188, StandardForm, lines 603--622. -/
theorem originalSiteHeisenbergInputWindowEquiv_middle (d k : ℕ)
    (e : Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k) ×
      Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k))
    (c : HalfPair (MPSTensor.blockPhysDim d k)) :
    (fun i : Fin (2 * k) ↦
      (originalSiteHeisenbergInputWindowEquiv d k) (e, c)
          ⟨2 * k + i.val, by omega⟩) = originalSiteHeisenbergCentreEquiv d k c := by
  funext i
  have hi : (⟨2 * k + i.val, by omega⟩ : Fin (3 * (2 * k))) =
      finProdFinEquiv ((1 : Fin 3), i) := by
    apply Fin.ext
    change 2 * k + i.val = i.val + (2 * k) * 1
    omega
  rw [hi]
  exact originalWindowMiddleEquiv_block d k _ 1 i

/-- Equality outside the complete central interval is exactly equality
of the two exterior block coordinates; arXiv:1703.09188, finite local
inclusions in lines 2292--2295. -/
theorem originalSiteHeisenbergInputWindowEquiv_outside_eq_iff (d k : ℕ)
    (e e' : Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k) ×
      Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k))
    (c c' : HalfPair (MPSTensor.blockPhysDim d k)) :
    (∀ i : Fin (3 * (2 * k)), ¬ (2 * k ≤ i.val ∧ i.val < 2 * k + 2 * k) →
      (originalSiteHeisenbergInputWindowEquiv d k) (e, c) i =
      (originalSiteHeisenbergInputWindowEquiv d k) (e', c') i) ↔ e = e' := by
  constructor
  · intro h
    apply Prod.ext
    · apply (twoSiteDirectBlockEquiv d k).symm.injective
      apply (MPSTensor.decodeBlockEquiv d (2 * k)).injective
      funext j
      have hj := h (finProdFinEquiv ((0 : Fin 3), j)) (by
        change ¬ (2 * k ≤ j.val + (2 * k) * 0 ∧
          j.val + (2 * k) * 0 < 2 * k + 2 * k)
        omega)
      simpa only [originalSiteHeisenbergInputWindowEquiv, Equiv.trans_apply,
        originalWindowMiddleEquiv_block] using hj
    · apply (twoSiteDirectBlockEquiv d k).symm.injective
      apply (MPSTensor.decodeBlockEquiv d (2 * k)).injective
      funext j
      have hj := h (finProdFinEquiv ((2 : Fin 3), j)) (by
        change ¬ (2 * k ≤ j.val + (2 * k) * 2 ∧
          j.val + (2 * k) * 2 < 2 * k + 2 * k)
        omega)
      simpa only [originalSiteHeisenbergInputWindowEquiv, Equiv.trans_apply,
        originalWindowMiddleEquiv_block] using hj
  · intro h
    subst e'
    intro i hi
    obtain ⟨⟨b, j⟩, rfl⟩ := finProdFinEquiv.surjective i
    fin_cases b
    · simp only [originalSiteHeisenbergInputWindowEquiv, Equiv.trans_apply,
        originalWindowMiddleEquiv_block]
    · exfalso
      apply hi
      change 2 * k ≤ j.val + (2 * k) * 1 ∧
        j.val + (2 * k) * 1 < 2 * k + 2 * k
      omega
    · simp only [originalSiteHeisenbergInputWindowEquiv, Equiv.trans_apply,
        originalWindowMiddleEquiv_block]


/-- The original central input decoder is the ordinary two-block
configuration concatenation. Source: CPSV17, StandardForm and physical
blocking, lines 603–622. -/
theorem originalSiteHeisenbergCentreEquiv_eq_blockedConfigEquiv (d k : ℕ)
    (c : HalfPair (MPSTensor.blockPhysDim d k)) :
    originalSiteHeisenbergCentreEquiv d k c =
      MPSTensor.blockedConfigEquiv d 2 k ![c.1, c.2] := by
  apply List.ofFn_injective
  change MPSTensor.wordOfBlock d (2 * k)
    ((twoSiteDirectBlockEquiv d k).symm (finProdFinEquiv c)) = _
  rw [wordOfBlock_twoSiteDirectBlockEquiv_symm, MPSTensor.ofFn_blockedConfigEquiv]
  simp [Kraus.flattenBlockedWord, List.ofFn_succ]

private theorem originalSiteHeisenbergCentreEquiv_block (d k : ℕ)
    (c : HalfPair (MPSTensor.blockPhysDim d k)) (b : Fin 2) (j : Fin k) :
    originalSiteHeisenbergCentreEquiv d k c (finProdFinEquiv (b, j)) =
      MPSTensor.decodeBlock d k (![c.1, c.2] b) j := by
  rw [originalSiteHeisenbergCentreEquiv_eq_blockedConfigEquiv]
  simp [MPSTensor.blockedConfigEquiv, Equiv.arrowCongr, Equiv.curry, Function.comp]

/-- Four consecutive output half-block indices in their actual word order.
Source: CPSV17, StandardForm and Appendix index comparison,
lines 603–622 and 2313–2334. -/
def originalSiteHeisenbergOutputBlockEquiv (b : ℕ) : FourHalves b ≃ (Fin 4 → Fin b) where
  toFun c := ![c.1.1, c.1.2, c.2.1, c.2.2]
  invFun f := ((f 0, f 1), (f 2, f 3))
  left_inv _ := rfl
  right_inv f := by funext i; fin_cases i <;> rfl

/-- Original coordinates on the four consecutive output half blocks.
Source: CPSV17, StandardForm, lines 603–622. -/
noncomputable def originalSiteHeisenbergOutputCentreEquiv (d k : ℕ) :
    FourHalves (MPSTensor.blockPhysDim d k) ≃ (Fin (4 * k) → Fin d) :=
  (originalSiteHeisenbergOutputBlockEquiv (MPSTensor.blockPhysDim d k)).trans
    (MPSTensor.blockedConfigEquiv d 4 k)

private theorem originalSiteHeisenbergOutputWindowEquiv_half (d k : ℕ)
    (e : HalfPair (MPSTensor.blockPhysDim d k))
    (c : FourHalves (MPSTensor.blockPhysDim d k))
    (b : Fin 3) (t : Fin 2) (j : Fin k) :
    originalSiteHeisenbergOutputWindowEquiv d k (e, c)
        (finProdFinEquiv (b, finProdFinEquiv (t, j))) =
      MPSTensor.decodeBlock d k
        (![![(e.1), c.1.1], ![c.1.2, c.2.1], ![c.2.2, (e.2)]] b t) j := by
  rw [originalSiteHeisenbergOutputWindowEquiv, Equiv.trans_apply,
    originalWindowMiddleEquiv_block]
  change originalSiteHeisenbergCentreEquiv d k
    (![(e.1, c.1.1), (c.1.2, c.2.1), (c.2.2, e.2)] b)
      (finProdFinEquiv (t, j)) = _
  rw [originalSiteHeisenbergCentreEquiv_block]
  fin_cases b <;> rfl

/-- The middle four-half-block interval of the actual six-half-block
output reads precisely its four output coordinates.
Source: CPSV17, StandardForm and eq:appendix-1, lines 603–622 and 2300–2306. -/
theorem originalSiteHeisenbergOutputWindowEquiv_middle (d k : ℕ)
    (e : HalfPair (MPSTensor.blockPhysDim d k))
    (c : FourHalves (MPSTensor.blockPhysDim d k)) :
    (fun i : Fin (4 * k) ↦ originalSiteHeisenbergOutputWindowEquiv d k (e, c)
      ⟨k + i.val, by omega⟩) = originalSiteHeisenbergOutputCentreEquiv d k c := by
  funext i
  obtain ⟨⟨t, j⟩, rfl⟩ := finProdFinEquiv.surjective i
  have hread (b : Fin 3) (s : Fin 2)
      (hi : k + (finProdFinEquiv (t, j)).val =
        (finProdFinEquiv (b, finProdFinEquiv (s, j))).val) :
      originalSiteHeisenbergOutputWindowEquiv d k (e, c)
        ⟨k + (finProdFinEquiv (t, j)).val, by omega⟩ =
      MPSTensor.decodeBlock d k
        (![![e.1, c.1.1], ![c.1.2, c.2.1], ![c.2.2, e.2]] b s) j := by
    have hidx : (⟨k + (finProdFinEquiv (t, j)).val, by omega⟩ : Fin (3 * (2 * k))) =
        finProdFinEquiv (b, finProdFinEquiv (s, j)) := Fin.ext hi
    rw [hidx, originalSiteHeisenbergOutputWindowEquiv_half]
  have hcentre : originalSiteHeisenbergOutputCentreEquiv d k c (finProdFinEquiv (t, j)) =
      MPSTensor.decodeBlock d k (![c.1.1, c.1.2, c.2.1, c.2.2] t) j := by
    simp [originalSiteHeisenbergOutputCentreEquiv, originalSiteHeisenbergOutputBlockEquiv,
      MPSTensor.blockedConfigEquiv, Equiv.arrowCongr, Equiv.curry, Function.comp]
  rw [hcentre]
  fin_cases t
  · exact hread 0 1 (by change k + (j.val + k * 0) = j.val + k * 1 + (2 * k) * 0; omega)
  · exact hread 1 0 (by change k + (j.val + k * 1) = j.val + k * 0 + (2 * k) * 1; omega)
  · exact hread 1 1 (by change k + (j.val + k * 2) = j.val + k * 1 + (2 * k) * 1; omega)
  · exact hread 2 0 (by change k + (j.val + k * 3) = j.val + k * 0 + (2 * k) * 2; omega)

/-- Equality outside the four consecutive output half blocks is exactly
equality of the two exterior half-block coordinates. Source: CPSV17,
identity-tensor inclusions and eq:appendix-1, lines 2292–2306. -/
theorem originalSiteHeisenbergOutputWindowEquiv_outside_eq_iff (d k : ℕ)
    (e e' : HalfPair (MPSTensor.blockPhysDim d k))
    (c c' : FourHalves (MPSTensor.blockPhysDim d k)) :
    (∀ i : Fin (3 * (2 * k)), ¬ (k ≤ i.val ∧ i.val < k + 4 * k) →
      originalSiteHeisenbergOutputWindowEquiv d k (e, c) i =
        originalSiteHeisenbergOutputWindowEquiv d k (e', c') i) ↔ e = e' := by
  constructor
  · intro h
    apply Prod.ext
    · apply (MPSTensor.decodeBlockEquiv d k).injective
      funext j
      have hj := h (finProdFinEquiv ((0 : Fin 3), finProdFinEquiv ((0 : Fin 2), j)))
        (by change ¬ (k ≤ j.val + k * 0 + (2 * k) * 0 ∧
          j.val + k * 0 + (2 * k) * 0 < k + 4 * k); omega)
      simpa only [originalSiteHeisenbergOutputWindowEquiv_half,
        Matrix.cons_val_zero] using hj
    · apply (MPSTensor.decodeBlockEquiv d k).injective
      funext j
      have hj := h (finProdFinEquiv ((2 : Fin 3), finProdFinEquiv ((1 : Fin 2), j)))
        (by change ¬ (k ≤ j.val + k * 1 + (2 * k) * 2 ∧
          j.val + k * 1 + (2 * k) * 2 < k + 4 * k); omega)
      simpa only [originalSiteHeisenbergOutputWindowEquiv_half, Matrix.cons_val_succ,
        Matrix.cons_val_zero] using hj
  · intro h
    subst e'
    intro i hi
    obtain ⟨⟨b, q⟩, rfl⟩ := finProdFinEquiv.surjective i
    obtain ⟨⟨t, j⟩, rfl⟩ := finProdFinEquiv.surjective q
    fin_cases b <;> fin_cases t
    · simp only [originalSiteHeisenbergOutputWindowEquiv_half, Matrix.cons_val_zero]
    · exfalso; apply hi
      change k ≤ j.val + k * 1 + (2 * k) * 0 ∧
        j.val + k * 1 + (2 * k) * 0 < k + 4 * k
      omega
    · exfalso; apply hi
      change k ≤ j.val + k * 0 + (2 * k) * 1 ∧
        j.val + k * 0 + (2 * k) * 1 < k + 4 * k
      omega
    · exfalso; apply hi
      change k ≤ j.val + k * 1 + (2 * k) * 1 ∧
        j.val + k * 1 + (2 * k) * 1 < k + 4 * k
      omega
    · exfalso; apply hi
      change k ≤ j.val + k * 0 + (2 * k) * 2 ∧
        j.val + k * 0 + (2 * k) * 2 < k + 4 * k
      omega
    · simp only [originalSiteHeisenbergOutputWindowEquiv_half, Matrix.cons_val_succ,
        Matrix.cons_val_zero]

end MPOTensor
