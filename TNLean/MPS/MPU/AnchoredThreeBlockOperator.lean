/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.AnchoredResidualCoordinates
import TNLean.MPS.MPU.TwoSiteStandardFormResidualWord

/-!
# A three-block operator on an anchored finite chain

A finite chain with three consecutive complete blocks is written with an
arbitrary original-site prefix and suffix. Its output configurations are
reindexed by the four shifted half-blocks and all exterior output letters;
its input configurations are reindexed by the central complete block and all
exterior input letters. Each fixed-exterior slice of the periodic MPO matrix
is the three-block window of the supplied two-site standard form.

The open-word identity then becomes an operator intertwiner for the full
finite-chain MPO matrix. If the original tensor is an MPU, conjugation by
that matrix sends an observable on the central input block to an observable
on the four neighboring output half-blocks, with the identity on all
exterior output coordinates. The prefix and suffix are arbitrary and may
contain residual sites or further complete blocks.

This statement assumes supplied two-site standard-form data on the blocked
tensor. It does not construct such data, identify the output-coordinate
Kronecker product with site-indexed local inclusion, or establish
interval-independent QCA conjugation.

## References

* arXiv:1703.09188, equations `uuvv` and `StandardForm`, lines 532--543,
  603--622, and 2300--2306.
* arXiv:1606.00608, Appendix C.4, lines 1952--2017.
-/

namespace MPOTensor

private def sixCellShuffle (P : Type*) :
    ((P × P) × ((P × P) × (P × P))) ≃
      (((P × P) × (P × P)) × (P × P)) where
  toFun := fun e => (((e.1.1, e.2.1.1), (e.2.1.2, e.2.2.1)),
    (e.2.2.2, e.1.2))
  invFun := fun t => ((t.1.1.1, t.2.2), ((t.1.1.2, t.1.2.1),
    (t.1.2.2, t.2.1)))
  left_inv := by intro ⟨⟨_, _⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩; rfl
  right_inv := by intro ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩; rfl

private def threeTupleEquiv (B : Type*) :
    ((B × B) × B) ≃ (Fin 3 → B) :=
  ((Equiv.prodAssoc B B B).trans
    ((Equiv.refl B).prodCongr (finTwoArrowEquiv B).symm)).trans
    (Fin.consEquiv fun _ : Fin 3 => B)

private theorem threeTupleEquiv_apply (B : Type*) (b₀ b₁ b₂ : B) :
    threeTupleEquiv B ((b₀, b₁), b₂) = ![b₀, b₁, b₂] := by
  funext t
  fin_cases t <;> rfl

/-- The three direct physical blocks on the output side, parametrized by the
four neighboring half-blocks and the two exposed exterior half-blocks.
Source context: arXiv:1703.09188, `StandardForm`, lines 603--622. -/
noncomputable def threeBlockOutputEquiv (d k : ℕ) :
    ((Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ×
      (((Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ×
        (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))))) ≃
      (Fin 3 → Fin (MPSTensor.blockPhysDim d (2 * k))) := by
  let P := Fin (MPSTensor.blockPhysDim d k)
  let Q := Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k)
  let e₁ := sixCellShuffle P
  let e₂ := threeTupleEquiv (P × P)
  let e₃ : (Fin 3 → P × P) ≃ (Fin 3 → Q) :=
    Equiv.arrowCongr (Equiv.refl _) finProdFinEquiv
  let e₄ : (Fin 3 → Q) ≃ (Fin 3 → Fin (MPSTensor.blockPhysDim d (2 * k))) :=
    Equiv.arrowCongr (Equiv.refl _) (twoSiteDirectBlockEquiv d k).symm
  exact ((e₁.trans e₂).trans e₃).trans e₄

/-- The output relabeling has the shifted order of the source three-block word. -/
theorem threeBlockOutputEquiv_apply (d k : ℕ)
    (eL eR : Fin (MPSTensor.blockPhysDim d k))
    (x : ((Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ×
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)))) :
    threeBlockOutputEquiv d k ((eL, eR), x) =
      fun t => (twoSiteDirectBlockEquiv d k).symm
        (![finProdFinEquiv (eL, x.1.1), finProdFinEquiv (x.1.2, x.2.1),
          finProdFinEquiv (x.2.2, eR)] t) := by
  funext t
  fin_cases t <;>
    simp [threeBlockOutputEquiv, sixCellShuffle, threeTupleEquiv,
      Fin.consEquiv, finTwoArrowEquiv]

/-- The input relabeling singles out the central block and retains the two
outer complete input blocks. Source context: arXiv:1703.09188,
`StandardForm`, lines 603--622. -/
noncomputable def threeBlockInputEquiv (d k : ℕ) :
    ((Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k) ×
      Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k)) ×
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))) ≃
      (Fin 3 → Fin (MPSTensor.blockPhysDim d (2 * k))) := by
  let P := Fin (MPSTensor.blockPhysDim d k)
  let Q := Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k)
  let e₁ : ((Q × Q) × (P × P)) ≃ ((Q × Q) × Q) :=
    (Equiv.refl _).prodCongr finProdFinEquiv
  let e₁' : ((Q × Q) × Q) ≃ ((Q × Q) × Q) :=
    { toFun := fun t => ((t.1.1, t.2), t.1.2)
      invFun := fun t => ((t.1.1, t.2), t.1.2)
      left_inv := by intro ⟨⟨_, _⟩, _⟩; rfl
      right_inv := by intro ⟨⟨_, _⟩, _⟩; rfl }
  let e₂ := threeTupleEquiv Q
  let e₃ : (Fin 3 → Q) ≃ (Fin 3 → Fin (MPSTensor.blockPhysDim d (2 * k))) :=
    Equiv.arrowCongr (Equiv.refl _) (twoSiteDirectBlockEquiv d k).symm
  exact ((e₁.trans e₁').trans e₂).trans e₃

/-- The central input pair is the middle letter in the three-block word. -/
theorem threeBlockInputEquiv_apply (d k : ℕ)
    (j₀ j₂ : Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k))
    (j : Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) :
    threeBlockInputEquiv d k ((j₀, j₂), j) =
      fun t => (twoSiteDirectBlockEquiv d k).symm
        (![j₀, finProdFinEquiv j, j₂] t) := by
  funext t
  fin_cases t <;>
    simp [threeBlockInputEquiv, threeTupleEquiv,
      Fin.consEquiv, finTwoArrowEquiv]

private def outerShuffle (A B C X : Type*) :
    (((A × B) × C) × X) ≃ ((A × (B × X)) × C) where
  toFun := fun t => ((t.1.1.1, (t.1.1.2, t.2)), t.1.2)
  invFun := fun t => (((t.1.1, t.1.2.1), t.2), t.1.2.2)
  left_inv := by intro ⟨⟨⟨_, _⟩, _⟩, _⟩; rfl
  right_inv := by intro ⟨⟨_, ⟨_, _⟩⟩, _⟩; rfl

end MPOTensor

namespace MPOTensor

private abbrev Half (d k : ℕ) := Fin (MPSTensor.blockPhysDim d k)
private abbrev Pair (d k : ℕ) := Half d k × Half d k
private abbrev Quad (d k : ℕ) := Pair d k × Pair d k
private abbrev PairLabel (d k : ℕ) :=
  Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k)
private abbrev OutputExterior (d k p s : ℕ) :=
  (((Fin p → Fin d) × (Half d k × Half d k)) × (Fin s → Fin d))
private abbrev InputExterior (d k p s : ℕ) :=
  (((Fin p → Fin d) × (PairLabel d k × PairLabel d k)) × (Fin s → Fin d))

/-- Reindex a finite interval by all output letters outside the four shifted
half-blocks, followed by those four half-blocks. -/
noncomputable def threeBlockOutputConfigEquiv (d k p s : ℕ) (a : ℤ) :
    (OutputExterior d k p s × Quad d k) ≃
      SpinChain.Config d (SpinChain.finiteChainRegion a (p + (3 * (2 * k) + s))) := by
  let e₁ := outerShuffle (Fin p → Fin d) (Half d k × Half d k)
    (Fin s → Fin d) (Quad d k)
  let e₂ := (Equiv.refl (Fin p → Fin d)).prodCongr
    (threeBlockOutputEquiv d k)
  let e₃ := e₂.prodCongr (Equiv.refl (Fin s → Fin d))
  exact (e₁.trans e₃).trans
    (SpinChain.anchoredResidualConfigEquiv d (p + (3 * (2 * k) + s))
      (2 * k) p 3 s a rfl)

/-- Reindex the same interval by all input letters outside its central
complete block, followed by the central input pair. -/
noncomputable def threeBlockInputConfigEquiv (d k p s : ℕ) (a : ℤ) :
    (InputExterior d k p s × Pair d k) ≃
      SpinChain.Config d (SpinChain.finiteChainRegion a (p + (3 * (2 * k) + s))) := by
  let e₁ := outerShuffle (Fin p → Fin d) (PairLabel d k × PairLabel d k)
    (Fin s → Fin d) (Pair d k)
  let e₂ := (Equiv.refl (Fin p → Fin d)).prodCongr
    (threeBlockInputEquiv d k)
  let e₃ := e₂.prodCongr (Equiv.refl (Fin s → Fin d))
  exact (e₁.trans e₃).trans
    (SpinChain.anchoredResidualConfigEquiv d (p + (3 * (2 * k) + s))
      (2 * k) p 3 s a rfl)

/-- The output configuration equivalence preserves the original-site prefix,
the four local output half-blocks, and the original-site suffix in order. -/
theorem threeBlockOutputConfigEquiv_apply (d k p s : ℕ) (a : ℤ)
    (pre : Fin p → Fin d) (edges : Half d k × Half d k)
    (suf : Fin s → Fin d) (x : Quad d k) :
    threeBlockOutputConfigEquiv d k p s a (((pre, edges), suf), x) =
      SpinChain.anchoredResidualConfig d (p + (3 * (2 * k) + s))
        (2 * k) p 3 s a rfl pre (threeBlockOutputEquiv d k (edges, x)) suf := by
  change SpinChain.anchoredResidualConfigEquiv d (p + (3 * (2 * k) + s))
      (2 * k) p 3 s a rfl ((pre, threeBlockOutputEquiv d k (edges, x)), suf) = _
  exact SpinChain.anchoredResidualConfigEquiv_apply d (p + (3 * (2 * k) + s))
    (2 * k) p 3 s a rfl pre _ suf

/-- The input configuration equivalence preserves the original-site prefix,
the central complete block, and the original-site suffix in order. -/
theorem threeBlockInputConfigEquiv_apply (d k p s : ℕ) (a : ℤ)
    (pre : Fin p → Fin d) (outer : PairLabel d k × PairLabel d k)
    (suf : Fin s → Fin d) (j : Pair d k) :
    threeBlockInputConfigEquiv d k p s a (((pre, outer), suf), j) =
      SpinChain.anchoredResidualConfig d (p + (3 * (2 * k) + s))
        (2 * k) p 3 s a rfl pre (threeBlockInputEquiv d k (outer, j)) suf := by
  change SpinChain.anchoredResidualConfigEquiv d (p + (3 * (2 * k) + s))
      (2 * k) p 3 s a rfl ((pre, threeBlockInputEquiv d k (outer, j)), suf) = _
  exact SpinChain.anchoredResidualConfigEquiv_apply d (p + (3 * (2 * k) + s))
    (2 * k) p 3 s a rfl pre _ suf

end MPOTensor
namespace MPOTensor

/-- The full periodic MPO matrix in the output and input three-block
coordinates. The two coordinate spaces have equal total dimension but
different exterior factors. Source context: arXiv:1703.09188,
lines 603--622 and 2300--2306. -/
noncomputable def threeBlockFiniteChainMatrix
    {d D : ℕ} (U : MPOTensor d D) (k p s : ℕ) (a : ℤ) :
    Matrix (OutputExterior d k p s × Quad d k)
      (InputExterior d k p s × Pair d k) ℂ :=
  fun x j => SpinChain.finiteChainMPOMatrix U (p + (3 * (2 * k) + s)) a
    (threeBlockOutputConfigEquiv d k p s a x)
    (threeBlockInputConfigEquiv d k p s a j)

/-- Fixing every exterior input and output coordinate recovers precisely
the original-site three-block window, including arbitrary prefix and suffix
matrix products. Source context: arXiv:1703.09188, lines 603--622. -/
theorem threeBlockFiniteChainMatrix_slice
    {d D ℓ r : ℕ} (U : MPOTensor d D) (k p s : ℕ) (a : ℤ)
    {u : Matrix (Fin ℓ × Fin r)
      (Pair d k) ℂ}
    {v : Matrix (Pair d k) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData (blockTwo (blockTensor U k)) u v)
    (preI preJ : Fin p → Fin d) (sufI sufJ : Fin s → Fin d)
    (eL eR : Half d k) (j₀ j₂ : PairLabel d k) :
    (show Matrix (Quad d k) (Pair d k) ℂ from
      fun x j => threeBlockFiniteChainMatrix U k p s a
        (((preI, (eL, eR)), sufI), x)
        (((preJ, (j₀, j₂)), sufJ), j)) =
      twoSiteThreeBlockTrace S
        (evalWord U (List.ofFn preI) (List.ofFn preJ))
        (evalWord U (List.ofFn sufI) (List.ofFn sufJ))
        eL eR j₀ j₂ := by
  ext x j
  have hI : (fun t => twoSiteDirectBlockEquiv d k
      (threeBlockOutputEquiv d k ((eL, eR), x) t)) =
      ![finProdFinEquiv (eL, x.1.1), finProdFinEquiv (x.1.2, x.2.1),
        finProdFinEquiv (x.2.2, eR)] := by
    funext t
    rw [threeBlockOutputEquiv_apply]
    simp
  have hJ : (fun t => twoSiteDirectBlockEquiv d k
      (threeBlockInputEquiv d k ((j₀, j₂), j) t)) =
      ![j₀, finProdFinEquiv j, j₂] := by
    funext t
    rw [threeBlockInputEquiv_apply]
    simp
  change SpinChain.finiteChainMPOMatrix U (p + (3 * (2 * k) + s)) a
      (threeBlockOutputConfigEquiv d k p s a
        (((preI, (eL, eR)), sufI), x))
      (threeBlockInputConfigEquiv d k p s a
        (((preJ, (j₀, j₂)), sufJ), j)) = _
  rw [threeBlockOutputConfigEquiv_apply, threeBlockInputConfigEquiv_apply]
  rw [SpinChain.finiteChainMPOMatrix_apply_anchoredResidualConfig]
  simpa only [Fin.cast_refl, id_eq, Function.comp_id] using
    originalSite_threeBlock_window_entry U k p s S preI preJ sufI sufJ
      (threeBlockOutputEquiv d k ((eL, eR), x))
      (threeBlockInputEquiv d k ((j₀, j₂), j)) eL eR j₀ j₂ x j hI hJ

end MPOTensor

namespace Matrix

/-- If every fixed-exterior slice intertwines an input and output operator,
then the full matrix intertwines their tensor products with the identities
on the exterior factors. -/
theorem intertwiner_of_slices
    {E F X J : Type*}
    [Fintype E] [Fintype F] [Fintype X] [Fintype J]
    [DecidableEq E] [DecidableEq F]
    (U : Matrix (E × X) (F × J) ℂ)
    (A : Matrix J J ℂ) (B : Matrix X X ℂ)
    (h : ∀ e f, (show Matrix X J ℂ from fun x j => U (e, x) (f, j)) * A =
      B * (show Matrix X J ℂ from fun x j => U (e, x) (f, j))) :
    U * Matrix.kronecker (1 : Matrix F F ℂ) A =
      Matrix.kronecker (1 : Matrix E E ℂ) B * U := by
  ext ⟨e, x⟩ ⟨f, j⟩
  have hs := congrArg (fun M : Matrix X J ℂ => M x j) (h e f)
  change (∑ t : J, U (e, x) (f, t) * A t j) =
    ∑ t : X, B x t * U (e, t) (f, j) at hs
  simpa [Matrix.mul_apply, Matrix.kronecker_apply, Fintype.sum_prod_type,
    Matrix.one_apply, mul_ite] using hs

end Matrix

namespace MPOTensor

/-- The complete anchored finite-chain MPO intertwines a central-block input
observable with the same two-link output observable at every exterior word.
No MPU assumption is needed. Source context: arXiv:1703.09188,
equations `uuvv` and `StandardForm`, lines 532--543 and 603--622. -/
theorem threeBlockFiniteChainMatrix_intertwiner
    {d D ℓ r : ℕ} (U : MPOTensor d D) (k p s : ℕ) (a : ℤ)
    {u : Matrix (Fin ℓ × Fin r) (Pair d k) ℂ}
    {v : Matrix (Pair d k) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData (blockTwo (blockTensor U k)) u v)
    (A : Matrix (Pair d k) (Pair d k) ℂ) :
    threeBlockFiniteChainMatrix U k p s a *
        Matrix.kronecker (1 : Matrix (InputExterior d k p s) (InputExterior d k p s) ℂ) A =
      Matrix.kronecker (1 : Matrix (OutputExterior d k p s) (OutputExterior d k p s) ℂ)
          (twoLinkOutputObservable u v A) *
        threeBlockFiniteChainMatrix U k p s a := by
  classical
  apply Matrix.intertwiner_of_slices
  intro e f
  rcases e with ⟨⟨preI, ⟨eL, eR⟩⟩, sufI⟩
  rcases f with ⟨⟨preJ, ⟨j₀, j₂⟩⟩, sufJ⟩
  rw [threeBlockFiniteChainMatrix_slice U k p s a S preI preJ sufI sufJ eL eR j₀ j₂]
  exact twoSite_threeBlock_trace_intertwiner_with_endpoints S
    (evalWord U (List.ofFn preI) (List.ofFn preJ))
    (evalWord U (List.ofFn sufI) (List.ofFn sufJ)) eL eR j₀ j₂ A

end MPOTensor

namespace MPOTensor

/-- For an MPU, finite-chain conjugation of a central-block observable is
the identity on all exterior output coordinates tensored with the two-link
output observable. The chain has an arbitrary original-site prefix and
suffix. This is a coordinate support statement, not yet the corresponding
site-indexed local-algebra inclusion. Source context: arXiv:1703.09188,
lines 603--622 and 2300--2306. -/
theorem threeBlockFiniteChainMatrix_conjugation
    {d D ℓ r : ℕ} {U : MPOTensor d D} (hU : U.IsMPU)
    (k p s : ℕ) (a : ℤ) (hN : 1 < p + (3 * (2 * k) + s))
    {u : Matrix (Fin ℓ × Fin r) (Pair d k) ℂ}
    {v : Matrix (Pair d k) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData (blockTwo (blockTensor U k)) u v)
    (A : Matrix (Pair d k) (Pair d k) ℂ) :
    let M := threeBlockFiniteChainMatrix U k p s a
    M * Matrix.kronecker
        (1 : Matrix (InputExterior d k p s) (InputExterior d k p s) ℂ) A * Mᴴ =
      Matrix.kronecker
        (1 : Matrix (OutputExterior d k p s) (OutputExterior d k p s) ℂ)
        (twoLinkOutputObservable u v A) := by
  dsimp only
  classical
  let C := SpinChain.finiteChainMPOMatrix U (p + (3 * (2 * k) + s)) a
  have hC : C.IsUnitaryBetween := by
    apply (Matrix.isUnitaryBetween_iff_mem_unitaryGroup C).2
    exact (SpinChain.finiteChainMPUUnitary hU hN a).property
  have hM : (threeBlockFiniteChainMatrix U k p s a).IsUnitaryBetween := by
    have hR : threeBlockFiniteChainMatrix U k p s a =
        Matrix.reindex (threeBlockOutputConfigEquiv d k p s a).symm
          (threeBlockInputConfigEquiv d k p s a).symm C := by
      rfl
    rw [hR]
    exact hC.reindex C _ _
  calc
    threeBlockFiniteChainMatrix U k p s a *
        Matrix.kronecker (1 : Matrix (InputExterior d k p s) (InputExterior d k p s) ℂ) A *
        (threeBlockFiniteChainMatrix U k p s a)ᴴ =
      (Matrix.kronecker
          (1 : Matrix (OutputExterior d k p s) (OutputExterior d k p s) ℂ)
          (twoLinkOutputObservable u v A) *
        threeBlockFiniteChainMatrix U k p s a) *
        (threeBlockFiniteChainMatrix U k p s a)ᴴ := by
          rw [threeBlockFiniteChainMatrix_intertwiner U k p s a S A]
    _ = Matrix.kronecker
          (1 : Matrix (OutputExterior d k p s) (OutputExterior d k p s) ℂ)
          (twoLinkOutputObservable u v A) := by
          rw [Matrix.mul_assoc, hM.2, Matrix.mul_one]

end MPOTensor
