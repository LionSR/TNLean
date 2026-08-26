/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.BondReindex
import TNLean.MPS.FundamentalTheorem.SectorBNT.Supplier
import TNLean.MPS.SharedInfra.BlockAssembly

/-!
# Exact reconstruction from prepared blocks

This module strengthens the prepared-block SectorBNT supplier from positive-length
matrix-product-vector equality to a letterwise reconstruction. It retains the precise
phase-class scalar, assembles the resulting block gauges, and reindexes the heterogeneous
block sum by an equivalence of flattened bond coordinates. The bundled
`PreparedBNTBlocks.exists_isBNTCanonicalForm_exact` method exposes this reconstruction
without repeating the prepared family and its invariants.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

private lemma cast_gl_conj_apply {n m : ℕ} (h : n = m)
    (G : GL (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) (x y : Fin m) :
    (((cast (congr_arg (fun t => GL (Fin t) ℂ) h.symm) G : GL (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ) * B *
          (↑((cast (congr_arg (fun t => GL (Fin t) ℂ) h.symm) G :
            GL (Fin n) ℂ)⁻¹) : Matrix (Fin n) (Fin n) ℂ))
      (Fin.cast h.symm x) (Fin.cast h.symm y) =
    ((G : Matrix (Fin m) (Fin m) ℂ) *
      cast (congr_arg (fun t => Matrix (Fin t) (Fin t) ℂ) h) B *
      (↑(G⁻¹) : Matrix (Fin m) (Fin m) ℂ)) x y := by
  subst h
  rfl

/-- Prepared TP, primitive, irreducible blocks admit an exact BNT reconstruction after a
coordinate permutation and a block-diagonal gauge.

The equality retains the precise phase-class scalar used in the collapsed BNT weights. It is
therefore letterwise, not only an equality of positive-length matrix product vectors.

Source: arXiv:1606.00608, lines 237--301, 1080--1117, and 1135--1148;
arXiv:2011.12127, lines 1831--1885. -/
theorem exists_isBNTCanonicalForm_exact_of_tp_primitive_irr_blocks
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hDim : ∀ k, 0 < dim k)
    (hTP : ∀ k, IsLeftCanonical (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (Kraus.transferMap (blocks k)))
    (hIrr : ∀ k, Kraus.IsIrreducibleFamily (blocks k))
    (hμne : ∀ k, μ k ≠ 0)
    (hμLe : ∀ k, ‖μ k‖ ≤ 1)
    (hμUnit : ∃ k, ‖μ k‖ = 1) :
    ∃ P : SectorDecomposition d,
      IsBNTCanonicalForm P ∧ P.totalDim = ∑ k : Fin r, dim k ∧
      ∃ e : Fin P.totalDim ≃ Fin (∑ k : Fin r, dim k),
      ∃ X : GL (Fin P.totalDim) ℂ, ∀ i,
        toTensorFromBlocks (d := d) μ blocks i =
          Matrix.reindex e e
            ((X : Matrix _ _ ℂ) * P.toTensor i * (↑(X⁻¹) : Matrix _ _ ℂ)) := by
  classical
  have : ∀ k, NeZero (dim k) := fun k => ⟨(hDim k).ne'⟩
  let P := collapsedBntSectorDecomp (d := d) μ blocks hμne
  have hBNT := isBNTCanonicalForm_collapsedBntSectorDecomp_of_tp_primitive_irr_blocks
    μ blocks hDim hTP hPrim hIrr hμne hμLe hμUnit
  have hTotal := collapsedBntSectorDecomp_totalDim_eq_sum_dim_of_tp_primitive_irr
    μ blocks hDim hTP hPrim hIrr hμne
  choose hEq G hG using fun j q =>
    exists_gauge_choose_MPVBlockPhaseEquiv_of_tp_primitive_irr
      (hTP ((mpvPhaseClassData (d := d) blocks).repr j))
      (hTP ((mpvPhaseClassData (d := d) blocks).enum j q))
      (hPrim ((mpvPhaseClassData (d := d) blocks).repr j))
      (hPrim ((mpvPhaseClassData (d := d) blocks).enum j q))
      (hIrr ((mpvPhaseClassData (d := d) blocks).repr j))
      (hIrr ((mpvPhaseClassData (d := d) blocks).enum j q))
      ((mpvPhaseClassData (d := d) blocks).enum_phase j q)
  let copyEquiv : Fin P.totalCopies ≃ Fin r :=
    P.flatIndexEquiv.symm.trans (mpvPhaseClassData (d := d) blocks).enumEquiv
  have hFlatDim : ∀ s : Fin P.totalCopies, P.flatDim s = dim (copyEquiv s) := by
    intro s
    let jq := P.flatIndexEquiv.symm s
    change dim ((mpvPhaseClassData (d := d) blocks).repr jq.1) =
      dim ((mpvPhaseClassData (d := d) blocks).enum jq.1 jq.2)
    exact hEq jq.1 jq.2
  let Xcopy : (jq : (j : Fin P.basisCount) × Fin (P.copies j)) →
      GL (Fin (P.basisDim jq.1)) ℂ := fun jq =>
    cast (congr_arg (fun n => GL (Fin n) ℂ) (hEq jq.1 jq.2).symm)
      (G jq.1 jq.2)
  let Xflat : (s : Fin P.totalCopies) → GL (Fin (P.flatDim s)) ℂ := fun s =>
    Xcopy (P.flatIndexEquiv.symm s)
  let X := globalGaugeOfBlocks Xflat
  let gaugedFlat : (s : Fin P.totalCopies) → MPSTensor d (P.flatDim s) := fun s i =>
    (Xflat s : Matrix _ _ ℂ) * P.flatBasis s i *
      (↑((Xflat s)⁻¹) : Matrix _ _ ℂ)
  have hX : ∀ i, (X : Matrix _ _ ℂ) * P.toTensor i *
      (↑(X⁻¹) : Matrix _ _ ℂ) =
      toTensorFromBlocks (d := d) P.flatWeight gaugedFlat i := by
    intro i
    symm
    exact toTensorFromBlocks_eq_globalGaugeOfBlocks_conj P.flatWeight P.flatBasis
      gaugedFlat Xflat (fun _ _ => rfl) i
  let blockEquiv : Fin r ≃ Fin P.totalCopies :=
    (mpvPhaseClassData (d := d) blocks).enumEquiv.symm.trans P.flatIndexEquiv
  have hBlockDim : ∀ k : Fin r, dim k = P.flatDim (blockEquiv k) := by
    intro k
    let jq := (mpvPhaseClassData (d := d) blocks).enumEquiv.symm k
    have hb : blockEquiv k = P.flatIndexEquiv jq := by
      simp [blockEquiv, jq]
      rfl
    rw [hb, hFlatDim]
    have hcopy : copyEquiv (P.flatIndexEquiv jq) =
        (mpvPhaseClassData (d := d) blocks).enum jq.1 jq.2 := by
      change (mpvPhaseClassData (d := d) blocks).enumEquiv
        (P.flatIndexEquiv.symm (P.flatIndexEquiv jq)) =
          (mpvPhaseClassData (d := d) blocks).enum jq.1 jq.2
      exact congrArg (mpvPhaseClassData (d := d) blocks).enumEquiv
        (P.flatIndexEquiv.symm_apply_apply jq) |>.trans
          ((mpvPhaseClassData (d := d) blocks).enumEquiv_apply jq.1 jq.2)
    rw [hcopy]
    exact congrArg dim ((mpvPhaseClassData (d := d) blocks).enumEquiv.apply_symm_apply k).symm
  have hBlock : ∀ k i, μ k • blocks k i =
      Matrix.reindex (finCongr (hBlockDim k)).symm (finCongr (hBlockDim k)).symm
        (P.flatWeight (blockEquiv k) • gaugedFlat (blockEquiv k) i) := by
    intro k i
    generalize hjq : (mpvPhaseClassData (d := d) blocks).enumEquiv.symm k = jq
    have henum : (mpvPhaseClassData (d := d) blocks).enum jq.1 jq.2 = k := by
      rw [← hjq]
      exact (mpvPhaseClassData (d := d) blocks).enumEquiv.apply_symm_apply k
    clear hjq
    subst k
    let jqP : (j : Fin P.basisCount) × Fin (P.copies j) := ⟨jq.1, jq.2⟩
    have hbe :
        blockEquiv ((mpvPhaseClassData (d := d) blocks).enum jq.1 jq.2) =
          P.flatIndexEquiv jqP := by
      change P.flatIndexEquiv
          ((mpvPhaseClassData (d := d) blocks).enumEquiv.symm
            ((mpvPhaseClassData (d := d) blocks).enum jq.1 jq.2)) =
        P.flatIndexEquiv jqP
      apply congrArg P.flatIndexEquiv
      exact ((mpvPhaseClassData (d := d) blocks).enumEquiv.symm_apply_eq).mpr
        ((mpvPhaseClassData (d := d) blocks).enumEquiv_apply jq.1 jq.2).symm
    have hcopyF : copyEquiv (P.flatIndexEquiv jqP) =
        (mpvPhaseClassData (d := d) blocks).enum jq.1 jq.2 := by
      change (mpvPhaseClassData (d := d) blocks).enumEquiv
        (P.flatIndexEquiv.symm (P.flatIndexEquiv jqP)) =
          (mpvPhaseClassData (d := d) blocks).enum jq.1 jq.2
      exact congrArg (mpvPhaseClassData (d := d) blocks).enumEquiv
        (P.flatIndexEquiv.symm_apply_apply jq) |>.trans
          ((mpvPhaseClassData (d := d) blocks).enumEquiv_apply jq.1 jq.2)
    have hdLocal : dim ((mpvPhaseClassData (d := d) blocks).enum jq.1 jq.2) =
        P.flatDim (P.flatIndexEquiv jqP) := by
      rw [← hcopyF]
      exact (hFlatDim (P.flatIndexEquiv jqP)).symm
    have hLocal :
        μ ((mpvPhaseClassData (d := d) blocks).enum jq.1 jq.2) •
            blocks ((mpvPhaseClassData (d := d) blocks).enum jq.1 jq.2) i =
        Matrix.reindex (finCongr hdLocal).symm (finCongr hdLocal).symm
          (P.flatWeight (P.flatIndexEquiv jqP) •
            gaugedFlat (P.flatIndexEquiv jqP) i) := by
      ext x y
      simp only [Matrix.smul_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
      let C : Matrix (Fin (dim ((mpvPhaseClassData (d := d) blocks).enum jq.1 jq.2)))
          (Fin (dim ((mpvPhaseClassData (d := d) blocks).enum jq.1 jq.2))) ℂ :=
        (G jq.1 jq.2 : Matrix _ _ ℂ) *
          (cast (congr_arg (MPSTensor d) (hEq jq.1 jq.2))
            (blocks ((mpvPhaseClassData (d := d) blocks).repr jq.1))) i *
          (↑((G jq.1 jq.2)⁻¹) : Matrix _ _ ℂ)
      have hg := congrFun (congrFun (hG jq.1 jq.2 i) x) y
      have hgEntry : blocks ((mpvPhaseClassData (d := d) blocks).enum jq.1 jq.2) i x y =
          ((mpvPhaseClassData (d := d) blocks).enum_phase jq.1 jq.2).choose * C x y := by
        simpa [C, Matrix.smul_apply, smul_eq_mul] using hg
      rw [hgEntry]
      have hinv : P.flatIndexEquiv.symm (P.flatIndexEquiv jqP) = jqP :=
        P.flatIndexEquiv.symm_apply_apply jqP
      have hXflat : Xflat (P.flatIndexEquiv jqP) ≍ Xcopy jqP := by
        dsimp [Xflat]
        exact congr_arg_heq Xcopy hinv
      have hBasis := SectorDecomposition.flatBasis_flatIndexEquiv_heq P jqP
      have hXcopy : Xcopy jqP ≍
          cast (congr_arg (fun n => GL (Fin n) ℂ) hdLocal) (G jq.1 jq.2) := by
        dsimp [Xcopy]
        exact (cast_heq _ _).trans (cast_heq _ _).symm
      have hGauge : Xflat (P.flatIndexEquiv jqP) =
          cast (congr_arg (fun n => GL (Fin n) ℂ) hdLocal) (G jq.1 jq.2) := by
        apply eq_of_heq
        exact HEq.trans hXflat hXcopy
      have hBasisConcrete : P.flatBasis (P.flatIndexEquiv jqP) ≍
          blocks ((mpvPhaseClassData (d := d) blocks).repr jq.1) := by
        exact HEq.trans hBasis (by rfl)
      have hRepDim : P.flatDim (P.flatIndexEquiv jqP) =
          dim ((mpvPhaseClassData (d := d) blocks).repr jq.1) := by
        exact hdLocal.symm.trans (hEq jq.1 jq.2).symm
      have hBasis_i : P.flatBasis (P.flatIndexEquiv jqP) i ≍
          blocks ((mpvPhaseClassData (d := d) blocks).repr jq.1) i := by
        exact dcongr_heq (HEq.rfl : i ≍ i)
          (fun _ _ _ => congrArg (fun n => Matrix (Fin n) (Fin n) ℂ) hRepDim)
          (fun _ _ => hBasisConcrete)
      have hCastBasisMatrix :
          cast (congr_arg (fun n => Matrix (Fin n) (Fin n) ℂ) (hEq jq.1 jq.2))
              (blocks ((mpvPhaseClassData (d := d) blocks).repr jq.1) i) =
            cast (congr_arg (fun n => Matrix (Fin n) (Fin n) ℂ) hdLocal.symm)
              (P.flatBasis (P.flatIndexEquiv jqP) i) := by
        apply eq_of_heq
        exact (cast_heq _ _).trans
          (hBasis_i.symm.trans (cast_heq _ _).symm)
      have hgauged : gaugedFlat (P.flatIndexEquiv jqP) i
            (Fin.cast hdLocal x) (Fin.cast hdLocal y) = C x y := by
        dsimp [gaugedFlat]
        rw [hGauge]
        rw [cast_gl_conj_apply hdLocal.symm (G jq.1 jq.2)
          (P.flatBasis (P.flatIndexEquiv jqP) i) x y]
        rw [← hCastBasisMatrix]
        dsimp [C]
        rw [cast_eq_reindex (hEq jq.1 jq.2),
          reindex_apply_eq_cast (hEq jq.1 jq.2)]
      have hfin (z : Fin (dim ((mpvPhaseClassData (d := d) blocks).enum jq.1 jq.2))) :
          (finCongr hdLocal).symm.symm z = Fin.cast hdLocal z := by
        apply Fin.ext
        rfl
      rw [hfin x, hfin y, hgauged]
      have hw : P.flatWeight (P.flatIndexEquiv jqP) =
          ((mpvPhaseClassData (d := d) blocks).enum_phase jq.1 jq.2).choose *
            μ ((mpvPhaseClassData (d := d) blocks).enum jq.1 jq.2) := by
        rw [SectorDecomposition.flatWeight_flatIndexEquiv]
        rfl
      rw [hw]
      simp only [smul_eq_mul]
      ring
    let Pack := {s : Fin P.totalCopies //
      dim ((mpvPhaseClassData (d := d) blocks).enum jq.1 jq.2) = P.flatDim s}
    let rhs (z : Pack) : Matrix
        (Fin (dim ((mpvPhaseClassData (d := d) blocks).enum jq.1 jq.2)))
        (Fin (dim ((mpvPhaseClassData (d := d) blocks).enum jq.1 jq.2))) ℂ :=
      Matrix.reindex (finCongr z.property).symm (finCongr z.property).symm
        (P.flatWeight z.val • gaugedFlat z.val i)
    let z₁ : Pack := ⟨blockEquiv ((mpvPhaseClassData (d := d) blocks).enum jq.1 jq.2),
      hBlockDim ((mpvPhaseClassData (d := d) blocks).enum jq.1 jq.2)⟩
    let z₂ : Pack := ⟨P.flatIndexEquiv jqP, hdLocal⟩
    have hz : z₁ = z₂ := by
      apply Subtype.ext
      exact hbe
    have hr : rhs z₁ = rhs z₂ := congrArg rhs hz
    exact hLocal.trans hr.symm
  let e := blockDimEquiv blockEquiv hBlockDim
  refine ⟨P, hBNT, hTotal, e, X, ?_⟩
  intro i
  rw [hX]
  exact toTensorFromBlocks_eq_reindex_of_equiv μ blocks P.flatWeight gaugedFlat
    blockEquiv hBlockDim hBlock i

/-- Normalized prepared blocks have an exact, dimension-preserving BNT reconstruction. -/
theorem PreparedBNTBlocks.exists_isBNTCanonicalForm_exact
    (data : PreparedBNTBlocks d) (hNorm : data.IsWeightNormalized) :
    ∃ P : SectorDecomposition d,
      IsBNTCanonicalForm P ∧ P.totalDim = ∑ k : Fin data.r, data.dim k ∧
      ∃ e : Fin P.totalDim ≃ Fin (∑ k : Fin data.r, data.dim k),
      ∃ X : GL (Fin P.totalDim) ℂ, ∀ i,
        toTensorFromBlocks (d := d) data.weight data.blocks i =
          Matrix.reindex e e
            ((X : Matrix _ _ ℂ) * P.toTensor i * (↑(X⁻¹) : Matrix _ _ ℂ)) :=
  exists_isBNTCanonicalForm_exact_of_tp_primitive_irr_blocks
    data.weight data.blocks data.dim_pos data.leftCanonical data.primitive data.irreducible
      data.weight_ne_zero hNorm.norm_le_one hNorm.unit_exists

end MPSTensor
