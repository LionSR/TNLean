/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.DirectSumBlockRetraction
import TNLean.MPS.MPDO.VerticalSectorFixedPointProductSpan

/-!
# Product spans of density-weighted fixed points

Wolf's density-block description identifies the fixed points of a positive
trace-preserving map with blocks of the form $\sigma_k\otimes X_k$.  Products
of $L$ fixed points therefore have blocks
$\sigma_k^L\otimes(X_{1,k}\cdots X_{L,k})$.  The main result bounds the
dimension of their span by the dimension of the fixed-point space, through
the density-block parametrization of Wolf's Theorem 6.14.

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.14 and
  Equation (6.63); local source
  `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1469--1494.
* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.4, lines 1980--1995.
-/

open scoped Matrix MatrixOrder ComplexOrder Kronecker

noncomputable section

namespace MPOTensor

private def matrixFixedPointProductSpan
    {n : Type*} [Fintype n] [DecidableEq n] (L : ℕ)
    (F : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) :
    Submodule ℂ (Matrix n n ℂ) :=
  Submodule.span ℂ (Set.range fun X : Fin L → F.fixedSubmodule ↦
    (List.ofFn fun t ↦ (X t : Matrix n n ℂ)).prod)

private def densityBlockLinearMap
    {K : ℕ} {m d : Fin K → ℕ}
    (σ : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ) :
    (∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) →ₗ[ℂ]
      Matrix ((k : Fin K) × (Fin (m k) × Fin (d k)))
        ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ where
  toFun X := Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X k
  map_add' X Y := by
    rw [← Matrix.blockDiagonal'_add]
    congr 1
    funext k
    exact Matrix.kronecker_add (σ k) (X k) (Y k)
  map_smul' c X := by
    rw [← Matrix.blockDiagonal'_smul]
    congr 1
    funext k
    exact Matrix.kronecker_smul c (σ k) (X k)

private theorem densityBlockLinearMap_injective
    {K : ℕ} {m d : Fin K → ℕ}
    (σ : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ)
    (hσtrace : ∀ k, (σ k).trace = 1) :
    Function.Injective (densityBlockLinearMap (d := d) σ) := by
  intro X Y hXY
  apply funext
  intro k
  change Matrix.blockDiagonal' (fun k ↦ σ k ⊗ₖ X k) =
    Matrix.blockDiagonal' (fun k ↦ σ k ⊗ₖ Y k) at hXY
  have hblocks := Matrix.blockDiagonal'_injective hXY
  have hk := congrFun hblocks k
  have hpartial := congrArg Matrix.partialTraceLeft hk
  simpa only [Matrix.partialTraceLeft_kronecker, hσtrace, one_smul] using hpartial

private theorem unitaryReindexLinearEquiv_one
    {n H : Type*} [Fintype n] [DecidableEq n]
    [Fintype H] [DecidableEq H] (e : H ≃ n)
    (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    Matrix.unitaryReindexLinearEquiv e U hU 1 = 1 := by
  rw [Matrix.unitaryReindexLinearEquiv_apply]
  rw [Matrix.mul_one, Matrix.mem_unitaryGroup_iff'.mp hU]
  exact Matrix.reindexLinearEquiv_one ℂ ℂ e.symm

private theorem unitaryReindexLinearEquiv_mul
    {n H : Type*} [Fintype n] [DecidableEq n]
    [Fintype H] [DecidableEq H] (e : H ≃ n)
    (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (A B : Matrix n n ℂ) :
    Matrix.unitaryReindexLinearEquiv e U hU (A * B) =
      Matrix.unitaryReindexLinearEquiv e U hU A *
        Matrix.unitaryReindexLinearEquiv e U hU B := by
  rw [Matrix.unitaryReindexLinearEquiv_apply,
    Matrix.unitaryReindexLinearEquiv_apply,
    Matrix.unitaryReindexLinearEquiv_apply]
  have hUright : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hconj : star U * (A * B) * U =
      (star U * A * U) * (star U * B * U) := by
    calc
      star U * (A * B) * U = star U * A * (U * star U) * B * U := by
        rw [hUright]
        simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = (star U * A * U) * (star U * B * U) := by
        simp only [Matrix.mul_assoc]
  calc
    Matrix.reindex e.symm e.symm (star U * (A * B) * U) =
        Matrix.reindex e.symm e.symm
          ((star U * A * U) * (star U * B * U)) := congrArg _ hconj
    _ = Matrix.reindex e.symm e.symm (star U * A * U) *
        Matrix.reindex e.symm e.symm (star U * B * U) :=
      (Matrix.reindexLinearEquiv_mul ℂ ℂ e.symm e.symm e.symm _ _).symm

private theorem unitaryReindexLinearEquiv_list_prod
    {n H : Type*} [Fintype n] [DecidableEq n]
    [Fintype H] [DecidableEq H] (e : H ≃ n)
    (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (A : List (Matrix n n ℂ)) :
    Matrix.unitaryReindexLinearEquiv e U hU A.prod =
      (A.map (Matrix.unitaryReindexLinearEquiv e U hU)).prod := by
  induction A with
  | nil =>
      simpa only [List.prod_nil, List.map_nil] using
        unitaryReindexLinearEquiv_one e U hU
  | cons A l ih =>
      rw [List.prod_cons, List.map_cons, List.prod_cons,
        unitaryReindexLinearEquiv_mul, ih]

private theorem densityBlockLinearMap_list_prod
    {K L : ℕ} {m d : Fin K → ℕ}
    (σ : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ)
    (X : Fin L → ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) :
    (List.ofFn fun t ↦ densityBlockLinearMap σ (X t)).prod =
      densityBlockLinearMap (fun k ↦ (σ k) ^ L)
        (fun k ↦ (List.ofFn fun t ↦ X t k).prod) := by
  induction L with
  | zero =>
      simp only [List.ofFn_zero, List.prod_nil, pow_zero]
      change 1 = Matrix.blockDiagonal' fun k ↦
        (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ
          (1 : Matrix (Fin (d k)) (Fin (d k)) ℂ)
      simp only [Matrix.one_kronecker_one]
      rw [show (fun k ↦ (1 : Matrix (Fin (m k) × Fin (d k))
        (Fin (m k) × Fin (d k)) ℂ)) = 1 by rfl]
      exact Matrix.blockDiagonal'_one.symm
  | succ L ih =>
      rw [List.ofFn_succ, List.prod_cons]
      have ih' := ih (fun t ↦ X t.succ)
      rw [ih']
      change Matrix.blockDiagonal' (fun k ↦ σ k ⊗ₖ X 0 k) *
          Matrix.blockDiagonal' (fun k ↦
            ((σ k) ^ L) ⊗ₖ (List.ofFn fun t ↦ X t.succ k).prod) =
        Matrix.blockDiagonal' (fun k ↦
          ((σ k) ^ (L + 1)) ⊗ₖ (List.ofFn fun t ↦ X t k).prod)
      rw [← Matrix.blockDiagonal'_mul]
      congr 1
      funext k
      rw [← Matrix.mul_kronecker_mul, pow_succ']
      rw [List.ofFn_succ, List.prod_cons]

private theorem reindex_directSumDiagonalEmbedding_list_prod
    {ι β : Type*} [Finite ι] [DecidableEq ι]
    {n : ι → Type*} [∀ k, Fintype (n k)] [∀ k, DecidableEq (n k)]
    [Fintype β] [DecidableEq β] (e : ((k : ι) × n k) ≃ β)
    (A : List (∀ k, Matrix (n k) (n k) ℂ)) :
    Matrix.reindex e e (Matrix.directSumDiagonalEmbedding A.prod) =
      (A.map fun X ↦
        Matrix.reindex e e (Matrix.directSumDiagonalEmbedding X)).prod := by
  letI := Fintype.ofFinite ι
  induction A with
  | nil =>
      simp only [List.prod_nil, List.map_nil]
      change Matrix.reindex e e (Matrix.blockDiagonal' 1) = 1
      rw [Matrix.blockDiagonal'_one]
      exact Matrix.reindexLinearEquiv_one ℂ ℂ e
  | cons A l ih =>
      rw [List.prod_cons, List.map_cons, List.prod_cons,
        Matrix.directSumDiagonalEmbedding_mul]
      rw [show Matrix.reindex e e
          (Matrix.directSumDiagonalEmbedding A *
            Matrix.directSumDiagonalEmbedding l.prod) =
          Matrix.reindex e e (Matrix.directSumDiagonalEmbedding A) *
            Matrix.reindex e e (Matrix.directSumDiagonalEmbedding l.prod) by
        exact (Matrix.reindexLinearEquiv_mul ℂ ℂ e e e _ _).symm]
      rw [ih]

private theorem pi_list_prod_apply
    {ι : Type*} {M : ι → Type*} [∀ k, Monoid (M k)]
    (A : List (∀ k, M k)) (k : ι) :
    A.prod k = (A.map fun X ↦ X k).prod := by
  induction A with
  | nil => rfl
  | cons A l ih =>
      rw [List.prod_cons, List.map_cons, List.prod_cons, Pi.mul_apply, ih]

/-- Full-matrix density-block argument underlying the public direct-sum
theorem below.  This is the dimension implication of Wolf, Theorem 6.14 and
Equation (6.63); see the public wrapper for the source and scope discussion. -/
private theorem matrixFixedPointProductSpan_finrank_le_of_densityBlocks
    {N : ℕ} {F : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ]
      Matrix (Fin N) (Fin N) ℂ}
    (hF : IsPositiveMap F) (hTP : IsTracePreservingMap F)
    (hSchwarz : IsSchwarzMap (Matrix.traceAdjointMap F))
    {ρ : Matrix (Fin N) (Fin N) ℂ} (hρ : ρ.PosDef) (hρfix : F ρ = ρ)
    (L : ℕ) :
    Module.finrank ℂ (matrixFixedPointProductSpan L F) ≤
      Module.finrank ℂ F.fixedSubmodule := by
  obtain ⟨K, d, m, e, U, σ, hU, _, _, _, hσtrace, _, hfixed⟩ :=
    hF.exists_block_densities_of_meanErgodicProjection
      hTP hSchwarz hρ hρfix
  let Φ := Matrix.unitaryReindexLinearEquiv e U hU
  let D := densityBlockLinearMap (d := d) σ
  let DL := densityBlockLinearMap (d := d) (fun k ↦ (σ k) ^ L)
  have hDinj : Function.Injective D :=
    densityBlockLinearMap_injective (d := d) σ hσtrace
  have hFixedRange : F.fixedSubmodule.map Φ.toLinearMap =
      LinearMap.range D := by
    ext B
    constructor
    · rintro ⟨A, hA, rfl⟩
      obtain ⟨X, hX⟩ :=
        (hfixed A).mp (LinearMap.mem_fixedSubmodule_iff.mp hA)
      refine ⟨X, ?_⟩
      apply Eq.symm
      dsimp only [D, Φ]
      change Matrix.reindex e.symm e.symm (star U * A * U) =
        densityBlockLinearMap (d := d) σ X
      change star U * A * U =
        Matrix.reindex e e (densityBlockLinearMap (d := d) σ X) at hX
      rw [hX]
      simpa only [Matrix.coe_reindexLinearEquiv,
        Matrix.symm_reindexLinearEquiv] using
        (Matrix.reindexLinearEquiv ℂ ℂ e e).symm_apply_apply
          (densityBlockLinearMap (d := d) σ X)
    · rintro ⟨X, rfl⟩
      let A := Φ.symm (D X)
      have hAcoord : star U * A * U = Matrix.reindex e e (D X) := by
        rw [show A = U * Matrix.reindex e e (D X) * star U by
          exact Matrix.unitaryReindexLinearEquiv_symm_apply e U hU (D X)]
        have hUleft : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
        calc
          star U * (U * Matrix.reindex e e (D X) * star U) * U =
              (star U * U) * Matrix.reindex e e (D X) * (star U * U) := by
            simp only [Matrix.mul_assoc]
          _ = Matrix.reindex e e (D X) := by rw [hUleft]; simp
      have hAfix : F A = A := (hfixed A).mpr ⟨X, hAcoord⟩
      refine ⟨A, LinearMap.mem_fixedSubmodule_iff.mpr hAfix, ?_⟩
      exact Φ.apply_symm_apply (D X)
  have hProductMap :
      (matrixFixedPointProductSpan L F).map Φ.toLinearMap ≤
        LinearMap.range DL := by
    rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨X, rfl⟩
    change Φ ((List.ofFn fun t ↦ (X t : Matrix (Fin N) (Fin N) ℂ)).prod) ∈
      LinearMap.range DL
    choose Y hY using fun t ↦ (hfixed (X t)).mp (X t).property
    have hΦ (t : Fin L) : Φ (X t) = D (Y t) := by
      dsimp only [Φ, D]
      change Matrix.reindex e.symm e.symm
          (star U * (X t : Matrix (Fin N) (Fin N) ℂ) * U) =
        densityBlockLinearMap (d := d) σ (Y t)
      have hYt := hY t
      change star U * (X t : Matrix (Fin N) (Fin N) ℂ) * U =
        Matrix.reindex e e (densityBlockLinearMap (d := d) σ (Y t)) at hYt
      rw [hYt]
      simpa only [Matrix.coe_reindexLinearEquiv,
        Matrix.symm_reindexLinearEquiv] using
        (Matrix.reindexLinearEquiv ℂ ℂ e e).symm_apply_apply
          (densityBlockLinearMap (d := d) σ (Y t))
    refine ⟨fun k ↦ (List.ofFn fun t ↦ Y t k).prod, ?_⟩
    calc
      DL (fun k ↦ (List.ofFn fun t ↦ Y t k).prod) =
          (List.ofFn fun t ↦ D (Y t)).prod := by
        exact (densityBlockLinearMap_list_prod σ Y).symm
      _ = (List.ofFn fun t ↦ Φ (X t)).prod := by
        congr 2
        funext t
        exact (hΦ t).symm
      _ = Φ ((List.ofFn fun t ↦
          (X t : Matrix (Fin N) (Fin N) ℂ)).prod) := by
        rw [unitaryReindexLinearEquiv_list_prod]
        rw [List.map_ofFn]
        rfl
  calc
    Module.finrank ℂ (matrixFixedPointProductSpan L F) =
        Module.finrank ℂ
          ((matrixFixedPointProductSpan L F).map Φ.toLinearMap) :=
      (LinearEquiv.finrank_map_eq Φ (matrixFixedPointProductSpan L F)).symm
    _ ≤ Module.finrank ℂ (LinearMap.range DL) :=
      Submodule.finrank_mono hProductMap
    _ ≤ Module.finrank ℂ (∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) :=
      LinearMap.finrank_range_le DL
    _ = Module.finrank ℂ (LinearMap.range D) :=
      (LinearMap.finrank_range_of_inj hDinj).symm
    _ = Module.finrank ℂ (F.fixedSubmodule.map Φ.toLinearMap) := by
      rw [hFixedRange]
    _ = Module.finrank ℂ F.fixedSubmodule :=
      LinearEquiv.finrank_map_eq Φ F.fixedSubmodule

/-- Products of $L$ fixed points of a positive trace-preserving map on a
finite direct sum have dimension at most that of the fixed-point space,
provided that the trace adjoint satisfies the Schwarz inequality and the map
has a positive-definite fixed family.

The proof applies Wolf's density-block classification to the canonical
full-matrix extension.  In density-block coordinates the fixed points are
$\bigoplus_k \sigma_k\otimes X_k$, whereas their $L$-fold products lie in the
range of $X\mapsto\bigoplus_k\sigma_k^L\otimes X_k$.  Both parameter spaces
therefore have the same dimension bound.

Source: Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.14 and
Equation (6.63); local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1469--1494.
This is the dimension implication used in arXiv:1606.00608, Appendix C.4,
lines 1980--1995.

**Scope restriction (faithful fixed family):** Wolf's Theorem 6.14 does not
assume a positive-definite fixed point and allows a complementary zero
summand.  The present theorem is its full-support corollary for a direct-sum
map with a positive-definite fixed family.  In the CPSV16 argument this family
is supplied separately by the fixed contraction factors and their
positive-length product span.  This restriction and its elimination in the
tensor-attached argument are documented in
`docs/paper-gaps/cpsv16_vertical_sector_invertibility.tex`.

The condition $L>0$ is retained to match the quantifier in the cited
formulation; the proof also gives the bound for $L=0$. -/
theorem fixedPointProductSpan_finrank_le_of_densityBlocks
    {g : ℕ} {dim : Fin g → ℕ}
    {F : VerticalSectorAlgebra dim →ₗ[ℂ] VerticalSectorAlgebra dim}
    (hF : Matrix.IsPositiveDirectSumMap F)
    (hTP : Matrix.IsTracePreservingDirectSumMap F)
    (hSchwarz : Matrix.IsSchwarzDirectSumMap
      (Matrix.directSumTraceAdjointMap F))
    {ρ : VerticalSectorAlgebra dim} (hρ : ∀ k, (ρ k).PosDef)
    (hρfix : F ρ = ρ) (L : ℕ) (_hL : 0 < L) :
    Module.finrank ℂ (fixedPointProductSpan L F) ≤
      Module.finrank ℂ F.fixedSubmodule := by
  let s := (k : Fin g) × Fin (dim k)
  let efin : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  let E := Matrix.directSumExtension F
  let EFin := Matrix.reindexEndomorphism efin E
  let ρExt := Matrix.directSumDiagonalEmbedding ρ
  let ρFin := Matrix.reindex efin efin ρExt
  obtain ⟨hEFin, hTPFin, hSchwarzFin, hρFin, hρFinFix⟩ :
      IsPositiveMap EFin ∧ IsTracePreservingMap EFin ∧
        IsSchwarzMap (Matrix.traceAdjointMap EFin) ∧
        ρFin.PosDef ∧ EFin ρFin = ρFin := by
    simpa only [ρFin, ρExt, EFin, E] using
      hF.reindexedExtension_properties hTP hSchwarz hρ hρfix efin
  have hFull := matrixFixedPointProductSpan_finrank_le_of_densityBlocks
    hEFin hTPFin hSchwarzFin hρFin hρFinFix L
  let ιmap : VerticalSectorAlgebra dim →ₗ[ℂ]
      Matrix (Fin (Fintype.card s)) (Fin (Fintype.card s)) ℂ :=
    (Matrix.reindexLinearEquiv ℂ ℂ efin efin).toLinearMap.comp
      Matrix.directSumDiagonalEmbedding
  have hιinj : Function.Injective ιmap := by
    intro A B hAB
    apply Matrix.blockDiagonal'_injective
    apply (Matrix.reindexLinearEquiv ℂ ℂ efin efin).injective
    exact hAB
  have hιfixed (A : VerticalSectorAlgebra dim) (hA : F A = A) :
      EFin (ιmap A) = ιmap A := by
    change Matrix.reindex efin efin
        (E (Matrix.reindex efin.symm efin.symm
          (Matrix.reindex efin efin
            (Matrix.directSumDiagonalEmbedding A)))) =
      Matrix.reindex efin efin (Matrix.directSumDiagonalEmbedding A)
    have hback : Matrix.reindex efin.symm efin.symm
        (Matrix.reindex efin efin (Matrix.directSumDiagonalEmbedding A)) =
        Matrix.directSumDiagonalEmbedding A := by
      simpa only [Matrix.coe_reindexLinearEquiv,
        Matrix.symm_reindexLinearEquiv] using
        (Matrix.reindexLinearEquiv ℂ ℂ efin efin).symm_apply_apply
          (Matrix.directSumDiagonalEmbedding A)
    rw [hback]
    rw [(Matrix.directSumExtension_embedding_eq_self_iff F A).2 hA]
  have hProductMap : (fixedPointProductSpan L F).map ιmap ≤
      matrixFixedPointProductSpan L EFin := by
    rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨X, rfl⟩
    change ιmap (fun α ↦
        (List.ofFn fun t ↦ (X t : VerticalSectorAlgebra dim) α).prod) ∈
      matrixFixedPointProductSpan L EFin
    have hsector : (fun α ↦
        (List.ofFn fun t ↦ (X t : VerticalSectorAlgebra dim) α).prod) =
        (List.ofFn fun t ↦ (X t : VerticalSectorAlgebra dim)).prod := by
      funext α
      rw [pi_list_prod_apply, List.map_ofFn]
      rfl
    rw [hsector]
    apply Submodule.subset_span
    let XFin : Fin L → EFin.fixedSubmodule := fun t ↦
      ⟨ιmap (X t), hιfixed (X t) (X t).property⟩
    refine ⟨XFin, ?_⟩
    change (List.ofFn fun t ↦ (XFin t : Matrix (Fin (Fintype.card s))
        (Fin (Fintype.card s)) ℂ)).prod =
      ιmap (List.ofFn fun t ↦ (X t : VerticalSectorAlgebra dim)).prod
    symm
    change Matrix.reindex efin efin
        (Matrix.directSumDiagonalEmbedding
          (List.ofFn fun t ↦ (X t : VerticalSectorAlgebra dim)).prod) = _
    rw [reindex_directSumDiagonalEmbedding_list_prod]
    rw [List.map_ofFn]
    rfl
  let back : Matrix (Fin (Fintype.card s)) (Fin (Fintype.card s)) ℂ →ₗ[ℂ]
      Matrix s s ℂ :=
    (Matrix.reindexLinearEquiv ℂ ℂ efin.symm efin.symm).toLinearMap
  let compress : EFin.fixedSubmodule →ₗ[ℂ] VerticalSectorAlgebra dim :=
    Matrix.directSumDiagonalCompression.comp
      (back.comp EFin.fixedSubmodule.subtype)
  have hBackFixed (B : EFin.fixedSubmodule) : E (back B) = back B := by
    have hB := B.property
    change Matrix.reindex efin efin
        (E (Matrix.reindex efin.symm efin.symm
          (B : Matrix (Fin (Fintype.card s)) (Fin (Fintype.card s)) ℂ))) =
      (B : Matrix (Fin (Fintype.card s)) (Fin (Fintype.card s)) ℂ) at hB
    apply (Matrix.reindexLinearEquiv ℂ ℂ efin efin).injective
    change Matrix.reindex efin efin (E (back B)) =
      Matrix.reindex efin efin (back B)
    calc
      Matrix.reindex efin efin (E (back B)) = B := hB
      _ = Matrix.reindex efin efin (back B) := by
        dsimp only [back, LinearMap.coe_comp, LinearEquiv.coe_coe,
          Function.comp_apply, Submodule.coe_subtype]
        simpa only [Matrix.coe_reindexLinearEquiv,
          Matrix.symm_reindexLinearEquiv] using
          ((Matrix.reindexLinearEquiv ℂ ℂ efin efin).apply_symm_apply
            (B : Matrix (Fin (Fintype.card s))
              (Fin (Fintype.card s)) ℂ)).symm
  have hCompressFixed (B : EFin.fixedSubmodule) : F (compress B) = compress B := by
    have hB := congrArg Matrix.directSumDiagonalCompression (hBackFixed B)
    change F (Matrix.directSumDiagonalCompression (back B)) =
      Matrix.directSumDiagonalCompression (back B)
    simpa only [E, Matrix.directSumExtension_apply,
      Matrix.directSumDiagonalCompression_embedding] using hB
  let κ : EFin.fixedSubmodule →ₗ[ℂ] F.fixedSubmodule :=
    LinearMap.codRestrict F.fixedSubmodule compress
      (fun B ↦ LinearMap.mem_fixedSubmodule_iff.mpr (hCompressFixed B))
  have hκinj : Function.Injective κ := by
    intro B C hBC
    apply Subtype.ext
    apply (Matrix.reindexLinearEquiv ℂ ℂ efin.symm efin.symm).injective
    change back B = back C
    have hEmbed (X : EFin.fixedSubmodule) :
        back X = Matrix.directSumDiagonalEmbedding (compress X) := by
      calc
        back X = E (back X) := (hBackFixed X).symm
        _ = Matrix.directSumDiagonalEmbedding
            (F (Matrix.directSumDiagonalCompression (back X))) := rfl
        _ = Matrix.directSumDiagonalEmbedding (compress X) := by
          change Matrix.directSumDiagonalEmbedding (F (compress X)) =
            Matrix.directSumDiagonalEmbedding (compress X)
          rw [hCompressFixed X]
    rw [hEmbed B, hEmbed C]
    congr 1
    change compress B = compress C
    exact congrArg Subtype.val hBC
  let ιProduct : fixedPointProductSpan L F →ₗ[ℂ]
      matrixFixedPointProductSpan L EFin :=
    LinearMap.codRestrict (matrixFixedPointProductSpan L EFin)
      (ιmap.comp (fixedPointProductSpan L F).subtype) (fun X ↦ by
        apply hProductMap
        exact ⟨X, X.property, rfl⟩)
  have hιProductInj : Function.Injective ιProduct := by
    intro A B hAB
    apply Subtype.ext
    apply hιinj
    exact congrArg Subtype.val hAB
  exact (LinearMap.finrank_le_finrank_of_injective hιProductInj).trans
    (hFull.trans (LinearMap.finrank_le_finrank_of_injective hκinj))

end MPOTensor
