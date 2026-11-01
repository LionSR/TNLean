/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.ConjugationSymmetry
import TNLean.MPS.MPU.PhysicalAdjointCanonicalForm
import TNLean.MPS.MPU.SourceFactorChoiceGates

/-!
# Conjugation transport of the actual source cuts and half factors

Entrywise conjugation preserves both source ranks. A supplied compact
decomposition conjugates to a compact decomposition with exactly the same
positive singular-value matrices. The six supplied source factors likewise
conjugate, with only the canonical equality of the source-rank dimensions
used to index the transformed factors. Their contracted gates are exactly
the conjugates of the supplied gates in those coordinates.

These are comparison ingredients for arXiv:1703.09188, proof of `prop1conj`,
lines 1030–1033, using the source cuts and factors of `eq:sf-svd`,
`Y1Y1X1X1`, and `YZ=1`, lines 479–506. No new choice of source decomposition
or assumed existence of local conjugation gauges is introduced.
-/

open scoped Matrix Kronecker ComplexOrder BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- The first source cut conjugates coefficient by coefficient, in the
comparison of `prop1conj` (arXiv:1703.09188, lines 1030–1033). -/
theorem sourceCutM₁_mapStar (U : MPOTensor d D) :
    sourceCutM₁ (mapStar U) = (sourceCutM₁ U).map (starRingEnd ℂ) := rfl

/-- The second source cut conjugates coefficient by coefficient, in the
comparison of `prop1conj` (arXiv:1703.09188, lines 1030–1033). -/
theorem sourceCutM₂_mapStar (U : MPOTensor d D) :
    sourceCutM₂ (mapStar U) = (sourceCutM₂ U).map (starRingEnd ℂ) := rfl

private theorem rank_map_star {a b : Type*} [Finite a] [Fintype b]
    (M : Matrix a b ℂ) : (M.map (starRingEnd ℂ)).rank = M.rank := by
  classical
  let := Fintype.ofFinite a
  have h : M.map (starRingEnd ℂ) = Mᴴᵀ := by ext i j; rfl
  rw [h, Matrix.rank_transpose, Matrix.rank_conjTranspose]

/-- Both source ranks are unchanged under conjugation, as used before
`prop1conj` in arXiv:1703.09188, lines 1008–1012. -/
theorem source_ranks_mapStar (U : MPOTensor d D) :
    r[mapStar U] = r[U] ∧ ℓ[mapStar U] = ℓ[U] := by
  constructor
  · change ((sourceCutM₁ U).map (starRingEnd ℂ)).rank = _
    exact rank_map_star _
  · change ((sourceCutM₂ U).map (starRingEnd ℂ)).rank = _
    exact rank_map_star _

/-- Normalized flattening commutes with entrywise conjugation, since the
normalizing scalar is real. Source: arXiv:1703.09188, `eq:transfer-op`,
lines 336–340, in the comparison of `prop1conj`, lines 1030–1033. -/
theorem normalizedFlattening_mapStar (U : MPOTensor d D) :
    (mapStar U).normalizedFlattening = MPSTensor.mapStar U.normalizedFlattening := by
  ext i α β
  simp [normalizedFlattening, MPOTensor.mapStar, MPSTensor.mapStar, toMPSTensor,
    Matrix.smul_apply, Matrix.map_apply]

/-- Canonical-form-II data, full ambient support, and the same real diagonal
fixed matrix transport to the coefficientwise conjugate tensor. This is the
canonical-data comparison in arXiv:1703.09188, proof of `prop1conj`,
lines 1030–1033, with `Erightleft`, lines 269–281. -/
noncomputable def IsMPUCanonicalFormII.mapStar {U : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) : IsMPUCanonicalFormII (MPOTensor.mapStar U) := by
  let data := hU.cfii.physicalAdjointNormalizedFlattening.reindexPhysical
    (physicalPairSwapEquiv d)
  have heq : (MPOTensor.mapStar U).normalizedFlattening =
      Kraus.reindexPhysical (physicalPairSwapEquiv d)
        (physicalAdjointTensor U).normalizedFlattening := by
    ext i α β
    rw [show i = finProdFinEquiv (i.divNat, i.modNat) by
      exact (finProdFinEquiv.apply_symm_apply i).symm]
    simp [normalizedFlattening, MPOTensor.mapStar, physicalAdjointTensor,
      Kraus.reindexPhysical, toMPSTensor, Matrix.smul_apply, Matrix.map_apply]
  have hfull : data.toCPSVCanonicalFormData.HasFullSupport := by
    change ∑ k, hU.cfii.toCPSVCanonicalFormData.dim k = D
    exact hU.fullSupport_eq
  refine {
    isMPU := ?_
    cfii := heq.symm ▸ data
    fullSupport_eq := MPSTensor.CPSVCanonicalFormIIData.hasFullSupport_cast data hfull heq
    ρ := hU.ρ
    ρ_posDef := hU.ρ_posDef
    ρ_isDiag := hU.ρ_isDiag
    ρ_trace := hU.ρ_trace
    ρ_fixed := ?_
  }
  · intro N hN
    rw [mpo_map_star]
    exact Matrix.map_star_mem_unitaryGroup_iff.mpr (hU.isMPU N hN)
  · rw [normalizedFlattening_mapStar,
      ← MPSTensor.map_star_eq_self_of_posDef_isDiag hU.ρ_posDef hU.ρ_isDiag,
      MPSTensor.transferMap_mapStar, hU.ρ_fixed,
      MPSTensor.map_star_eq_self_of_posDef_isDiag hU.ρ_posDef hU.ρ_isDiag]

namespace SourceCutSVD

/-- Conjugate the supplied compact decomposition itself, retaining its
positive diagonal singular values and their inverses. This is the literal
source-cut comparison needed in arXiv:1703.09188, proof of `prop1conj`,
lines 1030–1033, with `eq:sf-svd`, lines 479–486. -/
noncomputable def mapStar {a b : Type*} [Fintype a] [Fintype b]
    {M : Matrix a b ℂ} {r : ℕ} (S : SourceCutSVD M r) :
    SourceCutSVD (M.map (starRingEnd ℂ)) r where
  V := S.V.map (starRingEnd ℂ)
  U := S.U.map (starRingEnd ℂ)
  diagonal := S.diagonal
  inverseDiagonal := S.inverseDiagonal
  factorization := by
    have h := congrArg (fun M ↦ M.map (starRingEnd ℂ)) S.factorization
    rw [Matrix.map_mul, Matrix.map_mul,
      Matrix.conjTranspose_map (starRingEnd ℂ) (by simp [Function.Semiconj]),
      MPSTensor.map_star_eq_self_of_posDef_isDiag S.diagonal_posDef S.diagonal_isDiag] at h
    exact h
  V_coisometry := by
    have h := congrArg (fun M ↦ M.map (starRingEnd ℂ)) S.V_coisometry
    simpa [Matrix.IsCoisometry, Matrix.map_mul,
      Matrix.conjTranspose_map (starRingEnd ℂ) (by simp [Function.Semiconj])] using h
  U_coisometry := by
    have h := congrArg (fun M ↦ M.map (starRingEnd ℂ)) S.U_coisometry
    simpa [Matrix.IsCoisometry, Matrix.map_mul,
      Matrix.conjTranspose_map (starRingEnd ℂ) (by simp [Function.Semiconj])] using h
  diagonal_isDiag := S.diagonal_isDiag
  diagonal_posDef := S.diagonal_posDef
  inverseDiagonal_isDiag := S.inverseDiagonal_isDiag
  inverseDiagonal_posDef := S.inverseDiagonal_posDef
  diagonal_mul_inverseDiagonal := S.diagonal_mul_inverseDiagonal

end SourceCutSVD

namespace SourceFactors

/-- Conjugate all six supplied source factors and their normalization weight.
Only the canonical equality of the source-rank dimensions changes their
indices. This transports `eq:sf-svd`, `Y1Y1X1X1`, and `YZ=1` of
arXiv:1703.09188, lines 479–506, for the comparison in `prop1conj`,
lines 1030–1033. -/
noncomputable def mapStar {U : MPOTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (S : SourceFactors U ρ) : SourceFactors (MPOTensor.mapStar U) (ρ.map (starRingEnd ℂ)) := by
  let er := finCongr (source_ranks_mapStar U).1.symm
  let el := finCongr (source_ranks_mapStar U).2.symm
  have hweight : sourceWeight (d := d) (ρ.map (starRingEnd ℂ)) =
      (sourceWeight (d := d) ρ).map (starRingEnd ℂ) := by
    ext i j
    by_cases hij : i.1 = j.1 <;>
      simp [sourceWeight, Matrix.kroneckerMap_apply, Matrix.one_apply, hij]
  refine {
    X₁ := Matrix.reindex (Equiv.refl _) er (S.X₁.map (starRingEnd ℂ))
    Y₁ := Matrix.reindex er (Equiv.refl _) (S.Y₁.map (starRingEnd ℂ))
    Z₁ := Matrix.reindex (Equiv.refl _) er (S.Z₁.map (starRingEnd ℂ))
    X₂ := Matrix.reindex (Equiv.refl _) el (S.X₂.map (starRingEnd ℂ))
    Y₂ := Matrix.reindex el (Equiv.refl _) (S.Y₂.map (starRingEnd ℂ))
    Z₂ := Matrix.reindex (Equiv.refl _) el (S.Z₂.map (starRingEnd ℂ))
    sourceCutM₁_eq := ?_
    sourceCutM₂_eq := ?_
    X₁_weighted_isometry := ?_
    X₂_isometry := ?_
    Y₁_mul_Z₁ := ?_
    Y₂_mul_Z₂ := ?_
  }
  · rw [sourceCutM₁_mapStar, S.sourceCutM₁_eq, Matrix.map_mul]
    exact (Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.refl _) er (Equiv.refl _) _ _).symm
  · rw [sourceCutM₂_mapStar, S.sourceCutM₂_eq, Matrix.map_mul]
    exact (Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.refl _) el (Equiv.refl _) _ _).symm
  · rw [Matrix.conjTranspose_reindex]
    change Matrix.reindexLinearEquiv ℂ ℂ er (Equiv.refl _)
        (S.X₁.map (starRingEnd ℂ))ᴴ *
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) (Equiv.refl _)
        (sourceWeight (d := d) (ρ.map (starRingEnd ℂ))) *
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) er
        (S.X₁.map (starRingEnd ℂ)) = 1
    rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_mul]
    rw [hweight, ← Matrix.conjTranspose_map (starRingEnd ℂ)
      (by simp [Function.Semiconj]), ← Matrix.map_mul, ← Matrix.map_mul,
      S.X₁_weighted_isometry]
    simp
  · exact (Matrix.IsIsometry.reindex _ (by
      have h := congrArg (fun M ↦ M.map (starRingEnd ℂ)) S.X₂_isometry
      simpa [Matrix.IsIsometry, Matrix.map_mul,
        Matrix.conjTranspose_map (starRingEnd ℂ) (by simp [Function.Semiconj])] using h)
      (Equiv.refl _) el)
  · change Matrix.reindexLinearEquiv ℂ ℂ er (Equiv.refl (Fin D × Fin d))
        (S.Y₁.map (starRingEnd ℂ)) *
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl (Fin D × Fin d)) er
        (S.Z₁.map (starRingEnd ℂ)) = 1
    rw [Matrix.reindexLinearEquiv_mul, ← Matrix.map_mul, S.Y₁_mul_Z₁]
    simp
  · change Matrix.reindexLinearEquiv ℂ ℂ el (Equiv.refl (Fin d × Fin D))
        (S.Y₂.map (starRingEnd ℂ)) *
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl (Fin d × Fin D)) el
        (S.Z₂.map (starRingEnd ℂ)) = 1
    rw [Matrix.reindexLinearEquiv_mul, ← Matrix.map_mul, S.Y₂_mul_Z₂]
    simp

/-- The unshifted gate of the transported factors is the conjugate of the
actual supplied gate, in the canonical rank coordinates. Source:
arXiv:1703.09188, `uconjugation` and its proof, lines 1021–1033. -/
theorem sourceU_mapStar {U : MPOTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (S : SourceFactors U ρ) :
    sourceU (MPOTensor.mapStar U) S.mapStar =
      Matrix.reindex
        (Equiv.prodCongr (finCongr (source_ranks_mapStar U).2.symm)
          (finCongr (source_ranks_mapStar U).1.symm)) (Equiv.refl _)
        ((sourceU U S).map (starRingEnd ℂ)) := by
  ext ⟨l, r⟩ ⟨i, j⟩
  simp [sourceU, mapStar, Matrix.reindex_apply, Matrix.map_apply, map_sum, map_mul]

/-- The shifted gate of the transported factors is the conjugate of the
actual supplied gate, in the canonical rank coordinates. Source:
arXiv:1703.09188, `vconjugation` and its proof, lines 1023–1033. -/
theorem sourceV_mapStar {U : MPOTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (S : SourceFactors U ρ) :
    sourceV (MPOTensor.mapStar U) S.mapStar =
      Matrix.reindex (Equiv.refl _)
        (Equiv.prodCongr (finCongr (source_ranks_mapStar U).1.symm)
          (finCongr (source_ranks_mapStar U).2.symm))
        ((sourceV U S).map (starRingEnd ℂ)) := by
  ext ⟨i, j⟩ ⟨r, l⟩
  simp [sourceV, mapStar, Matrix.reindex_apply, Matrix.map_apply, map_sum, map_mul]

end SourceFactors

/-- The gate necessity direction of the Fundamental Theorem for the actual
supplied normalized source factors. The rank identifications are canonical
casts of equal dimensions. Source: arXiv:1703.09188, `FundamentalMPU`,
lines 624–648; used for `prop1conj`, lines 1030–1033. -/
theorem IsMPUCanonicalFormII.exists_supplied_source_gate_unitary_gauges_of_mpo_eq
    {U V : MPOTensor d D} (hU : IsMPUCanonicalFormII U) (hV : IsMPUCanonicalFormII V)
    {ρ ρ' : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ) (T : SourceFactors V ρ')
    (huS : (SourceFactors.sourceU U S).IsUnitaryBetween)
    (huT : (SourceFactors.sourceU V T).IsUnitaryBetween)
    (hEq : ∀ N : ℕ, 1 < N → mpo U N = mpo V N) :
    ∃ (hr : r[V] = r[U]) (hl : ℓ[V] = ℓ[U])
      (x : Matrix.unitaryGroup (Fin ℓ[V]) ℂ) (y : Matrix.unitaryGroup (Fin r[V]) ℂ),
      SourceFactors.sourceU V T =
        ((x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) ⊗ₖ (y : Matrix (Fin r[V]) (Fin r[V]) ℂ)) *
          Matrix.reindex (Equiv.prodCongr (finCongr hl.symm) (finCongr hr.symm))
            (Equiv.refl _) (SourceFactors.sourceU U S) ∧
      SourceFactors.sourceV V T =
        Matrix.reindex (Equiv.refl _)
            (Equiv.prodCongr (finCongr hr.symm) (finCongr hl.symm))
            (SourceFactors.sourceV U S) *
          (star (y : Matrix (Fin r[V]) (Fin r[V]) ℂ) ⊗ₖ
            star (x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ)) := by
  obtain ⟨z, rfl⟩ := hU.eq_virtualSandwich_of_mpo_eq hV hEq
  obtain ⟨W₁, W₂, hX₁, hY₁, hX₂, hY₂⟩ :=
    exists_source_factor_unitary_gauges_of_virtualSandwich U z S T huS huT
  obtain ⟨x, y, hu, hv⟩ := supplied_source_factor_gate_relations S T z _ _ W₁ W₂
    hX₁ hY₁ hX₂ hY₂
  exact ⟨(source_rank_virtual_unitary_sandwich U z).1,
    (source_rank_virtual_unitary_sandwich U z).2, x, y, hu, hv⟩

private theorem remove_source_rank_reindex_left
    {a b a' b' p : Type*} [Fintype a] [Fintype b] [Fintype a'] [Fintype b']
    (el : a ≃ a') (er : b ≃ b')
    (x : Matrix a' a' ℂ) (y : Matrix b' b' ℂ) (u : Matrix (a × b) p ℂ) :
    Matrix.reindex (Equiv.prodCongr el.symm er.symm) (Equiv.refl _)
        ((x ⊗ₖ y) * Matrix.reindex (Equiv.prodCongr el er) (Equiv.refl _) u) =
      (Matrix.reindex el.symm el.symm x ⊗ₖ Matrix.reindex er.symm er.symm y) * u := by
  change Matrix.reindexLinearEquiv ℂ ℂ (Equiv.prodCongr el.symm er.symm)
      (Equiv.refl _) ((x ⊗ₖ y) *
        Matrix.reindexLinearEquiv ℂ ℂ (Equiv.prodCongr el er) (Equiv.refl _) u) = _
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.prodCongr el.symm er.symm)
    (Equiv.prodCongr el.symm er.symm) (Equiv.refl _)]
  have hk : Matrix.reindexLinearEquiv ℂ ℂ (Equiv.prodCongr el.symm er.symm)
      (Equiv.prodCongr el.symm er.symm) (x ⊗ₖ y) =
      Matrix.reindex el.symm el.symm x ⊗ₖ Matrix.reindex er.symm er.symm y :=
    (Matrix.kroneckerMap_reindex (fun a b : ℂ ↦ a * b)
      el.symm el.symm er.symm er.symm x y).symm
  have hu : Matrix.reindexLinearEquiv ℂ ℂ (Equiv.prodCongr el.symm er.symm)
      (Equiv.refl p)
      (Matrix.reindexLinearEquiv ℂ ℂ (Equiv.prodCongr el er) (Equiv.refl p) u) = u := by
    ext ⟨i₁, i₂⟩ j
    simp [Matrix.reindex_apply]
  rw [hk, hu]

private theorem remove_source_rank_reindex_right
    {a b a' b' p : Type*} [Fintype a] [Fintype b] [Fintype a'] [Fintype b']
    (el : a ≃ a') (er : b ≃ b')
    (x : Matrix a' a' ℂ) (y : Matrix b' b' ℂ) (v : Matrix p (b × a) ℂ) :
    Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er.symm el.symm)
        (Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er el) v * (yᴴ ⊗ₖ xᴴ)) =
      v * ((Matrix.reindex er.symm er.symm y)ᴴ ⊗ₖ
        (Matrix.reindex el.symm el.symm x)ᴴ) := by
  change Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _)
      (Equiv.prodCongr er.symm el.symm)
      (Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) (Equiv.prodCongr er el) v *
        (yᴴ ⊗ₖ xᴴ)) = _
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.refl _)
    (Equiv.prodCongr er.symm el.symm) (Equiv.prodCongr er.symm el.symm)]
  have hv : Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl p)
      (Equiv.prodCongr er.symm el.symm)
      (Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl p) (Equiv.prodCongr er el) v) = v := by
    ext i ⟨j₁, j₂⟩
    simp [Matrix.reindex_apply]
  have hk : Matrix.reindexLinearEquiv ℂ ℂ (Equiv.prodCongr er.symm el.symm)
      (Equiv.prodCongr er.symm el.symm) (yᴴ ⊗ₖ xᴴ) =
      (Matrix.reindex er.symm er.symm y)ᴴ ⊗ₖ
        (Matrix.reindex el.symm el.symm x)ᴴ := by
    rw [Matrix.conjTranspose_reindex, Matrix.conjTranspose_reindex]
    exact (Matrix.kroneckerMap_reindex (fun a b : ℂ ↦ a * b)
      er.symm er.symm el.symm el.symm yᴴ xᴴ).symm
  rw [hv, hk]

/-- Global conjugation invariance produces the literal local equations for
the actual supplied source factors of a canonical-form-II tensor. The gates
are not chosen anew, and no local gauge-existence premise is used.
Source: arXiv:1703.09188, `prop1conj`, lines 1030–1033.

**Scope restriction (reduced canonical presentation):** This theorem and
`exists_local_conjugation_gauges_common_transpose_case` concern the supplied
reduced canonical presentation, not an arbitrary nonminimal ambient tensor;
see `docs/paper-gaps/mpu_canonical_form_full_support.tex`. -/
theorem IsMPUCanonicalFormII.exists_local_conjugation_gauges
    {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (huS : (SourceFactors.sourceU U S).IsUnitaryBetween)
    (hconj : ∀ N : ℕ, 1 < N → mpo U N = (mpo U N).map (starRingEnd ℂ)) :
    ∃ (x : Matrix.unitaryGroup (Fin ℓ[U]) ℂ) (y : Matrix.unitaryGroup (Fin r[U]) ℂ),
      (SourceFactors.sourceU U S).map (starRingEnd ℂ) =
        ((x : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ) ⊗ₖ (y : Matrix (Fin r[U]) (Fin r[U]) ℂ)) *
          SourceFactors.sourceU U S ∧
      (SourceFactors.sourceV U S).map (starRingEnd ℂ) =
        SourceFactors.sourceV U S *
          (star (y : Matrix (Fin r[U]) (Fin r[U]) ℂ) ⊗ₖ
            star (x : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ)) := by
  classical
  let er := finCongr (source_ranks_mapStar U).1.symm
  let el := finCongr (source_ranks_mapStar U).2.symm
  have huT : (SourceFactors.sourceU (MPOTensor.mapStar U) S.mapStar).IsUnitaryBetween := by
    rw [S.sourceU_mapStar]
    exact huS.map_star.reindex _ (Equiv.prodCongr el er) (Equiv.refl _)
  obtain ⟨hr, hl, x, y, hu, hv⟩ :=
    hU.exists_supplied_source_gate_unitary_gauges_of_mpo_eq hU.mapStar S S.mapStar huS huT
      (by intro N hN; rw [mpo_map_star]; exact hconj N hN)
  let x' : Matrix.unitaryGroup (Fin ℓ[U]) ℂ :=
    ⟨Matrix.reindex el.symm el.symm x, Matrix.reindex_mem_unitaryGroup _ _ x.property⟩
  let y' : Matrix.unitaryGroup (Fin r[U]) ℂ :=
    ⟨Matrix.reindex er.symm er.symm y, Matrix.reindex_mem_unitaryGroup _ _ y.property⟩
  refine ⟨x', y', ?_, ?_⟩
  · have h := congrArg
      (Matrix.reindex (Equiv.prodCongr el.symm er.symm) (Equiv.refl _)) hu
    rw [S.sourceU_mapStar] at h
    change Matrix.reindex (Equiv.prodCongr el.symm er.symm) (Equiv.refl _)
        (Matrix.reindex (Equiv.prodCongr el er) (Equiv.refl _)
          ((SourceFactors.sourceU U S).map (starRingEnd ℂ))) =
      Matrix.reindex (Equiv.prodCongr el.symm er.symm) (Equiv.refl _)
        (((x : Matrix (Fin ℓ[MPOTensor.mapStar U]) (Fin ℓ[MPOTensor.mapStar U]) ℂ) ⊗ₖ
          (y : Matrix (Fin r[MPOTensor.mapStar U]) (Fin r[MPOTensor.mapStar U]) ℂ)) *
          Matrix.reindex (Equiv.prodCongr el er) (Equiv.refl _)
          (SourceFactors.sourceU U S)) at h
    rw [remove_source_rank_reindex_left el er
      (x : Matrix (Fin ℓ[MPOTensor.mapStar U]) (Fin ℓ[MPOTensor.mapStar U]) ℂ)
      (y : Matrix (Fin r[MPOTensor.mapStar U]) (Fin r[MPOTensor.mapStar U]) ℂ)
      (SourceFactors.sourceU U S)] at h
    have hcancel : Matrix.reindex (Equiv.prodCongr el.symm er.symm) (Equiv.refl _)
        (Matrix.reindex (Equiv.prodCongr el er) (Equiv.refl _)
          ((SourceFactors.sourceU U S).map (starRingEnd ℂ))) =
        (SourceFactors.sourceU U S).map (starRingEnd ℂ) := by
      let E := Matrix.reindexLinearEquiv ℂ ℂ (Equiv.prodCongr el er)
        (Equiv.refl (Fin d × Fin d))
      change E.symm (E ((SourceFactors.sourceU U S).map (starRingEnd ℂ))) = _
      exact E.symm_apply_apply _
    rw [hcancel] at h
    simpa only [x', y'] using h
  · have h := congrArg
      (Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er.symm el.symm)) hv
    rw [S.sourceV_mapStar] at h
    change Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er.symm el.symm)
        (Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er el)
          ((SourceFactors.sourceV U S).map (starRingEnd ℂ))) =
      Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er.symm el.symm)
        (Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er el) (SourceFactors.sourceV U S) *
          ((y : Matrix (Fin r[MPOTensor.mapStar U]) (Fin r[MPOTensor.mapStar U]) ℂ)ᴴ ⊗ₖ
            (x : Matrix (Fin ℓ[MPOTensor.mapStar U]) (Fin ℓ[MPOTensor.mapStar U]) ℂ)ᴴ)) at h
    rw [remove_source_rank_reindex_right el er
      (x : Matrix (Fin ℓ[MPOTensor.mapStar U]) (Fin ℓ[MPOTensor.mapStar U]) ℂ)
      (y : Matrix (Fin r[MPOTensor.mapStar U]) (Fin r[MPOTensor.mapStar U]) ℂ)
      (SourceFactors.sourceV U S)] at h
    have hcancel : Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er.symm el.symm)
        (Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er el)
          ((SourceFactors.sourceV U S).map (starRingEnd ℂ))) =
        (SourceFactors.sourceV U S).map (starRingEnd ℂ) := by
      let E := Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl (Fin d × Fin d))
        (Equiv.prodCongr er el)
      change E.symm (E ((SourceFactors.sourceV U S).map (starRingEnd ℂ))) = _
      exact E.symm_apply_apply _
    rw [hcancel] at h
    simpa only [x', y', Matrix.star_eq_conjTranspose] using h

/-- The forward local conjugation equations have one common symmetric or
skew-symmetric case for the actual supplied source gates. This completes
the algebraic forward argument of arXiv:1703.09188, `prop1conj`,
lines 1030–1038, in the reduced canonical presentation specified above. -/
theorem IsMPUCanonicalFormII.exists_local_conjugation_gauges_common_transpose_case
    {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (huS : (SourceFactors.sourceU U S).IsUnitaryBetween)
    (hconj : ∀ N : ℕ, 1 < N → mpo U N = (mpo U N).map (starRingEnd ℂ)) :
    let u := SourceFactors.sourceU U S
    let v := SourceFactors.sourceV U S
    ∃ (x : Matrix.unitaryGroup (Fin ℓ[U]) ℂ) (y : Matrix.unitaryGroup (Fin r[U]) ℂ),
      (((x : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ)ᵀ = x ∧
          (y : Matrix (Fin r[U]) (Fin r[U]) ℂ)ᵀ = y) ∨
        ((x : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ)ᵀ = -x ∧
          (y : Matrix (Fin r[U]) (Fin r[U]) ℂ)ᵀ = -y)) ∧
      u.map (starRingEnd ℂ) =
        ((x : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ) ⊗ₖ (y : Matrix (Fin r[U]) (Fin r[U]) ℂ)) * u ∧
      v.map (starRingEnd ℂ) = v *
        (star (y : Matrix (Fin r[U]) (Fin r[U]) ℂ) ⊗ₖ
          star (x : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ)) := by
  classical
  let : NeZero d := hU.neZero_phys
  have hpos : 0 < Fintype.card (Fin ℓ[U] × Fin r[U]) :=
    lt_of_lt_of_le (by simpa using Nat.mul_pos (NeZero.pos d) (NeZero.pos d))
      (huS.1.card_le _)
  obtain ⟨l, r⟩ := Fintype.card_pos_iff.mp hpos
  let : Nonempty (Fin ℓ[U]) := ⟨l⟩
  let : Nonempty (Fin r[U]) := ⟨r⟩
  obtain ⟨x, y, hu, hv⟩ := hU.exists_local_conjugation_gauges S huS hconj
  exact ⟨x, y, Matrix.transpose_eq_self_or_transpose_eq_neg_of_gate_conjugation
    x.property y.property huS.2 hu, hu, hv⟩

end MPOTensor
