/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ConjugationGateGauge
import TNLean.MPS.MPU.ConjugationSourceFactors

/-!
# Orthogonal and symplectic standard forms of conjugation-invariant MPUs

Supplied source factors `X_i, Y_i, Z_i` of an MPO tensor can be changed by
unitaries `a, b` on the two source ranks: `Y₂ ↦ a Y₂`, `Y₁ ↦ b Y₁`, with the
compensating changes of `X_i, Z_i`. These are again source factors of the same
tensor at the same weight, and their gates are `(a ⊗ b) u` and
`v (b† ⊗ a†)`. Choosing `a, b` from the unitary-congruence normal forms of the
conjugation gauges `x, y` of `prop1conj` puts the gates in the orthogonal
Case I or the symplectic Case II of arXiv:1703.09188, Proposition `corconj`.

## Main statements

* `MPOTensor.SourceFactors.rankGauge`: the rank change of source factors.
* `MPOTensor.SourceFactors.exists_orthogonal_rankGauge_of_symmetric`,
  `MPOTensor.SourceFactors.exists_symplectic_rankGauge_of_skew`: Case I and
  Case II, starting from the local conjugation equations.
* `MPOTensor.IsMPUCanonicalFormII.exists_conjugation_standard_form`: the
  existence part of `corconj` from global conjugation invariance.
* `MPOTensor.IsMPUCanonicalFormII.exists_orthogonal_gauge_of_mpo_eq`,
  `MPOTensor.IsMPUCanonicalFormII.exists_symplectic_gauge_of_mpo_eq`: the
  uniqueness parts of `corconj`.

**Scope restriction (reduced canonical presentation):** the last three
theorems concern tensors in canonical form II with supplied source factors
whose gate `u` is unitary, as in
`MPOTensor.IsMPUCanonicalFormII.exists_local_conjugation_gauges`, not an
arbitrary standard form; see
`docs/paper-gaps/mpu_canonical_form_full_support.tex`.

**Local fix (Case II uniqueness of `v`):**
`exists_symplectic_gauge_of_mpo_eq` states `v'' = v' (S_r† ⊗ S_ℓ†)` where the
source prints `S_rᵀ ⊗ S_ℓᵀ`; see
`docs/paper-gaps/mpu_conjugation_symplectic_uniqueness_transpose.tex`.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D : ℕ}

namespace SourceFactors

variable {U : MPOTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}

/-- Change supplied source factors by unitaries `a` on the left rank `ℓ` and
`b` on the right rank `r`: `Y₂ ↦ a Y₂`, `X₂ ↦ X₂ a†`, `Z₂ ↦ Z₂ a†` and
`Y₁ ↦ b Y₁`, `X₁ ↦ X₁ b†`, `Z₁ ↦ Z₁ b†`. These are the changes of standard form
`u' = (U ⊗ V) u`, `v' = v (V† ⊗ U†)` in the proof of arXiv:1703.09188,
`corconj`, lines 1142--1145, carried out on the source factors of `eq:sf-svd`,
`Y1Y1X1X1` and `YZ=1` (lines 479--506). -/
noncomputable def rankGauge (S : SourceFactors U ρ)
    {a : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ} {b : Matrix (Fin r[U]) (Fin r[U]) ℂ}
    (ha : a ∈ Matrix.unitaryGroup (Fin ℓ[U]) ℂ) (hb : b ∈ Matrix.unitaryGroup (Fin r[U]) ℂ) :
    SourceFactors U ρ where
  X₁ := S.X₁ * bᴴ
  Y₁ := b * S.Y₁
  Z₁ := S.Z₁ * bᴴ
  X₂ := S.X₂ * aᴴ
  Y₂ := a * S.Y₂
  Z₂ := S.Z₂ * aᴴ
  sourceCutM₁_eq := by
    rw [S.sourceCutM₁_eq, Matrix.mul_assoc, ← Matrix.mul_assoc bᴴ, ← Matrix.star_eq_conjTranspose,
      Matrix.mem_unitaryGroup_iff'.mp hb, Matrix.one_mul]
  sourceCutM₂_eq := by
    rw [S.sourceCutM₂_eq, Matrix.mul_assoc, ← Matrix.mul_assoc aᴴ, ← Matrix.star_eq_conjTranspose,
      Matrix.mem_unitaryGroup_iff'.mp ha, Matrix.one_mul]
  X₁_weighted_isometry := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc b * S.X₁ᴴ * sourceWeight (d := d) ρ * (S.X₁ * bᴴ) =
        b * (S.X₁ᴴ * sourceWeight (d := d) ρ * S.X₁) * bᴴ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [S.X₁_weighted_isometry, Matrix.mul_one, ← Matrix.star_eq_conjTranspose,
            Matrix.mem_unitaryGroup_iff.mp hb]
  X₂_isometry := by
    rw [Matrix.IsIsometry, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc a * S.X₂ᴴ * (S.X₂ * aᴴ) = a * (S.X₂ᴴ * S.X₂) * aᴴ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [show S.X₂ᴴ * S.X₂ = 1 from S.X₂_isometry, Matrix.mul_one,
            ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff.mp ha]
  Y₁_mul_Z₁ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc S.Y₁, S.Y₁_mul_Z₁, Matrix.one_mul,
      ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff.mp hb]
  Y₂_mul_Z₂ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc S.Y₂, S.Y₂_mul_Z₂, Matrix.one_mul,
      ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff.mp ha]

/-- The gate `u` of rank-changed source factors is `(a ⊗ b) u`.
Source: arXiv:1703.09188, `corconj`, line 1143, with `u = Y₂ - Y₁` from `uu`
(lines 532--543). -/
theorem sourceU_rankGauge (S : SourceFactors U ρ)
    {a : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ} {b : Matrix (Fin r[U]) (Fin r[U]) ℂ}
    (ha : a ∈ Matrix.unitaryGroup (Fin ℓ[U]) ℂ) (hb : b ∈ Matrix.unitaryGroup (Fin r[U]) ℂ) :
    SourceFactors.sourceU U (S.rankGauge ha hb) = (a ⊗ₖ b) * SourceFactors.sourceU U S := by
  ext ⟨l, r⟩ ⟨i₁, i₂⟩
  simp only [SourceFactors.sourceU_apply, rankGauge, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => enter [2, β]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l' _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r' _ ↦ Finset.sum_congr rfl fun β _ ↦ ?_
  ring

/-- The gate `v` of rank-changed source factors is `v (b† ⊗ a†)`.
Source: arXiv:1703.09188, `corconj`, line 1144, with `v = X₁ - X₂` from
`vdagger` (lines 532--543). -/
theorem sourceV_rankGauge (S : SourceFactors U ρ)
    {a : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ} {b : Matrix (Fin r[U]) (Fin r[U]) ℂ}
    (ha : a ∈ Matrix.unitaryGroup (Fin ℓ[U]) ℂ) (hb : b ∈ Matrix.unitaryGroup (Fin r[U]) ℂ) :
    SourceFactors.sourceV U (S.rankGauge ha hb) = SourceFactors.sourceV U S * (bᴴ ⊗ₖ aᴴ) := by
  ext ⟨j₁, j₂⟩ ⟨r, l⟩
  simp only [SourceFactors.sourceV_apply, rankGauge, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => enter [2, α]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r' _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l' _ ↦ Finset.sum_congr rfl fun α _ ↦ ?_
  ring

/-- **Case I of `corconj` from the local conjugation equations.** If the gates
of supplied source factors satisfy `conj(u) = (x ⊗ y) u` and
`conj(v) = v (y† ⊗ x†)` with symmetric unitaries `x, y`, then a rank change of
the source factors makes both gates real.
Source: arXiv:1703.09188, `corconj`, Case I, eq. `ortuv` (lines 1104--1112),
proof at lines 1129--1149. -/
theorem exists_orthogonal_rankGauge_of_symmetric (S : SourceFactors U ρ)
    {x : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ} {y : Matrix (Fin r[U]) (Fin r[U]) ℂ}
    (hx : x ∈ Matrix.unitaryGroup (Fin ℓ[U]) ℂ) (hy : y ∈ Matrix.unitaryGroup (Fin r[U]) ℂ)
    (hxT : xᵀ = x) (hyT : yᵀ = y)
    (hu : (SourceFactors.sourceU U S).map (starRingEnd ℂ) =
      (x ⊗ₖ y) * SourceFactors.sourceU U S)
    (hv : (SourceFactors.sourceV U S).map (starRingEnd ℂ) =
      SourceFactors.sourceV U S * (yᴴ ⊗ₖ xᴴ)) :
    ∃ (a : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ) (b : Matrix (Fin r[U]) (Fin r[U]) ℂ)
      (ha : a ∈ Matrix.unitaryGroup (Fin ℓ[U]) ℂ) (hb : b ∈ Matrix.unitaryGroup (Fin r[U]) ℂ),
      (SourceFactors.sourceU U (S.rankGauge ha hb)).map (starRingEnd ℂ) =
        SourceFactors.sourceU U (S.rankGauge ha hb) ∧
      (SourceFactors.sourceV U (S.rankGauge ha hb)).map (starRingEnd ℂ) =
        SourceFactors.sourceV U (S.rankGauge ha hb) := by
  obtain ⟨a, b, ha, hb, hu', hv'⟩ :=
    Matrix.exists_orthogonal_gauge_of_symmetric hx hy hxT hyT hu hv
  exact ⟨a, b, ha, hb, by rw [sourceU_rankGauge]; exact hu',
    by rw [sourceV_rankGauge]; exact hv'⟩

/-- **Case II of `corconj` from the local conjugation equations.** If the
gates of supplied source factors satisfy `conj(u) = (x ⊗ y) u` and
`conj(v) = v (y† ⊗ x†)` with skew-symmetric unitaries `x, y`, then both ranks
are even and a rank change of the source factors gives
`conj(u') = (Σ_ℓ ⊗ Σ_r) u'` and `conj(v') = v' (Σ_r ⊗ Σ_ℓ)`.
Source: arXiv:1703.09188, `corconj`, Case II, eq. `sympuv` (lines 1113--1125),
proof at lines 1129--1149. -/
theorem exists_symplectic_rankGauge_of_skew (S : SourceFactors U ρ)
    {x : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ} {y : Matrix (Fin r[U]) (Fin r[U]) ℂ}
    (hx : x ∈ Matrix.unitaryGroup (Fin ℓ[U]) ℂ) (hy : y ∈ Matrix.unitaryGroup (Fin r[U]) ℂ)
    (hxT : xᵀ = -x) (hyT : yᵀ = -y)
    (hu : (SourceFactors.sourceU U S).map (starRingEnd ℂ) =
      (x ⊗ₖ y) * SourceFactors.sourceU U S)
    (hv : (SourceFactors.sourceV U S).map (starRingEnd ℂ) =
      SourceFactors.sourceV U S * (yᴴ ⊗ₖ xᴴ)) :
    ∃ (hℓ : Even ℓ[U]) (hr : Even r[U])
      (a : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ) (b : Matrix (Fin r[U]) (Fin r[U]) ℂ)
      (ha : a ∈ Matrix.unitaryGroup (Fin ℓ[U]) ℂ) (hb : b ∈ Matrix.unitaryGroup (Fin r[U]) ℂ),
      (SourceFactors.sourceU U (S.rankGauge ha hb)).map (starRingEnd ℂ) =
        (Matrix.sourceSkewForm hℓ ⊗ₖ Matrix.sourceSkewForm hr) *
          SourceFactors.sourceU U (S.rankGauge ha hb) ∧
      (SourceFactors.sourceV U (S.rankGauge ha hb)).map (starRingEnd ℂ) =
        SourceFactors.sourceV U (S.rankGauge ha hb) *
          (Matrix.sourceSkewForm hr ⊗ₖ Matrix.sourceSkewForm hℓ) := by
  obtain ⟨hℓ, hr, a, b, ha, hb, hu', hv'⟩ :=
    Matrix.exists_symplectic_gauge_of_skew hx hy hxT hyT hu hv
  exact ⟨hℓ, hr, a, b, ha, hb, by rw [sourceU_rankGauge]; exact hu',
    by rw [sourceV_rankGauge]; exact hv'⟩

end SourceFactors

/-- **Orthogonal or symplectic standard form.** Let `U` be in reduced canonical
form II with supplied source factors whose gate `u` is unitary, and let
`U^{(N)}` be fixed by complex conjugation at every length `N > 1`. Then a rank
change of the source factors gives real gates (Case I), or both ranks are even
and the gates satisfy `conj(u') = (Σ_ℓ ⊗ Σ_r) u'` and
`conj(v') = v' (Σ_r ⊗ Σ_ℓ)` (Case II).
Source: arXiv:1703.09188, `corconj`, lines 1098--1149, using the forward
direction of `prop1conj` (lines 1030--1038). The scope restriction of this
module applies. -/
theorem IsMPUCanonicalFormII.exists_conjugation_standard_form
    {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (huS : (SourceFactors.sourceU U S).IsUnitaryBetween)
    (hconj : ∀ N : ℕ, 1 < N → mpo U N = (mpo U N).map (starRingEnd ℂ)) :
    (∃ S' : SourceFactors U ρ,
      (SourceFactors.sourceU U S').map (starRingEnd ℂ) = SourceFactors.sourceU U S' ∧
      (SourceFactors.sourceV U S').map (starRingEnd ℂ) = SourceFactors.sourceV U S') ∨
    (∃ (hℓ : Even ℓ[U]) (hr : Even r[U]) (S' : SourceFactors U ρ),
      (SourceFactors.sourceU U S').map (starRingEnd ℂ) =
        (Matrix.sourceSkewForm hℓ ⊗ₖ Matrix.sourceSkewForm hr) * SourceFactors.sourceU U S' ∧
      (SourceFactors.sourceV U S').map (starRingEnd ℂ) =
        SourceFactors.sourceV U S' * (Matrix.sourceSkewForm hr ⊗ₖ Matrix.sourceSkewForm hℓ)) := by
  obtain ⟨x, y, hcase, hu, hv⟩ :=
    hU.exists_local_conjugation_gauges_common_transpose_case S huS hconj
  rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose] at hv
  rcases hcase with ⟨hxT, hyT⟩ | ⟨hxT, hyT⟩
  · obtain ⟨a, b, ha, hb, hu', hv'⟩ :=
      S.exists_orthogonal_rankGauge_of_symmetric x.property y.property hxT hyT hu hv
    exact Or.inl ⟨S.rankGauge ha hb, hu', hv'⟩
  · obtain ⟨hℓ, hr, a, b, ha, hb, hu', hv'⟩ :=
      S.exists_symplectic_rankGauge_of_skew x.property y.property hxT hyT hu hv
    exact Or.inr ⟨hℓ, hr, S.rankGauge ha hb, hu', hv'⟩

/-- Both source ranks of a canonical-form-II tensor with unitary gate are
nonzero. -/
private theorem nonempty_source_ranks {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (huS : (SourceFactors.sourceU U S).IsUnitaryBetween) :
    Nonempty (Fin ℓ[U]) ∧ Nonempty (Fin r[U]) := by
  let : NeZero d := hU.neZero_phys
  have hpos : 0 < Fintype.card (Fin ℓ[U] × Fin r[U]) :=
    lt_of_lt_of_le (by simpa using Nat.mul_pos (NeZero.pos d) (NeZero.pos d))
      (huS.1.card_le _)
  obtain ⟨l, r⟩ := Fintype.card_pos_iff.mp hpos
  exact ⟨⟨l⟩, ⟨r⟩⟩

/-- Reindexing a left Kronecker action along a product of equivalences. -/
private theorem reindex_kronecker_mul {a a' b b' P : Type*} [Fintype a] [Fintype b]
    [Fintype a'] [Fintype b'] (ea : a ≃ a') (eb : b ≃ b')
    (A : Matrix a a ℂ) (B : Matrix b b ℂ) (M : Matrix (a × b) P ℂ) :
    Matrix.reindex (Equiv.prodCongr ea eb) (Equiv.refl P) ((A ⊗ₖ B) * M) =
      (Matrix.reindex ea ea A ⊗ₖ Matrix.reindex eb eb B) *
        Matrix.reindex (Equiv.prodCongr ea eb) (Equiv.refl P) M := by
  rw [Matrix.kroneckerMap_reindex]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

/-- **Case I uniqueness of `corconj`.** Let `U, V` be in reduced canonical
form II with equal periodic operators at every length `N > 1`, and let supplied
source factors of both have unitary gate `u` and real gates `u'` and `u''`.
Then the ranks agree and there are real orthogonal `O_ℓ, O_r` with
`u'' = (O_ℓ ⊗ O_r) u'` and `v'' = v' (O_rᵀ ⊗ O_ℓᵀ)`.
Source: arXiv:1703.09188, `corconj`, Case I (lines 1104--1112), proof at
lines 1151--1157. The scope restriction of this module applies. -/
theorem IsMPUCanonicalFormII.exists_orthogonal_gauge_of_mpo_eq
    {U V : MPOTensor d D} (hU : IsMPUCanonicalFormII U) (hV : IsMPUCanonicalFormII V)
    {ρ ρ' : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ) (T : SourceFactors V ρ')
    (huS : (SourceFactors.sourceU U S).IsUnitaryBetween)
    (huT : (SourceFactors.sourceU V T).IsUnitaryBetween)
    (hEq : ∀ N : ℕ, 1 < N → mpo U N = mpo V N)
    (hS : (SourceFactors.sourceU U S).map (starRingEnd ℂ) = SourceFactors.sourceU U S)
    (hT : (SourceFactors.sourceU V T).map (starRingEnd ℂ) = SourceFactors.sourceU V T) :
    ∃ (hr : r[V] = r[U]) (hl : ℓ[V] = ℓ[U])
      (Oℓ : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) (Or : Matrix (Fin r[V]) (Fin r[V]) ℂ),
      Oℓ ∈ Matrix.unitaryGroup (Fin ℓ[V]) ℂ ∧ Oℓ.map (starRingEnd ℂ) = Oℓ ∧
      Or ∈ Matrix.unitaryGroup (Fin r[V]) ℂ ∧ Or.map (starRingEnd ℂ) = Or ∧
      SourceFactors.sourceU V T = (Oℓ ⊗ₖ Or) *
          Matrix.reindex (Equiv.prodCongr (finCongr hl.symm) (finCongr hr.symm))
            (Equiv.refl _) (SourceFactors.sourceU U S) ∧
      SourceFactors.sourceV V T =
        Matrix.reindex (Equiv.refl _)
            (Equiv.prodCongr (finCongr hr.symm) (finCongr hl.symm))
            (SourceFactors.sourceV U S) * (Orᵀ ⊗ₖ Oℓᵀ) := by
  obtain ⟨hr, hl, x, y, hu, hv⟩ :=
    hU.exists_supplied_source_gate_unitary_gauges_of_mpo_eq hV S T huS huT hEq
  obtain ⟨hnl, hnr⟩ := nonempty_source_ranks hV T huT
  set u₀ := Matrix.reindex (Equiv.prodCongr (finCongr hl.symm) (finCongr hr.symm))
    (Equiv.refl _) (SourceFactors.sourceU U S)
  have hu₀ : u₀.IsCoisometry := (huS.reindex _ _ _).2
  have hu₀real : u₀.map (starRingEnd ℂ) = u₀ := by
    simp only [u₀, Matrix.reindex_apply, ← Matrix.submatrix_map, hS]
  obtain ⟨Oℓ, Or, hOℓ, hOℓr, hOr, hOrr, hab, hba⟩ :=
    Matrix.exists_orthogonal_factors_of_kronecker_mul hu₀ x.property y.property hu₀real
      (by rw [← hu]; exact hT)
  refine ⟨hr, hl, Oℓ, Or, hOℓ, hOℓr, hOr, hOrr, by rw [hu, hab], ?_⟩
  rw [hv, Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose, hba]

/-- **Case II uniqueness of `corconj`.** Let `U, V` be in reduced canonical
form II with equal periodic operators at every length `N > 1`, and let supplied
source factors of both have unitary gate `u` and gates in the symplectic form
`conj(u') = (Σ_ℓ ⊗ Σ_r) u'` and `conj(u'') = (Σ_ℓ ⊗ Σ_r) u''`. Then the ranks
agree and there are unitaries `S_ℓ, S_r` with `S_xᵀ Σ_x S_x = Σ_x`,
`u'' = (S_ℓ ⊗ S_r) u'` and `v'' = v' (S_r† ⊗ S_ℓ†)`.
Source: arXiv:1703.09188, `corconj`, Case II (lines 1113--1125), proof at
lines 1151--1163. The scope restriction and the local fix of this module
apply. -/
theorem IsMPUCanonicalFormII.exists_symplectic_gauge_of_mpo_eq
    {U V : MPOTensor d D} (hU : IsMPUCanonicalFormII U) (hV : IsMPUCanonicalFormII V)
    {ρ ρ' : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ) (T : SourceFactors V ρ')
    (huS : (SourceFactors.sourceU U S).IsUnitaryBetween)
    (huT : (SourceFactors.sourceU V T).IsUnitaryBetween)
    (hEq : ∀ N : ℕ, 1 < N → mpo U N = mpo V N)
    (hℓ : Even ℓ[U]) (hr : Even r[U]) (hℓ' : Even ℓ[V]) (hr' : Even r[V])
    (hS : (SourceFactors.sourceU U S).map (starRingEnd ℂ) =
      (Matrix.sourceSkewForm hℓ ⊗ₖ Matrix.sourceSkewForm hr) * SourceFactors.sourceU U S)
    (hT : (SourceFactors.sourceU V T).map (starRingEnd ℂ) =
      (Matrix.sourceSkewForm hℓ' ⊗ₖ Matrix.sourceSkewForm hr') * SourceFactors.sourceU V T) :
    ∃ (hrr : r[V] = r[U]) (hll : ℓ[V] = ℓ[U])
      (Sℓ : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) (Sr : Matrix (Fin r[V]) (Fin r[V]) ℂ),
      Sℓ ∈ Matrix.unitaryGroup (Fin ℓ[V]) ℂ ∧
      Sℓᵀ * Matrix.sourceSkewForm hℓ' * Sℓ = Matrix.sourceSkewForm hℓ' ∧
      Sr ∈ Matrix.unitaryGroup (Fin r[V]) ℂ ∧
      Srᵀ * Matrix.sourceSkewForm hr' * Sr = Matrix.sourceSkewForm hr' ∧
      SourceFactors.sourceU V T = (Sℓ ⊗ₖ Sr) *
          Matrix.reindex (Equiv.prodCongr (finCongr hll.symm) (finCongr hrr.symm))
            (Equiv.refl _) (SourceFactors.sourceU U S) ∧
      SourceFactors.sourceV V T =
        Matrix.reindex (Equiv.refl _)
            (Equiv.prodCongr (finCongr hrr.symm) (finCongr hll.symm))
            (SourceFactors.sourceV U S) * (Srᴴ ⊗ₖ Sℓᴴ) := by
  obtain ⟨hrr, hll, x, y, hu, hv⟩ :=
    hU.exists_supplied_source_gate_unitary_gauges_of_mpo_eq hV S T huS huT hEq
  obtain ⟨hnl, hnr⟩ := nonempty_source_ranks hV T huT
  set u₀ := Matrix.reindex (Equiv.prodCongr (finCongr hll.symm) (finCongr hrr.symm))
    (Equiv.refl _) (SourceFactors.sourceU U S)
  have hu₀ : u₀.IsCoisometry := (huS.reindex _ _ _).2
  have hu₀S : u₀.map (starRingEnd ℂ) =
      (Matrix.sourceSkewForm hℓ' ⊗ₖ Matrix.sourceSkewForm hr') * u₀ := by
    have h := congrArg (Matrix.reindex (Equiv.prodCongr (finCongr hll.symm)
      (finCongr hrr.symm)) (Equiv.refl _)) hS
    rw [reindex_kronecker_mul, Matrix.reindex_finCongr_sourceSkewForm,
      Matrix.reindex_finCongr_sourceSkewForm] at h
    simpa only [u₀, Matrix.reindex_apply, ← Matrix.submatrix_map] using h
  obtain ⟨Sℓ, Sr, hSℓ, hSℓS, hSr, hSrS, hab, hba⟩ :=
    Matrix.exists_symplectic_factors_of_kronecker_mul hℓ' hr' hu₀ x.property y.property hu₀S
      (by rw [← hu]; exact hT)
  refine ⟨hrr, hll, Sℓ, Sr, hSℓ, hSℓS, hSr, hSrS, by rw [hu, hab], ?_⟩
  rw [hv, Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose, hba]

end MPOTensor
