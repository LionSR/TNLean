/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.UnitaryKronecker
import TNLean.MPS.MPU.SourceFactorChoice
import TNLean.MPS.MPU.TwoSiteStandardForm
import TNLean.MPS.MPU.FundamentalTheoremGatesNecessity
import TNLean.MPS.MPU.FundamentalTheoremGatesBlocked

/-!
# The gate statements for every choice of compact decompositions

The gate theorems of arXiv:1703.09188 (lines 545--622) are proved in the library for the gates
built from one fixed choice of the compact decompositions of the two source cuts
(`eq:sf-svd`, `Y1Y1X1X1`, `Z1Z2`, lines 479--502). By the change-of-decomposition theorem
(`MPOTensor.sourceU_sourceV_sourceFactorsOf_relatingUnitary`), the gates of any other choice
are $u'=(x_2\otimes x_1)u$ and $v'=v(x_1^\dagger\otimes x_2^\dagger)$ with unitaries
$x_1,x_2$. This module transports the gate statements along these unitaries (milestone M-E
proposal, `ME.tex`, Corollary 1.4).

## Main results

* `MPOTensor.IsMPUCanonicalFormII.sourceU_sourceFactorsOf_isIsometry`: the gate $u$ of any
  choice is an isometry (Corollary 1.4(a)).
* `MPOTensor.IsMPUCanonicalFormII.isMPUSimple_iff_sourceU_sourceFactorsOf_isUnitaryBetween`,
  `isMPUSimple_iff_sourceV_sourceFactorsOf_isUnitaryBetween`: simplicity is unitarity of either
  gate of any choice (Corollary 1.4(b)).
* `MPOTensor.TwoSiteStandardFormData.ofGateGauges`: two-site standard-form data transported along
  unitaries on the two internal legs.
* `MPOTensor.IsMPUCanonicalFormII.exists_twoSiteStandardFormData_sourceFactorsOf`: two-site
  standard-form data for the gates of any choice (Corollary 1.4(c)).
* `MPOTensor.IsMPUCanonicalFormII.exists_source_gate_unitary_gauges_of_mpo_eq_sourceFactorsOf`:
  the gate relation of the fundamental theorem for any choices (Corollary 1.4(d)).

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017, arXiv:1703.09188], lines 479--502 and
  545--622, and Theorem `FundamentalMPU` (lines 624--648).
* Milestone M-E proposal `ME.tex` (mpu-notes, programme `mpu-close`), Section 2.4.
-/

open scoped Matrix Kronecker ComplexOrder
open Matrix

namespace Matrix

variable {m n o m' n' : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- A member of the unitary group is unitary between its coordinate spaces. -/
theorem isUnitaryBetween_coe_unitaryGroup (x : unitaryGroup m ℂ) :
    (x : Matrix m m ℂ).IsUnitaryBetween :=
  (isUnitaryBetween_iff_mem_unitaryGroup _).mpr x.2

/-- The adjoint of a member of the unitary group is unitary between its coordinate spaces. -/
theorem isUnitaryBetween_star_coe_unitaryGroup (x : unitaryGroup m ℂ) :
    (star (x : Matrix m m ℂ)).IsUnitaryBetween :=
  (isUnitaryBetween_iff_mem_unitaryGroup _).mpr (Unitary.star_mem x.2)

/-- Left multiplication by a unitary-between matrix preserves and reflects unitarity. -/
theorem isUnitaryBetween_mul_iff_of_left [Fintype o] [DecidableEq o] {K : Matrix m n ℂ}
    (hK : K.IsUnitaryBetween) (u : Matrix n o ℂ) :
    (K * u).IsUnitaryBetween ↔ u.IsUnitaryBetween :=
  ⟨IsUnitaryBetween.of_mul_left K u hK, fun hu ↦ hK.mul K u hu⟩

/-- Right multiplication by a unitary-between matrix preserves and reflects unitarity. -/
theorem isUnitaryBetween_mul_iff_of_right [Fintype o] [DecidableEq o] {K : Matrix n o ℂ}
    (hK : K.IsUnitaryBetween) (v : Matrix m n ℂ) :
    (v * K).IsUnitaryBetween ↔ v.IsUnitaryBetween :=
  ⟨IsUnitaryBetween.of_mul_right v K hK, fun hv ↦ hv.mul v K hK⟩

omit [DecidableEq m] [DecidableEq n] in
/-- Reindexing the rows of a product with a Kronecker left factor. -/
theorem reindex_kronecker_mul [Fintype m'] [Fintype n'] (el : m ≃ m') (er : n ≃ n')
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (w : Matrix (m × n) o ℂ) :
    Matrix.reindex (el.prodCongr er) (Equiv.refl o) ((A ⊗ₖ B) * w) =
      (Matrix.reindex el el A ⊗ₖ Matrix.reindex er er B) *
        Matrix.reindex (el.prodCongr er) (Equiv.refl o) w := by
  rw [Matrix.kroneckerMap_reindex, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

omit [DecidableEq m] [DecidableEq n] in
/-- Reindexing the columns of a product with a Kronecker right factor. -/
theorem reindex_mul_kronecker [Fintype m'] [Fintype n'] (er : m ≃ m') (el : n ≃ n')
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (w : Matrix o (m × n) ℂ) :
    Matrix.reindex (Equiv.refl o) (er.prodCongr el) (w * (A ⊗ₖ B)) =
      Matrix.reindex (Equiv.refl o) (er.prodCongr el) w *
        (Matrix.reindex er er A ⊗ₖ Matrix.reindex el el B) := by
  rw [Matrix.kroneckerMap_reindex, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

omit [DecidableEq m] [DecidableEq n] in
/-- A product vector times a Kronecker product is the product of the two vector-matrix
products. -/
theorem vecMul_kronecker (p : m → ℂ) (w : n → ℂ) (A : Matrix m m' ℂ) (B : Matrix n n' ℂ) :
    (fun q : m × n ↦ p q.1 * w q.2) ᵥ* (A ⊗ₖ B) = fun q ↦ (p ᵥ* A) q.1 * (w ᵥ* B) q.2 := by
  funext q
  simp only [Matrix.vecMul, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- Contracting a gauged gate against gauged half factors: the unitaries cancel on the
contracted legs (ME.tex, proof of Corollary 1.4(c)). -/
theorem sum_sum_vecMul_star_mul_kronecker_mul (a : m → ℂ) (b : n → ℂ)
    (u : Matrix (m × n) o ℂ) (x : unitaryGroup m ℂ) (y : unitaryGroup n ℂ) (j : o) :
    ∑ t, ∑ s, (a ᵥ* star (x : Matrix m m ℂ)) t *
        (((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * u) (t, s) j *
          (b ᵥ* star (y : Matrix n n ℂ)) s =
      ∑ t, ∑ s, a t * u (t, s) j * b s := by
  set c' : m × n → ℂ := fun q ↦ (a ᵥ* star (x : Matrix m m ℂ)) q.1 *
    (b ᵥ* star (y : Matrix n n ℂ)) q.2
  have hx : (a ᵥ* star (x : Matrix m m ℂ)) ᵥ* (x : Matrix m m ℂ) = a := by
    rw [Matrix.vecMul_vecMul, Unitary.coe_star_mul_self, Matrix.vecMul_one]
  have hy : (b ᵥ* star (y : Matrix n n ℂ)) ᵥ* (y : Matrix n n ℂ) = b := by
    rw [Matrix.vecMul_vecMul, Unitary.coe_star_mul_self, Matrix.vecMul_one]
  have hc : c' ᵥ* ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) = fun q ↦ a q.1 * b q.2 := by
    rw [vecMul_kronecker, hx, hy]
  calc
    _ = (c' ᵥ* (((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * u)) j := by
      simp only [c', Matrix.vecMul, dotProduct, Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
    _ = ((fun q : m × n ↦ a q.1 * b q.2) ᵥ* u) j := by rw [← Matrix.vecMul_vecMul, hc]
    _ = _ := by
      simp only [Matrix.vecMul, dotProduct, Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

end Matrix

namespace MPOTensor

/-- Two-site standard-form data for gates $u$, $v$ give data for the gauged gates
$(x\otimes y)u$ and $v(y^\dagger\otimes x^\dagger)$, with half factors $X_1y^\dagger$ and
$X_2x^\dagger$ (ME.tex, proof of Corollary 1.4(c); arXiv:1703.09188, `StandardForm` and
Definition `SF`, lines 603--622). -/
noncomputable def TwoSiteStandardFormData.ofGateGauges {d D ℓ r : ℕ} {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ} {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (data : TwoSiteStandardFormData W u v) (x : unitaryGroup (Fin ℓ) ℂ)
    (y : unitaryGroup (Fin r) ℂ) :
    TwoSiteStandardFormData W ((x : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y : Matrix (Fin r) (Fin r) ℂ) * u)
      (v * (star (y : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ star (x : Matrix (Fin ℓ) (Fin ℓ) ℂ))) where
  phys_pos := data.phys_pos
  bond_pos := data.bond_pos
  left_pos := data.left_pos
  right_pos := data.right_pos
  X₁ := data.X₁ * star (y : Matrix (Fin r) (Fin r) ℂ)
  X₂ := data.X₂ * star (x : Matrix (Fin ℓ) (Fin ℓ) ℂ)
  u_unitary := ((Matrix.isUnitaryBetween_coe_unitaryGroup x).kronecker _ _
    (Matrix.isUnitaryBetween_coe_unitaryGroup y)).mul _ _ data.u_unitary
  v_unitary := data.v_unitary.mul _ _ ((Matrix.isUnitaryBetween_star_coe_unitaryGroup y).kronecker
    _ _ (Matrix.isUnitaryBetween_star_coe_unitaryGroup x))
  v_apply := by
    intro i₁ i₂ s t
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, data.v_apply,
      Finset.sum_mul, Finset.mul_sum]
    conv_lhs =>
      enter [2, s']
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ ↦ ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  W_apply := by
    intro i j α γ
    rw [data.W_apply]
    exact (Matrix.sum_sum_vecMul_star_mul_kronecker_mul (data.X₂ (α, _)) (data.X₁ (_, γ))
      u x y _).symm

variable {d D : ℕ} {U : MPOTensor d D}

/-- The gate $u$ of an MPU tensor in canonical form II, built from any compact decompositions of
its cuts, is an isometry (ME.tex, Corollary 1.4(a); arXiv:1703.09188, Lemma `lemuisometry`,
lines 545--557, with the factors of lines 479--502). -/
theorem IsMPUCanonicalFormII.sourceU_sourceFactorsOf_isIsometry (hU : IsMPUCanonicalFormII U)
    (S₁ : SourceCutSVD (sourceCutM₁ U) r[U]) (S₂ : SourceCutSVD (sourceCutM₂ U) ℓ[U]) :
    (SourceFactors.sourceU U (sourceFactorsOf S₁ S₂ hU.ρ hU.ρ_posDef)).IsIsometry :=
  have := hU.neZero_phys
  SourceFactors.sourceU_isIsometry_of_isMPU U hU.isMPU _ hU.ρ_isDiag _
    hU.normalizedDiagonal_pow_eq_vecMulVec

/-- Simplicity is unitarity of the gate $u$ built from any compact decompositions
(ME.tex, Corollary 1.4(b); arXiv:1703.09188, Theorem `ThmFund1`, lines 563--601, with the
factors of lines 479--502). -/
theorem IsMPUCanonicalFormII.isMPUSimple_iff_sourceU_sourceFactorsOf_isUnitaryBetween
    (hU : IsMPUCanonicalFormII U) (S₁ : SourceCutSVD (sourceCutM₁ U) r[U])
    (S₂ : SourceCutSVD (sourceCutM₂ U) ℓ[U]) :
    IsMPUSimple U ↔
      (SourceFactors.sourceU U (sourceFactorsOf S₁ S₂ hU.ρ hU.ρ_posDef)).IsUnitaryBetween := by
  rw [(sourceU_sourceV_sourceFactorsOf_relatingUnitary (sourceSVD₁ U) S₁ (sourceSVD₂ U) S₂
      hU.ρ hU.ρ_posDef).1,
    Matrix.isUnitaryBetween_mul_iff_of_left ((Matrix.isUnitaryBetween_coe_unitaryGroup _).kronecker
      _ _ (Matrix.isUnitaryBetween_coe_unitaryGroup _))]
  have h := hU.isMPUSimple_tfae.out 1 3
  rwa [← sourceFactors_sourceU, sourceFactors_eq_sourceFactorsOf] at h

/-- Simplicity is unitarity of the gate $v$ built from any compact decompositions
(ME.tex, Corollary 1.4(b); arXiv:1703.09188, Theorem `ThmFund1`, lines 563--601, with the
factors of lines 479--502). -/
theorem IsMPUCanonicalFormII.isMPUSimple_iff_sourceV_sourceFactorsOf_isUnitaryBetween
    (hU : IsMPUCanonicalFormII U) (S₁ : SourceCutSVD (sourceCutM₁ U) r[U])
    (S₂ : SourceCutSVD (sourceCutM₂ U) ℓ[U]) :
    IsMPUSimple U ↔
      (SourceFactors.sourceV U (sourceFactorsOf S₁ S₂ hU.ρ hU.ρ_posDef)).IsUnitaryBetween := by
  rw [(sourceU_sourceV_sourceFactorsOf_relatingUnitary (sourceSVD₁ U) S₁ (sourceSVD₂ U) S₂
      hU.ρ hU.ρ_posDef).2,
    Matrix.isUnitaryBetween_mul_iff_of_right
      ((Matrix.isUnitaryBetween_star_coe_unitaryGroup _).kronecker
        _ _ (Matrix.isUnitaryBetween_star_coe_unitaryGroup _))]
  have h := hU.isMPUSimple_tfae.out 1 4
  rwa [← sourceFactors_sourceV, sourceFactors_eq_sourceFactorsOf] at h

/-- For a simple MPU tensor in canonical form II, the gates built from any compact
decompositions carry two-site standard-form data (ME.tex, Corollary 1.4(c); arXiv:1703.09188,
`StandardForm` and Definition `SF`, lines 603--622, with the factors of lines 479--502). -/
theorem IsMPUCanonicalFormII.exists_twoSiteStandardFormData_sourceFactorsOf
    (hU : IsMPUCanonicalFormII U) (hS : IsMPUSimple U) (S₁ : SourceCutSVD (sourceCutM₁ U) r[U])
    (S₂ : SourceCutSVD (sourceCutM₂ U) ℓ[U]) :
    Nonempty (TwoSiteStandardFormData (blockTwo U)
      (SourceFactors.sourceU U (sourceFactorsOf S₁ S₂ hU.ρ hU.ρ_posDef))
      (SourceFactors.sourceV U (sourceFactorsOf S₁ S₂ hU.ρ hU.ρ_posDef))) := by
  obtain ⟨hu, hv⟩ := sourceU_sourceV_sourceFactorsOf_relatingUnitary (sourceSVD₁ U) S₁
    (sourceSVD₂ U) S₂ hU.ρ hU.ρ_posDef
  rw [hu, hv]
  exact ⟨(hU.twoSiteStandardFormData hS).ofGateGauges _ _⟩

/-- **Fundamental theorem, gates, necessity, for every choice of decompositions.** Simple tensors
in canonical form II with equal periodic operators at every length at least two have gates,
built from any compact decompositions of their cuts, related by unitaries $x$ on the left rank
and $y$ on the right rank: $u_V=(x\otimes y)u_U$ and $v_V=v_U(y^\dagger\otimes x^\dagger)$ after
identifying the rank spaces (ME.tex, Corollary 1.4(d); arXiv:1703.09188, Theorem
`FundamentalMPU`, lines 624--648, with the factors of lines 479--502). -/
theorem IsMPUCanonicalFormII.exists_source_gate_unitary_gauges_of_mpo_eq_sourceFactorsOf
    {U V : MPOTensor d D} (hU : IsMPUCanonicalFormII U) (hSU : IsMPUSimple U)
    (hV : IsMPUCanonicalFormII V) (hSV : IsMPUSimple V)
    (hEq : ∀ N : ℕ, 1 < N → mpo U N = mpo V N)
    (S₁ : SourceCutSVD (sourceCutM₁ U) r[U]) (S₂ : SourceCutSVD (sourceCutM₂ U) ℓ[U])
    (T₁ : SourceCutSVD (sourceCutM₁ V) r[V]) (T₂ : SourceCutSVD (sourceCutM₂ V) ℓ[V]) :
    ∃ (er : Fin r[U] ≃ Fin r[V]) (el : Fin ℓ[U] ≃ Fin ℓ[V])
      (x : Matrix.unitaryGroup (Fin ℓ[V]) ℂ) (y : Matrix.unitaryGroup (Fin r[V]) ℂ),
      SourceFactors.sourceU V (sourceFactorsOf T₁ T₂ hV.ρ hV.ρ_posDef) =
        ((x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) ⊗ₖ (y : Matrix (Fin r[V]) (Fin r[V]) ℂ)) *
          Matrix.reindex (Equiv.prodCongr el er) (Equiv.refl _)
            (SourceFactors.sourceU U (sourceFactorsOf S₁ S₂ hU.ρ hU.ρ_posDef)) ∧
      SourceFactors.sourceV V (sourceFactorsOf T₁ T₂ hV.ρ hV.ρ_posDef) =
        Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er el)
            (SourceFactors.sourceV U (sourceFactorsOf S₁ S₂ hU.ρ hU.ρ_posDef)) *
          (star (y : Matrix (Fin r[V]) (Fin r[V]) ℂ) ⊗ₖ
            star (x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ)) := by
  obtain ⟨er, el, x, y, hu, hv⟩ := hU.exists_source_gate_unitary_gauges_of_mpo_eq hSU hV hSV hEq
  obtain ⟨huU, hvU⟩ := sourceU_sourceV_sourceFactorsOf_relatingUnitary (sourceSVD₁ U) S₁
    (sourceSVD₂ U) S₂ hU.ρ hU.ρ_posDef
  obtain ⟨huV, hvV⟩ := sourceU_sourceV_sourceFactorsOf_relatingUnitary (sourceSVD₁ V) T₁
    (sourceSVD₂ V) T₂ hV.ρ hV.ρ_posDef
  set a₁ := (sourceSVD₁ U).relatingUnitary S₁
  set a₂ := (sourceSVD₂ U).relatingUnitary S₂
  set b₁ := (sourceSVD₁ V).relatingUnitary T₁
  set b₂ := (sourceSVD₂ V).relatingUnitary T₂
  set uU := SourceFactors.sourceU U (sourceFactorsOf (sourceSVD₁ U) (sourceSVD₂ U) hU.ρ
    hU.ρ_posDef)
  set vU := SourceFactors.sourceV U (sourceFactorsOf (sourceSVD₁ U) (sourceSVD₂ U) hU.ρ
    hU.ρ_posDef)
  have hu' : SourceFactors.sourceU V (sourceFactorsOf (sourceSVD₁ V) (sourceSVD₂ V) hV.ρ
      hV.ρ_posDef) =
        ((x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) ⊗ₖ (y : Matrix (Fin r[V]) (Fin r[V]) ℂ)) *
          Matrix.reindex (Equiv.prodCongr el er) (Equiv.refl _) uU := hu
  have hv' : SourceFactors.sourceV V (sourceFactorsOf (sourceSVD₁ V) (sourceSVD₂ V) hV.ρ
      hV.ρ_posDef) = Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er el) vU *
        (star (y : Matrix (Fin r[V]) (Fin r[V]) ℂ) ⊗ₖ
          star (x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ)) := hv
  have huU' : uU = (star (a₂ : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ) ⊗ₖ
      star (a₁ : Matrix (Fin r[U]) (Fin r[U]) ℂ)) *
        SourceFactors.sourceU U (sourceFactorsOf S₁ S₂ hU.ρ hU.ρ_posDef) := by
    rw [huU, ← Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, Unitary.coe_star_mul_self,
      Unitary.coe_star_mul_self, Matrix.one_kronecker_one, Matrix.one_mul]
  have hvU' : vU = SourceFactors.sourceV U (sourceFactorsOf S₁ S₂ hU.ρ hU.ρ_posDef) *
      ((a₁ : Matrix (Fin r[U]) (Fin r[U]) ℂ) ⊗ₖ (a₂ : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ)) := by
    rw [hvU, Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, Unitary.coe_star_mul_self,
      Unitary.coe_star_mul_self, Matrix.one_kronecker_one, Matrix.mul_one]
  let z₁ : Matrix.unitaryGroup (Fin r[V]) ℂ :=
    ⟨Matrix.reindex er er (star (a₁ : Matrix (Fin r[U]) (Fin r[U]) ℂ)),
      Matrix.reindex_mem_unitaryGroup er _ (Unitary.star_mem a₁.2)⟩
  let z₂ : Matrix.unitaryGroup (Fin ℓ[V]) ℂ :=
    ⟨Matrix.reindex el el (star (a₂ : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ)),
      Matrix.reindex_mem_unitaryGroup el _ (Unitary.star_mem a₂.2)⟩
  have hstar : ∀ {k k' : ℕ} (e : Fin k ≃ Fin k') (A : Matrix (Fin k) (Fin k) ℂ),
      star (Matrix.reindex e e (star A)) = Matrix.reindex e e A := by
    intro k k' e A
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex,
      ← Matrix.star_eq_conjTranspose, star_star]
  refine ⟨er, el, b₂ * x * z₂, b₁ * y * z₁, ?_, ?_⟩
  · rw [huV, hu', huU', Matrix.reindex_kronecker_mul, Submonoid.coe_mul, Submonoid.coe_mul,
      Submonoid.coe_mul, Submonoid.coe_mul, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]
    simp only [Matrix.mul_assoc]
    rfl
  · rw [hvV, hv', hvU', Matrix.reindex_mul_kronecker, Submonoid.coe_mul, Submonoid.coe_mul,
      Submonoid.coe_mul, Submonoid.coe_mul, star_mul, star_mul, star_mul, star_mul,
      Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]
    have h₁ : star (z₁ : Matrix (Fin r[V]) (Fin r[V]) ℂ) =
        Matrix.reindex er er (a₁ : Matrix (Fin r[U]) (Fin r[U]) ℂ) := hstar er _
    have h₂ : star (z₂ : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) =
        Matrix.reindex el el (a₂ : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ) := hstar el _
    rw [h₁, h₂]
    simp only [Matrix.mul_assoc]

namespace SourceFactors

variable (U : MPOTensor d D)

/-- The traced product of two local letters factors through the gates $v$ and $u$ of any
source factors (chapter Lemma `lem:twosite`; arXiv:1703.09188, `SVDforms2` and `uuvv`,
lines 525--543, with the factors of lines 479--502; ME.tex, Corollary 1.4). -/
theorem trace_mul_eq_sourceV_mul_sourceU_swap {ρ : Matrix (Fin D) (Fin D) ℂ}
    (S : SourceFactors U ρ) (i₁ i₂ j₁ j₂ : Fin d) :
    Matrix.trace (U i₁ j₁ * U i₂ j₂) =
      ∑ lr : Fin ℓ[U] × Fin r[U],
        sourceV U S (i₁, i₂) (lr.2, lr.1) * sourceU U S lr (j₂, j₁) := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  have h₁ (α β : Fin D) :
      U i₁ j₁ α β = ∑ r, S.X₁ (i₁, β) r * S.Y₁ r (α, j₁) := by
    simpa only [Matrix.mul_apply] using (X₁_mul_Y₁_apply U S i₁ β α j₁).symm
  have h₂ (β α : Fin D) :
      U i₂ j₂ β α = ∑ l, S.X₂ (β, i₂) l * S.Y₂ l (j₂, α) := by
    simpa only [Matrix.mul_apply] using (X₂_mul_Y₂_apply U S β i₂ j₂ α).symm
  simp_rw [h₁, h₂]
  simp only [Finset.mul_sum, Finset.sum_mul]
  let f := fun (α β : Fin D) (l : Fin ℓ[U]) (r : Fin r[U]) ↦
    S.X₁ (i₁, β) r * S.Y₁ r (α, j₁) * (S.X₂ (β, i₂) l * S.Y₂ l (j₂, α))
  change (∑ α, ∑ β, ∑ l, ∑ r, f α β l r) = _
  calc
    _ = ∑ α, ∑ l, ∑ β, ∑ r, f α β l r := by
      apply Finset.sum_congr rfl
      intro α _
      exact Finset.sum_comm
    _ = ∑ l, ∑ α, ∑ β, ∑ r, f α β l r := Finset.sum_comm
    _ = ∑ l, ∑ α, ∑ r, ∑ β, f α β l r := by
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro α _
      exact Finset.sum_comm
    _ = ∑ l, ∑ r, ∑ α, ∑ β, f α β l r := by
      apply Finset.sum_congr rfl
      intro l _
      exact Finset.sum_comm
    _ = ∑ lr : Fin ℓ[U] × Fin r[U], ∑ α, ∑ β, f α β lr.1 lr.2 := by
      rw [Fintype.sum_prod_type]
    _ = _ := by
      refine Finset.sum_congr rfl fun lr _ => ?_
      obtain ⟨l, r⟩ := lr
      rw [SourceFactors.sourceV_apply, SourceFactors.sourceU_apply, Finset.sum_mul_sum,
        Finset.sum_comm]
      refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
      simp only [f]
      ring

/-- Entrywise two-site factorization through the gates $v$ and $u$ of any source factors
(chapter Lemma `lem:twosite`; arXiv:1703.09188, `SVDforms2` and `uuvv`, lines 525--543). -/
theorem mpo_two_pair_entry_eq_sourceV_mul_sourceU_swap {ρ : Matrix (Fin D) (Fin D) ℂ}
    (S : SourceFactors U ρ) (i₁ i₂ j₁ j₂ : Fin d) :
    mpo U 2 ![i₁, i₂] ![j₁, j₂] =
      ∑ lr : Fin ℓ[U] × Fin r[U],
        sourceV U S (i₁, i₂) (lr.2, lr.1) * sourceU U S lr (j₂, j₁) := by
  rw [mpo_apply, mpoMatrixEntry, evalWord_ofFn]
  simpa only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    Matrix.mul_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one] using
    trace_mul_eq_sourceV_mul_sourceU_swap U S i₁ i₂ j₁ j₂

/-- The two-site periodic operator factors through the gates $v$ and $u$ of any source factors,
$\operatorname{reindex}(U^{(2)})=v\,\operatorname{swap}(u)$ (chapter Lemma `lem:twosite`;
arXiv:1703.09188, `SVDforms2` and `uuvv`, lines 525--543; ME.tex, Corollary 1.4). -/
theorem mpo_two_reindex_eq_sourceV_mul_sourceU_swap {ρ : Matrix (Fin D) (Fin D) ℂ}
    (S : SourceFactors U ρ) :
    Matrix.reindex (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d)) (mpo U 2) =
      sourceV U S *
        Matrix.reindex (Equiv.prodComm (Fin ℓ[U]) (Fin r[U]))
          (Equiv.prodComm (Fin d) (Fin d)) (sourceU U S) := by
  classical
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply,
    Equiv.prodComm_symm, Equiv.prodComm_apply, finTwoArrowEquiv_symm_apply]
  rw [mpo_two_pair_entry_eq_sourceV_mul_sourceU_swap U S i₁ i₂ j₁ j₂]
  exact Fintype.sum_equiv (Equiv.prodComm (Fin ℓ[U]) (Fin r[U])) _ _ fun lr => rfl

end SourceFactors

/-- Source factors of a tensor and of its unitary virtual conjugate differ, after transport, by
unitary changes of the two rank coordinates, for any source factors whose gates $u$ are unitary
(chapter Lemma 6.4; arXiv:1703.09188, Theorem `FundamentalMPU`, lines 624--648, with the factors
of lines 479--502; ME.tex, Corollary 1.4). -/
theorem exists_source_factor_unitary_gauges_of_virtualSandwich
    (U : MPOTensor d D) (z : Matrix.unitaryGroup (Fin D) ℂ)
    {ρ ρ' : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (T : SourceFactors (virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U
      (star (z : Matrix (Fin D) (Fin D) ℂ))) ρ')
    (huS : (SourceFactors.sourceU U S).IsUnitaryBetween)
    (huT : (SourceFactors.sourceU _ T).IsUnitaryBetween) :
    let V := virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U
      (star (z : Matrix (Fin D) (Fin D) ℂ))
    let er : Fin r[U] ≃ Fin r[V] :=
      (finCongr (source_rank_virtual_unitary_sandwich U z).1).symm
    let el : Fin ℓ[U] ≃ Fin ℓ[V] :=
      (finCongr (source_rank_virtual_unitary_sandwich U z).2).symm
    let X₁ := Matrix.reindex (Equiv.refl _) er
      (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
        (star (z : Matrix (Fin D) (Fin D) ℂ)).transpose) * S.X₁)
    let Y₁ := Matrix.reindex er (Equiv.refl _)
      (S.Y₁ * ((z : Matrix (Fin D) (Fin D) ℂ).transpose ⊗ₖ
        (1 : Matrix (Fin d) (Fin d) ℂ)))
    let X₂ := Matrix.reindex (Equiv.refl _) el
      (((z : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ
        (1 : Matrix (Fin d) (Fin d) ℂ)) * S.X₂)
    let Y₂ := Matrix.reindex el (Equiv.refl _)
      (S.Y₂ * ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
        star (z : Matrix (Fin D) (Fin D) ℂ)))
    ∃ (W₁ : Matrix.unitaryGroup (Fin r[V]) ℂ)
      (W₂ : Matrix.unitaryGroup (Fin ℓ[V]) ℂ),
      T.X₁ = X₁ * (W₁ : Matrix (Fin r[V]) (Fin r[V]) ℂ) ∧
      T.Y₁ = star (W₁ : Matrix (Fin r[V]) (Fin r[V]) ℂ) * Y₁ ∧
      T.X₂ = X₂ * (W₂ : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) ∧
      T.Y₂ = star (W₂ : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) * Y₂ := by
  let V := virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U
      (star (z : Matrix (Fin D) (Fin D) ℂ))
  let er : Fin r[U] ≃ Fin r[V] :=
    (finCongr (source_rank_virtual_unitary_sandwich U z).1).symm
  let el : Fin ℓ[U] ≃ Fin ℓ[V] :=
    (finCongr (source_rank_virtual_unitary_sandwich U z).2).symm
  let R₁ := ((z : Matrix (Fin D) (Fin D) ℂ).transpose ⊗ₖ
      (1 : Matrix (Fin d) (Fin d) ℂ))
  let R₂ := ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
      star (z : Matrix (Fin D) (Fin D) ℂ))
  let X₁ := Matrix.reindex (Equiv.refl _) er
      (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
        (star (z : Matrix (Fin D) (Fin D) ℂ)).transpose) * S.X₁)
  let Y₁ := Matrix.reindex er (Equiv.refl _) (S.Y₁ * R₁)
  let Z₁ := Matrix.reindex (Equiv.refl _) er (R₁ᴴ * S.Z₁)
  let X₂ := Matrix.reindex (Equiv.refl _) el
      (((z : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ
        (1 : Matrix (Fin d) (Fin d) ℂ)) * S.X₂)
  let Y₂ := Matrix.reindex el (Equiv.refl _) (S.Y₂ * R₂)
  let Z₂ := Matrix.reindex (Equiv.refl _) el (R₂ᴴ * S.Z₂)
  have hp := transported_source_factor_premises_at_selected_ranks U z S huS
  have hleft₁ : (T.X₁ᴴ * sourceWeight (d := d) ρ') * T.X₁ = 1 :=
    T.X₁_weighted_isometry
  have hleft₂ : T.X₂ᴴ * T.X₂ = 1 := T.X₂_isometry
  exact exists_unitary_source_gauges_of_isometric_second_factors
    (U := V) (X₁ := X₁) (Xt₁ := T.X₁) (Y₁ := Y₁) (Yt₁ := T.Y₁)
    (X₂ := X₂) (Xt₂ := T.X₂) (Y₂ := Y₂) (Yt₂ := T.Y₂)
    (Lt₁ := T.X₁ᴴ * sourceWeight (d := d) ρ') (R₁ := Z₁)
    (Lt₂ := T.X₂ᴴ) (R₂ := Z₂)
    hp.1.symm T.sourceCutM₁_eq.symm hp.2.1.symm T.sourceCutM₂_eq.symm
    hleft₁ hp.2.2.1 hleft₂ hp.2.2.2.1 hp.2.2.2.2.2 huT
    hp.2.2.2.2.1 T.X₂_isometry

/-- The factors of two simple tensors in canonical form II related by a bond unitary, built from
any compact decompositions of their cuts, differ by unitaries on the two rank coordinates
(chapter Lemma 6.4 for every choice; arXiv:1703.09188, Theorem `FundamentalMPU`, lines
624--648, with the factors of lines 479--502; ME.tex, Corollary 1.4). -/
theorem IsMPUCanonicalFormII.exists_selected_source_factor_unitary_gauges_sourceFactorsOf
    {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U) (hSimpleU : IsMPUSimple U)
    (z : Matrix.unitaryGroup (Fin D) ℂ)
    (hV : IsMPUCanonicalFormII
      (virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U
        (star (z : Matrix (Fin D) (Fin D) ℂ))))
    (hSimpleV : IsMPUSimple
      (virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U
        (star (z : Matrix (Fin D) (Fin D) ℂ))))
    (S₁ : SourceCutSVD (sourceCutM₁ U) r[U]) (S₂ : SourceCutSVD (sourceCutM₂ U) ℓ[U])
    (T₁ : SourceCutSVD (sourceCutM₁ (virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U
      (star (z : Matrix (Fin D) (Fin D) ℂ))))
      r[virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U (star (z : Matrix (Fin D) (Fin D) ℂ))])
    (T₂ : SourceCutSVD (sourceCutM₂ (virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U
      (star (z : Matrix (Fin D) (Fin D) ℂ))))
      ℓ[virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U (star (z : Matrix (Fin D) (Fin D) ℂ))]) :
    let V := virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U
      (star (z : Matrix (Fin D) (Fin D) ℂ))
    let er : Fin r[U] ≃ Fin r[V] :=
      (finCongr (source_rank_virtual_unitary_sandwich U z).1).symm
    let el : Fin ℓ[U] ≃ Fin ℓ[V] :=
      (finCongr (source_rank_virtual_unitary_sandwich U z).2).symm
    let S := sourceFactorsOf S₁ S₂ hU.ρ hU.ρ_posDef
    let T := sourceFactorsOf T₁ T₂ hV.ρ hV.ρ_posDef
    let X₁ := Matrix.reindex (Equiv.refl _) er
      (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
        (star (z : Matrix (Fin D) (Fin D) ℂ)).transpose) * S.X₁)
    let Y₁ := Matrix.reindex er (Equiv.refl _)
      (S.Y₁ * ((z : Matrix (Fin D) (Fin D) ℂ).transpose ⊗ₖ
        (1 : Matrix (Fin d) (Fin d) ℂ)))
    let X₂ := Matrix.reindex (Equiv.refl _) el
      (((z : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ
        (1 : Matrix (Fin d) (Fin d) ℂ)) * S.X₂)
    let Y₂ := Matrix.reindex el (Equiv.refl _)
      (S.Y₂ * ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
        star (z : Matrix (Fin D) (Fin D) ℂ)))
    ∃ (W₁ : Matrix.unitaryGroup (Fin r[V]) ℂ)
      (W₂ : Matrix.unitaryGroup (Fin ℓ[V]) ℂ),
      T.X₁ = X₁ * (W₁ : Matrix (Fin r[V]) (Fin r[V]) ℂ) ∧
      T.Y₁ = star (W₁ : Matrix (Fin r[V]) (Fin r[V]) ℂ) * Y₁ ∧
      T.X₂ = X₂ * (W₂ : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) ∧
      T.Y₂ = star (W₂ : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) * Y₂ :=
  exists_source_factor_unitary_gauges_of_virtualSandwich U z _ _
    ((hU.isMPUSimple_iff_sourceU_sourceFactorsOf_isUnitaryBetween S₁ S₂).mp hSimpleU)
    ((hV.isMPUSimple_iff_sourceU_sourceFactorsOf_isUnitaryBetween T₁ T₂).mp hSimpleV)

/-- **Fundamental theorem, gates, sufficiency, for every choice of decompositions.** If, after
bijections `el`, `er` of the internal legs, the gates of `V` built from any decompositions are
those of `U` built from any decompositions dressed by unitaries, then the two-site blocks of `U`
and `V` generate the same periodic operators at every positive length (arXiv:1703.09188,
Theorem `FundamentalMPU`, lines 624--648, with the factors of lines 479--502; ME.tex,
Corollary 1.4). -/
theorem IsMPUCanonicalFormII.mpo_blockTwo_eq_of_source_gate_gauges_sourceFactorsOf
    {U V : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) (hSU : IsMPUSimple U)
    (hV : IsMPUCanonicalFormII V) (hSV : IsMPUSimple V)
    (S₁ : SourceCutSVD (sourceCutM₁ U) r[U]) (S₂ : SourceCutSVD (sourceCutM₂ U) ℓ[U])
    (T₁ : SourceCutSVD (sourceCutM₁ V) r[V]) (T₂ : SourceCutSVD (sourceCutM₂ V) ℓ[V])
    (er : Fin r[U] ≃ Fin r[V]) (el : Fin ℓ[U] ≃ Fin ℓ[V])
    (x : Matrix.unitaryGroup (Fin ℓ[V]) ℂ) (y : Matrix.unitaryGroup (Fin r[V]) ℂ)
    (hu : SourceFactors.sourceU V (sourceFactorsOf T₁ T₂ hV.ρ hV.ρ_posDef) =
      ((x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) ⊗ₖ (y : Matrix (Fin r[V]) (Fin r[V]) ℂ)) *
        Matrix.reindex (Equiv.prodCongr el er) (Equiv.refl _)
          (SourceFactors.sourceU U (sourceFactorsOf S₁ S₂ hU.ρ hU.ρ_posDef)))
    (hv : SourceFactors.sourceV V (sourceFactorsOf T₁ T₂ hV.ρ hV.ρ_posDef) =
      Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er el)
          (SourceFactors.sourceV U (sourceFactorsOf S₁ S₂ hU.ρ hU.ρ_posDef)) *
        (star (y : Matrix (Fin r[V]) (Fin r[V]) ℂ) ⊗ₖ star (x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ)))
    (N : ℕ) [NeZero N] :
    mpo (blockTwo U) N = mpo (blockTwo V) N := by
  obtain ⟨S⟩ := hU.exists_twoSiteStandardFormData_sourceFactorsOf hSU S₁ S₂
  obtain ⟨T⟩ := hV.exists_twoSiteStandardFormData_sourceFactorsOf hSV T₁ T₂
  rw [hu, hv] at T
  exact (S.reindexRanks el er).mpo_eq_of_gate_gauges x y T

/-- **Fundamental theorem, part (c), for every choice of decompositions.** Under the hypotheses
of `IsMPUCanonicalFormII.mpo_blockTwo_eq_of_source_gate_gauges_sourceFactorsOf`, the tensors
`U` and `V` generate the same periodic operators on every ring of positive even length
(arXiv:1703.09188, Theorem `FundamentalMPU`, lines 624--648; ME.tex, Corollary 1.4). -/
theorem IsMPUCanonicalFormII.mpo_two_mul_eq_of_source_gate_gauges_sourceFactorsOf
    {U V : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) (hSU : IsMPUSimple U)
    (hV : IsMPUCanonicalFormII V) (hSV : IsMPUSimple V)
    (S₁ : SourceCutSVD (sourceCutM₁ U) r[U]) (S₂ : SourceCutSVD (sourceCutM₂ U) ℓ[U])
    (T₁ : SourceCutSVD (sourceCutM₁ V) r[V]) (T₂ : SourceCutSVD (sourceCutM₂ V) ℓ[V])
    (er : Fin r[U] ≃ Fin r[V]) (el : Fin ℓ[U] ≃ Fin ℓ[V])
    (x : Matrix.unitaryGroup (Fin ℓ[V]) ℂ) (y : Matrix.unitaryGroup (Fin r[V]) ℂ)
    (hu : SourceFactors.sourceU V (sourceFactorsOf T₁ T₂ hV.ρ hV.ρ_posDef) =
      ((x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) ⊗ₖ (y : Matrix (Fin r[V]) (Fin r[V]) ℂ)) *
        Matrix.reindex (Equiv.prodCongr el er) (Equiv.refl _)
          (SourceFactors.sourceU U (sourceFactorsOf S₁ S₂ hU.ρ hU.ρ_posDef)))
    (hv : SourceFactors.sourceV V (sourceFactorsOf T₁ T₂ hV.ρ hV.ρ_posDef) =
      Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er el)
          (SourceFactors.sourceV U (sourceFactorsOf S₁ S₂ hU.ρ hU.ρ_posDef)) *
        (star (y : Matrix (Fin r[V]) (Fin r[V]) ℂ) ⊗ₖ star (x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ)))
    (N : ℕ) [NeZero N] :
    mpo U (2 * N) = mpo V (2 * N) := by
  have h := hU.mpo_blockTwo_eq_of_source_gate_gauges_sourceFactorsOf hSU hV hSV S₁ S₂ T₁ T₂
    er el x y hu hv N
  rw [mpo_blockTwo_eq_reindex_blockTensor, mpo_blockTwo_eq_reindex_blockTensor,
    mpo_blockTensor_eq_reindex, mpo_blockTensor_eq_reindex] at h
  rw [Nat.mul_comm]
  exact (Matrix.reindex _ _).injective ((Matrix.reindex _ _).injective h)

end MPOTensor
