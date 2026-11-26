/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.StandardForm.SuppliedTwoBlockStandardForm
import TNLean.MPS.MPU.Symmetry.TimeReversal.TimeReversalSignIntrinsic
import TNLean.MPS.MPU.Symmetry.TimeReversal.SuppliedTimeReversalCriterion

/-!
# The local relation for sequential blocking

The one-block and literal two-block time-reversal equations imply the
four-spin relation used to move the boundary unitary through the blocked
gates. The eight-spin contraction and the cancellation of its two tensor
factors are explicit.

Source: arXiv:1703.09188, equations `eq:defeq-sigma1` and
`eq:unwind-dagger-trick`, lines 1657--1687.

**Scope restriction (square supplied gates):** The supplied-form applications
start with both intermediate spaces equal to the original spin space.
Reduction from a general rectangular standard form is separate; see
`docs/paper-gaps/mpu_printed_blocking_square_scope.tex`.
-/

open scoped Matrix Kronecker BigOperators
open Matrix

namespace MPOTensor

private theorem adjoint_factor_of_kronecker
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (hA : A.IsIsometry)
    (X : Matrix.unitaryGroup ι ℂ) (c : ℂ)
    (h : A ⊗ₖ B = c • ((X : Matrix ι ι ℂ) ⊗ₖ (X : Matrix ι ι ℂ)ᴴ)) :
    B = c • Aᴴ := by
  have hAB : A * B = c • 1 := by
    ext i j
    have hentry (k : ι) := congrArg (fun M ↦ M (i, k) (k, j)) h
    have hsum := congrArg (fun f : ι → ℂ ↦ ∑ k, f k) (funext hentry)
    have hXX : (X : Matrix ι ι ℂ) * (X : Matrix ι ι ℂ)ᴴ = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using
        Matrix.mem_unitaryGroup_iff.mp X.property
    simpa only [kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum,
      ← Matrix.mul_apply, hXX] using hsum
  calc
    B = Aᴴ * (A * B) := by rw [← Matrix.mul_assoc, hA, Matrix.one_mul]
    _ = c • Aᴴ := by rw [hAB, Matrix.mul_smul, Matrix.mul_one]

variable {d : ℕ}

private theorem middle_sandwich
    {α : Type*} [Fintype α] [DecidableEq α]
    (M N : Matrix (α × α) (α × α) ℂ) (a b c e : Matrix α α ℂ) :
    staircaseMiddle (A := α) (E := α) M * ((a ⊗ₖ b) ⊗ₖ (c ⊗ₖ e)) *
        staircaseMiddle N =
      ((a ⊗ₖ (1 : Matrix α α ℂ)) ⊗ₖ ((1 : Matrix α α ℂ) ⊗ₖ e)) *
        staircaseMiddle (M * (b ⊗ₖ c) * N) := by
  ext ⟨⟨i, j⟩, k, l⟩ ⟨⟨i', j'⟩, k', l'⟩
  simp only [staircaseMiddle, Matrix.mul_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    mul_comm, mul_ite, mul_one, mul_zero, ite_self, mul_left_comm, mul_assoc,
    Fintype.sum_prod_type, Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, Finset.sum_const_zero, Finset.mul_sum, Finset.sum_ite_eq']
  rw [Fintype.sum_last_two_first_four]
  refine Finset.sum_congr₂ fun p _ q _ ↦ Finset.sum_congr₂ fun s _ t _ ↦ ?_
  ring

private theorem nested_middle_commute
    (v w z : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    staircaseMiddle (A := Fin d × Fin d) (E := Fin d × Fin d)
        (staircaseMiddle (A := Fin d) (E := Fin d) v) *
      (staircaseMiddle (A := Fin d) (E := Fin d) w ⊗ₖ
        staircaseMiddle (A := Fin d) (E := Fin d) z) =
    (staircaseMiddle (A := Fin d) (E := Fin d) w ⊗ₖ
        staircaseMiddle (A := Fin d) (E := Fin d) z) *
      staircaseMiddle (A := Fin d × Fin d) (E := Fin d × Fin d)
        (staircaseMiddle (A := Fin d) (E := Fin d) v) := by
  ext ⟨⟨⟨a, b⟩, c, e⟩, ⟨f, g⟩, h, i⟩
    ⟨⟨⟨a', b'⟩, c', e'⟩, ⟨f', g'⟩, h', i'⟩
  simp [staircaseMiddle, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, ite_mul,
    Finset.sum_ite_irrel, mul_comm, mul_left_comm, mul_assoc]

/-- In the literal two-block equation, the middle one-block relation splits
the eight-spin network into the two four-spin factors
`v₂₃ (u₁₂ ⊗ x₃₄)` and `v₆₇ (x₅₆† ⊗ u₇₈)`.
Source: arXiv:1703.09188, lines 1662--1680. -/
theorem blocking_network_eq_kronecker
    (u v x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (σ : ℂ)
    (hlocal : staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u) *
        staircaseMiddle v = σ • (x ⊗ₖ xᴴ)) :
    staircaseMiddle (A := Fin d × Fin d) (E := Fin d × Fin d)
        (staircaseMiddle (A := Fin d) (E := Fin d) v) *
      ((staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u)) ⊗ₖ
        (staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u))) *
      staircaseMiddle (A := Fin d × Fin d) (E := Fin d × Fin d)
        (staircaseMiddle (A := Fin d) (E := Fin d) v) =
      σ • ((staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ x)) ⊗ₖ
        (staircaseMiddle (A := Fin d) (E := Fin d) v * (xᴴ ⊗ₖ u))) := by
  rw [Matrix.mul_kronecker_mul, ← Matrix.mul_assoc, nested_middle_commute]
  simp only [Matrix.mul_assoc]
  have hs := middle_sandwich
    (staircaseMiddle (A := Fin d) (E := Fin d) v)
    (staircaseMiddle (A := Fin d) (E := Fin d) v) u u u u
  rw [Matrix.mul_assoc] at hs
  rw [hs, hlocal]
  have hinner :
      ((u ⊗ₖ (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)) ⊗ₖ
          ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ u)) *
        staircaseMiddle (A := Fin d × Fin d) (E := Fin d × Fin d)
          (σ • (x ⊗ₖ xᴴ)) = σ • ((u ⊗ₖ x) ⊗ₖ (xᴴ ⊗ₖ u)) := by
    ext ⟨⟨⟨a, b⟩, c, e⟩, ⟨f, g⟩, h, i⟩
      ⟨⟨⟨a', b'⟩, c', e'⟩, ⟨f', g'⟩, h', i'⟩
    simp [Matrix.mul_apply, staircaseMiddle, Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type, Matrix.one_apply,
      mul_ite, ite_mul, Finset.sum_ite_irrel, mul_comm, mul_left_comm, mul_assoc]
  rw [hinner, Matrix.mul_smul, ← Matrix.mul_kronecker_mul]

/-- The one-block and literal two-block local equations imply the source
unwinding relation, with phase `σ₁ σ₂`. The two-block certificate is written
in the original eight-spin order; its unitary may be arbitrary.

Source: arXiv:1703.09188, `eq:unwind-dagger-trick`, lines 1662--1687. -/
theorem unwind_dagger_trick_of_local_relations
    (u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hu : u.IsUnitaryBetween) (hv : v.IsUnitaryBetween)
    (x : Matrix.unitaryGroup (Fin d × Fin d) ℂ)
    (X : Matrix.unitaryGroup ((Fin d × Fin d) × (Fin d × Fin d)) ℂ)
    (σ₁ σ₂ : ℂ) (hσ₁ : σ₁ * σ₁ = 1)
    (hlocal : staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u) *
        staircaseMiddle v =
      σ₁ • ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
        (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ))
    (hblocked :
      staircaseMiddle (A := Fin d × Fin d) (E := Fin d × Fin d)
          (staircaseMiddle (A := Fin d) (E := Fin d) v) *
        ((staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u)) ⊗ₖ
          (staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u))) *
        staircaseMiddle (A := Fin d × Fin d) (E := Fin d × Fin d)
          (staircaseMiddle (A := Fin d) (E := Fin d) v) =
        σ₂ • ((X : Matrix _ _ ℂ) ⊗ₖ (X : Matrix _ _ ℂ)ᴴ)) :
    (σ₁ * σ₂) •
        (staircaseMiddle (A := Fin d) (E := Fin d) v *
          (u ⊗ₖ (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)))ᴴ =
      staircaseMiddle (A := Fin d) (E := Fin d) v *
        ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ ⊗ₖ u) := by
  let A := staircaseMiddle (A := Fin d) (E := Fin d) v *
    (u ⊗ₖ (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ))
  let B := staircaseMiddle (A := Fin d) (E := Fin d) v *
    ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ ⊗ₖ u)
  have hnet : σ₁ • (A ⊗ₖ B) =
      σ₂ • ((X : Matrix _ _ ℂ) ⊗ₖ (X : Matrix _ _ ℂ)ᴴ) :=
    (blocking_network_eq_kronecker u v x σ₁ hlocal).symm.trans hblocked
  have hprod : A ⊗ₖ B =
      (σ₁ * σ₂) • ((X : Matrix _ _ ℂ) ⊗ₖ (X : Matrix _ _ ℂ)ᴴ) := by
    simpa only [smul_smul, hσ₁, one_smul] using congrArg (σ₁ • ·) hnet
  have hA : A.IsIsometry :=
    (staircaseMiddle_isIsometry v hv.1).mul _ _
      (hu.1.kronecker _ _ ((Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mpr x.property).1)
  exact (adjoint_factor_of_kronecker A B hA X (σ₁ * σ₂) hprod).symm

/-- The local equations of a supplied square standard form and its actual
printed two-block form imply the four-spin unwinding relation. No unitary
comparison between chosen decompositions is assumed.

Source: arXiv:1703.09188, `eq:defeq-sigma1` and
`eq:unwind-dagger-trick`, lines 1657--1687. -/
theorem TwoSiteStandardFormData.unwind_dagger_trick
    {D : ℕ} {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v)
    (x : Matrix.unitaryGroup (Fin d × Fin d) ℂ)
    (X : Matrix.unitaryGroup (Fin (d * d) × Fin (d * d)) ℂ)
    (σ₁ σ₂ : ℂ) (hσ₁ : σ₁ = 1 ∨ σ₁ = -1)
    (hlocal : staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u) =
      σ₁ • ((x : Matrix _ _ ℂ) ⊗ₖ (x : Matrix _ _ ℂ)ᴴ) *
        (staircaseMiddle v)ᴴ)
    (hblocked :
      staircaseMiddle (A := Fin (d * d)) (E := Fin (d * d)) (twoBlockOutputGate v) *
        (twoBlockInputGate u v ⊗ₖ twoBlockInputGate u v) =
      σ₂ • ((X : Matrix _ _ ℂ) ⊗ₖ (X : Matrix _ _ ℂ)ᴴ) *
        (staircaseMiddle (twoBlockOutputGate v))ᴴ) :
    (σ₁ * σ₂) •
        (staircaseMiddle (A := Fin d) (E := Fin d) v *
          (u ⊗ₖ (x : Matrix _ _ ℂ)))ᴴ =
      staircaseMiddle (A := Fin d) (E := Fin d) v *
        ((x : Matrix _ _ ℂ)ᴴ ⊗ₖ u) := by
  let e : ((Fin d × Fin d) × (Fin d × Fin d)) ≃
      (Fin (d * d) × Fin (d * d)) := finProdFinEquiv.prodCongr finProdFinEquiv
  let f := e.prodCongr e
  let X₀ : Matrix.unitaryGroup ((Fin d × Fin d) × (Fin d × Fin d)) ℂ :=
    ⟨Matrix.reindex e.symm e.symm X,
      Matrix.reindex_mem_unitaryGroup e.symm _ X.property⟩
  have hmiddle : Matrix.reindex f.symm f.symm
      (staircaseMiddle (A := Fin (d * d)) (E := Fin (d * d)) (twoBlockOutputGate v)) =
      staircaseMiddle (A := Fin d × Fin d) (E := Fin d × Fin d)
        (staircaseMiddle (A := Fin d) (E := Fin d) v) := by
    change Matrix.reindex f.symm f.symm
      (staircaseMiddle (A := Fin (d * d)) (E := Fin (d * d))
        (Matrix.reindex e e (staircaseMiddle (A := Fin d) (E := Fin d) v))) = _
    ext a b
    simp [staircaseMiddle, Matrix.reindex_apply, f, e,
      Matrix.kroneckerMap_apply, Matrix.one_apply]
  have hinput : Matrix.reindex f.symm f.symm
      (twoBlockInputGate u v ⊗ₖ twoBlockInputGate u v) =
      ((staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u)) ⊗ₖ
        (staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u))) := by
    have hi (a b : (Fin d × Fin d) × (Fin d × Fin d)) :
        twoBlockInputGate u v (e a) (e b) =
          (staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u)) a b := by
      change (staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u))
        (e.symm (e a)) (e.symm (e b)) = _
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    ext a b
    change twoBlockInputGate u v (e a.1) (e b.1) *
      twoBlockInputGate u v (e a.2) (e b.2) = _
    rw [hi, hi]
    rfl
  have hX : Matrix.reindex f.symm f.symm
      ((X : Matrix _ _ ℂ) ⊗ₖ (X : Matrix _ _ ℂ)ᴴ) =
      ((X₀ : Matrix _ _ ℂ) ⊗ₖ (X₀ : Matrix _ _ ℂ)ᴴ) := by
    ext a b
    rfl
  have hfirst := congrArg (fun M ↦ M * staircaseMiddle (A := Fin d) (E := Fin d) v)
    hlocal
  have hlast := congrArg (fun M ↦ M *
    staircaseMiddle (A := Fin (d * d)) (E := Fin (d * d)) (twoBlockOutputGate v))
      hblocked
  have hv := staircaseMiddle_isIsometry (A := Fin d) (E := Fin d) v S.v_unitary.1
  have hv₂ := staircaseMiddle_isIsometry (A := Fin (d * d)) (E := Fin (d * d))
    (twoBlockOutputGate v) S.blockTwo.v_unitary.1
  simp only [Matrix.mul_assoc, show (staircaseMiddle (A := Fin d) (E := Fin d) v)ᴴ *
    staircaseMiddle v = 1 from hv, Matrix.mul_one] at hfirst
  simp only [Matrix.mul_assoc, show
    (staircaseMiddle (A := Fin (d * d)) (E := Fin (d * d)) (twoBlockOutputGate v))ᴴ *
      staircaseMiddle (twoBlockOutputGate v) = 1 from hv₂, Matrix.mul_one] at hlast
  have hlast₀ := congrArg (Matrix.reindexLinearEquiv ℂ ℂ f.symm f.symm) hlast
  simp only [← Matrix.reindexLinearEquiv_mul ℂ ℂ f.symm f.symm f.symm,
    map_smul, Matrix.coe_reindexLinearEquiv, hmiddle, hinput, hX] at hlast₀
  exact unwind_dagger_trick_of_local_relations u v S.u_unitary S.v_unitary x X₀
    σ₁ σ₂ (by rcases hσ₁ with rfl | rfl <;> norm_num)
    (by simpa only [Matrix.mul_assoc] using hfirst)
    (by simpa only [Matrix.mul_assoc] using hlast₀)

/-- A supplied square standard form in a reduced full-support canonical
ambient tensor has the local unwinding relation with its actual one- and
two-block trace signs. The local time-reversal certificates are derived
from even-chain adjoint symmetry, including for the literal blocked gates.

Source: arXiv:1703.09188, `eq:unwind-dagger-trick`, lines 1657--1687.

**Scope restriction (canonical ambient tensor):** The local-certificate
theorem used here assumes a reduced full-support canonical-form-II
presentation of the supplied tensor. Removing this presentation is the
separate problem in `docs/paper-gaps/mpu_canonical_form_full_support.tex`.
This does not construct the printed gates at arbitrary blocking lengths. -/
theorem TwoSiteStandardFormData.exists_unwind_dagger_trick
    {D : ℕ} {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v) (hW : IsMPUCanonicalFormII W)
    (hTR : ∀ N : ℕ, 1 < N → Even N → mpo W N = (mpo W N)ᴴ) :
    ∃ x : Matrix.unitaryGroup (Fin d × Fin d) ℂ,
      (timeReversalSign u v * timeReversalSign (twoBlockInputGate u v) (twoBlockOutputGate v)) •
          (staircaseMiddle (A := Fin d) (E := Fin d) v *
            (u ⊗ₖ (x : Matrix _ _ ℂ)))ᴴ =
        staircaseMiddle (A := Fin d) (E := Fin d) v *
          ((x : Matrix _ _ ℂ)ᴴ ⊗ₖ u) := by
  have hW₂ : IsMPUCanonicalFormII (MPOTensor.blockTwo W) := by
    rw [blockTwo_eq_blockTensor_reindex]
    exact (hW.blockTensor 2 (by omega)).reindexPhysical (twoSiteBlockEquiv (d * d))
  have hTR₂ : ∀ N : ℕ, 1 < N → Even N →
      mpo (MPOTensor.blockTwo W) N = (mpo (MPOTensor.blockTwo W) N)ᴴ := by
    intro N hN _
    rw [mpo_blockTwo_eq_reindex_blockTensor, mpo_blockTensor_eq_reindex]
    have h := hTR (N * 2) (by omega) ⟨N, by omega⟩
    simp only [Matrix.reindex_apply]
    have hh : (mpo W (N * 2)).IsHermitian := h.symm
    exact ((hh.submatrix _).submatrix _).symm
  obtain ⟨σ₁, x, hσ₁, hx⟩ := S.exists_timeReversal_certificate_of_square_ranks hW hTR
  obtain ⟨σ₂, X, _, hX⟩ := S.blockTwo.exists_timeReversal_certificate_of_square_ranks hW₂ hTR₂
  have hfirst := S.timeReversalSign_eq_of_local_relation x hx
  have hsecond := S.blockTwo.timeReversalSign_eq_of_local_relation X hX
  refine ⟨x, ?_⟩
  rw [hfirst, hsecond]
  exact S.unwind_dagger_trick x X σ₁ σ₂ hσ₁ hx hX

end MPOTensor
