/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.IntervalJointSuffixFactorization
import QICLean.Algebra.MatrixIsometryKronecker

/-!
# Joining contractions with arbitrary spectator states

Inserting a spectator identity and moving its index before the joining pair
commutes with the normalized joining contraction. Consequently the parent
isometry is preserved, including for states entangled with the spectator.
The weighted child tensor is exactly this inserted spectator form after the
prescribed output regrouping.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

open Matrix MPSTensor MPSPreparation
open scoped Matrix Kronecker ComplexOrder MatrixOrder

namespace MPUCircuit

/-- Columns with an unchanged spectator inserted before the joining pair.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def joiningSpectatorColumns {r : ℕ} {ρ μ τ : Type*}
    [DecidableEq τ] (V : Matrix (ρ × (Fin r × Fin r)) μ ℂ) :
    Matrix ((ρ × τ) × (Fin r × Fin r)) (μ × τ) ℂ :=
  fun p b ↦ V (p.1.1, p.2) b.1 * (1 : Matrix τ τ ℂ) p.1.2 b.2

/-- The inserted spectator is a reindexing of the tensor product with its identity.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem joiningSpectatorColumns_eq_reindex {r : ℕ} {ρ μ τ : Type*}
    [DecidableEq τ] (V : Matrix (ρ × (Fin r × Fin r)) μ ℂ) :
    joiningSpectatorColumns (τ := τ) V =
      Matrix.reindex (outerSpectatorJoiningRegrouping ρ (Fin r × Fin r) τ).symm
        (Equiv.refl (μ × τ)) (V ⊗ₖ (1 : Matrix τ τ ℂ)) := rfl

/-- The joining contraction commutes with insertion of an unchanged spectator.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem normalizedJoiningParent_joiningSpectatorColumns
    {r : ℕ} {ρ μ τ : Type*} [Fintype ρ] [DecidableEq ρ]
    [Fintype τ] [DecidableEq τ]
    (hr : 0 < r) (P : Matrix (Fin r) (Fin r) ℂ)
    (V : Matrix (ρ × (Fin r × Fin r)) μ ℂ) :
    normalizedJoiningParent hr P (joiningSpectatorColumns (τ := τ) V) =
      joiningSpectatorColumns (τ := τ) (normalizedJoiningParent hr P V) := by
  ext p b
  simp only [normalizedJoiningParent, joiningSpectatorColumns, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Matrix.smul_apply, smul_eq_mul]
  by_cases h : p.1.2 = b.2 <;> simp [Prod.ext_iff, h]

/-- A normalized parent isometry remains an isometry with an arbitrary spectator.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem normalizedJoiningParent_joiningSpectatorColumns_isIsometry
    {r : ℕ} {ρ μ τ : Type*} [Fintype ρ] [DecidableEq ρ]
    [DecidableEq μ] [Fintype τ] [DecidableEq τ]
    (hr : 0 < r) (P : Matrix (Fin r) (Fin r) ℂ)
    (V : Matrix (ρ × (Fin r × Fin r)) μ ℂ)
    (hV : (normalizedJoiningParent hr P V).IsIsometry) :
    (normalizedJoiningParent hr P (joiningSpectatorColumns (τ := τ) V)).IsIsometry := by
  rw [normalizedJoiningParent_joiningSpectatorColumns, joiningSpectatorColumns_eq_reindex]
  have hI : (1 : Matrix τ τ ℂ).IsIsometry := by simp [Matrix.IsIsometry]
  have hK := Matrix.IsIsometry.kronecker (normalizedJoiningParent hr P V)
    (1 : Matrix τ τ ℂ) hV hI
  exact hK.reindex _ (outerSpectatorJoiningRegrouping ρ (Fin r × Fin r) τ).symm
    (Equiv.refl (μ × τ))


/-- The regrouped weighted child tensor is exactly the inserted spectator form.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem regroupedWeightedChildren_joiningSpectatorColumns
    {r : ℕ} {o i o' i' l n τ : Type*}
    [Fintype l] [Fintype n] [DecidableEq τ]
    (A : o → i → Matrix l (Fin r) ℂ) (B : o' → i' → Matrix (Fin r) n ℂ)
    (L : Matrix l l ℂ) (R : Matrix n n ℂ) (P : Matrix (Fin r) (Fin r) ℂ) :
    (((vectorizedWeightedInterval A L (CFC.sqrt (dualGramMetric P))) ⊗ₖ
        (vectorizedWeightedInterval B (CFC.sqrt P) R)) ⊗ₖ (1 : Matrix τ τ ℂ)).submatrix
      ((outerSpectatorJoiningRegrouping ((o × o') × (n × l)) (Fin r × Fin r) τ).trans
        (Equiv.prodCongr intervalChildrenRegrouping.symm (Equiv.refl τ))) id =
      joiningSpectatorColumns (τ := τ) (balancedIntervalChildren A B L R P) := rfl

end MPUCircuit
