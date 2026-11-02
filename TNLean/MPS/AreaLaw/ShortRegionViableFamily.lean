/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import QICLean.Analysis.ViableSubspaceBootstrap
import QICLean.Analysis.ViableSubspaceCoordinates

/-!
# Configuration matrix units on a short physical region

A fixed family of configuration matrix units enlarges every nonzero viable regional subspace
to the whole regional space. Extending the family by zero gives the same squared cardinality
budget used for long intervals and a positive viability-improvement parameter.

These results support ALVV, arXiv:1602.08828v2,
`def:hard-trunc`, lines 873–886, and Theorem `t:ais`, lines 1010–1024.
-/

section

section

open scoped TensorProduct

open scoped TensorProduct

namespace TNLean.MPS.AreaLaw

/-- The number of configuration matrix units on at most `4 ell` sites is
at most `d^(8 ell)`. This numerical short-middle bound requires `1 ≤ d`;
the fixed-family theorem itself allows every local dimension and length.
Supporting ALVV, arXiv:1602.08828v2, `t:ais`, lines 1010–1024. -/
private theorem card_configuration_matrix_units_le (m d ell : ℕ)
    (hd : 1 ≤ d) (hm : m ≤ 4 * ell) :
    Fintype.card ((Fin m → Fin d) × (Fin m → Fin d)) ≤ d ^ (8 * ell) := by
  calc
    Fintype.card ((Fin m → Fin d) × (Fin m → Fin d)) = d ^ (2 * m) := by
      simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
        ← pow_add, ← two_mul]
    _ ≤ d ^ (8 * ell) := Nat.pow_le_pow_right (by omega) (by omega)
end TNLean.MPS.AreaLaw

open scoped TensorProduct

namespace TNLean.MPS.AreaLaw

/-- The short-middle matrix-unit count fits the supplied joint squared
budget. Supporting ALVV, arXiv:1602.08828v2, `t:ais`, lines 1010–1024. -/
private theorem card_configuration_matrix_units_le_joint_square (m d ell : ℕ)
    (hd : 2 ≤ d) (hell : 1 ≤ ell) (hm : m ≤ 4 * ell) :
    Fintype.card ((Fin m → Fin d) × (Fin m → Fin d)) ≤
      ((d * ell ^ 2) ^ (22 * ell)) ^ 2 := by
  have hell2 : 1 ≤ ell ^ 2 :=
    hell.trans (Nat.le_self_pow (by decide : (2 : ℕ) ≠ 0) ell)
  have hbase : d ≤ d * ell ^ 2 := by
    simpa only [mul_one] using Nat.mul_le_mul_left d hell2
  have hbasepos : 0 < d * ell ^ 2 := (by omega : 0 < d).trans_le hbase
  calc
    Fintype.card ((Fin m → Fin d) × (Fin m → Fin d)) ≤ d ^ (8 * ell) :=
      card_configuration_matrix_units_le m d ell (by omega) hm
    _ ≤ (d * ell ^ 2) ^ (8 * ell) := Nat.pow_le_pow_left hbase _
    _ ≤ (d * ell ^ 2) ^ ((22 * ell) * 2) :=
      Nat.pow_le_pow_right hbasepos (by omega)
    _ = ((d * ell ^ 2) ^ (22 * ell)) ^ 2 := pow_mul _ _ _
end TNLean.MPS.AreaLaw
end

section

open scoped TensorProduct

namespace TNLean.MPS.AreaLaw

/-- A short actual region admits a fixed family of configuration matrix units,
extended by zero to the joint squared budget. Its images of a viable
subspace span the whole regional Hilbert space whenever the error is below
one and the target is nonzero. The family is chosen before these viability
data. Auxiliary to ALVV, arXiv:1602.08828v2, `t:ais`, lines 1010–1024.
The boundary `δ < 1` is documented at
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf.
No coordinate transport or nonzero-subspace premise is supplied. -/
private theorem exists_fixed_short_actual_region_clm_family
    (L q ell : ℕ) (J : Finset (Fin L))
    (hq : 2 ≤ q) (hell : 1 ≤ ell) (hJ : J.card ≤ 4 * ell)
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] :
    let E := EuclideanSpace ℂ (J → Fin q)
    let D : ℕ := (q * ell ^ 2) ^ (22 * ell)
    ∃ A : Fin (D ^ 2) → E →L[ℂ] E,
      ∀ (δ : ℝ) (S : Submodule ℂ E) (T : Submodule ℂ (E ⊗[ℂ] F)),
        Submodule.IsViable δ S T → δ < 1 → T ≠ ⊥ →
          (⨆ j, S.map (A j : E →ₗ[ℂ] E)) = ⊤ ∧
          Submodule.IsViable 0 (⨆ j, S.map (A j : E →ₗ[ℂ] E)) T := by
  classical
  intro E D
  let b : Module.Basis (J → Fin q) ℂ E :=
    (EuclideanSpace.basisFun (J → Fin q) ℂ).toBasis
  let W : ((J → Fin q) × (J → Fin q)) → E →L[ℂ] E := fun r ↦
    ((b.coord r.2).smulRight (b r.1)).toContinuousLinearMap
  have hcard : Fintype.card ((J → Fin q) × (J → Fin q)) ≤ D ^ 2 := by
    have hc := card_configuration_matrix_units_le_joint_square J.card q ell hq hell hJ
    simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_coe] using hc
  obtain ⟨_f, A, _hA, _hzero, hgrow⟩ :=
    Submodule.exists_clm_family_extension_of_card_le hcard W
  refine ⟨A, ?_⟩
  intro δ S T hviable hδ hT
  have hS : S ≠ ⊥ := Submodule.isViable_ne_bot_of_target_ne_bot hviable hδ hT
  have hWtop : (⨆ r, S.map (W r : E →ₗ[ℂ] E)) = ⊤ := by
    rw [iSup_prod]
    exact Submodule.iSup_map_basis_matrixUnits_eq_top b S hS
  have htop : (⨆ j, S.map (A j : E →ₗ[ℂ] E)) = ⊤ := (hgrow S).trans hWtop
  refine ⟨htop, ?_⟩
  rw [htop]
  exact Submodule.isViable_top 0 le_rfl T
end TNLean.MPS.AreaLaw
end

section

open scoped TensorProduct

namespace TNLean.MPS.AreaLaw

/-- The fixed family on a short actual region improves every viable subspace,
with a positive error parameter satisfying the joint squared-count tradeoff.
Both choices precede the target, source subspace and viability error. The
zero target is included. Supporting the short-middle alternative in ALVV,
arXiv:1602.08828v2, `t:ais`, lines 1010–1024, and
`prop:albootstrap-dg`, lines 1065–1074. The boundary `δ < 1` is documented at
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf.
This result uses the same joint count as the long-middle branch; no new
universal scale is selected. -/
theorem exists_short_actual_region_improving_family
    (L q ell : ℕ) (J : Finset (Fin L))
    (hq : 2 ≤ q) (hell : 1 ≤ ell) (hJ : J.card ≤ 4 * ell)
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] :
    let E := EuclideanSpace ℂ (J → Fin q)
    let D : ℕ := (q * ell ^ 2) ^ (22 * ell)
    ∃ (A : Fin (D ^ 2) → E →L[ℂ] E) (Delta : ℝ),
      0 < Delta ∧ (D : ℝ) ^ 12 * Delta ≤ 1 / 100000 ∧
      ∀ (T : Submodule ℂ (E ⊗[ℂ] F)) (S : Submodule ℂ E) (δ : ℝ),
        Submodule.IsViable δ S T → δ < 1 →
          Submodule.IsViable (Delta / (1 - δ) ^ 2)
            (⨆ j, S.map (A j : E →ₗ[ℂ] E)) T := by
  intro E D
  obtain ⟨A, hA⟩ :=
    exists_fixed_short_actual_region_clm_family (F := F) L q ell J hq hell hJ
  have hDpos : 0 < D := by
    dsimp only [D]
    exact pow_pos (Nat.mul_pos (by omega : 0 < q)
      (pow_pos (by omega : 0 < ell) 2)) _
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hDpos
  let Delta : ℝ := 1 / (100000 * (D : ℝ) ^ 12)
  have hDelta : 0 < Delta := by
    dsimp only [Delta]
    exact one_div_pos.mpr (mul_pos (by norm_num) (pow_pos hDR 12))
  have hDeltaEq : Delta = (1 / 100000 : ℝ) / (D : ℝ) ^ 12 := by
    dsimp only [Delta]
    rw [div_div]
  have hbudget : (D : ℝ) ^ 12 * Delta ≤ 1 / 100000 := by
    rw [hDeltaEq]
    exact (mul_div_cancel₀ _ (pow_ne_zero 12 hDR.ne')).le
  refine ⟨A, Delta, hDelta, hbudget, ?_⟩
  intro T S δ hviable hδ
  by_cases hT : T = ⊥
  · subst T
    unfold Submodule.IsViable
    apply Submodule.isCloseTo_iff.mpr
    intro v hv
    have hv0 : v = 0 := by simpa using hv
    subst v
    simp
  · obtain ⟨htop, _hzero⟩ := hA δ S T hviable hδ hT
    rw [htop]
    exact Submodule.isViable_top _
      (div_nonneg hDelta.le (sq_nonneg (1 - δ))) T
end TNLean.MPS.AreaLaw
end
end
