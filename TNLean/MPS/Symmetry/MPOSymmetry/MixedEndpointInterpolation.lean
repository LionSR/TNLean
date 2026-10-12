/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Defs
import TNLean.Algebra.MatrixSingleSpan
import TNLean.MPS.Symmetry.BondInterpolation
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Mixed interpolation between arbitrary injective endpoint tensors

Garre-Rubio–Lootens–Molnár, arXiv:2203.12563, Section 5,
`defAgamma`, lines 1580–1601 and 1687: retain the two endpoint tensors on
the diagonal bond blocks and insert matrix units in the off-diagonal
blocks. Right multiplication by `(1 - γ) I ⊕ γ I` gives a continuous
family, injective for `0 < γ < 1`.

The endpoints below are arbitrary injective tensors on their physical
supports, not matrix-unit or zero-correlation tensors. The physical
support coordinates have dimensions `D₀²` and `D₁²`, as in the source.
No symmetry, chosen action tensors, parent-Hamiltonian gap, or conclusion
about phase equivalence is assumed or asserted here. The mixed MPO
construction and the limiting parent interactions are separate arguments.
-/

open scoped Matrix

namespace MPSTensor
namespace MPOSymmetry

variable {D₀ D₁ : ℕ}

/-- The unweighted mixed tensor in direct-sum bond coordinates: the original
endpoint letters in the diagonal sectors and matrix units in the two mixed
sectors. Source: arXiv:2203.12563, `defAgamma`, lines 1586–1601. -/
def mixedEndpointLetter
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (i j : Fin D₀ ⊕ Fin D₁) :
    Matrix (Fin D₀ ⊕ Fin D₁) (Fin D₀ ⊕ Fin D₁) ℂ :=
  match i, j with
  | .inl a, .inl b => Matrix.fromBlocks (A₀ (finProdFinEquiv (a, b))) 0 0 0
  | .inl a, .inr b => Matrix.single (.inl a) (.inr b) 1
  | .inr a, .inl b => Matrix.single (.inr a) (.inl b) 1
  | .inr a, .inr b => Matrix.fromBlocks 0 0 0 (A₁ (finProdFinEquiv (a, b)))

/-- The unweighted mixed letters span the full enlarged bond algebra when
both endpoint tensors are injective. Source: arXiv:2203.12563,
`defAgamma`, lines 1586–1601 and the injectivity claim at line 1687. -/
theorem span_mixedEndpointLetter_eq_top
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁) :
    Submodule.span ℂ (Set.range fun p : (Fin D₀ ⊕ Fin D₁) × (Fin D₀ ⊕ Fin D₁) =>
      mixedEndpointLetter A₀ A₁ p.1 p.2) = ⊤ := by
  classical
  let S := Submodule.span ℂ (Set.range fun p :
    (Fin D₀ ⊕ Fin D₁) × (Fin D₀ ⊕ Fin D₁) => mixedEndpointLetter A₀ A₁ p.1 p.2)
  have hleft (M : Matrix (Fin D₀) (Fin D₀) ℂ) :
      Matrix.fromBlocks M (0 : Matrix (Fin D₀) (Fin D₁) ℂ) 0 0 ∈ S := by
    have hM : M ∈ Submodule.span ℂ (Set.range A₀) := h₀ ▸ Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem M hM =>
        obtain ⟨p, rfl⟩ := hM
        obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective p
        exact Submodule.subset_span ⟨(.inl a, .inl b), rfl⟩
    | zero => simp
    | add M N _ _ hM hN =>
        simpa only [Matrix.fromBlocks_add, add_zero] using S.add_mem hM hN
    | smul c M _ hM =>
        simpa only [Matrix.fromBlocks_smul, smul_zero] using S.smul_mem c hM
  have hright (M : Matrix (Fin D₁) (Fin D₁) ℂ) :
      Matrix.fromBlocks (0 : Matrix (Fin D₀) (Fin D₀) ℂ) 0 0 M ∈ S := by
    have hM : M ∈ Submodule.span ℂ (Set.range A₁) := h₁ ▸ Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem M hM =>
        obtain ⟨p, rfl⟩ := hM
        obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective p
        exact Submodule.subset_span ⟨(.inr a, .inr b), rfl⟩
    | zero => simp
    | add M N _ _ hM hN =>
        simpa only [Matrix.fromBlocks_add, add_zero] using S.add_mem hM hN
    | smul c M _ hM =>
        simpa only [Matrix.fromBlocks_smul, smul_zero] using S.smul_mem c hM
  apply Submodule.eq_top_of_forall_single_mem
  intro i j
  cases i with
  | inl a =>
      cases j with
      | inl b =>
          convert hleft (Matrix.single a b 1) using 1
          ext i j
          cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.single_apply]
      | inr b => exact Submodule.subset_span ⟨(.inl a, .inr b), rfl⟩
  | inr a =>
      cases j with
      | inl b => exact Submodule.subset_span ⟨(.inr a, .inl b), rfl⟩
      | inr b =>
          convert hright (Matrix.single a b 1) using 1
          ext i j
          cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.single_apply]

/-- The unweighted mixed tensor in the common physical and bond coordinates.
Source: arXiv:2203.12563, `defAgamma`, lines 1586–1601. -/
def mixedEndpointBase
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    MPSTensor ((D₀ + D₁) * (D₀ + D₁)) (D₀ + D₁) := fun p =>
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (mixedEndpointLetter A₀ A₁
      (finSumFinEquiv.symm (finProdFinEquiv.symm p).1)
      (finSumFinEquiv.symm (finProdFinEquiv.symm p).2))

/-- The source interpolation with the prescribed arbitrary endpoint letters.
Source: arXiv:2203.12563, `defAgamma`, lines 1586–1601. -/
def mixedEndpointInterpolation
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (γ : ℝ) : MPSTensor ((D₀ + D₁) * (D₀ + D₁)) (D₀ + D₁) := fun p =>
  mixedEndpointBase A₀ A₁ p * bondInterpolationMatrix D₀ D₁ γ

/-- Multiplication by the block weight rescales each physical sector by the
weight of its right register. Source: arXiv:2203.12563, `defAgamma`. -/
theorem mixedEndpointInterpolation_eq_smul
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (γ : ℝ) (p : Fin ((D₀ + D₁) * (D₀ + D₁))) :
    mixedEndpointInterpolation A₀ A₁ γ p =
      bondInterpolationWeight D₀ D₁ γ (finProdFinEquiv.symm p).2 •
        mixedEndpointBase A₀ A₁ p := by
  ext i j
  simp only [mixedEndpointInterpolation, bondInterpolationMatrix,
    Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
  unfold mixedEndpointBase
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  generalize ha : finSumFinEquiv.symm (finProdFinEquiv.symm p).1 = a
  generalize hb : finSumFinEquiv.symm (finProdFinEquiv.symm p).2 = b
  unfold bondInterpolationWeight
  rw [hb]
  cases a <;> cases b <;>
    cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
    simp [mixedEndpointLetter, Matrix.fromBlocks, Matrix.single_apply, mul_comm]

/-- The actual mixed interpolation is continuous on the entire real line.
No injectivity or symmetry is needed for this algebraic statement.
Source: arXiv:2203.12563, `defAgamma`, lines 1586–1601. -/
theorem continuous_mixedEndpointInterpolation
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    Continuous (mixedEndpointInterpolation A₀ A₁) := by
  apply continuous_pi
  intro p
  exact continuous_const.matrix_mul (continuous_bondInterpolationMatrix D₀ D₁)

/-- Injectivity of the unweighted mixed tensor follows from endpoint
injectivity, without assuming that either endpoint is a fixed-point tensor.
Source: arXiv:2203.12563, `defAgamma`, lines 1586–1601 and 1687. -/
theorem isInjective_mixedEndpointBase
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁) :
    Kraus.IsInjective (mixedEndpointBase A₀ A₁) := by
  let e : Matrix (Fin D₀ ⊕ Fin D₁) (Fin D₀ ⊕ Fin D₁) ℂ ≃ₗ[ℂ]
      Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ :=
    Matrix.reindexLinearEquiv ℂ ℂ finSumFinEquiv finSumFinEquiv
  have hspan := span_mixedEndpointLetter_eq_top A₀ A₁ h₀ h₁
  have hrange : Set.range (mixedEndpointBase A₀ A₁) =
      e '' Set.range (fun p : (Fin D₀ ⊕ Fin D₁) × (Fin D₀ ⊕ Fin D₁) =>
        mixedEndpointLetter A₀ A₁ p.1 p.2) := by
    ext M
    constructor
    · rintro ⟨p, rfl⟩
      refine ⟨_, ⟨(finSumFinEquiv.symm (finProdFinEquiv.symm p).1,
        finSumFinEquiv.symm (finProdFinEquiv.symm p).2), rfl⟩, ?_⟩
      rfl
    · rintro ⟨_, ⟨⟨a, b⟩, rfl⟩, rfl⟩
      refine ⟨finProdFinEquiv (finSumFinEquiv a, finSumFinEquiv b), ?_⟩
      simp [mixedEndpointBase, e]
  rw [Kraus.IsInjective, hrange]
  change Submodule.span ℂ (e.toLinearMap '' Set.range (fun p :
    (Fin D₀ ⊕ Fin D₁) × (Fin D₀ ⊕ Fin D₁) => mixedEndpointLetter A₀ A₁ p.1 p.2)) = ⊤
  rw [← Submodule.map_span]
  exact (Submodule.map_eq_top_iff (e := e)).2 hspan

/-- Every virtual weight is nonzero in the open interpolation interval.
Source: arXiv:2203.12563, Section 5, lines 1687–1690. -/
theorem bondInterpolationWeight_ne_zero_of_mem_Ioo
    {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (j : Fin (D₀ + D₁)) :
    bondInterpolationWeight D₀ D₁ γ j ≠ 0 := by
  unfold bondInterpolationWeight
  split
  · exact_mod_cast (ne_of_gt (sub_pos.mpr hγ.2))
  · exact_mod_cast (ne_of_gt hγ.1)

/-- The inserted block weight is invertible in the open interpolation
interval. Source: arXiv:2203.12563, Section 5, line 1690. -/
theorem isUnit_bondInterpolationMatrix_of_mem_Ioo
    {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    IsUnit (bondInterpolationMatrix D₀ D₁ γ) := by
  rw [bondInterpolationMatrix, Matrix.isUnit_diagonal, Pi.isUnit_iff]
  exact fun j => isUnit_iff_ne_zero.mpr (bondInterpolationWeight_ne_zero_of_mem_Ioo hγ j)

/-- The source mixed-tensor path is injective at every interior parameter.
Both diagonal sectors retain the full endpoint matrix spans, and both
mixed sectors retain all matrix units, since their weights are nonzero.
Source: arXiv:2203.12563, Section 5, line 1687. -/
theorem isInjective_mixedEndpointInterpolation
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    Kraus.IsInjective (mixedEndpointInterpolation A₀ A₁ γ) := by
  have hw := bondInterpolationWeight_ne_zero_of_mem_Ioo (D₀ := D₀) (D₁ := D₁) hγ
  have hle : Submodule.span ℂ (Set.range (mixedEndpointBase A₀ A₁)) ≤
      Submodule.span ℂ (Set.range (mixedEndpointInterpolation A₀ A₁ γ)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    have hm : mixedEndpointInterpolation A₀ A₁ γ p ∈
        Submodule.span ℂ (Set.range (mixedEndpointInterpolation A₀ A₁ γ)) :=
      Submodule.subset_span ⟨p, rfl⟩
    have hs := Submodule.smul_mem _
      (bondInterpolationWeight D₀ D₁ γ (finProdFinEquiv.symm p).2)⁻¹ hm
    simpa [mixedEndpointInterpolation_eq_smul, smul_smul, hw] using hs
  rw [isInjective_mixedEndpointBase A₀ A₁ h₀ h₁] at hle
  exact top_unique hle

end MPOSymmetry
end MPSTensor
