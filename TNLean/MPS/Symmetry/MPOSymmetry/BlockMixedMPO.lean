/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointMPOAction
import TNLean.MPS.MPDO.PhysicalBasisAction

/-!
# The block-injective mixed path and the action of its common MPO

GLM23 extends the interpolation between two MPO-symmetric states to systems
with ground-state degeneracy (`REsubmission.tex`, lines 1695--1775):

> We now deal with the case of systems with ground state degeneracy. We want
> to connect two block-injective MPSs (with the same number of blocks) that
> share the $L$-symbols under the action of two MPO algebras with the same
> fusion category $\mathcal{C}$ and same $F$-symbols. For this we first have
> to establish a correspondence between the blocks of each MPS,
> $x:x_0 \to x_1$, and the degeneracies compatible with the action of
> $\mathcal{C}$ [...]. The embedding MPS tensor has the block-diagonal form
> $A(\gamma)=\bigoplus_x A_x(\gamma)$. For every block $x$ the bond dimension
> is $D^0_x+D^1_x$ [...]

Both endpoints are indexed by the same block labels `Fin s`, which encodes the
block correspondence `x : x₀ → x₁`, and the action multiplicities `M x y` are
shared, which encodes the correspondence of the degeneracies. As in the
injective case (lines 1584--1586), the local Hilbert space of endpoint `p` is
the span of its tensor, `⊕ₓ ℂ^{D^p_x} ⊗ ℂ^{D^p_x}`: the block `A^p_x` is a
square-alphabet tensor placed in the sector `x` of that space by
`sectorTensor`. The block `A_x(γ)` of the path is the mixed interpolation of
`A^0_x` and `A^1_x`, placed in the sector `x` of
`⊕ₓ (ℂ^{D^0_x} ⊕ ℂ^{D^1_x})^{⊗ 2}`.

The common MPO `blockMixedMPO` maps the sector `x` to the sector `y` by the
cross contractions of the endpoint action maps of `x → y`, as in the source's
`T^{0,1}_a = ⊕_{x,y,i} ...` (lines 1708--1724). Its exact block action
(the displayed relation at lines 1729--1771) holds at every real parameter:
`T_a A_x(γ) = ∑_{i,y} (W ⊕ W) A_y(γ) (V ⊕ V)`. No injectivity, fusion, or
equality of L-symbols is needed for the action. Fusion and the ground-space
claims are treated separately.

Source: Garre-Rubio–Lootens–Molnár, arXiv:2203.12563v3, `REsubmission.tex`,
lines 1695--1775, with `defAgamma` and `Agammasym`.
-/

open scoped Matrix BigOperators Kronecker

namespace MPSTensor.MPOSymmetry

section Sector

variable {D₀ D₁ E₀ E₁ F₀ F₁ χ₀ χ₁ m : ℕ}

/-- Analysis from the acted bond of an input block (dimensions `D₀`, `D₁`) to
an output block (dimensions `E₀`, `E₁`), supported on matching sectors.
Source: GLM23, the direct sums in the block relation at lines 1729--1771. -/
def blockMixedAnalysis
    (V₀ : Matrix (Fin E₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ : Matrix (Fin E₁) (Fin (χ₁ * D₁)) ℂ) :
    Matrix (Fin E₀ ⊕ Fin E₁)
      ((Fin χ₀ ⊕ Fin χ₁) × (Fin D₀ ⊕ Fin D₁)) ℂ :=
  fun r (α, k) => match r, α, k with
  | .inl r, .inl α, .inl k => V₀ r (finProdFinEquiv (α, k))
  | .inr r, .inr α, .inr k => V₁ r (finProdFinEquiv (α, k))
  | _, _, _ => 0

/-- Synthesis from an output block to the acted bond of an input block,
supported on matching sectors. Source: GLM23, lines 1729--1771. -/
def blockMixedSynthesis
    (W₀ : Matrix (Fin (χ₀ * D₀)) (Fin E₀) ℂ)
    (W₁ : Matrix (Fin (χ₁ * D₁)) (Fin E₁) ℂ) :
    Matrix ((Fin χ₀ ⊕ Fin χ₁) × (Fin D₀ ⊕ Fin D₁))
      (Fin E₀ ⊕ Fin E₁) ℂ :=
  fun (α, k) r => match α, k, r with
  | .inl α, .inl k, .inl r => W₀ (finProdFinEquiv (α, k)) r
  | .inr α, .inr k, .inr r => W₁ (finProdFinEquiv (α, k)) r
  | _, _, _ => 0

/-- The sector of the common MPO from an input block to an output block, in
direct-sum coordinates. The diagonal sectors keep the endpoint operator
sectors; the cross sectors contract endpoint synthesis with endpoint
analysis over the shared multiplicity index `i`.
Source: GLM23, the definition of `T^{0,1}_a` at lines 1708--1724. -/
noncomputable def blockMixedMPOLetter
    (T₀ : Fin (E₀ * E₀) → Fin (D₀ * D₀) → Matrix (Fin χ₀) (Fin χ₀) ℂ)
    (T₁ : Fin (E₁ * E₁) → Fin (D₁ * D₁) → Matrix (Fin χ₁) (Fin χ₁) ℂ)
    (V₀ : Fin m → Matrix (Fin E₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ : Fin m → Matrix (Fin E₁) (Fin (χ₁ * D₁)) ℂ)
    (W₀ : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin E₀) ℂ)
    (W₁ : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin E₁) ℂ)
    (r s : Fin E₀ ⊕ Fin E₁) (k l : Fin D₀ ⊕ Fin D₁) :
    Matrix (Fin χ₀ ⊕ Fin χ₁) (Fin χ₀ ⊕ Fin χ₁) ℂ :=
  fun α β => match r, s, k, l, α, β with
  | .inl r, .inl s, .inl k, .inl l, .inl α, .inl β =>
      T₀ (finProdFinEquiv (r, s)) (finProdFinEquiv (k, l)) α β
  | .inl r, .inr s, .inl k, .inr l, .inl α, .inr β =>
      ∑ μ, W₀ μ (finProdFinEquiv (α, k)) r * V₁ μ s (finProdFinEquiv (β, l))
  | .inr r, .inl s, .inr k, .inl l, .inr α, .inl β =>
      ∑ μ, W₁ μ (finProdFinEquiv (α, k)) r * V₀ μ s (finProdFinEquiv (β, l))
  | .inr r, .inr s, .inr k, .inr l, .inr α, .inr β =>
      T₁ (finProdFinEquiv (r, s)) (finProdFinEquiv (k, l)) α β
  | _, _, _, _, _, _ => 0

/-- The block analysis-synthesis product is the direct sum of the endpoint
products; the unmatched acted sectors contribute zero. -/
theorem blockMixedAnalysis_mul_synthesis
    (V₀ : Matrix (Fin E₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ : Matrix (Fin E₁) (Fin (χ₁ * D₁)) ℂ)
    (W₀ : Matrix (Fin (χ₀ * D₀)) (Fin F₀) ℂ)
    (W₁ : Matrix (Fin (χ₁ * D₁)) (Fin F₁) ℂ) :
    blockMixedAnalysis V₀ V₁ * blockMixedSynthesis W₀ W₁ =
      Matrix.fromBlocks (V₀ * W₀) 0 0 (V₁ * W₁) := by
  classical
  ext i j
  cases i <;> cases j <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.mul_apply,
      Fintype.sum_prod_type, Fintype.sum_sum_type, blockMixedAnalysis,
      blockMixedSynthesis, Matrix.zero_apply, zero_mul, mul_zero,
      Finset.sum_const_zero, zero_add, add_zero]
  · rename_i i j
    simpa only [Fintype.sum_prod_type] using
      (finProdFinEquiv.sum_comp (fun k => V₀ i k * W₀ k j))
  · rename_i i j
    simpa only [Fintype.sum_prod_type] using
      (finProdFinEquiv.sum_comp (fun k => V₁ i k * W₁ k j))

set_option maxHeartbeats 800000 in
-- The six independent sector indices give 64 finite cases in this coordinate identity.
/-- Entrywise reconstruction of one block sector of the unweighted action.
The input block has dimensions `D₀`, `D₁` and the output block `E₀`, `E₁`.
The hypotheses are the corresponding sectors of the endpoint action
relations. Source: GLM23, the block relation at lines 1729--1771. -/
theorem blockMixedMPOLetter_action
    (T₀ : Fin (E₀ * E₀) → Fin (D₀ * D₀) → Matrix (Fin χ₀) (Fin χ₀) ℂ)
    (T₁ : Fin (E₁ * E₁) → Fin (D₁ * D₁) → Matrix (Fin χ₁) (Fin χ₁) ℂ)
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (B₀ : MPSTensor (E₀ * E₀) E₀) (B₁ : MPSTensor (E₁ * E₁) E₁)
    (V₀ : Fin m → Matrix (Fin E₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ : Fin m → Matrix (Fin E₁) (Fin (χ₁ * D₁)) ℂ)
    (W₀ : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin E₀) ℂ)
    (W₁ : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin E₁) ℂ)
    (h₀ : ∀ (r s : Fin E₀) (i j : Fin D₀) (α β : Fin χ₀),
      (∑ k : Fin D₀, ∑ l : Fin D₀,
        T₀ (finProdFinEquiv (r, s)) (finProdFinEquiv (k, l)) α β *
          A₀ (finProdFinEquiv (k, l)) i j) =
        ∑ μ, (W₀ μ * B₀ (finProdFinEquiv (r, s)) * V₀ μ)
          (finProdFinEquiv (α, i)) (finProdFinEquiv (β, j)))
    (h₁ : ∀ (r s : Fin E₁) (i j : Fin D₁) (α β : Fin χ₁),
      (∑ k : Fin D₁, ∑ l : Fin D₁,
        T₁ (finProdFinEquiv (r, s)) (finProdFinEquiv (k, l)) α β *
          A₁ (finProdFinEquiv (k, l)) i j) =
        ∑ μ, (W₁ μ * B₁ (finProdFinEquiv (r, s)) * V₁ μ)
          (finProdFinEquiv (α, i)) (finProdFinEquiv (β, j)))
    (r s : Fin E₀ ⊕ Fin E₁) (i j : Fin D₀ ⊕ Fin D₁) (α β : Fin χ₀ ⊕ Fin χ₁) :
    (∑ k : Fin D₀ ⊕ Fin D₁, ∑ l : Fin D₀ ⊕ Fin D₁,
      blockMixedMPOLetter T₀ T₁ V₀ V₁ W₀ W₁ r s k l α β *
        mixedEndpointLetter A₀ A₁ k l i j) =
      ∑ μ, (blockMixedSynthesis (W₀ μ) (W₁ μ) *
        mixedEndpointLetter B₀ B₁ r s * blockMixedAnalysis (V₀ μ) (V₁ μ))
          (α, i) (β, j) := by
  classical
  cases r <;> cases s <;> cases i <;> cases j <;> cases α <;> cases β <;>
    simp only [Fintype.sum_sum_type, blockMixedMPOLetter, mixedEndpointLetter,
      blockMixedSynthesis, blockMixedAnalysis, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.mul_apply, Matrix.single_apply, ite_and, mul_ite, ite_mul,
      Finset.sum_mul, Matrix.zero_apply, zero_mul, mul_zero, Finset.sum_const_zero,
      zero_add, add_zero, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr,
      Sum.inr_ne_inl, and_false, false_and, ite_false, ite_true,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel,
      Finset.mem_univ, mul_one]
  · simpa [Matrix.mul_apply, Finset.sum_mul] using h₀ _ _ _ _ _ _
  · simpa [Matrix.mul_apply, Finset.sum_mul] using h₁ _ _ _ _ _ _

/-- The block analysis map in standard finite coordinates. -/
def blockMixedMPOAnalysis
    (V₀ : Matrix (Fin E₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ : Matrix (Fin E₁) (Fin (χ₁ * D₁)) ℂ) :
    Matrix (Fin (E₀ + E₁)) (Fin ((χ₀ + χ₁) * (D₀ + D₁))) ℂ :=
  (blockMixedAnalysis V₀ V₁).submatrix finSumFinEquiv.symm
    (mixedEndpointActedEquiv χ₀ χ₁ D₀ D₁).symm

/-- The block synthesis map in standard finite coordinates. -/
def blockMixedMPOSynthesis
    (W₀ : Matrix (Fin (χ₀ * D₀)) (Fin E₀) ℂ)
    (W₁ : Matrix (Fin (χ₁ * D₁)) (Fin E₁) ℂ) :
    Matrix (Fin ((χ₀ + χ₁) * (D₀ + D₁))) (Fin (E₀ + E₁)) ℂ :=
  (blockMixedSynthesis W₀ W₁).submatrix
    (mixedEndpointActedEquiv χ₀ χ₁ D₀ D₁).symm finSumFinEquiv.symm

/-- Standard-coordinate block maps inherit biorthogonality from the endpoint
maps, also between different output blocks. -/
theorem blockMixedMPOAnalysis_mul_synthesis
    (V₀ : Matrix (Fin E₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ : Matrix (Fin E₁) (Fin (χ₁ * D₁)) ℂ)
    (W₀ : Matrix (Fin (χ₀ * D₀)) (Fin F₀) ℂ)
    (W₁ : Matrix (Fin (χ₁ * D₁)) (Fin F₁) ℂ) :
    blockMixedMPOAnalysis V₀ V₁ * blockMixedMPOSynthesis W₀ W₁ =
      (Matrix.fromBlocks (V₀ * W₀) 0 0 (V₁ * W₁)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
  rw [blockMixedMPOAnalysis, blockMixedMPOSynthesis,
    Matrix.submatrix_mul_equiv, blockMixedAnalysis_mul_synthesis]

/-- The block analysis map intertwines the lifted bond weight of the input
block with the bond weight of the output block, at every real parameter.
Source: GLM23, the weights `W_x(γ)` of lines 1697--1704. -/
theorem blockMixedMPOAnalysis_mul_weight
    (V₀ : Matrix (Fin E₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ : Matrix (Fin E₁) (Fin (χ₁ * D₁)) ℂ) (γ : ℝ) :
    blockMixedMPOAnalysis V₀ V₁ *
        MPOTensor.productBoundary (1 : Matrix (Fin (χ₀ + χ₁)) (Fin (χ₀ + χ₁)) ℂ)
          (bondInterpolationMatrix D₀ D₁ γ) =
      bondInterpolationMatrix E₀ E₁ γ * blockMixedMPOAnalysis V₀ V₁ := by
  classical
  ext i j
  simp only [bondInterpolationMatrix, MPOTensor.productBoundary_one_diagonal,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  obtain ⟨r, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨⟨α, k⟩, rfl⟩ := (mixedEndpointActedEquiv χ₀ χ₁ D₀ D₁).surjective j
  simp only [blockMixedMPOAnalysis, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  simp only [mixedEndpointActedEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.prodCongr_apply]
  cases r <;> cases α <;> cases k <;>
    simp [blockMixedAnalysis, bondInterpolationWeight, mul_comm]

/-- The sector of the common MPO from an input block to an output block, in
the standard physical and bond coordinates. Source: GLM23,
lines 1708--1724. -/
noncomputable def blockMixedMPOSector
    (T₀ : Fin (E₀ * E₀) → Fin (D₀ * D₀) → Matrix (Fin χ₀) (Fin χ₀) ℂ)
    (T₁ : Fin (E₁ * E₁) → Fin (D₁ * D₁) → Matrix (Fin χ₁) (Fin χ₁) ℂ)
    (V₀ : Fin m → Matrix (Fin E₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ : Fin m → Matrix (Fin E₁) (Fin (χ₁ * D₁)) ℂ)
    (W₀ : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin E₀) ℂ)
    (W₁ : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin E₁) ℂ)
    (t : Fin ((E₀ + E₁) * (E₀ + E₁))) (u : Fin ((D₀ + D₁) * (D₀ + D₁))) :
    Matrix (Fin (χ₀ + χ₁)) (Fin (χ₀ + χ₁)) ℂ :=
  (blockMixedMPOLetter T₀ T₁ V₀ V₁ W₀ W₁
    ((mixedEndpointPhysicalEquiv E₀ E₁).symm t).1
    ((mixedEndpointPhysicalEquiv E₀ E₁).symm t).2
    ((mixedEndpointPhysicalEquiv D₀ D₁).symm u).1
    ((mixedEndpointPhysicalEquiv D₀ D₁).symm u).2).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm

/-- Exact reconstruction of one block sector of the unweighted action in
standard coordinates. Source: GLM23, lines 1729--1771, before right
multiplication by the interpolation weight. -/
theorem blockMixedMPOSector_action
    (T₀ : Fin (E₀ * E₀) → Fin (D₀ * D₀) → Matrix (Fin χ₀) (Fin χ₀) ℂ)
    (T₁ : Fin (E₁ * E₁) → Fin (D₁ * D₁) → Matrix (Fin χ₁) (Fin χ₁) ℂ)
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (B₀ : MPSTensor (E₀ * E₀) E₀) (B₁ : MPSTensor (E₁ * E₁) E₁)
    (V₀ : Fin m → Matrix (Fin E₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ : Fin m → Matrix (Fin E₁) (Fin (χ₁ * D₁)) ℂ)
    (W₀ : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin E₀) ℂ)
    (W₁ : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin E₁) ℂ)
    (h₀ : ∀ (r s : Fin E₀) (i j : Fin D₀) (α β : Fin χ₀),
      (∑ k : Fin D₀, ∑ l : Fin D₀,
        T₀ (finProdFinEquiv (r, s)) (finProdFinEquiv (k, l)) α β *
          A₀ (finProdFinEquiv (k, l)) i j) =
        ∑ μ, (W₀ μ * B₀ (finProdFinEquiv (r, s)) * V₀ μ)
          (finProdFinEquiv (α, i)) (finProdFinEquiv (β, j)))
    (h₁ : ∀ (r s : Fin E₁) (i j : Fin D₁) (α β : Fin χ₁),
      (∑ k : Fin D₁, ∑ l : Fin D₁,
        T₁ (finProdFinEquiv (r, s)) (finProdFinEquiv (k, l)) α β *
          A₁ (finProdFinEquiv (k, l)) i j) =
        ∑ μ, (W₁ μ * B₁ (finProdFinEquiv (r, s)) * V₁ μ)
          (finProdFinEquiv (α, i)) (finProdFinEquiv (β, j)))
    (t : Fin ((E₀ + E₁) * (E₀ + E₁))) :
    (∑ u, blockMixedMPOSector T₀ T₁ V₀ V₁ W₀ W₁ t u ⊗ₖ
        mixedEndpointBase A₀ A₁ u).submatrix finProdFinEquiv.symm finProdFinEquiv.symm =
      ∑ μ, blockMixedMPOSynthesis (W₀ μ) (W₁ μ) *
        mixedEndpointBase B₀ B₁ t * blockMixedMPOAnalysis (V₀ μ) (V₁ μ) := by
  classical
  obtain ⟨⟨r, s⟩, rfl⟩ := (mixedEndpointPhysicalEquiv E₀ E₁).surjective t
  ext a b
  obtain ⟨⟨α, i⟩, rfl⟩ := (mixedEndpointActedEquiv χ₀ χ₁ D₀ D₁).surjective a
  obtain ⟨⟨β, j⟩, rfl⟩ := (mixedEndpointActedEquiv χ₀ χ₁ D₀ D₁).surjective b
  simp only [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.kroneckerMap_apply]
  rw [← (mixedEndpointPhysicalEquiv D₀ D₁).sum_comp, Fintype.sum_prod_type]
  simp only [blockMixedMPOSector, Equiv.symm_apply_apply, mixedEndpointBase_physicalEquiv,
    blockMixedMPOSynthesis, blockMixedMPOAnalysis,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_apply,
    mixedEndpointActedEquiv, Equiv.trans_apply, Equiv.prodCongr_apply]
  simpa [Equiv.symm_trans, Equiv.prodCongr_symm] using
    blockMixedMPOLetter_action T₀ T₁ A₀ A₁ B₀ B₁ V₀ V₁ W₀ W₁ h₀ h₁ r s i j α β

end Sector

section SectorTensor

variable {s : ℕ} {n D : Fin s → ℕ}

/-- A family of tensors placed in the physical sectors of a direct sum: the
block `x` is supported on the sector `x`. -/
def sectorLetter (A : ∀ y, MPSTensor (n y) (D y)) (x : Fin s) :
    ((y : Fin s) × Fin (n y)) → Matrix (Fin (D x)) (Fin (D x)) ℂ
  | ⟨y, t⟩ => if h : y = x then h ▸ A y t else 0

/-- The block `x` of a family of tensors placed in the physical sectors of the
direct sum `⊕ᵧ ℂ^{n y}`. This is the source's restriction of the local
Hilbert space to the span of a block-diagonal tensor. Source: GLM23,
lines 317 and 1584--1586. -/
def sectorTensor (A : ∀ y, MPSTensor (n y) (D y)) (x : Fin s) :
    MPSTensor (∑ y, n y) (D x) :=
  fun p => sectorLetter A x (finSigmaFinEquiv.symm p)

@[simp] theorem sectorTensor_self (A : ∀ y, MPSTensor (n y) (D y)) (x : Fin s)
    (t : Fin (n x)) : sectorTensor A x (finSigmaFinEquiv ⟨x, t⟩) = A x t := by
  unfold sectorTensor
  rw [Equiv.symm_apply_apply]
  simp [sectorLetter]

theorem sectorTensor_of_ne (A : ∀ y, MPSTensor (n y) (D y)) {x y : Fin s}
    (hxy : y ≠ x) (t : Fin (n y)) :
    sectorTensor A x (finSigmaFinEquiv ⟨y, t⟩) = 0 := by
  unfold sectorTensor
  rw [Equiv.symm_apply_apply]
  simp [sectorLetter, hxy]

/-- A sum over the physical alphabet against a sector tensor reduces to its
own sector. -/
theorem sum_sectorTensor {N : Type*} [AddCommMonoid N]
    (A : ∀ y, MPSTensor (n y) (D y)) (x : Fin s)
    (G : Fin (∑ y, n y) → Matrix (Fin (D x)) (Fin (D x)) ℂ → N)
    (hG : ∀ j, G j 0 = 0) :
    ∑ j, G j (sectorTensor A x j) = ∑ t, G (finSigmaFinEquiv ⟨x, t⟩) (A x t) := by
  classical
  rw [← finSigmaFinEquiv.sum_comp, Fintype.sum_sigma, Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [sectorTensor_of_ne A hy, hG]
  · simp

/-- A sum over a family of blocks, evaluated at one physical letter, reduces
to the sector of that letter. -/
theorem sum_sigma_sectorTensor {N : Type*} [AddCommMonoid N] {k : Fin s → ℕ}
    (A : ∀ y, MPSTensor (n y) (D y)) (y : Fin s) (t : Fin (n y))
    (G : ∀ q : (z : Fin s) × Fin (k z), Matrix (Fin (D q.1)) (Fin (D q.1)) ℂ → N)
    (hG : ∀ q, G q 0 = 0) :
    ∑ q : (z : Fin s) × Fin (k z), G q (sectorTensor A q.1 (finSigmaFinEquiv ⟨y, t⟩)) =
      ∑ μ : Fin (k y), G ⟨y, μ⟩ (A y t) := by
  classical
  rw [Fintype.sum_sigma, Finset.sum_eq_single y]
  · simp
  · intro z _ hz
    simp [sectorTensor_of_ne A (Ne.symm hz), hG]
  · simp

/-- A sector tensor has the same letter span as its block. -/
theorem span_range_sectorTensor (A : ∀ y, MPSTensor (n y) (D y)) (x : Fin s) :
    Submodule.span ℂ (Set.range (sectorTensor A x)) =
      Submodule.span ℂ (Set.range (A x)) := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    obtain ⟨⟨y, t⟩, rfl⟩ := finSigmaFinEquiv.surjective p
    by_cases hy : y = x
    · subst hy
      rw [sectorTensor_self]
      exact Submodule.subset_span ⟨t, rfl⟩
    · rw [sectorTensor_of_ne A hy]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    rw [← sectorTensor_self A x t]
    exact Submodule.subset_span ⟨_, rfl⟩

/-- A sector tensor is injective exactly when its block is. -/
theorem isInjective_sectorTensor_iff (A : ∀ y, MPSTensor (n y) (D y)) (x : Fin s) :
    Kraus.IsInjective (sectorTensor A x) ↔ Kraus.IsInjective (A x) := by
  rw [Kraus.IsInjective, Kraus.IsInjective, span_range_sectorTensor]

/-- Right multiplication of every block commutes with placement in sectors. -/
theorem sectorTensor_mul_right (A : ∀ y, MPSTensor (n y) (D y))
    (H : ∀ y, Matrix (Fin (D y)) (Fin (D y)) ℂ) (x : Fin s) (p : Fin (∑ y, n y)) :
    sectorTensor (fun y t => A y t * H y) x p = sectorTensor A x p * H x := by
  obtain ⟨⟨y, t⟩, rfl⟩ := finSigmaFinEquiv.surjective p
  by_cases hy : y = x
  · subst hy
    simp
  · simp [sectorTensor_of_ne _ hy]

end SectorTensor

section Block

variable {s χ₀ χ₁ : ℕ} {D₀ D₁ : Fin s → ℕ} {M : Fin s → Fin s → ℕ}

/-- The physical dimension of the block-injective mixed path,
`∑ₓ (D⁰ₓ + D¹ₓ)²`. -/
abbrev blockMixedPhysicalDim (D₀ D₁ : Fin s → ℕ) : ℕ :=
  ∑ x, (D₀ x + D₁ x) * (D₀ x + D₁ x)

/-- The block `A_x(γ) = A_x · W_x(γ)` of the block-injective mixed path, in
the sector `x` of the common physical space.
Source: GLM23, `REsubmission.tex`, lines 1697--1704:
"For every block $x$ the bond dimension is $D^0_x+D^1_x$ and it is defined
by $A_x(\gamma)= A_x \cdot W_x(\gamma)$". -/
noncomputable def blockMixedInterpolation
    (A₀ : ∀ x, MPSTensor (D₀ x * D₀ x) (D₀ x)) (A₁ : ∀ x, MPSTensor (D₁ x * D₁ x) (D₁ x))
    (γ : ℝ) (x : Fin s) :
    MPSTensor (blockMixedPhysicalDim D₀ D₁) (D₀ x + D₁ x) :=
  sectorTensor (fun y => mixedEndpointInterpolation (A₀ y) (A₁ y) γ) x

/-- The block-diagonal embedding tensor `A(γ) = ⊕ₓ A_x(γ)`.
Source: GLM23, `REsubmission.tex`, line 1697: "The embedding MPS tensor has
the block-diagonal form $A(\gamma)=\bigoplus_x A_x(\gamma)$." -/
noncomputable def blockMixedTensor
    (A₀ : ∀ x, MPSTensor (D₀ x * D₀ x) (D₀ x)) (A₁ : ∀ x, MPSTensor (D₁ x * D₁ x) (D₁ x))
    (γ : ℝ) : MPSTensor (blockMixedPhysicalDim D₀ D₁) (∑ x, (D₀ x + D₁ x)) :=
  toTensorFromBlocks (fun _ => 1) (blockMixedInterpolation A₀ A₁ γ)

/-- Each block of the path is continuous in the real parameter.
Source: GLM23, `defAgamma` and lines 1697--1704. -/
theorem continuous_blockMixedInterpolation
    (A₀ : ∀ x, MPSTensor (D₀ x * D₀ x) (D₀ x)) (A₁ : ∀ x, MPSTensor (D₁ x * D₁ x) (D₁ x))
    (x : Fin s) :
    Continuous fun γ => blockMixedInterpolation A₀ A₁ γ x := by
  apply continuous_pi
  intro p
  obtain ⟨⟨y, t⟩, rfl⟩ := finSigmaFinEquiv.surjective p
  by_cases hy : y = x
  · subst hy
    simp only [blockMixedInterpolation, sectorTensor_self]
    exact (continuous_apply t).comp (continuous_mixedEndpointInterpolation (A₀ y) (A₁ y))
  · simp only [blockMixedInterpolation, sectorTensor_of_ne _ hy]
    exact continuous_const

/-- Every block of the path is injective in the open interval when the
corresponding endpoint blocks are injective. Source: GLM23,
`REsubmission.tex`, line 1773: "The injectivity of every block of
$A(\gamma)$ [...] is justified in the same way as in the previous case." -/
theorem isInjective_blockMixedInterpolation
    (A₀ : ∀ x, MPSTensor (D₀ x * D₀ x) (D₀ x)) (A₁ : ∀ x, MPSTensor (D₁ x * D₁ x) (D₁ x))
    (x : Fin s) (h₀ : Kraus.IsInjective (A₀ x)) (h₁ : Kraus.IsInjective (A₁ x))
    {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    Kraus.IsInjective (blockMixedInterpolation A₀ A₁ γ x) :=
  (isInjective_sectorTensor_iff _ x).2
    (isInjective_mixedEndpointInterpolation (A₀ x) (A₁ x) h₀ h₁ hγ)

/-- The physical sector of the endpoint operator `T` from the input block `x`
to the output block `y`. -/
def operatorSector {n : Fin s → ℕ} {χ : ℕ} (T : MPOTensor (∑ y, n y) χ) (y x : Fin s) :
    Fin (n y) → Fin (n x) → Matrix (Fin χ) (Fin χ) ℂ :=
  fun t u => T (finSigmaFinEquiv ⟨y, t⟩) (finSigmaFinEquiv ⟨x, u⟩)

/-- The letter of the common MPO between two physical sectors. -/
noncomputable def blockMixedMPOEntry
    (T₀ : MPOTensor (∑ x, D₀ x * D₀ x) χ₀) (T₁ : MPOTensor (∑ x, D₁ x * D₁ x) χ₁)
    (V₀ : ∀ x y, Fin (M x y) → Matrix (Fin (D₀ y)) (Fin (χ₀ * D₀ x)) ℂ)
    (V₁ : ∀ x y, Fin (M x y) → Matrix (Fin (D₁ y)) (Fin (χ₁ * D₁ x)) ℂ)
    (W₀ : ∀ x y, Fin (M x y) → Matrix (Fin (χ₀ * D₀ x)) (Fin (D₀ y)) ℂ)
    (W₁ : ∀ x y, Fin (M x y) → Matrix (Fin (χ₁ * D₁ x)) (Fin (D₁ y)) ℂ) :
    ((y : Fin s) × Fin ((D₀ y + D₁ y) * (D₀ y + D₁ y))) →
      ((x : Fin s) × Fin ((D₀ x + D₁ x) * (D₀ x + D₁ x))) →
        Matrix (Fin (χ₀ + χ₁)) (Fin (χ₀ + χ₁)) ℂ
  | ⟨y, t⟩, ⟨x, u⟩ =>
      blockMixedMPOSector (operatorSector T₀ y x) (operatorSector T₁ y x)
        (V₀ x y) (V₁ x y) (W₀ x y) (W₁ x y) t u

/-- The common MPO `T_a` of the block-injective mixed path, with bond
dimension `χ⁰_a + χ¹_a`. Its diagonal sectors are the endpoint operators and
its cross sectors are `T^{0,1}_a = ⊕_{x,y,i} V^{y₀ a x₀}_{i₀} W^{y₁ a x₁}_{i₁}`
and its mirror, using the block correspondence and the shared action
multiplicities. Source: GLM23, `REsubmission.tex`, lines 1706--1726: "The MPO
tensor $T_a$ is defined as in the injective case, with bond dimension
$\chi^0_a + \chi^1_a$ for every $a \in \mathcal{C}$, but now we have to
define the action on all blocks". -/
noncomputable def blockMixedMPO
    (T₀ : MPOTensor (∑ x, D₀ x * D₀ x) χ₀) (T₁ : MPOTensor (∑ x, D₁ x * D₁ x) χ₁)
    (V₀ : ∀ x y, Fin (M x y) → Matrix (Fin (D₀ y)) (Fin (χ₀ * D₀ x)) ℂ)
    (V₁ : ∀ x y, Fin (M x y) → Matrix (Fin (D₁ y)) (Fin (χ₁ * D₁ x)) ℂ)
    (W₀ : ∀ x y, Fin (M x y) → Matrix (Fin (χ₀ * D₀ x)) (Fin (D₀ y)) ℂ)
    (W₁ : ∀ x y, Fin (M x y) → Matrix (Fin (χ₁ * D₁ x)) (Fin (D₁ y)) ℂ) :
    MPOTensor (blockMixedPhysicalDim D₀ D₁) (χ₀ + χ₁) :=
  fun p q => blockMixedMPOEntry T₀ T₁ V₀ V₁ W₀ W₁
    (finSigmaFinEquiv.symm p) (finSigmaFinEquiv.symm q)

@[simp] theorem blockMixedMPO_finSigmaFinEquiv
    (T₀ : MPOTensor (∑ x, D₀ x * D₀ x) χ₀) (T₁ : MPOTensor (∑ x, D₁ x * D₁ x) χ₁)
    (V₀ : ∀ x y, Fin (M x y) → Matrix (Fin (D₀ y)) (Fin (χ₀ * D₀ x)) ℂ)
    (V₁ : ∀ x y, Fin (M x y) → Matrix (Fin (D₁ y)) (Fin (χ₁ * D₁ x)) ℂ)
    (W₀ : ∀ x y, Fin (M x y) → Matrix (Fin (χ₀ * D₀ x)) (Fin (D₀ y)) ℂ)
    (W₁ : ∀ x y, Fin (M x y) → Matrix (Fin (χ₁ * D₁ x)) (Fin (D₁ y)) ℂ)
    (y x : Fin s) (t : Fin ((D₀ y + D₁ y) * (D₀ y + D₁ y)))
    (u : Fin ((D₀ x + D₁ x) * (D₀ x + D₁ x))) :
    blockMixedMPO T₀ T₁ V₀ V₁ W₀ W₁ (finSigmaFinEquiv ⟨y, t⟩) (finSigmaFinEquiv ⟨x, u⟩) =
      blockMixedMPOSector (operatorSector T₀ y x) (operatorSector T₁ y x)
        (V₀ x y) (V₁ x y) (W₀ x y) (W₁ x y) t u := by
  unfold blockMixedMPO
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl

/-- The sector form of an endpoint block action decomposition. -/
private theorem endpoint_block_action_entry {D : Fin s → ℕ} {χ : ℕ}
    (T : MPOTensor (∑ x, D x * D x) χ) (A : ∀ x, MPSTensor (D x * D x) (D x))
    (V : ∀ x y, Fin (M x y) → Matrix (Fin (D y)) (Fin (χ * D x)) ℂ)
    (W : ∀ x y, Fin (M x y) → Matrix (Fin (χ * D x)) (Fin (D y)) ℂ) (x : Fin s)
    (h : IsBiorthogonalDecomposition (MPOTensor.actTensor T (sectorTensor A x))
      (fun q : (y : Fin s) × Fin (M x y) => sectorTensor A q.1)
      (fun q => V x q.1 q.2) (fun q => W x q.1 q.2))
    (y : Fin s) (r t : Fin (D y)) (i j : Fin (D x)) (α β : Fin χ) :
    (∑ k : Fin (D x), ∑ l : Fin (D x),
      operatorSector T y x (finProdFinEquiv (r, t)) (finProdFinEquiv (k, l)) α β *
        A x (finProdFinEquiv (k, l)) i j) =
      ∑ μ, (W x y μ * A y (finProdFinEquiv (r, t)) * V x y μ)
        (finProdFinEquiv (α, i)) (finProdFinEquiv (β, j)) := by
  classical
  have hh := congrArg
    (fun Z : Matrix (Fin (χ * D x)) (Fin (χ * D x)) ℂ =>
      Z (finProdFinEquiv (α, i)) (finProdFinEquiv (β, j)))
    (h.letter (finSigmaFinEquiv ⟨y, finProdFinEquiv (r, t)⟩))
  simp only [MPOTensor.actTensor_apply_finProdFinEquiv, Matrix.sum_apply] at hh
  rw [sum_sectorTensor A x (fun q Z => T _ q α β * Z i j) (by simp),
    sum_sigma_sectorTensor A y _ (fun q Z => (W x q.1 q.2 * Z * V x q.1 q.2)
      (finProdFinEquiv (α, i)) (finProdFinEquiv (β, j))) (by simp)] at hh
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type] at hh
  exact hh

variable (A₀ : ∀ x, MPSTensor (D₀ x * D₀ x) (D₀ x))
  (A₁ : ∀ x, MPSTensor (D₁ x * D₁ x) (D₁ x))
  (T₀ : MPOTensor (∑ x, D₀ x * D₀ x) χ₀) (T₁ : MPOTensor (∑ x, D₁ x * D₁ x) χ₁)
  (V₀ : ∀ x y, Fin (M x y) → Matrix (Fin (D₀ y)) (Fin (χ₀ * D₀ x)) ℂ)
  (V₁ : ∀ x y, Fin (M x y) → Matrix (Fin (D₁ y)) (Fin (χ₁ * D₁ x)) ℂ)
  (W₀ : ∀ x y, Fin (M x y) → Matrix (Fin (χ₀ * D₀ x)) (Fin (D₀ y)) ℂ)
  (W₁ : ∀ x y, Fin (M x y) → Matrix (Fin (χ₁ * D₁ x)) (Fin (D₁ y)) ℂ)
  (h₀ : ∀ x, IsBiorthogonalDecomposition (MPOTensor.actTensor T₀ (sectorTensor A₀ x))
    (fun q : (y : Fin s) × Fin (M x y) => sectorTensor A₀ q.1)
    (fun q => V₀ x q.1 q.2) (fun q => W₀ x q.1 q.2))
  (h₁ : ∀ x, IsBiorthogonalDecomposition (MPOTensor.actTensor T₁ (sectorTensor A₁ x))
    (fun q : (y : Fin s) × Fin (M x y) => sectorTensor A₁ q.1)
    (fun q => V₁ x q.1 q.2) (fun q => W₁ x q.1 q.2))

include h₀ h₁ in
/-- The common MPO acts on every block of the block-injective mixed path by
an exact biorthogonal decomposition into the blocks `A_y(γ)`, with the
endpoint action multiplicities and the direct sums of the endpoint action
maps, at every real parameter. Neither injectivity nor fusion nor equality
of L-symbols is used.
Source: GLM23, `REsubmission.tex`, lines 1726--1771: "it corresponds to an
MPO symmetry of $|\psi_{A(\gamma)}\rangle$ since it satisfies
$T_a A_x(\gamma) = \sum_{i,y} (\ldots \oplus \ldots) A_y(\gamma)
(\ldots \oplus \ldots)$". -/
theorem isBiorthogonalDecomposition_blockMixedInterpolation (γ : ℝ) (x : Fin s) :
    IsBiorthogonalDecomposition
      (MPOTensor.actTensor (blockMixedMPO T₀ T₁ V₀ V₁ W₀ W₁)
        (blockMixedInterpolation A₀ A₁ γ x))
      (fun q : (y : Fin s) × Fin (M x y) => blockMixedInterpolation A₀ A₁ γ q.1)
      (fun q => blockMixedMPOAnalysis (V₀ x q.1 q.2) (V₁ x q.1 q.2))
      (fun q => blockMixedMPOSynthesis (W₀ x q.1 q.2) (W₁ x q.1 q.2)) where
  retract q := by
    rw [blockMixedMPOAnalysis_mul_synthesis, (h₀ x).retract q, (h₁ x).retract q,
      Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  orthogonal q t hqt := by
    rw [blockMixedMPOAnalysis_mul_synthesis, (h₀ x).orthogonal q t hqt,
      (h₁ x).orthogonal q t hqt, Matrix.fromBlocks_zero]
    rfl
  letter p := by
    classical
    have hB : ∀ z, blockMixedInterpolation A₀ A₁ γ z =
        fun p => sectorTensor (fun y => mixedEndpointBase (A₀ y) (A₁ y)) z p *
          bondInterpolationMatrix (D₀ z) (D₁ z) γ := by
      intro z
      funext p
      exact sectorTensor_mul_right (fun y => mixedEndpointBase (A₀ y) (A₁ y))
        (fun y => bondInterpolationMatrix (D₀ y) (D₁ y) γ) z p
    obtain ⟨⟨y, t⟩, rfl⟩ := finSigmaFinEquiv.surjective p
    rw [hB x, MPOTensor.actTensor_right_mul]
    simp only [hB]
    rw [MPOTensor.actTensor_apply,
      sum_sectorTensor _ x (fun q Z => blockMixedMPO T₀ T₁ V₀ V₁ W₀ W₁ _ q ⊗ₖ Z)
        (by simp)]
    simp only [blockMixedMPO_finSigmaFinEquiv]
    rw [blockMixedMPOSector_action _ _ (A₀ x) (A₁ x) (A₀ y) (A₁ y)
      (V₀ x y) (V₁ x y) (W₀ x y) (W₁ x y)
      (endpoint_block_action_entry T₀ A₀ V₀ W₀ x (h₀ x) y)
      (endpoint_block_action_entry T₁ A₁ V₁ W₁ x (h₁ x) y) t]
    rw [sum_sigma_sectorTensor (fun y => mixedEndpointBase (A₀ y) (A₁ y)) y t
      (fun q Z => blockMixedMPOSynthesis (W₀ x q.1 q.2) (W₁ x q.1 q.2) *
        (Z * bondInterpolationMatrix (D₀ q.1) (D₁ q.1) γ) *
          blockMixedMPOAnalysis (V₀ x q.1 q.2) (V₁ x q.1 q.2)) (by simp)]
    rw [Matrix.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Matrix.mul_assoc, blockMixedMPOAnalysis_mul_weight]
    simp only [Matrix.mul_assoc]

include h₀ h₁ in
/-- At every positive length the common MPO maps the periodic state of each
block to the multiplicity-weighted sum of the periodic states of the blocks,
`O_a |ψ_{A_x(γ)}⟩ = ∑_y M_{x y} |ψ_{A_y(γ)}⟩`. Source: GLM23, lines
1726--1771, with `eq:orthoV`. -/
theorem mpo_mulVec_blockMixedInterpolation (γ : ℝ) (x : Fin s) {L : ℕ} (hL : 0 < L) :
    MPOTensor.mpo (blockMixedMPO T₀ T₁ V₀ V₁ W₀ W₁) L *ᵥ
        (fun σ : Fin L → Fin (blockMixedPhysicalDim D₀ D₁) =>
          mpv (blockMixedInterpolation A₀ A₁ γ x) σ) =
      ∑ y, (M x y : ℂ) • (fun σ => mpv (blockMixedInterpolation A₀ A₁ γ y) σ) := by
  rw [MPOTensor.mpo_mulVec_mpv]
  funext σ
  have h := isBiorthogonalDecomposition_blockMixedInterpolation
    A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ h₀ h₁ γ x
  have ht := h.trace_mul_evalWord 1 (List.ofFn σ)
    (by rw [Ne, List.ofFn_eq_nil_iff]; omega)
  simp only [Matrix.mul_one, h.retract, Matrix.one_mul] at ht
  simp only [mpv, coeff, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ht,
    Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun y _ => ?_
  change ∑ _i : Fin (M x y),
      (Kraus.evalWord (blockMixedInterpolation A₀ A₁ γ y) (List.ofFn σ)).trace = _
  simp

end Block

end MPSTensor.MPOSymmetry
