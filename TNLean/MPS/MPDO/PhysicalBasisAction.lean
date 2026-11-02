/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryTransport
import TNLean.MPS.MPDO.PhysicalIsometricEmbedding

/-!
# Physical coordinate changes of operator actions and fusion

A physical coordinate change `V` of an operator tensor, `T ↦ V T Vᴴ` on its
physical legs, acts on the state by moving `Vᴴ` to the state and `V` back
to the result. Exact biorthogonal action and fusion decompositions
therefore transport along `V` with the same analysis and synthesis maps.

For a product of two changed operators, the factor `Vᴴ V` appears between
them. It is harmless when `V` is an isometry onto the larger space. For the
compression onto the physical support of a state, `Vᴴ V` is the support
projection; an exact action decomposition of the second operator on that
state already forces the operator to preserve the support. This is the
physical-support restriction that precedes the mixed interpolation of
Garre-Rubio–Lootens–Molnár, derived here rather than assumed.

## Main statements

* `MPOTensor.actTensor_changePhysicalBasis`: the action of a changed operator.
* `MPSTensor.IsBiorthogonalDecomposition.actTensor_changePhysicalBasis` and
  `MPSTensor.IsBiorthogonalDecomposition.toMPSTensor_changePhysicalBasis`:
  transport of action and fusion decompositions.
* `MPOTensor.mulTensor_changePhysicalBasis_of_slice`: products of changed
  operators.
* `MPOTensor.physicalSlice_mul_eq_of_isBiorthogonalDecomposition`: an exact
  action decomposition forces support invariance.

## References

* Garre-Rubio–Lootens–Molnár, arXiv:2203.12563v3, `REsubmission.tex`,
  lines 1584–1586 (restriction to the physical support), `mpoMPSsten`,
  `fusiontensors`, and `fusiontensors2`.
-/

open scoped Matrix BigOperators Kronecker

open MPOTensor.PhysicalSectorFactorization (changePhysicalBasis changePhysicalBasis_apply_eq_sum)

namespace MPOTensor

variable {d e χ D D₁ D₂ : ℕ}

/-- One coefficient of the action tensor, in the operator-bond-first order
of `finProdFinEquiv`. Source: GLM23, `mpoMPSsten`, lines 1070–1090. -/
theorem actTensor_apply_finProdFinEquiv (T : MPOTensor d χ) (A : MPSTensor d D)
    (p : Fin d) (β α : Fin χ) (x y : Fin D) :
    actTensor T A p (finProdFinEquiv (β, x)) (finProdFinEquiv (α, y)) =
      ∑ q, T p q β α * A q x y := by
  simp [actTensor, Matrix.sum_apply, Matrix.kroneckerMap_apply]

/-- A physical coordinate change of the operator is the change of the
state by `Vᴴ`, followed by physical mixing of the action by `V`.
Source context: GLM23, `mpoMPSsten`, lines 1070–1090. -/
theorem actTensor_changePhysicalBasis (V : Matrix (Fin e) (Fin d) ℂ)
    (T : MPOTensor d χ) (B : MPSTensor e D) :
    actTensor (changePhysicalBasis V T) B =
      MPSTensor.rotatePhysical V (actTensor T (MPSTensor.rotatePhysical Vᴴ B)) := by
  funext i
  ext a b
  obtain ⟨⟨β, x⟩, rfl⟩ := finProdFinEquiv.surjective a
  obtain ⟨⟨α, y⟩, rfl⟩ := finProdFinEquiv.surjective b
  simp only [MPSTensor.rotatePhysical_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    actTensor_apply_finProdFinEquiv, changePhysicalBasis_apply_eq_sum, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The physical slice of a stacked product is the product of the slices.
Source context: GLM23, `fusiontensors`, lines 364–391. -/
theorem physicalSlice_mulTensor (M : MPOTensor d D₁) (N : MPOTensor d D₂)
    (β₁ α₁ : Fin D₁) (β₂ α₂ : Fin D₂) :
    physicalSlice (mulTensor M N) (finProdFinEquiv (β₁, β₂))
        (finProdFinEquiv (α₁, α₂)) =
      physicalSlice M β₁ α₁ * physicalSlice N β₂ α₂ := by
  ext i k
  simp [physicalSlice, mulTensor, Matrix.mul_apply, Matrix.sum_apply,
    Matrix.kroneckerMap_apply]

/-- Stacked products commute with a physical coordinate change once the
second factor is unchanged by the intermediate factor `Vᴴ V`.
Source context: GLM23, `fusiontensors`, lines 364–391. -/
theorem mulTensor_changePhysicalBasis_of_slice (V : Matrix (Fin e) (Fin d) ℂ)
    (M : MPOTensor d D₁) (N : MPOTensor d D₂)
    (hN : ∀ β α, Vᴴ * V * physicalSlice N β α * Vᴴ = physicalSlice N β α * Vᴴ) :
    mulTensor (changePhysicalBasis V M) (changePhysicalBasis V N) =
      changePhysicalBasis V (mulTensor M N) := by
  funext i k
  ext a b
  obtain ⟨⟨β₁, β₂⟩, rfl⟩ := finProdFinEquiv.surjective a
  obtain ⟨⟨α₁, α₂⟩, rfl⟩ := finProdFinEquiv.surjective b
  have key : (V * physicalSlice M β₁ α₁ * Vᴴ) * (V * physicalSlice N β₂ α₂ * Vᴴ) =
      V * physicalSlice (mulTensor M N) (finProdFinEquiv (β₁, β₂))
        (finProdFinEquiv (α₁, α₂)) * Vᴴ := by
    rw [physicalSlice_mulTensor]
    calc _ = V * physicalSlice M β₁ α₁ * (Vᴴ * V * physicalSlice N β₂ α₂ * Vᴴ) := by
            simp only [Matrix.mul_assoc]
      _ = _ := by rw [hN]; simp only [Matrix.mul_assoc]
  simp only [mulTensor_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.sum_apply, Matrix.kroneckerMap_apply]
  change ∑ j, (V * physicalSlice M β₁ α₁ * Vᴴ) i j * (V * physicalSlice N β₂ α₂ * Vᴴ) j k =
    (V * physicalSlice (mulTensor M N) (finProdFinEquiv (β₁, β₂))
      (finProdFinEquiv (α₁, α₂)) * Vᴴ) i k
  rw [← Matrix.mul_apply, key]

/-- Stacked products commute with an isometric physical coordinate change.
Source context: GLM23, `fusiontensors`, lines 364–391. -/
theorem mulTensor_changePhysicalBasis (V : Matrix (Fin e) (Fin d) ℂ) (hV : Vᴴ * V = 1)
    (M : MPOTensor d D₁) (N : MPOTensor d D₂) :
    mulTensor (changePhysicalBasis V M) (changePhysicalBasis V N) =
      changePhysicalBasis V (mulTensor M N) :=
  mulTensor_changePhysicalBasis_of_slice V M N fun _ _ => by rw [hV, Matrix.one_mul]

end MPOTensor

namespace MPSTensor.IsBiorthogonalDecomposition

variable {ι : Type*} [Fintype ι] {d e D : ℕ} {δ : ι → ℕ}

/-- Physical mixing preserves an exact biorthogonal decomposition, with the
same analysis and synthesis maps. Source context: GLM23, `fusiontensors2`
and `eq:orthoV`, lines 458–490. -/
protected theorem rotatePhysical {B : MPSTensor d D} {A : ∀ c : ι, MPSTensor d (δ c)}
    {V : ∀ c, Matrix (Fin (δ c)) (Fin D) ℂ} {W : ∀ c, Matrix (Fin D) (Fin (δ c)) ℂ}
    (h : IsBiorthogonalDecomposition B A V W) (M : Matrix (Fin e) (Fin d) ℂ) :
    IsBiorthogonalDecomposition (rotatePhysical M B)
      (fun c => rotatePhysical M (A c)) V W where
  retract := h.retract
  orthogonal := h.orthogonal
  letter i := by
    simp only [rotatePhysical_apply, h.letter, Finset.smul_sum, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.mul_smul, Matrix.smul_mul]
    exact Finset.sum_comm

/-- An action decomposition of an operator on `Vᴴ B` gives one of its
physical coordinate change on `B`, with the targets mixed by `V`.
Source context: GLM23, `fusiontensors2` and `eq:orthoV`, lines 458–490. -/
theorem actTensor_changePhysicalBasis {χ D' : ℕ} {A : ∀ c : ι, MPSTensor d (δ c)}
    {V : ∀ c, Matrix (Fin (δ c)) (Fin (χ * D')) ℂ}
    {W : ∀ c, Matrix (Fin (χ * D')) (Fin (δ c)) ℂ}
    (U : Matrix (Fin e) (Fin d) ℂ) (T : MPOTensor d χ) (B : MPSTensor e D')
    (h : IsBiorthogonalDecomposition (MPOTensor.actTensor T (rotatePhysical Uᴴ B)) A V W) :
    IsBiorthogonalDecomposition (MPOTensor.actTensor (changePhysicalBasis U T) B)
      (fun c => rotatePhysical U (A c)) V W := by
  rw [MPOTensor.actTensor_changePhysicalBasis]
  exact h.rotatePhysical U

/-- A fusion decomposition transports along a physical coordinate change of
every operator involved. Source context: GLM23, `fusiontensors` and
`eq:orthoW`, lines 364–391. -/
theorem toMPSTensor_changePhysicalBasis {χ : ℕ} {O : ∀ c : ι, MPOTensor d (δ c)}
    {V : ∀ c, Matrix (Fin (δ c)) (Fin χ) ℂ} {W : ∀ c, Matrix (Fin χ) (Fin (δ c)) ℂ}
    (U : Matrix (Fin e) (Fin d) ℂ) (T : MPOTensor d χ)
    (h : IsBiorthogonalDecomposition T.toMPSTensor (fun c => (O c).toMPSTensor) V W) :
    IsBiorthogonalDecomposition (changePhysicalBasis U T).toMPSTensor
      (fun c => (changePhysicalBasis U (O c)).toMPSTensor) V W := by
  simp only [MPOTensor.toMPSTensor_changePhysicalBasis]
  exact h.rotatePhysical (MPOTensor.doubledPhysicalMatrix U)

/-- A fusion decomposition of a stacked product transports along a physical
coordinate change, provided the second factor is unchanged by `Vᴴ V`.
Source context: GLM23, `fusiontensors` and `eq:orthoW`, lines 364–391. -/
theorem mulTensor_changePhysicalBasis {D₁ D₂ : ℕ} {O : ∀ c : ι, MPOTensor d (δ c)}
    {V : ∀ c, Matrix (Fin (δ c)) (Fin (D₁ * D₂)) ℂ}
    {W : ∀ c, Matrix (Fin (D₁ * D₂)) (Fin (δ c)) ℂ}
    (U : Matrix (Fin e) (Fin d) ℂ) (M : MPOTensor d D₁) (N : MPOTensor d D₂)
    (hN : ∀ β α, Uᴴ * U * MPOTensor.physicalSlice N β α * Uᴴ =
      MPOTensor.physicalSlice N β α * Uᴴ)
    (h : IsBiorthogonalDecomposition (MPOTensor.mulTensor M N).toMPSTensor
      (fun c => (O c).toMPSTensor) V W) :
    IsBiorthogonalDecomposition
      (MPOTensor.mulTensor (changePhysicalBasis U M)
        (changePhysicalBasis U N)).toMPSTensor
      (fun c => (changePhysicalBasis U (O c)).toMPSTensor) V W := by
  rw [MPOTensor.mulTensor_changePhysicalBasis_of_slice U M N hN]
  exact h.toMPSTensor_changePhysicalBasis U _

end MPSTensor.IsBiorthogonalDecomposition

namespace MPOTensor

variable {ι : Type*} [Fintype ι] {d e χ D : ℕ} {δ : ι → ℕ}

/-- If an operator acts on `U B` by an exact decomposition whose targets are
fixed by physical mixing with `G`, and the letters of `B` are linearly
independent, then every physical slice of the operator satisfies
`G T U = T U`. For a support projection `G` this is invariance of the
physical support. Source context: GLM23, `REsubmission.tex`, lines
1584–1586, together with `fusiontensors2`. -/
theorem physicalSlice_mul_eq_of_isBiorthogonalDecomposition
    (T : MPOTensor d χ) (U : Matrix (Fin d) (Fin e) ℂ) (B : MPSTensor e D)
    (hB : LinearIndependent ℂ B) (G : Matrix (Fin d) (Fin d) ℂ)
    {A : ∀ c : ι, MPSTensor d (δ c)}
    {V : ∀ c, Matrix (Fin (δ c)) (Fin (χ * D)) ℂ}
    {W : ∀ c, Matrix (Fin (χ * D)) (Fin (δ c)) ℂ}
    (h : MPSTensor.IsBiorthogonalDecomposition
      (actTensor T (MPSTensor.rotatePhysical U B)) A V W)
    (hG : ∀ c, MPSTensor.rotatePhysical G (A c) = A c) (β α : Fin χ) :
    G * physicalSlice T β α * U = physicalSlice T β α * U := by
  have hfix : MPSTensor.rotatePhysical G (actTensor T (MPSTensor.rotatePhysical U B)) =
      actTensor T (MPSTensor.rotatePhysical U B) := by
    funext p
    rw [(h.rotatePhysical G).letter p, h.letter p]
    simp only [hG]
  ext p k
  refine Fintype.linearIndependent_iffₛ.mp hB
    (fun k => (G * physicalSlice T β α * U) p k)
    (fun k => (physicalSlice T β α * U) p k) ?_ k
  ext x y
  have hxy := congrArg (fun F => F p (finProdFinEquiv (β, x)) (finProdFinEquiv (α, y))) hfix
  simp only [MPSTensor.rotatePhysical_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    actTensor_apply_finProdFinEquiv] at hxy
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, physicalSlice,
    Finset.sum_mul, Finset.mul_sum] at hxy ⊢
  calc
    _ = ∑ j, ∑ q, ∑ k, G p j * (T j q β α * (U q k * B k x y)) := by
      rw [← Fintype.sum_reverse_three]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => by ring
    _ = ∑ q, ∑ k, T p q β α * (U q k * B k x y) := hxy
    _ = _ := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end MPOTensor
