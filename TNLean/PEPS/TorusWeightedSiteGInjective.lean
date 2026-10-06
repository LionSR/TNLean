/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusBlockMultiplicityState

/-!
# G-injectivity of the actual fourth-root-weighted site

The native four-leg dressing precomposes a site map by the corresponding
four-leg matrix. An invertible dressing matrix commuting with the virtual
representation gives an injective virtual map preserving the invariant subspace.
It therefore preserves G-injectivity. Applying this to the normalized averaging
site proves G-injectivity of the actual tensor H in the reduced-bond construction.

Source: SCP10, arXiv:1001.3807, Definition 5.1, lines 1278–1296, and Section 7,
lines 2962–2977. The explicit fourth-root block weight is invertible whenever
the block dimensions are positive. This local assertion needs neither
irreducibility nor unitarity; constructing the source's multiplicity-one
semi-regular blocks remains the separate finite-group existence theorem.
-/

noncomputable section
open scoped BigOperators Matrix Kronecker
namespace TNLean.PEPS

variable {G W P : Type*} [Group G] [AddCommGroup W] [Module ℂ W]
variable [AddCommGroup P] [Module ℂ P]

/-- An injective virtual map commuting with the group action preserves G-injectivity.
Source: SCP10, Definition 5.1, lines 1278–1296, and the invertible virtual
weights of Section 7, lines 2962–2977. -/
theorem IsGInjective.precomp_of_injective_commute
    {ρ : Representation ℂ G W} {T : W →ₗ[ℂ] P} (ha : IsGInjective ρ T)
    (K : Module.End ℂ W) (hK : Function.Injective K) (hc : ∀ g, Commute K (ρ g)) :
    IsGInjective ρ (T ∘ₗ K) := by
  refine ⟨?_, ?_⟩
  · intro g
    rw [LinearMap.comp_assoc]
    change T ∘ₗ (K * ρ g) = _
    rw [(hc g).eq]
    change T ∘ₗ (ρ g ∘ₗ K) = _
    rw [← LinearMap.comp_assoc, ha.invariant g]
  · intro x hx hzero
    have hmem : K x ∈ ρ.invariants := by
      intro g
      rw [← Module.End.mul_apply, ← (hc g).eq, Module.End.mul_apply, hx g]
    exact hK (by simpa using ha.injOn_invariants (K x) hmem hzero)

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [AddCommGroup P] [Module ℂ P] [DecidableEq V] in
/-- Absorbing matrices into the four virtual legs precomposes the actual site map
with the native four-leg kernel. Source: SCP10, Section 7, lines 2974–2992. -/
theorem siteMap_torusDress (a : V → V → V → V → P → ℂ) (A B : Matrix V V ℂ) :
    siteMap (fun t r b l s => torusDress A B
      (fun c => a c.1 c.2.1 c.2.2.1 c.2.2.2 s) (t, r, b, l)) =
    siteMap a ∘ₗ Matrix.mulVecLin (torusLegKernel A B) := by
  classical
  ext x s
  simp only [siteMap_apply, LinearMap.comp_apply, Matrix.mulVecLin_apply,
    torusDress, Matrix.vecMul, Matrix.mulVec, dotProduct, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  ext c
  congr 1
  ext c'
  ring

private theorem torusLegKernel_isUnit {A B : Matrix V V ℂ} (hA : IsUnit A) (hB : IsUnit B) :
    IsUnit (torusLegKernel A B) := by
  rcases hA with ⟨A, rfl⟩
  rcases hB with ⟨B, rfl⟩
  refine ⟨⟨torusLegKernel (↑A) (↑B), torusLegKernel (↑A⁻¹) (↑B⁻¹), ?_, ?_⟩, rfl⟩ <;>
    rw [torusLegKernel_mul] <;> simp [torusLegKernel]

private theorem torusLegKernel_commute (U : G →* Matrix V V ℂ) (A : Matrix V V ℂ)
    (hc : ∀ g, Commute A (U g)) (g : G) :
    Commute (torusLegKernel A A) (torusLegMatrix U g) := by
  change torusLegKernel A A * torusLegKernel (U g) (U g⁻¹) =
    torusLegKernel (U g) (U g⁻¹) * torusLegKernel A A
  rw [torusLegKernel_mul, torusLegKernel_mul, (hc g).eq, (hc g⁻¹).eq]

variable [Fintype G]
/-- An invertible weight commuting with a matrix representation gives a G-injective
actual dressed averaging site. Source: SCP10, Section 7, lines 2962–2977.
No unitarity, irreducibility, or semi-regularity hypothesis is needed for this
local assertion. -/
theorem isGInjective_torusDress_averagingSite
    (U : G →* Matrix V V ℂ) (A : Matrix V V ℂ)
    (hA : IsUnit A) (hc : ∀ g, Commute A (U g)) :
    IsGInjective (torusLegRep U) (siteMap (fun t r b l s =>
      torusDress A A (fun c => averagingSite U c.1 c.2.1 c.2.2.1 c.2.2.2 s) (t, r, b, l))) := by
  rw [siteMap_torusDress]
  apply (isGInjective_averagingSite U).precomp_of_injective_commute
  · exact Matrix.mulVec_injective_of_isUnit (torusLegKernel_isUnit hA hA)
  · intro g
    exact (torusLegKernel_commute U A hc g).map Matrix.toLinAlgEquiv'

variable {I : Type*} [Fintype I] [DecidableEq I]
/-- Positive sector dimensions make the explicit fourth-root weight invertible.
Source: SCP10, Section 7, lines 2962–2977. -/
theorem blockFourthRootWeight_isUnit (d : I → ℕ) (hd : ∀ i, 0 < d i) :
    IsUnit (blockFourthRootWeight d) := by
  let c (i : I) : ℂ := (Real.sqrt (Real.sqrt (d i : ℝ)) : ℂ)
  have hc (i) : c i ≠ 0 := by
    change (Real.sqrt (Real.sqrt (d i : ℝ)) : ℂ) ≠ 0
    have hp : (0 : ℝ) < d i := by exact_mod_cast hd i
    exact_mod_cast (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hp)).ne'
  let B : Matrix (Σ i, Fin (d i)) (Σ i, Fin (d i)) ℂ :=
    Matrix.blockDiagonal' (fun i => (c i)⁻¹ • (1 : Matrix (Fin (d i)) (Fin (d i)) ℂ))
  have hl : blockFourthRootWeight d * B = 1 := by
    change Matrix.blockDiagonal' (fun i => c i • (1 : Matrix (Fin (d i)) (Fin (d i)) ℂ)) *
      Matrix.blockDiagonal' (fun i => (c i)⁻¹ • (1 : Matrix (Fin (d i)) (Fin (d i)) ℂ)) = _
    rw [← Matrix.blockDiagonal'_mul]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      inv_mul_cancel₀ (hc _), one_smul]
    exact Matrix.blockDiagonal'_one
  have hr : B * blockFourthRootWeight d = 1 := mul_eq_one_comm.mp hl
  exact ⟨⟨blockFourthRootWeight d, B, hl, hr⟩, rfl⟩

/-- The actual reduced-bond tensor H of the explicit block construction is G-injective.
Source: SCP10, equation `eq:ex:V-Theta-double-def`, lines 2974–2977.
This local conclusion holds for any positive-dimensional matrix representation
blocks, without requiring irreducibility or unitarity. -/
theorem isGInjective_blockFourthRootWeight (d : I → ℕ)
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ) (hd : ∀ i, 0 < d i) :
    IsGInjective (torusLegRep (blockMatrixRepresentation d D))
      (siteMap (fun t r b l s => torusDress (blockFourthRootWeight d) (blockFourthRootWeight d)
        (fun c => averagingSite (blockMatrixRepresentation d D)
          c.1 c.2.1 c.2.2.1 c.2.2.2 s) (t, r, b, l))) :=
  isGInjective_torusDress_averagingSite _ _ (blockFourthRootWeight_isUnit d hd)
    (blockFourthRootWeight_commute d D)
end TNLean.PEPS
