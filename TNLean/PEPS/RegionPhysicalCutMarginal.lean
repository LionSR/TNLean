/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegionBlock.AbsorbedEquality
import QICLean.Channel.FiniteProduct

/-!
# Restricting normalized physical cut densities to subregions

The row Gram matrix of a finite physical coefficient cut is its actual
regional partial trace. Its trace is independent of the cut. Consequently,
equality of normalized densities on a region implies equality on every
subregion, including disconnected and empty subregions. Nonvanishing of a
coefficient cut is likewise independent of the chosen region.

This supplies the marginal argument for SCP10, arXiv:1001.3807v3,
Lemma 6.14, under the explicit envelope conditions of the
native flux-density theorem. The partial-trace identities are those of
the pinned finite-product matrix library.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V] {d : ℕ}

/-- The actual coefficient matrix of an arbitrary finite physical vector
across a region and its complement. This cut describes regional observations in
SCP10,
Lemma 6.14, without any tensor-network assumption. -/
def regionPhysicalCutMatrix (ψ : (V → Fin d) → ℂ) (R : Finset V) :
    Matrix (RegionPhysicalConfig (d := d) R)
      (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ :=
  fun σ τ => ψ (assembleRegionσ R σ τ)

/-- A physical coefficient cut is nonzero exactly when the original vector
is nonzero, independently of the cut. -/
theorem regionPhysicalCutMatrix_ne_zero_iff (ψ : (V → Fin d) → ℂ) (R : Finset V) :
    regionPhysicalCutMatrix ψ R ≠ 0 ↔ ψ ≠ 0 := by
  constructor
  · intro h hψ
    apply h
    subst ψ
    rfl
  · intro h hM
    apply h
    funext σ
    have he := congrFun (congrFun hM (fun v => σ v.1)) (fun v => σ v.1)
    simpa only [regionPhysicalCutMatrix, assembleRegionσ_restrict,
      Matrix.zero_apply, Pi.zero_apply] using he

/-- The actual row Gram matrix of the physical coefficient cut is the
regional partial trace of the pure coefficient matrix. -/
theorem regionPhysicalCutMatrix_mul_conjTranspose (ψ : (V → Fin d) → ℂ) (R : Finset V) :
    regionPhysicalCutMatrix ψ R * (regionPhysicalCutMatrix ψ R).conjTranspose =
      FiniteProduct.reducedMatrix (fun _ : V => Fin d)
        (Matrix.vecMulVec ψ (star ψ)) R := by
  ext σ τ
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, regionPhysicalCutMatrix,
    FiniteProduct.reducedMatrix_apply, Matrix.vecMulVec_apply, Pi.star_apply]
  rfl

private theorem reduction_smul (c : ℂ) (ρ : Matrix (V → Fin d) (V → Fin d) ℂ)
    (R : Finset V) :
    FiniteProduct.reducedMatrix (fun _ : V => Fin d) (c • ρ) R =
      c • FiniteProduct.reducedMatrix (fun _ : V => Fin d) ρ R := by
  ext σ τ
  simp only [FiniteProduct.reducedMatrix_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]

private theorem reduction_eq_of_subset
    (ρ κ : Matrix (V → Fin d) (V → Fin d) ℂ) {R S : Finset V} (hRS : R ⊆ S)
    (h : FiniteProduct.reducedMatrix (fun _ : V => Fin d) ρ S =
      FiniteProduct.reducedMatrix (fun _ : V => Fin d) κ S) :
    FiniteProduct.reducedMatrix (fun _ : V => Fin d) ρ R =
      FiniteProduct.reducedMatrix (fun _ : V => Fin d) κ R := by
  have hdis : Disjoint R (S \ R) := disjoint_sdiff_self_right
  have hU : R ∪ (S \ R) = S := Finset.union_sdiff_of_subset hRS
  have h' : FiniteProduct.reducedMatrix (fun _ : V => Fin d) ρ (R ∪ (S \ R)) =
      FiniteProduct.reducedMatrix (fun _ : V => Fin d) κ (R ∪ (S \ R)) := by
    exact hU.symm ▸ h
  let e := (FiniteProduct.unionEquiv (fun _ : V => Fin d) R (S \ R) hdis).symm
  have hm := congrArg (fun M => Matrix.partialTraceRight (M.submatrix e e)) h'
  simpa only [e, FiniteProduct.partialTraceRight_reducedMatrix_union] using hm

/-- Equality of normalized physical reduced densities passes to every
subregion by the actual partial trace. No topology, connectedness or nonzero
premise is needed for this matrix identity. -/
theorem regionPhysicalCutMatrix_normalized_reduced_eq_of_subset
    (ψ φ : (V → Fin d) → ℂ) {R S : Finset V} (hRS : R ⊆ S)
    (h : let M := regionPhysicalCutMatrix ψ S
      let N := regionPhysicalCutMatrix φ S
      (M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose) =
        (N * N.conjTranspose).trace⁻¹ • (N * N.conjTranspose)) :
    let M := regionPhysicalCutMatrix ψ R
    let N := regionPhysicalCutMatrix φ R
    (M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose) =
      (N * N.conjTranspose).trace⁻¹ • (N * N.conjTranspose) := by
  dsimp only at h ⊢
  simp only [regionPhysicalCutMatrix_mul_conjTranspose,
    FiniteProduct.trace_reducedMatrix] at h ⊢
  rw [← reduction_smul, ← reduction_smul] at h ⊢
  exact reduction_eq_of_subset _ _ hRS h

end TNLean.PEPS
