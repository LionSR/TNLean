/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixReindexGap
import QICLean.Representation.SchmidtBellPrevector
import QICLean.Analysis.RegionalLowDefectProjection

/-!
# A common Schmidt--Bell label sequence in physical-site coordinates

An actual spectral restriction of a reduced density chooses the labels. The
initial vector is constructed from the original physical eigenvector and the
uniform auxiliary pair. Configuration reindexing preserves its exact energy,
symmetry and the two literal auxiliary projection equations.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`07-comparators.tex`, `comparator:prevector` and `comparator:high-label`,
lines 130–147 and 240–281, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open Matrix TensorPower PermutationRepresentation Filter
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.PEPS.AreaLaw

/-- A unit exact eigenvector and an actual selected spectral set determine
one Schmidt--Bell label sequence and the corresponding initial vector in
canonical physical-site coordinates. The selected typical vector chooses
labels; its energy is not asserted.
Source: area-law manuscript, `07-comparators.tex`, `comparator:prevector`
and `comparator:high-label`, lines 130–147 and 240–281; `08-scanner.tex`,
lines 50–59, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The two auxiliary operators are their literal coordinate transports,
before identification with singleton site-label projectors. -/
open Classical in
theorem exists_global_schmidtBellPrevector
    {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (Ω : EuclideanSpace ℂ (ι → Fin q)) (E₀ : ℝ)
    (hΩ : ‖Ω‖ = 1) (hE : H *ᵥ Ω.ofLp = (E₀ : ℂ) • Ω.ofLp)
    (X : Finset ι) (E : Finset (FiniteProduct.Configuration (fun _ : ι => Fin q) X)) :
    let β := fun _ : ι => Fin q
    let split := FiniteProduct.splitEquiv β X
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ split Ω
    0 < ((posSemidef_vecMulVec_self_star ΩX).partialTraceRight.isHermitian)
      .spectralRestrictionMass E →
    let ψ : FiniteProduct.Configuration β Xᶜ × Fin E.card → ℂ := fun x =>
      compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    ∃ ell : (k : ℕ) → PermutationRepresentation.IrrepLabel (Equiv.Perm (Fin k)),
      (∀ k : ℕ, 0 < k →
        let d := E.card
        let eₖ := TensorPower.globalReplicaCopiesEquiv β (Fin d) (Fin d) k
        let ξ := WithLp.toLp 2
          (TensorPower.replicaPrevector Ω d k (ell k) ∘ eₖ)
        let L := PermutationRepresentation.labelProj
          (TensorPower.copyPerm (Fin d) k) (ell k)
        let I := (1 : Matrix (Fin k → ι → Fin q) (Fin k → ι → Fin q) ℂ)
        let Pe := PermutationRepresentation.symProj
          (TensorPower.copyPerm
            ((v : Option (Option ι)) →
              TensorPower.addedSiteSpace (TensorPower.addedSiteSpace β (Fin d))
                (Fin d) v) k)
        ξ ≠ 0 ∧ ‖ξ‖ ≤ 1 ∧
          (((((k : ℝ)⁻¹ • Matrix.replicaHamiltonian H k) ⊗ₖ
            (1 : Matrix ((Fin k → Fin d) × (Fin k → Fin d))
              ((Fin k → Fin d) × (Fin k → Fin d)) ℂ)).submatrix eₖ eₖ) *ᵥ ξ =
            (E₀ : ℂ) • ξ.ofLp) ∧
          Pe *ᵥ ξ = ξ.ofLp ∧
          ((I ⊗ₖ (L ⊗ₖ (1 : Matrix (Fin k → Fin d)
            (Fin k → Fin d) ℂ))).submatrix eₖ eₖ) *ᵥ ξ = ξ.ofLp ∧
          ((I ⊗ₖ ((1 : Matrix (Fin k → Fin d)
            (Fin k → Fin d) ℂ) ⊗ₖ L)).submatrix eₖ eₖ) *ᵥ ξ = ξ.ofLp) ∧
      (∀ᶠ k : ℕ in Filter.atTop,
        (2 * (((k + 1) ^ (E.card ^ 2) : ℕ) : ℝ))⁻¹ ≤
          ‖WithLp.toLp 2
            (((1 : Matrix (Fin k → FiniteProduct.Configuration β Xᶜ)
              (Fin k → FiniteProduct.Configuration β Xᶜ) ℂ) ⊗ₖ
              PermutationRepresentation.labelProj
                (TensorPower.copyPerm (Fin E.card) k) (ell k)) *ᵥ
              (fun x : (Fin k → FiniteProduct.Configuration β Xᶜ) ×
                (Fin k → Fin E.card) => ∏ i, ψ (x.1 i, x.2 i)))‖ ^ 2) ∧
      Asymptotics.IsLittleO Filter.atTop
        (fun k : ℕ => Real.log (ell k).dim - (k : ℝ) *
          vonNeumannEntropy
            (Matrix.partialTraceLeft (Matrix.vecMulVec ψ (star ψ)))
            (Matrix.posSemidef_vecMulVec_self_star ψ).partialTraceLeft.isHermitian)
        (fun k : ℕ => (k : ℝ)) := by
  classical
  intro β split ΩX hz ψ
  have hψ : ‖WithLp.toLp 2 ψ‖ = 1 :=
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      ((Equiv.prodComm E (FiniteProduct.Configuration β Xᶜ)).trans
        ((Equiv.refl (FiniteProduct.Configuration β Xᶜ)).prodCongr
          (Finset.equivFin E)))).norm_map
      (compressedTypicalPureState ΩX E)).trans
      (norm_compressedTypicalPureState ΩX E hz)
  obtain ⟨ell, hpre, hmass, hdim⟩ :=
    exists_label_sequence_replicaPrevector Ω hΩ ψ hψ H E₀ hE
  refine ⟨ell, ?_, hmass, hdim⟩
  intro k hk d eₖ ξ L I Pe
  let u := replicaPrevector Ω d k (ell k)
  obtain ⟨hne, hnorm, henergy, hC, hR, hsym⟩ := hpre k hk
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ eₖ.symm
  have hξ : ξ = U (WithLp.toLp 2 u) := rfl
  have hξne : ξ ≠ 0 := fun h => hne
    (U.injective (((hξ.symm.trans h).trans U.map_zero.symm)))
  have hξnorm : ‖ξ‖ ≤ 1 :=
    (congrArg norm hξ).trans_le ((U.norm_map (WithLp.toLp 2 u)).trans_le hnorm)
  have htransport
      (K : Matrix ((Fin k → ι → Fin q) × ((Fin k → Fin d) × (Fin k → Fin d)))
        ((Fin k → ι → Fin q) × ((Fin k → Fin d) × (Fin k → Fin d))) ℂ)
      (c : ℂ) (hu : K *ᵥ u = c • u) :
      K.submatrix eₖ eₖ *ᵥ ξ = c • ξ.ofLp := by
    exact congrArg
      (fun v : EuclideanSpace ℂ
        (Config k (addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d))) => v.ofLp)
      ((toEuclideanLin_reindex_piLpCongrLeft eₖ.symm K
        (WithLp.toLp 2 u)).trans
        ((congrArg U (show toEuclideanLin K (WithLp.toLp 2 u) =
            c • WithLp.toLp 2 u from WithLp.ofLp_injective 2 hu)).trans
          (U.map_smul c (WithLp.toLp 2 u))))
  have hjoint : symProj (replicaJointCopyPerm (ι → Fin q) (Fin d) (Fin d) k) *ᵥ u = u :=
    symProj_mulVec_of_mem _ fun σ => by
      rw [permOp_replicaJointCopyPerm]
      exact hsym σ
  have hsite : Pe *ᵥ ξ = ξ.ofLp := by
    change symProj (copyPerm ((v : Option (Option ι)) →
      addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d) v) k) *ᵥ ξ = ξ.ofLp
    rw [← symProj_replicaJointCopyPerm_submatrix_globalReplicaCopiesEquiv
      β (Fin d) (Fin d) k]
    simpa only [one_smul] using
      htransport (symProj (replicaJointCopyPerm (ι → Fin q) (Fin d) (Fin d) k)) 1
        (by simpa only [one_smul] using hjoint)
  refine ⟨hξne, hξnorm,
    htransport _ (E₀ : ℂ) henergy, hsite, ?_, ?_⟩
  · simpa only [one_smul] using htransport
      ((1 : Matrix (Fin k → ι → Fin q) (Fin k → ι → Fin q) ℂ) ⊗ₖ
        (L ⊗ₖ (1 : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ))) 1
      (by simpa only [one_smul] using hC)
  · simpa only [one_smul] using htransport
      ((1 : Matrix (Fin k → ι → Fin q) (Fin k → ι → Fin q) ℂ) ⊗ₖ
        ((1 : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ) ⊗ₖ L)) 1
      (by simpa only [one_smul] using hR)

end TNLean.PEPS.AreaLaw
