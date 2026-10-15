/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualSharpUpper
import TNLean.PEPS.AreaLaw.GlobalSchmidtBellPrevector

/-!
# The common physical label sequence and its actual sharp upper estimate

One application of the Schmidt--Bell selection fixes the labels. Its exact
energy equation, full copy symmetry, both auxiliary equations, selected mass,
and dimension asymptotics are retained while the actual fill and charge
estimate is appended for that same sequence and physical vector.

Source: OpenAI area-law manuscript, `07-comparators.tex`,
`comparator:prevector`, `comparator:high-label`, and `comparator:sharp-upper`,
lines 130–153, 240–281 and 383–418, revision adc7f124.
-/

noncomputable section

open Matrix TensorPower PermutationRepresentation Filter
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Topology

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open ActualTerminals

open Classical in
/-- The selected physical label sequence carries the exact eigenvalue,
symmetry, both auxiliary labels, mass and little-o dimension properties,
together with the actual sharp upper estimate for that same sequence.
Source: `07-comparators.tex`, lines 130–153, 240–281 and 383–418;
`08-scanner.tex`, lines 416–474, revision adc7f124. -/
theorem exists_actualScan_schmidtBellPrevector_sharp_upper
    {q : ℕ} [NeZero q] {I : Type} [Fintype I] [LinearOrder I]
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (hm : 0 < S.m) (hM : 0 < S.M)
    (a Kmom r : ℝ) (ha : 0 < a) (har : 6 * a ≤ r) (ha1 : 6 * a ≤ 1)
    (L : ℕ) (hL : 8 * S.K * S.m ≤ L)
    (Ωt : EuclideanSpace ℂ (Site Λ → Fin q)) (hΩt : ‖Ωt‖ = 1)
    (H : Matrix (Site Λ → Fin q) (Site Λ → Fin q) ℂ) (E₀ : ℝ)
    (hE : H *ᵥ Ωt.ofLp = (E₀ : ℂ) • Ωt.ofLp)
    (E : Finset (FiniteProduct.Configuration (fun _ : Site Λ ↦ Fin q)
      (S.A.filter fun x ↦ x.val ∈ T)))
    (hmom : ∀ (s : ℕ) (hist : History S.K S.m S.M s) (g : Fin S.K),
      (s ≤ S.n * S.m → ∀ Q ∈ statusMarginalRegions S.depth (S.state hist g),
        ∀ u : ℝ, |u| ≤ r →
          Real.log (Entropy.surprisalMoment
            (reducedState_isHermitian Λ q Ωt Q).eigenvalues u) ≤
            u * regionalEntropy Λ q Ωt Q + Kmom * u ^ 2) ∧
      (s + 1 ≤ S.n * S.m →
        ∀ Q ∈ statusMarginalRegions S.depth (S.oldChargeState hist g),
          ∀ u : ℝ, |u| ≤ r →
            Real.log (Entropy.surprisalMoment
              (reducedState_isHermitian Λ q Ωt Q).eigenvalues u) ≤
              u * regionalEntropy Λ q Ωt Q + Kmom * u ^ 2)) :
    let X := S.A.filter fun x ↦ x.val ∈ T
    let β := fun _ : Site Λ ↦ Fin q
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (FiniteProduct.splitEquiv β X) Ωt
    let z := Matrix.IsHermitian.spectralRestrictionMass
      (posSemidef_vecMulVec_self_star ΩX).partialTraceRight.isHermitian E
    0 < z →
    let d := E.card
    let ψ : FiniteProduct.Configuration β Xᶜ × Fin E.card → ℂ := fun x ↦
      compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    ∃ ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)),
      let n := augmentedDimensions (V := Site Λ) q (fun _ ↦ d)
      let pre : (k : ℕ) → Config k (fun v ↦ Fin (n v)) → ℂ := fun k ↦
        replicaPrevector Ωt d k (ell k) ∘ augmentedSumReplicaCopiesEquiv q d k
      (∀ k : ℕ, 0 < k →
        let d := E.card
        let eₖ := TensorPower.globalReplicaCopiesEquiv β (Fin d) (Fin d) k
        let ξ := WithLp.toLp 2
          (TensorPower.replicaPrevector Ωt d k (ell k) ∘ eₖ)
        let L := PermutationRepresentation.labelProj
          (TensorPower.copyPerm (Fin d) k) (ell k)
        let I := (1 : Matrix (Fin k → (Site Λ) → Fin q) (Fin k → (Site Λ) → Fin q) ℂ)
        let Pe := PermutationRepresentation.symProj
          (TensorPower.copyPerm
            ((v : Option (Option (Site Λ))) →
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
      (Asymptotics.IsLittleO Filter.atTop
        (fun k : ℕ => Real.log (ell k).dim - (k : ℝ) *
          vonNeumannEntropy
            (Matrix.partialTraceLeft (Matrix.vecMulVec ψ (star ψ)))
            (Matrix.posSemidef_vecMulVec_self_star ψ).partialTraceLeft.isHermitian)
        (fun k : ℕ => (k : ℝ))) ∧
      ∃ c : ℝ, 0 ≤ c ∧
        Tendsto (Real.bellOverlapRemainder d c S.K) atTop (𝓝 0) ∧
        ∀ᶠ k : ℕ in atTop, ∀ (s : ℕ) (hs : s + 1 ≤ S.n * S.m) (p : ℝ),
          let σ := terminalPartition S (S.n * S.m)
          let gpost := fun j g ↦
            regionalEntropy Λ q Ωt (positiveNear S.depth (σ j g)) +
              regionalEntropy Λ q Ωt (positiveNearMiddle S.depth (σ j g)) -
                regionalEntropy Λ q Ωt (middle (σ j g))
          let p₀ := Set.projIcc (0 : ℝ) 1 zero_le_one p
          let bound := fun (tree : MeanTree (terminalFamily S.K S.m S.M (S.n * S.m))) ↦
            2 * Real.log (d : ℝ) - Real.log z +
              (a / 2) * (∑ g, ∑ j, tree.weight j * gpost j g) +
                6 * (S.K : ℝ) * Kmom * a ^ 2 - (S.K : ℝ) / 2 * Real.log z +
                  Real.bellOverlapRemainder d c S.K k
          let step : Fin (S.n * S.m) := ⟨s, Nat.lt_of_succ_le hs⟩
          let Nfill := Matrix.Transport.filteredNormSq
            ((S.actualFillData hm hM s).rootPath n (a / 2) k p) (pre k)
          let Ncharge := Matrix.Transport.filteredNormSq
            ((S.actualChargeData hm hM s).rootPath n (a / 2) k p) (pre k)
          (0 < Nfill ∧ -Real.log Nfill / (k : ℝ) ≤
            bound (((S.actualFillData hm hM s).tree p₀).map
              (fillTerminalIndex S.K S.m S.M (S.n * S.m) step))) ∧
          (0 < Ncharge ∧ -Real.log Ncharge / (k : ℝ) ≤
            bound (((S.actualChargeData hm hM s).tree p₀).map
              (chargeTerminalIndex S.K S.m S.M (S.n * S.m) step))) := by
  classical
  intro X β ΩX z hz d ψ
  obtain ⟨ell, hpre, hmass, hdim⟩ :=
    exists_global_schmidtBellPrevector H Ωt E₀ hΩt hE X E hz
  refine ⟨ell, hpre, hmass, hdim, ?_⟩
  exact eventually_actualScan_suppliedPrevector_sharp_upper
    hT S hdepth hm hM a Kmom r ha har ha1 L hL Ωt hΩt E ell hmom hz hmass

end TNLean.PEPS.AreaLaw.Scan.CollarScan
