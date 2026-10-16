/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualEndpointRoughBudget
import TNLean.PEPS.AreaLaw.Scan.PositivePrefixEntropyTransfer

/-!
# The source entropy input gives the same physical endpoint budget

The source whole-row entropy assumption concerns the original state. Its
accepted continuity estimate transfers that bound to the supplied truncated
state using the same target-window trace estimate and compact collar volume.
The actual rough endpoint theorem is then applied to the same target set and
label sequence. No new truncated vector, target set or labels are selected.

The continuity threshold precedes the finite physical system, the entropy
coefficient and its exponent. The explicit continuity and replica errors
are retained; no selected-density power or final absorption is asserted.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 353–357, 399–404 and 457–490, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open Matrix TensorPower TensorPower.ReplicaTransport PermutationRepresentation Filter
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Topology

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open Classical in
/-- The original-state entropy hypothesis and the same quantitative target
truncation supply the endpoint budget. The prefix bound on the truncated state
is derived, not assumed. All replica remainders and the `n^(-247)` continuity
cost remain explicit. Source: `08-scanner.tex`, lines 353–357, 399–404 and 457–490. -/
theorem exists_source_actualScan_suppliedPrevector_endpoint_budget
    {q : ℕ} [NeZero q] (hq : 1 ≤ q) (g Cvol : ℝ) (hg : 0 < g) :
    ∃ N : ℕ, 2 ≤ N ∧
      ∀ {I : Type} [Fintype I] [LinearOrder I]
        {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
        (S : CollarScan (Site Λ) I), N ≤ S.n →
        ∀ (_hgraph : S.graph = domainGraph Λ)
          (_hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
          (hm : 0 < S.m) (hM : 0 < S.M)
          (a : ℝ) (_ha : 0 < a) (_hr : S.r₀ ≤ S.D)
          (_hDpos : 1 ≤ S.D) (_hD : 4 * S.D ≤ S.m)
          (L : ℕ) (_hL : 8 * S.K * S.m ≤ L)
          (_hrows : ∀ j : ℕ, 1 ≤ j → j ≤ L →
            (ambientDilation T j \ ambientDilation T (j - 1)).card ≤ S.n)
          (Ω Ωt : StateSpace Λ q), ‖Ω‖ = 1 → ‖Ωt‖ = 1 →
          ((S.truncationSet L).card : ℝ) ≤ Cvol * (S.n : ℝ) ^ 2 →
          Matrix.traceDistance (Matrix.vecMulVec Ωt (star Ωt))
              (Matrix.vecMulVec Ω (star Ω)) ≤
            Real.sqrt (2 * min ((S.n : ℝ) ^ (-1000 : ℝ)) (g / 4) / g) →
          ∀ Ce e : ℝ,
            (∀ j : ℕ, j ≤ L →
              regionalEntropy Λ q Ω (positiveDepthPrefix S.A S.depth (j : ℤ)) ≤
                Ce * ((S.n : ℝ) * (L : ℝ) ^ e + S.n)) →
          ∀ (E : Finset (FiniteProduct.Configuration (fun _ : Site Λ ↦ Fin q)
            (S.A.filter fun x ↦ x.val ∈ T)))
            (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))),
          let Bsh := Ce * ((S.n : ℝ) * (L : ℝ) ^ e + S.n) +
            (S.n : ℝ) ^ (-247 : ℝ)
          let X := S.A.filter fun x ↦ x.val ∈ T
          let β := fun _ : Site Λ ↦ Fin q
          let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
            (FiniteProduct.splitEquiv β X) Ωt
          let z := Matrix.IsHermitian.spectralRestrictionMass
            (posSemidef_vecMulVec_self_star ΩX).partialTraceRight.isHermitian E
          0 < z →
          let d := E.card
          let n := augmentedDimensions (V := Site Λ) q (fun _ ↦ d)
          let pre : (k : ℕ) → Config k (fun v ↦ Fin (n v)) → ℂ := fun k ↦
            replicaPrevector Ωt d k (ell k) ∘ augmentedSumReplicaCopiesEquiv q d k
          let ψ : FiniteProduct.Configuration β Xᶜ × Fin E.card → ℂ := fun x ↦
            compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
          (∀ k : ℕ, 0 < k →
            ‖WithLp.toLp 2 (replicaPrevector Ωt d k (ell k) ∘
              globalReplicaCopiesEquiv β (Fin d) (Fin d) k)‖ ≤ 1) →
          (∀ᶠ k : ℕ in atTop,
            (2 * (((k + 1) ^ (E.card ^ 2) : ℕ) : ℝ))⁻¹ ≤
              ‖WithLp.toLp 2
                (((1 : Matrix (Fin k → FiniteProduct.Configuration β Xᶜ)
                  (Fin k → FiniteProduct.Configuration β Xᶜ) ℂ) ⊗ₖ
                  labelProj (copyPerm (Fin E.card) k) (ell k)) *ᵥ
                  (fun x : (Fin k → FiniteProduct.Configuration β Xᶜ) ×
                    (Fin k → Fin E.card) ↦ ∏ i, ψ (x.1 i, x.2 i)))‖ ^ 2) →
          ∃ c Ci : ℝ, 0 ≤ c ∧ 0 ≤ Ci ∧
            Tendsto (roughEndpointRemainder d c S.K Ci) atTop (𝓝 0) ∧
            ∀ᶠ k : ℕ in atTop,
              let Ninitial := Transport.filteredNormSq
                ((S.actualFillData hm hM 0).rootPath n (a / 2) k 0) (pre k)
              let Nfinal := Transport.filteredNormSq
                ((S.actualFillData hm hM (S.n * S.m)).rootPath n (a / 2) k 0) (pre k)
              0 < Nfinal ∧ (Real.log Ninitial - Real.log Nfinal) / (k : ℝ) ≤
                2 * Real.log (d : ℝ) - Real.log z + a * (S.K : ℝ) *
                  (Bsh / z + (1 + 3 * (S.n : ℝ) * (S.D : ℝ) * Real.log (q : ℝ))) +
                    roughEndpointRemainder d c S.K Ci k := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_regionalEntropy_positiveDepthPrefix_le q hq g Cvol hg)
  refine ⟨max N 2, le_max_right _ _, ?_⟩
  intro I _ _ Λ T hT S hn hgraph hdepth hm hM a ha hr hDpos hD L hL hrows
    Ω Ωt hΩ hΩt hcard hdist Ce e hsource E ell Bsh X β ΩX z hz d n pre ψ hpre hmass
  have hnpos : 0 < S.n := by have := (le_max_right N 2).trans hn; omega
  have htransfer := hN S.n ((le_max_left N 2).trans hn)
  have hcard' : ((depthPrefix S.A S.depth (L : ℤ)).card : ℝ) ≤
      Cvol * (S.n : ℝ) ^ 2 := hcard
  have hsh : ∀ j : Fin (L + 1),
      FiniteProduct.entropy (fun _ : Site Λ ↦ Fin q) Ωt
        (positiveDepthPrefix S.A S.depth (j.val : ℤ)) ≤ Bsh := by
    intro j
    simpa only [regionalEntropy_eq_finiteProduct] using
      htransfer Λ Ω Ωt hΩ hΩt S.A S.depth L hcard' hdist Ce e hsource
        j.val (Nat.le_of_lt_succ j.isLt)
  exact eventually_actualScan_suppliedPrevector_endpoint_budget hT S hgraph hdepth
    hm hM a ha hnpos hr hDpos hD L hL hrows Ωt hΩt E ell Bsh hsh hz hpre hmass

end TNLean.PEPS.AreaLaw.Scan.CollarScan
