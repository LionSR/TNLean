/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualRoughUpper
import TNLean.PEPS.AreaLaw.Scan.ActualInitialRootNorm
import TNLean.PEPS.AreaLaw.Scan.FillTransportEndpoints

/-!
# The actual endpoint log-norm budget for one physical sequence

The initial root has its accepted logarithmic floor estimate. The final fill
root is exactly the endpoint of the last charge, so the rough upper estimate
bounds it using the same supplied physical state, target set and label sequence.
Their difference gives the endpoint budget of actual charge selection, including
a remainder tending to zero. No endpoint norm bound is assumed.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`07-comparators.tex`, lines 332–381; `08-scanner.tex`, lines 457–490,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open Matrix TensorPower TensorPower.ReplicaTransport PermutationRepresentation Filter
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Topology

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Scan

/-- The rough Bell remainder together with the initial root's logarithmic
normalization cost. The coefficient can also retain accumulated logarithmic
transport errors. Source: `08-scanner.tex`, lines 457–490. -/
def roughEndpointRemainder (d : ℕ) (c : ℝ) (K : ℕ) (C : ℝ) (k : ℕ) : ℝ :=
  Real.bellOverlapRemainder d c K k + C * Real.log ((k : ℝ) + 2) / (k : ℝ)

/-- Every fixed physical endpoint remainder tends to zero in the replica count.
Source: `08-scanner.tex`, lines 457–490. -/
theorem tendsto_roughEndpointRemainder (d : ℕ) (c : ℝ) (K : ℕ) (C : ℝ) :
    Tendsto (roughEndpointRemainder d c K C) atTop (𝓝 0) := by
  have hshift : Tendsto (fun k : ℕ ↦ (k : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun k : ℕ ↦ Real.log ((k : ℝ) + 2) / (k : ℝ))
      atTop (𝓝 0) := by
    have hh := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 one_ne_zero).comp hshift
    simpa only [Function.comp_def, pow_one, one_mul, add_neg_cancel_right] using hh
  change Tendsto (fun k : ℕ ↦ Real.bellOverlapRemainder d c K k +
    C * Real.log ((k : ℝ) + 2) / (k : ℝ)) atTop (𝓝 0)
  simpa only [mul_div_assoc, mul_zero, add_zero] using
    (Real.tendsto_bellOverlapRemainder d c K).add (hlog.const_mul C)

namespace CollarScan

open Classical in
/-- The normalized initial-to-final log-norm loss is bounded by the physical
rough-comparison budget for the same supplied sequence. The endpoint at the
final fill is identified with the last charge at parameter one, rather than
extending a theorem beyond its stated scan horizon. The selected constants and
replica threshold precede every later use of the selection estimate.
Source: `08-scanner.tex`, lines 457–490. -/
theorem eventually_actualScan_suppliedPrevector_endpoint_budget
    {q : ℕ} [NeZero q] {I : Type} [Fintype I] [LinearOrder I]
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I)
    (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (hm : 0 < S.m) (hM : 0 < S.M)
    (a : ℝ) (ha : 0 < a)
    (hn : 0 < S.n) (hr : S.r₀ ≤ S.D)
    (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (L : ℕ) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ j : ℕ, 1 ≤ j → j ≤ L →
      (ambientDilation T j \ ambientDilation T (j - 1)).card ≤ S.n)
    (Ωt : EuclideanSpace ℂ (Site Λ → Fin q)) (hΩt : ‖Ωt‖ = 1)
    (E : Finset (FiniteProduct.Configuration (fun _ : Site Λ ↦ Fin q)
      (S.A.filter fun x ↦ x.val ∈ T)))
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Bsh : ℝ)
    (hsh : ∀ j : Fin (L + 1),
      FiniteProduct.entropy (fun _ : Site Λ ↦ Fin q) Ωt
        (positiveDepthPrefix S.A S.depth (j.val : ℤ)) ≤ Bsh) :
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
  intro X β ΩX z hz d n pre ψ hpre hmass
  have hzQ :
      0 < (FiniteProduct.reducedPure_posSemidef β Ωt X).isHermitian.spectralRestrictionMass E :=
    hz
  have hd : 0 < d := Finset.card_pos.mpr
    (Finset.nonempty_iff_ne_empty.mpr fun hE ↦ by
      simp [hE, Matrix.IsHermitian.spectralRestrictionMass] at hzQ)
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  obtain ⟨c, hc, _, hupper⟩ :=
    eventually_actualScan_suppliedPrevector_rough_upper hT S hgraph hdepth hm hM a ha
      hn hr hDpos hD L hL hrows Ωt hΩt E ell Bsh hsh hz hmass
  obtain ⟨Ci, hCi, hinitial⟩ :=
    S.exists_actualFillData_initial_log_filteredNormSq_bound hm hM n ha
  refine ⟨c, Ci, hc, hCi, tendsto_roughEndpointRemainder d c S.K Ci, ?_⟩
  filter_upwards [hupper, eventually_gt_atTop 0] with k hupperK hk
  intro Ninitial Nfinal
  have hlast : S.n * S.m - 1 + 1 = S.n * S.m := by
    have hnm := Nat.mul_pos hn hm
    omega
  have hendpoint :
      (S.actualChargeData hm hM (S.n * S.m - 1)).rootPath n (a / 2) k 1 =
        (S.actualFillData hm hM (S.n * S.m)).rootPath n (a / 2) k 0 := by
    exact (S.charge_rootPath_one_eq_actualFillData_zero hm hM (S.n * S.m - 1) n
      (half_pos ha).le k).trans
        (congrArg (fun s : ℕ ↦ (S.actualFillData hm hM s).rootPath n (a / 2) k 0) hlast)
  obtain ⟨hN, hfinal⟩ := (hupperK (S.n * S.m - 1) (by omega) 1).2
  rw [hendpoint] at hN hfinal
  have hprenorm : ‖WithLp.toLp 2 (pre k)‖ ≤ 1 :=
    (norm_augmentedReplicaPrevector_eq_global q d k Ωt (ell k)).trans_le (hpre k hk)
  have hinitialK := hinitial k (pre k) hprenorm
  have hinitialDiv := div_le_div_of_nonneg_right hinitialK (Nat.cast_nonneg k)
  refine ⟨hN, ?_⟩
  calc
    (Real.log Ninitial - Real.log Nfinal) / (k : ℝ) =
        Real.log Ninitial / (k : ℝ) + -Real.log Nfinal / (k : ℝ) := by ring
    _ ≤ Ci * Real.log ((k : ℝ) + 2) / (k : ℝ) +
        (2 * Real.log (d : ℝ) - Real.log z + a * (S.K : ℝ) *
          (Bsh / z + (1 + 3 * (S.n : ℝ) * (S.D : ℝ) * Real.log (q : ℝ))) +
            Real.bellOverlapRemainder d c S.K k) := add_le_add hinitialDiv hfinal
    _ = _ := by simp only [roughEndpointRemainder]; ring

end CollarScan
end TNLean.PEPS.AreaLaw.Scan
