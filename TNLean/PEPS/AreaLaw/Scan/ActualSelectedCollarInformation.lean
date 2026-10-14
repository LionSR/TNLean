/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualCollarInformation
import TNLean.PEPS.AreaLaw.SelectedSchmidtEntropyBounds

/-!
# The actual selected sharp expression controls physical mutual information

The selected auxiliary entropy differs from the same physical target entropy
by at most the actual window width minus log mass. The precise correction is
twice that amount for the sharp entropy expression. The accepted continuity
bound then transfers twice the mutual information to the original physical
state with coefficient 16 and only the target dimension.

The stage, parameter, terminal tree, weights and spectral set are all supplied
unchanged. No comparator bound, selected-density estimate or safe-box entropy
conclusion is assumed or proved here.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 900--911 and 936--941, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open ActualTerminals

open Classical in
/-- At the same actual charge point, the literal sharp entropy expression
controls the truncated mutual information with the outside collar and its
original-state counterpart. The selected-spectrum correction and the exact
trace-distance continuity cost remain explicit.
Source: `08-scanner.tex`, lines 900--911 and 936--941. -/
theorem actualCharge_two_mutualInformation_le_selectedSharpExpression
    {I : Type} [Fintype I] [LinearOrder I] {Λ T : Finset (ℤ × ℤ)} {q : ℕ}
    (hT : T.Nonempty) (S : CollarScan (Site Λ) I)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (hm : 0 < S.m) (hM : 0 < S.M) (hK : 0 < S.K)
    (L : ℕ) (hL : 8 * S.K * S.m ≤ L)
    (Ωt : StateSpace Λ q) (hΩt : ‖Ωt‖ = 1)
    (E : Finset (FiniteProduct.Configuration (fun _ : Site Λ ↦ Fin q)
      (S.A.filter fun x ↦ x.val ∈ T))) (w : ℝ)
    (hz : 0 < (reducedState_isHermitian Λ q Ωt
      (S.A.filter fun x ↦ x.val ∈ T)).spectralRestrictionMass E)
    (hE : ∀ i ∈ E,
      Real.exp (-regionalEntropy Λ q Ωt (S.A.filter fun x ↦ x.val ∈ T) - w) ≤
          (reducedState_isHermitian Λ q Ωt (S.A.filter fun x ↦ x.val ∈ T)).eigenvalues i ∧
        (reducedState_isHermitian Λ q Ωt (S.A.filter fun x ↦ x.val ∈ T)).eigenvalues i ≤
          Real.exp (-regionalEntropy Λ q Ωt (S.A.filter fun x ↦ x.val ∈ T) + w))
    (s : Fin (S.n * S.m)) (p : ℝ) :
    let β := fun _ : Site Λ ↦ Fin q
    let X := S.A.filter fun x ↦ x.val ∈ T
    let z := (reducedState_isHermitian Λ q Ωt X).spectralRestrictionMass E
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (FiniteProduct.splitEquiv β X) Ωt
    let ψ : FiniteProduct.Configuration β Xᶜ × Fin E.card → ℂ := fun x ↦
      compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    let Sent := vonNeumannEntropy (Matrix.partialTraceLeft (Matrix.vecMulVec ψ (star ψ)))
      (Matrix.posSemidef_vecMulVec_self_star ψ).partialTraceLeft.isHermitian
    let σ := terminalPartition S (S.n * S.m)
    let Q := fun j g ↦ receiving (σ j g) false
    let Y := fun j g ↦ middle (σ j g)
    let gpre := fun j g ↦ FiniteProduct.entropy β Ωt (Q j g) +
      FiniteProduct.entropy β Ωt (Q j g ∪ Y j g)ᶜ - FiniteProduct.entropy β Ωt (Y j g)
    let gpost := fun j g ↦ regionalEntropy Λ q Ωt (positiveNear S.depth (σ j g)) +
      regionalEntropy Λ q Ωt (positiveNearMiddle S.depth (σ j g)) -
      regionalEntropy Λ q Ωt (middle (σ j g))
    let tree := ((S.actualChargeData hm hM s.val).tree
      (Set.projIcc (0 : ℝ) 1 zero_le_one p)).map
        (chargeTerminalIndex S.K S.m S.M (S.n * S.m) s)
    let Gpre := (∑ g, ∑ j, tree.weight j * gpre j g) / (S.K : ℝ)
    let Gpost := (∑ g, ∑ j, tree.weight j * gpost j g) / (S.K : ℝ)
    2 * FiniteProduct.mutualInformation β Ωt X (S.truncationSet L)ᶜ ≤
      2 * Sent + Gpre - Gpost + 2 * (w - Real.log z) ∧
    ∀ Ω : StateSpace Λ q, ‖Ω‖ = 1 →
      2 * FiniteProduct.mutualInformation β Ω X (S.truncationSet L)ᶜ ≤
        2 * Sent + Gpre - Gpost + 2 * (w - Real.log z) +
          16 * Real.sqrt (Matrix.traceDistance
            (Matrix.vecMulVec Ωt.ofLp (star Ωt.ofLp))
            (Matrix.vecMulVec Ω.ofLp (star Ω.ofLp))) *
              Real.log (Real.exp 1 * Fintype.card (FiniteProduct.Configuration β X)) := by
  classical
  intro β X z ΩX ψ Sent σ Q Y gpre gpost tree Gpre Gpost
  have hMI := two_mutualInformation_le_actualTerminal_average hT S hdepth hK
    (S.n * S.m) L hL Ωt tree
  have hselected := (abs_log_card_and_selectedSchmidtEntropy_sub_le Ωt hΩt X E w hz hE).2
  change |Sent - regionalEntropy Λ q Ωt X| ≤ w - Real.log z at hselected
  have htarget := (abs_le.mp hselected).1
  have htruncated :
      2 * FiniteProduct.mutualInformation β Ωt X (S.truncationSet L)ᶜ ≤
        2 * Sent + Gpre - Gpost + 2 * (w - Real.log z) := by
    change 2 * FiniteProduct.mutualInformation β Ωt X (S.truncationSet L)ᶜ ≤
      2 * regionalEntropy Λ q Ωt X + Gpre - Gpost at hMI
    linarith only [hMI, htarget]
  refine ⟨htruncated, ?_⟩
  intro Ω hΩ
  have hXoutside : Disjoint X (S.truncationSet L)ᶜ := by
    refine Finset.disjoint_left.mpr fun x hx hout ↦ ?_
    have hd : S.depth x ≤ 0 := by
      simpa only [hdepth, Nat.cast_zero] using
        (ambientDepth_le_iff_mem_dilation T hT x.val 0).mpr
          ((ambientDilation_zero T).symm ▸ (Finset.mem_filter.mp hx).2)
    exact (Finset.mem_compl.mp hout) (Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hx).1, hd.trans (Nat.cast_nonneg L)⟩)
  have hcontinuity := (abs_le.mp
    (FiniteProduct.abs_mutualInformation_sub_le_of_traceDistance β hΩt hΩ hXoutside)).1
  linarith only [htruncated, hcontinuity]

end TNLean.PEPS.AreaLaw.Scan.CollarScan
