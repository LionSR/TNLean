/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.NormComparisons.ActualTerminalCollarGeometry
import TNLean.PEPS.AreaLaw.CollarInformation.CollarInformation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import TNLean.PEPS.AreaLaw.Regions.SelectedSchmidtEntropyBounds

/-!
# The mutual information measured by the actual sharp entropy expression

The exact terminal quantities in the actual sharp comparison are the collar
leaf quantities from the accepted pure-state entropy identity. Every terminal
far region contains the complement of the same compact truncation set.
The existing weighted mutual-information bound therefore applies to every
actual terminal mean tree, with its weights unchanged, and survives the
uniform average over the original bands.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 868--873 and 900--911, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## The actual selected sharp expression controls physical mutual information

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

section

noncomputable section

open Matrix
open scoped BigOperators
open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open ActualTerminals

/-- Average a scalar band inequality without normalizing its entropy-valued inputs. -/
private theorem band_average_le {K : ℕ} (hK : 0 < K) {J : Type*} [Fintype J]
    (p : J → ℝ) (pre post : J → Fin K → ℝ) (M C : ℝ)
    (hband : ∀ g, M ≤ C + ∑ j, p j * (pre j g - post j g)) :
    M ≤ C + (∑ g, ∑ j, p j * pre j g) / (K : ℝ) -
      (∑ g, ∑ j, p j * post j g) / (K : ℝ) := by
  classical
  have hsum := Finset.sum_le_sum (fun g (_ : g ∈ (Finset.univ : Finset (Fin K))) ↦
    hband g)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_sub, Finset.sum_sub_distrib] at hsum
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  calc
    M ≤ ((K : ℝ) * C + ((∑ g, ∑ j, p j * pre j g) -
        (∑ g, ∑ j, p j * post j g))) / (K : ℝ) := by
      apply (le_div_iff₀ hKr).mpr
      rw [mul_comm M (K : ℝ)]
      exact hsum
    _ = C + (∑ g, ∑ j, p j * pre j g) / (K : ℝ) -
        (∑ g, ∑ j, p j * post j g) / (K : ℝ) := by
      field_simp [hKr.ne']
      ring

open Classical in
/-- The literal completed or pre-charge terminal expression equals the two
far-side mutual informations. No selected state or probability law is chosen.
Source: `08-scanner.tex`, lines 900--905. -/
theorem terminalPartition_collar_entropy_identity
    {I : Type} [Fintype I] [LinearOrder I] {Λ T : Finset (ℤ × ℤ)} {q : ℕ}
    (hT : T.Nonempty) (S : CollarScan (Site Λ) I)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (H L : ℕ) (hL : 8 * S.K * S.m ≤ L) (Ωt : StateSpace Λ q)
    (j : terminalFamily S.K S.m S.M H) (g : Fin S.K) :
    let X := S.A.filter fun x ↦ x.val ∈ T
    let σ := terminalPartition S H j g
    let Q := receiving σ false
    let Y := middle σ
    let V := receiving σ true
    let gpre := ManyBody.regionEntropy Ωt Q + ManyBody.regionEntropy Ωt (Q ∪ Y)ᶜ -
      ManyBody.regionEntropy Ωt Y
    let gpost := ManyBody.regionEntropy Ωt (positiveNear S.depth σ) +
      ManyBody.regionEntropy Ωt (positiveNearMiddle S.depth σ) - ManyBody.regionEntropy Ωt Y
    2 * ManyBody.regionEntropy Ωt X + gpre - gpost =
      ManyBody.regionMutualInformation Ωt X V +
        ManyBody.regionMutualInformation Ωt X (Y ∪ V) := by
  classical
  intro X σ Q Y V gpre gpost
  let β := fun _ : Site Λ ↦ Fin q
  obtain ⟨hnear, hUYeq, hfar, hXU, hXY, hXV, hUY, hUV, hYV, hcover, _⟩ :=
    terminalPartition_collar_geometry hT S hdepth H L hL j g
  change Q = X ∪ positiveNear S.depth σ at hnear
  change positiveNear S.depth σ ∪ Y = positiveNearMiddle S.depth σ at hUYeq
  change V = (Q ∪ Y)ᶜ at hfar
  have hpre : ManyBody.collarPreQuantity β Ωt X (positiveNear S.depth σ) Y V =
      gpre := by
    change ManyBody.regionEntropy Ωt (X ∪ positiveNear S.depth σ) +
      ManyBody.regionEntropy Ωt V - ManyBody.regionEntropy Ωt Y =
      ManyBody.regionEntropy Ωt Q + ManyBody.regionEntropy Ωt (Q ∪ Y)ᶜ -
        ManyBody.regionEntropy Ωt Y
    rw [← hnear, hfar]
  have hpost : ManyBody.collarPostQuantity β Ωt (positiveNear S.depth σ) Y =
      gpost := by
    unfold ManyBody.collarPostQuantity
    rw [hUYeq]
  have hid : 2 * ManyBody.regionEntropy Ωt X +
      (ManyBody.collarPreQuantity β Ωt X (positiveNear S.depth σ) Y V -
        ManyBody.collarPostQuantity β Ωt (positiveNear S.depth σ) Y) =
      ManyBody.regionMutualInformation Ωt X V +
        ManyBody.regionMutualInformation Ωt X (Y ∪ V) :=
    ManyBody.collarLeaf_regionEntropy_identity β Ωt hXU hXY hXV hUY hUV hYV hcover
  rw [hpre, hpost] at hid
  simpa only [sub_eq_add_neg, add_assoc] using hid

open Classical in
/-- The exact terminal-tree and band average bounds twice the mutual
information with the outside of the same physical truncation set. The tree
is supplied unchanged; in the selected application it is the mapped actual
charge tree at the already selected stage and parameter.
Source: `08-scanner.tex`, lines 906--911. -/
theorem two_mutualInformation_le_actualTerminal_average
    {I : Type} [Fintype I] [LinearOrder I] {Λ T : Finset (ℤ × ℤ)} {q : ℕ}
    (hT : T.Nonempty) (S : CollarScan (Site Λ) I)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (hK : 0 < S.K) (H L : ℕ) (hL : 8 * S.K * S.m ≤ L)
    (Ωt : StateSpace Λ q) (tree : MeanTree (terminalFamily S.K S.m S.M H)) :
    let X := S.A.filter fun x ↦ x.val ∈ T
    let σ := terminalPartition S H
    let Q := fun j g ↦ receiving (σ j g) false
    let Y := fun j g ↦ middle (σ j g)
    let gpre := fun j g ↦ ManyBody.regionEntropy Ωt (Q j g) +
      ManyBody.regionEntropy Ωt (Q j g ∪ Y j g)ᶜ - ManyBody.regionEntropy Ωt (Y j g)
    let gpost := fun j g ↦ ManyBody.regionEntropy Ωt (positiveNear S.depth (σ j g)) +
      ManyBody.regionEntropy Ωt (positiveNearMiddle S.depth (σ j g)) -
      ManyBody.regionEntropy Ωt (middle (σ j g))
    let Gpre := (∑ g, ∑ j, tree.weight j * gpre j g) / (S.K : ℝ)
    let Gpost := (∑ g, ∑ j, tree.weight j * gpost j g) / (S.K : ℝ)
    2 * ManyBody.regionMutualInformation Ωt X (S.truncationSet L)ᶜ ≤
      2 * ManyBody.regionEntropy Ωt X + Gpre - Gpost := by
  classical
  intro X σ Q Y gpre gpost Gpre Gpost
  let β := fun _ : Site Λ ↦ Fin q
  let U := fun j g ↦ positiveNear S.depth (σ j g)
  let V := fun j g ↦ receiving (σ j g) true
  have hgeom (j) (g) :
      Q j g = X ∪ U j g ∧
        U j g ∪ Y j g = positiveNearMiddle S.depth (σ j g) ∧
        V j g = (Q j g ∪ Y j g)ᶜ ∧
        Disjoint X (U j g) ∧ Disjoint X (Y j g) ∧ Disjoint X (V j g) ∧
        Disjoint (U j g) (Y j g) ∧ Disjoint (U j g) (V j g) ∧
        Disjoint (Y j g) (V j g) ∧ X ∪ U j g ∪ Y j g ∪ V j g = Finset.univ ∧
        (S.truncationSet L)ᶜ ⊆ V j g :=
    terminalPartition_collar_geometry hT S hdepth H L hL j g
  have hpre (j) (g) : ManyBody.collarPreQuantity β Ωt X (U j g) (Y j g) (V j g) =
      gpre j g := by
    change ManyBody.regionEntropy Ωt (X ∪ U j g) + ManyBody.regionEntropy Ωt (V j g) -
      ManyBody.regionEntropy Ωt (Y j g) =
      ManyBody.regionEntropy Ωt (Q j g) + ManyBody.regionEntropy Ωt (Q j g ∪ Y j g)ᶜ -
        ManyBody.regionEntropy Ωt (Y j g)
    rw [← (hgeom j g).1, (hgeom j g).2.2.1]
  have hpost (j) (g) : ManyBody.collarPostQuantity β Ωt (U j g) (Y j g) =
      gpost j g := by
    unfold ManyBody.collarPostQuantity
    rw [(hgeom j g).2.1]
  have hband (g : Fin S.K) :
      2 * ManyBody.regionMutualInformation Ωt X (S.truncationSet L)ᶜ ≤
        2 * ManyBody.regionEntropy Ωt X +
          ∑ j, tree.weight j * (gpre j g - gpost j g) := by
    have havg := ManyBody.two_regionMutualInformation_le_collarLeaf_average β Ωt
      Finset.univ tree.weight (fun j _ ↦ tree.weight_nonneg j)
      (by simpa using tree.sum_weight) X (S.truncationSet L)ᶜ
      (fun j ↦ U j g) (fun j ↦ Y j g) (fun j ↦ V j g)
      (fun j _ ↦ (hgeom j g).2.2.2.1)
      (fun j _ ↦ (hgeom j g).2.2.2.2.1)
      (fun j _ ↦ (hgeom j g).2.2.2.2.2.1)
      (fun j _ ↦ (hgeom j g).2.2.2.2.2.2.1)
      (fun j _ ↦ (hgeom j g).2.2.2.2.2.2.2.1)
      (fun j _ ↦ (hgeom j g).2.2.2.2.2.2.2.2.1)
      (fun j _ ↦ (hgeom j g).2.2.2.2.2.2.2.2.2.1)
      (fun j _ ↦ (hgeom j g).2.2.2.2.2.2.2.2.2.2)
    simpa only [hpre, hpost] using havg
  exact band_average_le hK tree.weight gpre gpost
    (2 * ManyBody.regionMutualInformation Ωt X (S.truncationSet L)ᶜ)
    (2 * ManyBody.regionEntropy Ωt X) hband

end TNLean.PEPS.AreaLaw.Scan.CollarScan
end

end

section

noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
open TNLean.Lattice

open ManyBody (ambientDilation_zero)

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
    (E : Finset (ManyBody.RegionConfig (fun _ : Site Λ ↦ Fin q)
      (S.A.filter fun x ↦ x.val ∈ T))) (w : ℝ)
    (hz : 0 < (ManyBody.regionState_isHermitian (S.A.filter fun x ↦ x.val ∈ T)
      Ωt).spectralRestrictionMass E)
    (hE : ∀ i ∈ E,
      Real.exp (-ManyBody.regionEntropy Ωt (S.A.filter fun x ↦ x.val ∈ T) - w) ≤
          (ManyBody.regionState_isHermitian (S.A.filter fun x ↦ x.val ∈ T) Ωt).eigenvalues i ∧
        (ManyBody.regionState_isHermitian (S.A.filter fun x ↦ x.val ∈ T) Ωt).eigenvalues i ≤
          Real.exp (-ManyBody.regionEntropy Ωt (S.A.filter fun x ↦ x.val ∈ T) + w))
    (s : Fin (S.n * S.m)) (p : ℝ) :
    let β := fun _ : Site Λ ↦ Fin q
    let X := S.A.filter fun x ↦ x.val ∈ T
    let z := (ManyBody.regionState_isHermitian X Ωt).spectralRestrictionMass E
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (ManyBody.cutEquiv β X) Ωt
    let ψ : ManyBody.ComplConfig β X × Fin E.card → ℂ := fun x ↦
      compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    let Sent := vonNeumannEntropy (Matrix.partialTraceLeft (Matrix.vecMulVec ψ (star ψ)))
      (Matrix.posSemidef_vecMulVec_self_star ψ).partialTraceLeft.isHermitian
    let σ := terminalPartition S (S.n * S.m)
    let Q := fun j g ↦ receiving (σ j g) false
    let Y := fun j g ↦ middle (σ j g)
    let gpre := fun j g ↦ ManyBody.regionEntropy Ωt (Q j g) +
      ManyBody.regionEntropy Ωt (Q j g ∪ Y j g)ᶜ - ManyBody.regionEntropy Ωt (Y j g)
    let gpost := fun j g ↦ ManyBody.regionEntropy Ωt (positiveNear S.depth (σ j g)) +
      ManyBody.regionEntropy Ωt (positiveNearMiddle S.depth (σ j g)) -
      ManyBody.regionEntropy Ωt (middle (σ j g))
    let tree := ((S.actualChargeData hm hM s.val).tree
      (Set.projIcc (0 : ℝ) 1 zero_le_one p)).map
        (chargeTerminalIndex S.K S.m S.M (S.n * S.m) s)
    let Gpre := (∑ g, ∑ j, tree.weight j * gpre j g) / (S.K : ℝ)
    let Gpost := (∑ g, ∑ j, tree.weight j * gpost j g) / (S.K : ℝ)
    2 * ManyBody.regionMutualInformation Ωt X (S.truncationSet L)ᶜ ≤
      2 * Sent + Gpre - Gpost + 2 * (w - Real.log z) ∧
    ∀ Ω : StateSpace Λ q, ‖Ω‖ = 1 →
      2 * ManyBody.regionMutualInformation Ω X (S.truncationSet L)ᶜ ≤
        2 * Sent + Gpre - Gpost + 2 * (w - Real.log z) +
          16 * Real.sqrt (Matrix.traceDistance
            (Matrix.vecMulVec Ωt.ofLp (star Ωt.ofLp))
            (Matrix.vecMulVec Ω.ofLp (star Ω.ofLp))) *
              Real.log (Real.exp 1 * Fintype.card (ManyBody.RegionConfig β X)) := by
  classical
  intro β X z ΩX ψ Sent σ Q Y gpre gpost tree Gpre Gpost
  have hMI := two_mutualInformation_le_actualTerminal_average hT S hdepth hK
    (S.n * S.m) L hL Ωt tree
  have hselected := (abs_log_card_and_selectedSchmidtEntropy_sub_le Ωt hΩt X E w hz hE).2
  change |Sent - ManyBody.regionEntropy Ωt X| ≤ w - Real.log z at hselected
  have htarget := (abs_le.mp hselected).1
  have htruncated :
      2 * ManyBody.regionMutualInformation Ωt X (S.truncationSet L)ᶜ ≤
        2 * Sent + Gpre - Gpost + 2 * (w - Real.log z) := by
    change 2 * ManyBody.regionMutualInformation Ωt X (S.truncationSet L)ᶜ ≤
      2 * ManyBody.regionEntropy Ωt X + Gpre - Gpost at hMI
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
    (ManyBody.abs_regionMutualInformation_sub_le_of_traceDistance β hΩt hΩ hXoutside)).1
  linarith only [htruncated, hcontinuity]

end TNLean.PEPS.AreaLaw.Scan.CollarScan
end

end
