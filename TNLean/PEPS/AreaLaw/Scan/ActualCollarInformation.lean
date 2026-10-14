/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualTerminalCollarGeometry
import TNLean.PEPS.AreaLaw.CollarInformation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

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
-/

noncomputable section

open Matrix
open scoped BigOperators

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
    let β := fun _ : Site Λ ↦ Fin q
    let X := S.A.filter fun x ↦ x.val ∈ T
    let σ := terminalPartition S H j g
    let Q := receiving σ false
    let Y := middle σ
    let V := receiving σ true
    let gpre := FiniteProduct.entropy β Ωt Q + FiniteProduct.entropy β Ωt (Q ∪ Y)ᶜ -
      FiniteProduct.entropy β Ωt Y
    let gpost := regionalEntropy Λ q Ωt (positiveNear S.depth σ) +
      regionalEntropy Λ q Ωt (positiveNearMiddle S.depth σ) - regionalEntropy Λ q Ωt Y
    2 * regionalEntropy Λ q Ωt X + gpre - gpost =
      FiniteProduct.mutualInformation β Ωt X V +
        FiniteProduct.mutualInformation β Ωt X (Y ∪ V) := by
  classical
  intro β X σ Q Y V gpre gpost
  obtain ⟨hnear, hUYeq, hfar, hXU, hXY, hXV, hUY, hUV, hYV, hcover, _⟩ :=
    terminalPartition_collar_geometry hT S hdepth H L hL j g
  change Q = X ∪ positiveNear S.depth σ at hnear
  change positiveNear S.depth σ ∪ Y = positiveNearMiddle S.depth σ at hUYeq
  change V = (Q ∪ Y)ᶜ at hfar
  have hpre : FiniteProduct.collarPreQuantity β Ωt X (positiveNear S.depth σ) Y V =
      gpre := by
    change FiniteProduct.entropy β Ωt (X ∪ positiveNear S.depth σ) +
      FiniteProduct.entropy β Ωt V - FiniteProduct.entropy β Ωt Y =
      FiniteProduct.entropy β Ωt Q + FiniteProduct.entropy β Ωt (Q ∪ Y)ᶜ -
        FiniteProduct.entropy β Ωt Y
    rw [← hnear, hfar]
  have hpost : FiniteProduct.collarPostQuantity β Ωt (positiveNear S.depth σ) Y =
      gpost := by
    unfold FiniteProduct.collarPostQuantity
    rw [hUYeq]
    simp only [gpost, regionalEntropy_eq_finiteProduct]
  have hid : 2 * FiniteProduct.entropy β Ωt X +
      (FiniteProduct.collarPreQuantity β Ωt X (positiveNear S.depth σ) Y V -
        FiniteProduct.collarPostQuantity β Ωt (positiveNear S.depth σ) Y) =
      FiniteProduct.mutualInformation β Ωt X V +
        FiniteProduct.mutualInformation β Ωt X (Y ∪ V) :=
    FiniteProduct.collarLeaf_entropy_identity β Ωt hXU hXY hXV hUY hUV hYV hcover
  rw [hpre, hpost] at hid
  simpa only [regionalEntropy_eq_finiteProduct, sub_eq_add_neg, add_assoc] using hid

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
    let β := fun _ : Site Λ ↦ Fin q
    let X := S.A.filter fun x ↦ x.val ∈ T
    let σ := terminalPartition S H
    let Q := fun j g ↦ receiving (σ j g) false
    let Y := fun j g ↦ middle (σ j g)
    let gpre := fun j g ↦ FiniteProduct.entropy β Ωt (Q j g) +
      FiniteProduct.entropy β Ωt (Q j g ∪ Y j g)ᶜ - FiniteProduct.entropy β Ωt (Y j g)
    let gpost := fun j g ↦ regionalEntropy Λ q Ωt (positiveNear S.depth (σ j g)) +
      regionalEntropy Λ q Ωt (positiveNearMiddle S.depth (σ j g)) -
      regionalEntropy Λ q Ωt (middle (σ j g))
    let Gpre := (∑ g, ∑ j, tree.weight j * gpre j g) / (S.K : ℝ)
    let Gpost := (∑ g, ∑ j, tree.weight j * gpost j g) / (S.K : ℝ)
    2 * FiniteProduct.mutualInformation β Ωt X (S.truncationSet L)ᶜ ≤
      2 * regionalEntropy Λ q Ωt X + Gpre - Gpost := by
  classical
  intro β X σ Q Y gpre gpost Gpre Gpost
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
  have hpre (j) (g) : FiniteProduct.collarPreQuantity β Ωt X (U j g) (Y j g) (V j g) =
      gpre j g := by
    change FiniteProduct.entropy β Ωt (X ∪ U j g) + FiniteProduct.entropy β Ωt (V j g) -
      FiniteProduct.entropy β Ωt (Y j g) =
      FiniteProduct.entropy β Ωt (Q j g) + FiniteProduct.entropy β Ωt (Q j g ∪ Y j g)ᶜ -
        FiniteProduct.entropy β Ωt (Y j g)
    rw [← (hgeom j g).1, (hgeom j g).2.2.1]
  have hpost (j) (g) : FiniteProduct.collarPostQuantity β Ωt (U j g) (Y j g) =
      gpost j g := by
    unfold FiniteProduct.collarPostQuantity
    rw [(hgeom j g).2.1]
    simp only [gpost, U, Y, regionalEntropy_eq_finiteProduct]
  have hband (g : Fin S.K) :
      2 * FiniteProduct.mutualInformation β Ωt X (S.truncationSet L)ᶜ ≤
        2 * regionalEntropy Λ q Ωt X +
          ∑ j, tree.weight j * (gpre j g - gpost j g) := by
    have havg := FiniteProduct.two_mutualInformation_le_collarLeaf_average β Ωt
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
    simpa only [hpre, hpost, regionalEntropy_eq_finiteProduct] using havg
  exact band_average_le hK tree.weight gpre gpost
    (2 * FiniteProduct.mutualInformation β Ωt X (S.truncationSet L)ᶜ)
    (2 * regionalEntropy Λ q Ωt X) hband

end TNLean.PEPS.AreaLaw.Scan.CollarScan
