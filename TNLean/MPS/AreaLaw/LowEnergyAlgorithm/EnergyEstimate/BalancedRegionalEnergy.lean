/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.EnergyEstimate.SoftWordNodeEnergy
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTree.BalancedIntervalTree
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTree.IntervalSamplingChoices
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTree.CanonicalIntervalSamplingTree

/-!
# Recursive energy estimates on a fixed interval tree

The retained spaces and their operator families are fixed before assigning
energy estimates. Short leaves use actual attained minima. At every long
node, the scalar is the actual raw compressed minimum on the same family's
one-word child image, minus three. All assigned estimates have one-sided
error at most 49/16.

This is a corrected auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, line 1631, and the energy proof at line 1807.
**Local fix (recursive one-sided estimates):** The raw compressed minimum
is biased downward by three and the middle center uses the exact collar
minima. The family is not identified with literal soft Generate; no
running-time conclusion follows. See
`docs/paper-gaps/alvv16_soft_regional_energy_centering.tex`.

## Energy estimates on the actual successful sampled root subtree

The actual sampled root and its listed descendants are the only spaces
assumed viable. The same targets and operator families then determine one
scalar energy function, with attained minima at used short leaves and
literal raw compressed updates at used long nodes. No viability or raw
update is asserted at overlapping intervals outside this root subtree.

This is a corrected conditional auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, line 1631, and line 1807.
**Scope restriction (fixed family and actual joint success):** The calibrated
target and word certificates precede the sampling choices; joint viability
is required only for the actual root subtree. The family is hard-clipped,
not identified with literal soft Generate, and no running time is asserted.
See `docs/paper-gaps/alvv16_soft_regional_energy_centering.tex`.

## Root energy estimates from calibrated operator words

The original spectral minimum and a calibrated word family determine one
energy function on a successful canonical root subtree. This auxiliary
concerns the tree before final filtering and Ritz extraction.

Source: ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1631 and 1807.
**Scope restriction (calibrated hard-clipped family):** The family and its
word bounds are supplied, and viability is required on the actual root
subtree. This is an auxiliary to the physical construction, not literal
soft Generate; see `docs/paper-gaps/alvv16_soft_regional_energy_centering.tex`.
-/

section

open ManyBody (interval)

open Matrix
open scoped BigOperators TensorProduct InnerProductSpace ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

/-- A realized node update uses the estimates already assigned to its two
children, actual attained collar minima, and the same family's raw compressed
minimum. Corrected auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, line 1631. -/
def IsSoftWordNodeEnergyRealization {L q N l k u v r : ℕ} (hq : 0 < q)
    (hlk : l ≤ k) (hkr : k ≤ r)
    (Φ : ManyBody.BondInteraction L q)
    (F : Fin N → EuclideanSpace ℂ (interval L l r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L l r → Fin q))
    (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L l k → Fin q)))
    (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k r → Fin q)))
    (p1 p2 p : ℝ) : Prop :=
  ∃ (eLeft eRight : ℝ) (xLeft xRight : (Fin L → Fin q) → ℂ),
    star xLeft ⬝ᵥ xLeft = 1 ∧
    ManyBody.BondInteraction.threeRegionHamiltonians l u Φ 1 *ᵥ xLeft = (eLeft : ℂ) • xLeft ∧
    (ManyBody.BondInteraction.threeRegionHamiltonians l u Φ 1 - (eLeft : ℂ) • 1).PosSemidef ∧
    star xRight ⬝ᵥ xRight = 1 ∧
    ManyBody.BondInteraction.threeRegionHamiltonians v r Φ 1 *ᵥ xRight = (eRight : ℂ) • xRight ∧
    (ManyBody.BondInteraction.threeRegionHamiltonians v r Φ 1 - (eRight : ℂ) • 1).PosSemidef ∧
    IsRegionalLowerEnergyEstimate Φ u v 10 (p1 + p2 - eLeft - eRight - 2) ∧
    IsSoftWordEnergyUpdate (u := u) (v := v) hq hlk hkr Φ F S1 S2
      (p1 + p2 - eLeft - eRight - 2) p

private theorem realize_node_update {L q N l k u v r : ℕ} (hq : 0 < q)
    (hlk : l ≤ k) (hkr : k ≤ r)
    (Φ : ManyBody.BondInteraction L q)
    (F : Fin N → EuclideanSpace ℂ (interval L l r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L l r → Fin q))
    (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L l k → Fin q)))
    (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k r → Fin q)))
    (hn : HasSoftWordNodeEnergyUpdate (u := u) (v := v) hq hlk hkr Φ F S1 S2)
    (p1 p2 : ℝ) (hp1 : IsRegionalLowerEnergyEstimate Φ l k (49 / 16) p1)
    (hp2 : IsRegionalLowerEnergyEstimate Φ k r (49 / 16) p2) :
    ∃ p : ℝ, IsRegionalLowerEnergyEstimate Φ l r (49 / 16) p ∧
      IsSoftWordNodeEnergyRealization (u := u) (v := v) hq hlk hkr Φ F S1 S2 p1 p2 p := by
  obtain ⟨eL, eR, xL, xR, hxL, hL, hLmin, hxR, hR, hRmin, hupdate⟩ := hn
  obtain ⟨hcenter, p, hp, hraw⟩ := hupdate p1 p2 hp1 hp2
  exact ⟨p, hp, eL, eR, xL, xR, hxL, hL, hLmin, hxR, hR, hRmin, hcenter, hraw⟩

private theorem exists_leaf_energy {L q : ℕ} (hq : 0 < q)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (l r : ℕ) (hlr : l ≤ r) (hrL : r ≤ L) :
    ∃ p : ℝ, IsRegionalLowerEnergyEstimate Φ l r 0 p := by
  obtain ⟨eA, _eB, _eP, x, _z, hx, hAx, _hBx, hA, _hB, _rest⟩ :=
    exists_adjacent_interval_energy_merge hq hlr le_rfl hrL Φ h0 h1
  exact ⟨eA, eA, x, hx, hAx, hA, by simp, le_rfl⟩

private noncomputable def recursiveEnergy {L q : ℕ}
    (Φ : ManyBody.BondInteraction L q)
    (width : ℕ) (hwidth : 1 ≤ width)
    (R : ∀ (l r : ℕ), l ≤ r → r ≤ L → width < r - l → ℝ → ℝ → ℝ → Prop)
    (hleaf : ∀ (l r : ℕ), l ≤ r → r ≤ L →
      ∃ p : ℝ, IsRegionalLowerEnergyEstimate Φ l r 0 p)
    (hnode : ∀ (l r : ℕ) (hlr : l ≤ r) (hrL : r ≤ L) (hlong : width < r - l),
      let k := l + (r - l) / 2
      ∀ p1 p2 : ℝ,
        IsRegionalLowerEnergyEstimate Φ l k (49 / 16) p1 →
        IsRegionalLowerEnergyEstimate Φ k r (49 / 16) p2 →
        ∃ p : ℝ, IsRegionalLowerEnergyEstimate Φ l r (49 / 16) p ∧
          R l r hlr hrL hlong p1 p2 p)
    (l r : ℕ) (hlr : l ≤ r) (hrL : r ≤ L) :
    {p : ℝ // IsRegionalLowerEnergyEstimate Φ l r (49 / 16) p} :=
  if hshort : r - l ≤ width then
    ⟨Classical.choose (hleaf l r hlr hrL), by
      obtain ⟨e, x, hx, hAx, hA, hpLower, hpUpper⟩ :=
        Classical.choose_spec (hleaf l r hlr hrL)
      exact ⟨e, x, hx, hAx, hA, by linarith only [hpLower], hpUpper⟩⟩
  else
    let k := l + (r - l) / 2
    let p1 := recursiveEnergy Φ width hwidth R hleaf hnode l k (by omega) (by omega)
    let p2 := recursiveEnergy Φ width hwidth R hleaf hnode k r (by omega) hrL
    let choice := hnode l r hlr hrL (by omega) p1.val p2.val p1.property p2.property
    ⟨Classical.choose choice, (Classical.choose_spec choice).1⟩
termination_by r - l
decreasing_by all_goals omega

private theorem recursiveEnergy_node {L q : ℕ}
    (Φ : ManyBody.BondInteraction L q)
    (width : ℕ) (hwidth : 1 ≤ width)
    (R : ∀ (l r : ℕ), l ≤ r → r ≤ L → width < r - l → ℝ → ℝ → ℝ → Prop)
    (hleaf : ∀ (l r : ℕ), l ≤ r → r ≤ L →
      ∃ p : ℝ, IsRegionalLowerEnergyEstimate Φ l r 0 p)
    (hnode : ∀ (l r : ℕ) (hlr : l ≤ r) (hrL : r ≤ L) (hlong : width < r - l),
      let k := l + (r - l) / 2
      ∀ p1 p2 : ℝ,
        IsRegionalLowerEnergyEstimate Φ l k (49 / 16) p1 →
        IsRegionalLowerEnergyEstimate Φ k r (49 / 16) p2 →
        ∃ p : ℝ, IsRegionalLowerEnergyEstimate Φ l r (49 / 16) p ∧
          R l r hlr hrL hlong p1 p2 p)
    (l r : ℕ) (hlr : l ≤ r) (hrL : r ≤ L) (hlong : width < r - l) :
    let k := l + (r - l) / 2
    let hpk : l ≤ k := by dsimp only [k]; omega
    let hkr : k ≤ r := by dsimp only [k]; omega
    R l r hlr hrL hlong
      (recursiveEnergy Φ width hwidth R hleaf hnode l k hpk (hkr.trans hrL)).val
      (recursiveEnergy Φ width hwidth R hleaf hnode k r hkr hrL).val
      (recursiveEnergy Φ width hwidth R hleaf hnode l r hlr hrL).val := by
  intro k hpk hkr
  let left := recursiveEnergy Φ width hwidth R hleaf hnode l k hpk (hkr.trans hrL)
  let right := recursiveEnergy Φ width hwidth R hleaf hnode k r hkr hrL
  let choice := hnode l r hlr hrL hlong left.val right.val left.property right.property
  have hvalue : (recursiveEnergy Φ width hwidth R hleaf hnode l r hlr hrL).val =
      Classical.choose choice := by
    rw [recursiveEnergy]
    split
    · omega
    · rfl
  rw [hvalue]
  exact (Classical.choose_spec choice).2

/-- Actual short-leaf minima and an explicit energy-preserving node relation
construct one simultaneous scalar assignment at the balanced children. The
relation is arbitrary; no particular filtering or sampling construction is
assumed. Auxiliary to ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, line 1631. -/
theorem exists_energy_with_node_relation {L q : ℕ}
    (Φ : ManyBody.BondInteraction L q)
    (width : ℕ) (hwidth : 1 ≤ width)
    (R : ∀ (l r : ℕ), l ≤ r → r ≤ L → width < r - l → ℝ → ℝ → ℝ → Prop)
    (hleaf : ∀ (l r : ℕ), l ≤ r → r ≤ L →
      ∃ p : ℝ, IsRegionalLowerEnergyEstimate Φ l r 0 p)
    (hnode : ∀ (l r : ℕ) (hlr : l ≤ r) (hrL : r ≤ L) (hlong : width < r - l),
      let k := l + (r - l) / 2
      ∀ p1 p2 : ℝ,
        IsRegionalLowerEnergyEstimate Φ l k (49 / 16) p1 →
        IsRegionalLowerEnergyEstimate Φ k r (49 / 16) p2 →
        ∃ p : ℝ, IsRegionalLowerEnergyEstimate Φ l r (49 / 16) p ∧
          R l r hlr hrL hlong p1 p2 p)
 :
    ∃ estimate : ℕ → ℕ → ℝ,
      (∀ (l r : ℕ), l ≤ r → r ≤ L →
        IsRegionalLowerEnergyEstimate Φ l r (49 / 16) (estimate l r)) ∧
      (∀ (l r : ℕ), l ≤ r → r ≤ L → r - l ≤ width →
        IsRegionalLowerEnergyEstimate Φ l r 0 (estimate l r)) ∧
      ∀ (l r : ℕ) (hlr : l ≤ r) (hrL : r ≤ L) (hlong : width < r - l),
        let k := l + (r - l) / 2
        R l r hlr hrL hlong (estimate l k) (estimate k r) (estimate l r) := by
  classical
  let values := recursiveEnergy Φ width hwidth R hleaf hnode
  let estimate := fun l r : ℕ ↦ if valid : l ≤ r ∧ r ≤ L then
    (values l r valid.1 valid.2).val else 0
  have heval (l r : ℕ) (hlr : l ≤ r) (hrL : r ≤ L) :
      estimate l r = (values l r hlr hrL).val := by
    simp only [estimate, dite_eq_left (show l ≤ r ∧ r ≤ L from ⟨hlr, hrL⟩)]
  refine ⟨estimate, ?_, ?_, ?_⟩
  · intro l r hlr hrL
    rw [heval l r hlr hrL]
    exact (values l r hlr hrL).property
  · intro l r hlr hrL hshort
    rw [heval l r hlr hrL]
    change IsRegionalLowerEnergyEstimate Φ l r 0
      (recursiveEnergy Φ width hwidth R hleaf hnode l r hlr hrL).val
    rw [recursiveEnergy]
    split
    · exact Classical.choose_spec (hleaf l r hlr hrL)
    · contradiction
  · intro l r hlr hrL hlong k
    have hpk : l ≤ k := by dsimp only [k]; omega
    have hkr : k ≤ r := by dsimp only [k]; omega
    rw [heval l k hpk (hkr.trans hrL), heval k r hkr hrL, heval l r hlr hrL]
    exact recursiveEnergy_node Φ width hwidth R hleaf hnode l r hlr hrL hlong

/-- A node relation required only on the actual root merge list determines
one simultaneous scalar assignment there. Off that list the existing global
recursion is extended by original attained minima, without a node hypothesis.
The relation may describe arbitrary actual terminal images and interval cuts.
Conditional auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, line 1631 and line 1807. -/
theorem exists_root_energy_with_node_relation {L q : ℕ}
    (Φ : ManyBody.BondInteraction L q)
    (width : ℕ) (hwidth : 1 ≤ width)
    (R : LongIntervalIndex L width → ℝ → ℝ → ℝ → Prop)
    (hleaf : ∀ (l r : ℕ), l ≤ r → r ≤ L →
      ∃ p : ℝ, IsRegionalLowerEnergyEstimate Φ l r 0 p)
    (p0 r0 : ℕ) (hp0r0 : p0 ≤ r0) (hr0L : r0 ≤ L)
    (hnode : ∀ J : LongIntervalIndex L width,
      J.val ∈ balancedIntervalMergeList width hwidth p0 r0 →
      let l := J.val.1
      let r := J.val.2
      let k := l + (r - l) / 2
      ∀ p1 p2 : ℝ,
        IsRegionalLowerEnergyEstimate Φ l k (49 / 16) p1 →
        IsRegionalLowerEnergyEstimate Φ k r (49 / 16) p2 →
        ∃ p : ℝ, IsRegionalLowerEnergyEstimate Φ l r (49 / 16) p ∧ R J p1 p2 p) :
    ∃ estimate : ℕ → ℕ → ℝ,
      IsRegionalLowerEnergyEstimate Φ p0 r0 (49 / 16) (estimate p0 r0) ∧
      (r0 - p0 ≤ width → IsRegionalLowerEnergyEstimate Φ p0 r0 0 (estimate p0 r0)) ∧
      ∀ J : LongIntervalIndex L width,
        J.val ∈ balancedIntervalMergeList width hwidth p0 r0 →
        let l := J.val.1
        let r := J.val.2
        let k := l + (r - l) / 2
        IsRegionalLowerEnergyEstimate Φ l r (49 / 16) (estimate l r) ∧
        (k - l ≤ width → IsRegionalLowerEnergyEstimate Φ l k 0 (estimate l k)) ∧
        (r - k ≤ width → IsRegionalLowerEnergyEstimate Φ k r 0 (estimate k r)) ∧
        R J (estimate l k) (estimate k r) (estimate l r) := by
  classical
  let rootList := balancedIntervalMergeList width hwidth p0 r0
  let Rfull := fun (l r : ℕ) (hlr : l ≤ r) (hrL : r ≤ L) (hlong : width < r - l)
      (p1 p2 p : ℝ) ↦
    let J : LongIntervalIndex L width := ⟨(l, r), hlr, hrL, hlong⟩
    if (l, r) ∈ rootList then R J p1 p2 p else IsRegionalLowerEnergyEstimate Φ l r 0 p
  have hstep (l r : ℕ) (hlr : l ≤ r) (hrL : r ≤ L) (hlong : width < r - l) :
      let k := l + (r - l) / 2
      ∀ p1 p2 : ℝ,
        IsRegionalLowerEnergyEstimate Φ l k (49 / 16) p1 →
        IsRegionalLowerEnergyEstimate Φ k r (49 / 16) p2 →
        ∃ p : ℝ, IsRegionalLowerEnergyEstimate Φ l r (49 / 16) p ∧
          Rfull l r hlr hrL hlong p1 p2 p := by
    intro k p1 p2 hp1 hp2
    by_cases hmem : (l, r) ∈ rootList
    · obtain ⟨p, hp, hrel⟩ := hnode ⟨(l, r), hlr, hrL, hlong⟩ hmem p1 p2 hp1 hp2
      exact ⟨p, hp, by simpa only [Rfull, ite_eq_left hmem] using hrel⟩
    · obtain ⟨p, hp0⟩ := hleaf l r hlr hrL
      have hp : IsRegionalLowerEnergyEstimate Φ l r (49 / 16) p := by
        obtain ⟨e, x, hx, hAx, hA, hplower, hpupper⟩ := hp0
        exact ⟨e, x, hx, hAx, hA, by linarith only [hplower], hpupper⟩
      exact ⟨p, hp, by simpa only [Rfull, ite_eq_right hmem] using hp0⟩
  obtain ⟨estimate, hgood, hshort, hlong⟩ :=
    exists_energy_with_node_relation Φ width hwidth Rfull hleaf hstep
  refine ⟨estimate, hgood p0 r0 hp0r0 hr0L, hshort p0 r0 hp0r0 hr0L, ?_⟩
  intro J hJ l r k
  have hpk : l ≤ k := by dsimp only [k]; omega
  have hkr : k ≤ r := by dsimp only [k]; omega
  refine ⟨hgood l r J.property.1 J.property.2.1,
    hshort l k hpk (hkr.trans J.property.2.1), hshort k r hkr J.property.2.1, ?_⟩
  have hrel := hlong l r J.property.1 J.property.2.1 J.property.2.2
  have hmem : (l, r) ∈ rootList := hJ
  simpa only [Rfull, ite_eq_left hmem] using hrel

/-- A simultaneous scalar assignment on a fixed balanced interval tree.
Every valid interval has lower error at most 49/16; short leaves use actual
minima, and long nodes realize the same-family update at their actual
balanced children. Corrected auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, line 1631. -/
def IsBalancedRegionalEnergyAssignment {L q ell : ℕ} (hq : 0 < q)
    (Φ : ManyBody.BondInteraction L q)
    (N : LongIntervalIndex L (4 * ell) → ℕ)
    (F : ∀ J : LongIntervalIndex L (4 * ell),
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (operation : IntervalMergeOperation L q) (hwidth : 1 ≤ 4 * ell)
    (estimate : ℕ → ℕ → ℝ) : Prop :=
  (∀ (l r : ℕ), l ≤ r → r ≤ L →
    IsRegionalLowerEnergyEstimate Φ l r (49 / 16) (estimate l r)) ∧
  (∀ (l r : ℕ), l ≤ r → r ≤ L → r - l ≤ 4 * ell →
    IsRegionalLowerEnergyEstimate Φ l r 0 (estimate l r)) ∧
  ∀ J : LongIntervalIndex L (4 * ell),
    let l := J.val.1
    let r := J.val.2
    let k := l + (r - l) / 2
    let hpk : l ≤ k := by dsimp only [k]; omega
    let hkr : k ≤ r := by dsimp only [k]; omega
    let S1 := balancedIntervalSpace operation (4 * ell) hwidth l k
    let S2 := balancedIntervalSpace operation (4 * ell) hwidth k r
    IsSoftWordNodeEnergyRealization (u := l + ell) (v := r - ell)
      hq hpk hkr Φ (F J) S1 S2 (estimate l k) (estimate k r) (estimate l r)

/-- The node update on a fixed physical tree constructs one simultaneous
recursive energy assignment. Actual regional minima are used at all short
leaves. The targets, retained spaces and operator families are not selected
again. Corrected auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, line 1631, and line 1807. -/
theorem exists_balanced_regional_energy_assignment {L q ell : ℕ}
    (hq : 0 < q) (hwidth : 1 ≤ 4 * ell)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (N : LongIntervalIndex L (4 * ell) → ℕ)
    (F : ∀ J : LongIntervalIndex L (4 * ell),
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (operation : IntervalMergeOperation L q)
    (hcallbacks : ∀ J : LongIntervalIndex L (4 * ell),
      let l := J.val.1
      let r := J.val.2
      let k := l + (r - l) / 2
      let hpk : l ≤ k := by dsimp only [k]; omega
      let hkr : k ≤ r := by dsimp only [k]; omega
      let S1 := balancedIntervalSpace operation (4 * ell) hwidth l k
      let S2 := balancedIntervalSpace operation (4 * ell) hwidth k r
      HasSoftWordNodeEnergyUpdate (u := l + ell) (v := r - ell) hq hpk hkr Φ (F J) S1 S2) :
    ∃ estimate : ℕ → ℕ → ℝ,
      IsBalancedRegionalEnergyAssignment hq Φ N F operation hwidth estimate := by
  classical
  let R := fun (l r : ℕ) (hlr : l ≤ r) (hrL : r ≤ L) (hlong : 4 * ell < r - l)
      (p1 p2 p : ℝ) ↦
    let J : LongIntervalIndex L (4 * ell) := ⟨(l, r), hlr, hrL, hlong⟩
    let k := l + (r - l) / 2
    let hpk : l ≤ k := by dsimp only [k]; omega
    let hkr : k ≤ r := by dsimp only [k]; omega
    IsSoftWordNodeEnergyRealization (u := l + ell) (v := r - ell) hq hpk hkr Φ (F J)
      (balancedIntervalSpace operation (4 * ell) hwidth l k)
      (balancedIntervalSpace operation (4 * ell) hwidth k r) p1 p2 p
  have hleaf := exists_leaf_energy hq Φ h0 h1
  have hnode (l r : ℕ) (hlr : l ≤ r) (hrL : r ≤ L) (hlong : 4 * ell < r - l) :
      let k := l + (r - l) / 2
      ∀ p1 p2 : ℝ,
        IsRegionalLowerEnergyEstimate Φ l k (49 / 16) p1 →
        IsRegionalLowerEnergyEstimate Φ k r (49 / 16) p2 →
        ∃ p : ℝ, IsRegionalLowerEnergyEstimate Φ l r (49 / 16) p ∧
          R l r hlr hrL hlong p1 p2 p := by
    intro k p1 p2 hp1 hp2
    exact realize_node_update hq (by dsimp only [k]; omega) (by dsimp only [k]; omega)
      Φ _ _ _ (hcallbacks ⟨(l, r), hlr, hrL, hlong⟩) p1 p2 hp1 hp2
  obtain ⟨estimate, hgood, hshort, hlong⟩ :=
    exists_energy_with_node_relation Φ (4 * ell) hwidth R hleaf hnode
  refine ⟨estimate, hgood, hshort, ?_⟩
  intro J l r k hpk hkr S1 S2
  exact hlong l r J.property.1 J.property.2.1 J.property.2.2

/-- Node callbacks are required only on the actual root merge list.
One scalar function then has the certified lower energy at the root and
those internal nodes, true minima at their short children, and literal
same-family raw updates at exactly those listed nodes. Outside this root
subtree, the construction uses original attained minima as a mathematical
extension. Auxiliary to ALVV, arXiv:1602.08828v2, lines 1631 and 1807. -/
theorem exists_balanced_root_regional_energy_assignment {L q ell : ℕ}
    (hq : 0 < q) (hwidth : 1 ≤ 4 * ell)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (N : LongIntervalIndex L (4 * ell) → ℕ)
    (F : ∀ J : LongIntervalIndex L (4 * ell),
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (operation : IntervalMergeOperation L q) (p0 r0 : ℕ)
    (hp0r0 : p0 ≤ r0) (hr0L : r0 ≤ L)
    (hcallbacks : ∀ J : LongIntervalIndex L (4 * ell),
      J.val ∈ balancedIntervalMergeList (4 * ell) hwidth p0 r0 →
      let l := J.val.1
      let r := J.val.2
      let k := l + (r - l) / 2
      let hpk : l ≤ k := by dsimp only [k]; omega
      let hkr : k ≤ r := by dsimp only [k]; omega
      HasSoftWordNodeEnergyUpdate (u := l + ell) (v := r - ell) hq hpk hkr Φ (F J)
        (balancedIntervalSpace operation (4 * ell) hwidth l k)
        (balancedIntervalSpace operation (4 * ell) hwidth k r)) :
    ∃ estimate : ℕ → ℕ → ℝ,
      IsRegionalLowerEnergyEstimate Φ p0 r0 (49 / 16) (estimate p0 r0) ∧
      (r0 - p0 ≤ 4 * ell → IsRegionalLowerEnergyEstimate Φ p0 r0 0 (estimate p0 r0)) ∧
      ∀ J : LongIntervalIndex L (4 * ell),
        J.val ∈ balancedIntervalMergeList (4 * ell) hwidth p0 r0 →
        let l := J.val.1
        let r := J.val.2
        let k := l + (r - l) / 2
        let hpk : l ≤ k := by dsimp only [k]; omega
        let hkr : k ≤ r := by dsimp only [k]; omega
        IsRegionalLowerEnergyEstimate Φ l r (49 / 16) (estimate l r) ∧
        (k - l ≤ 4 * ell → IsRegionalLowerEnergyEstimate Φ l k 0 (estimate l k)) ∧
        (r - k ≤ 4 * ell → IsRegionalLowerEnergyEstimate Φ k r 0 (estimate k r)) ∧
        IsSoftWordNodeEnergyRealization (u := l + ell) (v := r - ell) hq hpk hkr Φ (F J)
          (balancedIntervalSpace operation (4 * ell) hwidth l k)
          (balancedIntervalSpace operation (4 * ell) hwidth k r)
          (estimate l k) (estimate k r) (estimate l r) := by
  classical
  let R := fun (J : LongIntervalIndex L (4 * ell)) (p1 p2 p : ℝ) ↦
    let l := J.val.1
    let r := J.val.2
    let k := l + (r - l) / 2
    let hpk : l ≤ k := by dsimp only [k]; omega
    let hkr : k ≤ r := by dsimp only [k]; omega
    IsSoftWordNodeEnergyRealization (u := l + ell) (v := r - ell) hq hpk hkr Φ (F J)
      (balancedIntervalSpace operation (4 * ell) hwidth l k)
      (balancedIntervalSpace operation (4 * ell) hwidth k r) p1 p2 p
  have hleaf := exists_leaf_energy hq Φ h0 h1
  have hnode (J : LongIntervalIndex L (4 * ell))
      (hJ : J.val ∈ balancedIntervalMergeList (4 * ell) hwidth p0 r0) :
      let l := J.val.1
      let r := J.val.2
      let k := l + (r - l) / 2
      ∀ p1 p2 : ℝ,
        IsRegionalLowerEnergyEstimate Φ l k (49 / 16) p1 →
        IsRegionalLowerEnergyEstimate Φ k r (49 / 16) p2 →
        ∃ p : ℝ, IsRegionalLowerEnergyEstimate Φ l r (49 / 16) p ∧ R J p1 p2 p := by
    intro l r k p1 p2 hp1 hp2
    exact realize_node_update hq (by omega) (by omega)
      Φ _ _ _ (hcallbacks J hJ) p1 p2 hp1 hp2
  obtain ⟨estimate, hgood, hshort, hlong⟩ :=
    exists_root_energy_with_node_relation Φ (4 * ell) hwidth R hleaf p0 r0 hp0r0 hr0L hnode
  refine ⟨estimate, hgood, hshort, ?_⟩
  intro J hJ
  exact hlong J hJ

end TNLean.MPS.AreaLaw.ALVV

end

section

open ManyBody (interval)

open Matrix
open scoped BigOperators TensorProduct InnerProductSpace ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

/-- The actual sampled root subtree acquires scalar energy estimates from
its joint original-ground viability and the same fixed target/family
certificates. All used callbacks are derived from the physical soft word
energy theorem. No energy, minimum, callback or all-overlap viability is
supplied. Corrected auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, line 1631, and line 1807. -/
theorem exists_canonical_interval_root_energy_assignment {L q ell D s : ℕ}
    (hq : 0 < q) (hell : 21 ≤ ell) (hD : 2 ≤ D)
    (hcount : 50 * ell ^ 2 ≤ D) (hsample : 1 ≤ s)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (T : LongIntervalIndex L (4 * ell) →
      Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (N : LongIntervalIndex L (4 * ell) → ℕ)
    (F : ∀ J : LongIntervalIndex L (4 * ell),
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)) :
    let _ : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
    let H := Φ.hamiltonian
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues (minEigenvalue hH)
    let a := 3 / (32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)
    let tau := a ^ 2 / 1048576
    let Delta := 1 / (200000 * (D : ℝ) ^ 12)
    let loss := Delta / (1 - (1 / 4 : ℝ)) ^ 2
    (∀ J : LongIntervalIndex L (4 * ell),
      Module.finrank ℂ (T J) = Module.finrank ℂ G ∧ Submodule.IsCloseTo tau G (T J) ∧
      ∀ S : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)),
        Submodule.IsViable (1 / 4 : ℝ) S ((T J).map
          (Entropy.regionTensorCoordinates q
            (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap) →
        let grow := ⨆ word : Fin 1 → Fin (N J),
          S.map ((List.ofFn (fun j ↦ F J (word j))).prod : _ →ₗ[ℂ] _)
        Module.finrank ℂ grow ≤ D ^ 2 * Module.finrank ℂ S ∧
          Submodule.IsViable loss grow ((T J).map
            (Entropy.regionTensorCoordinates q
              (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap)) →
    ∀ (xi : ℝ) (U : IntervalSamplingChoices L q) (p0 r0 : ℕ), p0 ≤ r0 → r0 ≤ L →
    let hwidth : 1 ≤ 4 * ell := by omega
    let operation := canonicalIntervalSamplingOperation D s N F xi U
    (Submodule.IsViable (3 / 200 : ℝ)
      (balancedIntervalSpace operation (4 * ell) hwidth p0 r0)
      (G.map (Entropy.regionTensorCoordinates q (interval L p0 r0)).toLinearEquiv.toLinearMap) ∧
      ∀ I ∈ balancedIntervalMergeList (4 * ell) hwidth p0 r0,
        Submodule.IsViable (3 / 200 : ℝ)
          (balancedIntervalSpace operation (4 * ell) hwidth I.1 I.2)
          (G.map (Entropy.regionTensorCoordinates q
            (interval L I.1 I.2)).toLinearEquiv.toLinearMap)) →
    ∃ estimate : ℕ → ℕ → ℝ,
      IsRegionalLowerEnergyEstimate Φ p0 r0 (49 / 16) (estimate p0 r0) ∧
      (r0 - p0 ≤ 4 * ell → IsRegionalLowerEnergyEstimate Φ p0 r0 0 (estimate p0 r0)) ∧
      ∀ J : LongIntervalIndex L (4 * ell),
        J.val ∈ balancedIntervalMergeList (4 * ell) hwidth p0 r0 →
        let l := J.val.1
        let r := J.val.2
        let k := l + (r - l) / 2
        let hpk : l ≤ k := by dsimp only [k]; omega
        let hkr : k ≤ r := by dsimp only [k]; omega
        IsRegionalLowerEnergyEstimate Φ l r (49 / 16) (estimate l r) ∧
        (k - l ≤ 4 * ell → IsRegionalLowerEnergyEstimate Φ l k 0 (estimate l k)) ∧
        (r - k ≤ 4 * ell → IsRegionalLowerEnergyEstimate Φ k r 0 (estimate k r)) ∧
        IsSoftWordNodeEnergyRealization (u := l + ell) (v := r - ell) hq hpk hkr Φ (F J)
          (balancedIntervalSpace operation (4 * ell) hwidth l k)
          (balancedIntervalSpace operation (4 * ell) hwidth k r)
          (estimate l k) (estimate k r) (estimate l r) := by
  classical
  intro config H hH G a tau Delta loss htargets xi U p0 r0 hp0r0 hr0L
    hwidth operation hjoint
  let : Nonempty (Fin L → Fin q) := config
  let rootList := balancedIntervalMergeList (4 * ell) hwidth p0 r0
  apply exists_balanced_root_regional_energy_assignment hq hwidth Φ h0 h1 N F
    operation p0 r0 hp0r0 hr0L
  intro J hJ l r k hpk hkr
  have hlong : 4 * ell < r - l := J.property.2.2
  have hdescendant (K : ℕ × ℕ)
      (hK : K ∈ balancedIntervalMergeList (4 * ell) hwidth l k ∨
        K ∈ balancedIntervalMergeList (4 * ell) hwidth k r) : K ∈ rootList := by
    apply mem_balancedIntervalMergeList_trans (4 * ell) hwidth hJ
    rw [balancedIntervalMergeList, dite_eq_right (by omega : ¬r - l ≤ 4 * ell)]
    simp only [List.mem_append, List.mem_singleton]
    tauto
  have hviable (a b : ℕ)
      (hcontained : 4 * ell < b - a → (a, b) ∈ rootList) :
      Submodule.IsViable (3 / 200 : ℝ)
        (balancedIntervalSpace operation (4 * ell) hwidth a b)
        (G.map (Entropy.regionTensorCoordinates q (interval L a b)).toLinearEquiv.toLinearMap) := by
    by_cases hshort : b - a ≤ 4 * ell
    · rw [balancedIntervalSpace_of_short operation hwidth hshort]
      exact Submodule.isViable_top _ (by norm_num) _
    · exact hjoint.2 (a, b) (hcontained (by omega))
  have hS1 := hviable l k (fun hchild ↦
    hdescendant (l, k) (Or.inl (self_mem_balancedIntervalMergeList _ hwidth l k hchild)))
  have hS2 := hviable k r (fun hchild ↦
    hdescendant (k, r) (Or.inr (self_mem_balancedIntervalMergeList _ hwidth k r hchild)))
  obtain ⟨hdimT, hGT, hword⟩ := htargets J
  exact exists_soft_word_node_energy_update hq (by omega : l ≤ l + ell)
    (by omega : l + ell ≤ r - ell) (Nat.sub_le _ _) J.property.2.1
    (by omega : l + ell - l ≤ 2 * ell) (by omega : r - (r - ell) ≤ 2 * ell)
    hell hD hcount hsample Φ h0 h1 (T J) (F J) hdimT hGT hword k hpk hkr
    (balancedIntervalSpace operation (4 * ell) hwidth l k)
    (balancedIntervalSpace operation (4 * ell) hwidth k r) hS1 hS2

end TNLean.MPS.AreaLaw.ALVV

end

section

open ManyBody (interval)

open MeasureTheory
open scoped ENNReal InnerProductSpace TensorProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- A calibrated word family and joint viability on the actual canonical
root subtree determine one energy function, before any terminal refinement.
Supporting ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1631 and 1807. -/
theorem exists_canonical_root_energy_of_calibrated_words {L q ell D s : ℕ}
    (hq : 0 < q) (hell : 21 ≤ ell) (hD2 : 2 ≤ D) (hsample : 1 ≤ s)
    (hDdef : D = (max q 50 * ell ^ 2) ^ (22 * ell))
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (mu gamma : ℝ) (hgamma : 0 < gamma) (hwidth : 1 ≤ 4 * ell)
    (T : LongIntervalIndex L (4 * ell) →
      Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (N : LongIntervalIndex L (4 * ell) → ℕ)
    (F : ∀ J : LongIntervalIndex L (4 * ell),
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)) :
    let H := Φ.hamiltonian
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    mu ∈ spectrum ℝ H →
    (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let tau := (3 / (32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)) ^ 2 / 1048576
    let Delta := (1 / 200000 : ℝ) / (D : ℝ) ^ 12
    (∀ J, Module.finrank ℂ (T J) = Module.finrank ℂ G ∧
      Submodule.IsCloseTo tau G (T J) ∧
      ∀ (power : ℕ)
        (S : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)))
        (delta : ℝ),
        Submodule.IsViable delta S ((T J).map (Entropy.regionTensorCoordinates q
          (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap) → delta < 1 →
        let grow := ⨆ word : Fin power → Fin (N J),
          S.map ((List.ofFn (fun j ↦ F J (word j))).prod : _ →ₗ[ℂ] _)
        Module.finrank ℂ grow ≤ (D ^ 2) ^ power * Module.finrank ℂ S ∧
          Submodule.IsViable (Delta ^ power / (1 - delta) ^ 2) grow
            ((T J).map (Entropy.regionTensorCoordinates q
              (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap)) →
    ∀ (xi : ℝ) (seed : IntervalSamplingChoices L q),
      seed ∈ canonicalIntervalSamplingTreeGood D s hwidth N F xi G (3 / 200 : ℝ) 0 L →
    ∃ estimate : ℕ → ℕ → ℝ,
      ALVV.IsRegionalLowerEnergyEstimate Φ 0 L (49 / 16) (estimate 0 L) ∧
      (L - 0 ≤ (4 * ell) →
        ALVV.IsRegionalLowerEnergyEstimate Φ 0 L 0 (estimate 0 L)) ∧
      (∀ J : LongIntervalIndex L (4 * ell),
        J.val ∈ balancedIntervalMergeList (4 * ell) hwidth 0 L →
        let l := J.val.1
        let r := J.val.2
        let k := l + (r - l) / 2
        let hpk : l ≤ k := Nat.le_add_right l ((r - l) / 2)
        let hkr : k ≤ r :=
          (Nat.add_le_add_left (Nat.div_le_self (r - l) 2) l).trans_eq
            (Nat.add_sub_of_le J.property.1)
        ALVV.IsRegionalLowerEnergyEstimate Φ l r (49 / 16) (estimate l r) ∧
        (k - l ≤ (4 * ell) → ALVV.IsRegionalLowerEnergyEstimate Φ l k 0 (estimate l k)) ∧
        (r - k ≤ (4 * ell) → ALVV.IsRegionalLowerEnergyEstimate Φ k r 0 (estimate k r)) ∧
        ALVV.IsSoftWordNodeEnergyRealization (u := l + ell) (v := r - ell)
          hq hpk hkr Φ (F J)
          (balancedIntervalSpace (canonicalIntervalSamplingOperation D s N F xi seed)
            (4 * ell) hwidth l k)
          (balancedIntervalSpace (canonicalIntervalSamplingOperation D s N F xi seed)
            (4 * ell) hwidth k r)
          (estimate l k) (estimate k r) (estimate l r)) := by
  classical
  intro H hH hmu hgap G tau Delta htargets xi seed hgood
  let : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
  have hmin : minEigenvalue hH = mu := by
    apply le_antisymm
    · obtain ⟨j, hj⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ hmu
      simpa only [hj] using minEigenvalue_le hH j
    · apply Finset.le_min'
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      rcases hgap _ (hH.eigenvalues_mem_spectrum_real i) with heq | hle
      · exact heq.ge
      · exact (le_add_of_nonneg_right hgamma.le).trans hle
  have hcount : 50 * ell ^ 2 ≤ D := by
    have hm : 50 ≤ max q 50 := Nat.le_max_right q 50
    have hell1 : 1 ≤ ell := (by decide : 1 ≤ 21).trans hell
    have he : 1 ≤ ell ^ 2 := Nat.one_le_pow 2 ell hell1
    have hbase : 1 ≤ max q 50 * ell ^ 2 := by
      simpa only [one_mul] using Nat.mul_le_mul ((by decide : 1 ≤ 50).trans hm) he
    calc
      50 * ell ^ 2 ≤ max q 50 * ell ^ 2 := Nat.mul_le_mul_right (ell ^ 2) hm
      _ ≤ (max q 50 * ell ^ 2) ^ (22 * ell) :=
        le_self_pow hbase (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hell1))
      _ = D := hDdef.symm
  let Gmin := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues
    (minEigenvalue hH)
  have htargetEq : Gmin = G :=
    congrArg (Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues) hmin
  have henergyTargets (J : LongIntervalIndex L (4 * ell)) :
      Module.finrank ℂ (T J) = Module.finrank ℂ Gmin ∧
      Submodule.IsCloseTo tau Gmin (T J) ∧
      ∀ S : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)),
        Submodule.IsViable (1 / 4 : ℝ) S ((T J).map
          (Entropy.regionTensorCoordinates q
            (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap) →
        let grow := ⨆ word : Fin 1 → Fin (N J),
          S.map ((List.ofFn (fun j ↦ F J (word j))).prod : _ →ₗ[ℂ] _)
        Module.finrank ℂ grow ≤ D ^ 2 * Module.finrank ℂ S ∧
          Submodule.IsViable ((1 / (200000 * (D : ℝ) ^ 12)) / (1 - (1 / 4 : ℝ)) ^ 2)
            grow ((T J).map (Entropy.regionTensorCoordinates q
              (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap) := by
    obtain ⟨hdim, hGT, hwords⟩ := htargets J
    have hdimEq : Module.finrank ℂ Gmin = Module.finrank ℂ G :=
      congrArg (fun V : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)) ↦
        Module.finrank ℂ V) htargetEq
    have hdimMin : Module.finrank ℂ (T J) = Module.finrank ℂ Gmin :=
      hdim.trans hdimEq.symm
    have hGTMin := Eq.mpr (congrArg (fun V ↦ Submodule.IsCloseTo tau V (T J))
      htargetEq) hGT
    refine ⟨hdimMin, hGTMin, ?_⟩
    intro S hS
    simpa only [pow_one, Delta, div_div] using hwords 1 S (1 / 4) hS (by norm_num)
  have hgoodMin : seed ∈
      canonicalIntervalSamplingTreeGood D s hwidth N F xi Gmin (3 / 200 : ℝ) 0 L :=
    Eq.mpr (congrArg (fun V ↦ seed ∈
      canonicalIntervalSamplingTreeGood D s hwidth N F xi V (3 / 200 : ℝ) 0 L)
      htargetEq) hgood
  obtain ⟨estimate, hrootEnergy, hshortEnergy, hnodesEnergy⟩ :=
    ALVV.exists_canonical_interval_root_energy_assignment
      hq hell hD2 hcount hsample Φ h0 h1 T N F henergyTargets
      xi seed 0 L (Nat.zero_le L) le_rfl hgoodMin
  exact ⟨estimate, hrootEnergy, hshortEnergy, hnodesEnergy⟩

end TNLean.MPS.AreaLaw

end
