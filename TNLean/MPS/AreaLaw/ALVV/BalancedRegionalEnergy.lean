/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.SoftWordNodeEnergy
import TNLean.MPS.AreaLaw.BalancedIntervalTree
import TNLean.MPS.AreaLaw.BalancedIntervalMergeList

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
-/

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
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (F : Fin N → EuclideanSpace ℂ (interval L l r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L l r → Fin q))
    (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L l k → Fin q)))
    (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k r → Fin q)))
    (p1 p2 p : ℝ) : Prop :=
  ∃ (eLeft eRight : ℝ) (xLeft xRight : (Fin L → Fin q) → ℂ),
    star xLeft ⬝ᵥ xLeft = 1 ∧
    aklvRegionalHamiltonians l u h 1 *ᵥ xLeft = (eLeft : ℂ) • xLeft ∧
    (aklvRegionalHamiltonians l u h 1 - (eLeft : ℂ) • 1).PosSemidef ∧
    star xRight ⬝ᵥ xRight = 1 ∧
    aklvRegionalHamiltonians v r h 1 *ᵥ xRight = (eRight : ℂ) • xRight ∧
    (aklvRegionalHamiltonians v r h 1 - (eRight : ℂ) • 1).PosSemidef ∧
    IsRegionalLowerEnergyEstimate h u v 10 (p1 + p2 - eLeft - eRight - 2) ∧
    IsSoftWordEnergyUpdate (u := u) (v := v) hq hlk hkr h F S1 S2
      (p1 + p2 - eLeft - eRight - 2) p

private theorem realize_node_update {L q N l k u v r : ℕ} (hq : 0 < q)
    (hlk : l ≤ k) (hkr : k ≤ r)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (F : Fin N → EuclideanSpace ℂ (interval L l r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L l r → Fin q))
    (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L l k → Fin q)))
    (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k r → Fin q)))
    (hn : HasSoftWordNodeEnergyUpdate (u := u) (v := v) hq hlk hkr h F S1 S2)
    (p1 p2 : ℝ) (hp1 : IsRegionalLowerEnergyEstimate h l k (49 / 16) p1)
    (hp2 : IsRegionalLowerEnergyEstimate h k r (49 / 16) p2) :
    ∃ p : ℝ, IsRegionalLowerEnergyEstimate h l r (49 / 16) p ∧
      IsSoftWordNodeEnergyRealization (u := u) (v := v) hq hlk hkr h F S1 S2 p1 p2 p := by
  obtain ⟨eL, eR, xL, xR, hxL, hL, hLmin, hxR, hR, hRmin, hupdate⟩ := hn
  obtain ⟨hcenter, p, hp, hraw⟩ := hupdate p1 p2 hp1 hp2
  exact ⟨p, hp, eL, eR, xL, xR, hxL, hL, hLmin, hxR, hR, hRmin, hcenter, hraw⟩

private theorem exists_leaf_energy {L q : ℕ} (hq : 0 < q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (l r : ℕ) (hlr : l ≤ r) (hrL : r ≤ L) :
    ∃ p : ℝ, IsRegionalLowerEnergyEstimate h l r 0 p := by
  obtain ⟨eA, _eB, _eP, x, _z, hx, hAx, _hBx, hA, _hB, _rest⟩ :=
    exists_adjacent_interval_energy_merge hq hlr le_rfl hrL h hs h0 h1
  exact ⟨eA, eA, x, hx, hAx, hA, by simp, le_rfl⟩

private noncomputable def recursiveEnergy {L q : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (width : ℕ) (hwidth : 1 ≤ width)
    (R : ∀ (l r : ℕ), l ≤ r → r ≤ L → width < r - l → ℝ → ℝ → ℝ → Prop)
    (hleaf : ∀ (l r : ℕ), l ≤ r → r ≤ L →
      ∃ p : ℝ, IsRegionalLowerEnergyEstimate h l r 0 p)
    (hnode : ∀ (l r : ℕ) (hlr : l ≤ r) (hrL : r ≤ L) (hlong : width < r - l),
      let k := l + (r - l) / 2
      ∀ p1 p2 : ℝ,
        IsRegionalLowerEnergyEstimate h l k (49 / 16) p1 →
        IsRegionalLowerEnergyEstimate h k r (49 / 16) p2 →
        ∃ p : ℝ, IsRegionalLowerEnergyEstimate h l r (49 / 16) p ∧
          R l r hlr hrL hlong p1 p2 p)
    (l r : ℕ) (hlr : l ≤ r) (hrL : r ≤ L) :
    {p : ℝ // IsRegionalLowerEnergyEstimate h l r (49 / 16) p} :=
  if hshort : r - l ≤ width then
    ⟨Classical.choose (hleaf l r hlr hrL), by
      obtain ⟨e, x, hx, hAx, hA, hpLower, hpUpper⟩ :=
        Classical.choose_spec (hleaf l r hlr hrL)
      exact ⟨e, x, hx, hAx, hA, by linarith only [hpLower], hpUpper⟩⟩
  else
    let k := l + (r - l) / 2
    let p1 := recursiveEnergy h width hwidth R hleaf hnode l k (by omega) (by omega)
    let p2 := recursiveEnergy h width hwidth R hleaf hnode k r (by omega) hrL
    let choice := hnode l r hlr hrL (by omega) p1.val p2.val p1.property p2.property
    ⟨Classical.choose choice, (Classical.choose_spec choice).1⟩
termination_by r - l
decreasing_by all_goals omega

private theorem recursiveEnergy_node {L q : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (width : ℕ) (hwidth : 1 ≤ width)
    (R : ∀ (l r : ℕ), l ≤ r → r ≤ L → width < r - l → ℝ → ℝ → ℝ → Prop)
    (hleaf : ∀ (l r : ℕ), l ≤ r → r ≤ L →
      ∃ p : ℝ, IsRegionalLowerEnergyEstimate h l r 0 p)
    (hnode : ∀ (l r : ℕ) (hlr : l ≤ r) (hrL : r ≤ L) (hlong : width < r - l),
      let k := l + (r - l) / 2
      ∀ p1 p2 : ℝ,
        IsRegionalLowerEnergyEstimate h l k (49 / 16) p1 →
        IsRegionalLowerEnergyEstimate h k r (49 / 16) p2 →
        ∃ p : ℝ, IsRegionalLowerEnergyEstimate h l r (49 / 16) p ∧
          R l r hlr hrL hlong p1 p2 p)
    (l r : ℕ) (hlr : l ≤ r) (hrL : r ≤ L) (hlong : width < r - l) :
    let k := l + (r - l) / 2
    let hpk : l ≤ k := by dsimp only [k]; omega
    let hkr : k ≤ r := by dsimp only [k]; omega
    R l r hlr hrL hlong
      (recursiveEnergy h width hwidth R hleaf hnode l k hpk (hkr.trans hrL)).val
      (recursiveEnergy h width hwidth R hleaf hnode k r hkr hrL).val
      (recursiveEnergy h width hwidth R hleaf hnode l r hlr hrL).val := by
  intro k hpk hkr
  let left := recursiveEnergy h width hwidth R hleaf hnode l k hpk (hkr.trans hrL)
  let right := recursiveEnergy h width hwidth R hleaf hnode k r hkr hrL
  let choice := hnode l r hlr hrL hlong left.val right.val left.property right.property
  have hvalue : (recursiveEnergy h width hwidth R hleaf hnode l r hlr hrL).val =
      Classical.choose choice := by
    rw [recursiveEnergy]
    split
    · omega
    · rfl
  rw [hvalue]
  exact (Classical.choose_spec choice).2

private theorem exists_energy_with_node_relation {L q : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (width : ℕ) (hwidth : 1 ≤ width)
    (R : ∀ (l r : ℕ), l ≤ r → r ≤ L → width < r - l → ℝ → ℝ → ℝ → Prop)
    (hleaf : ∀ (l r : ℕ), l ≤ r → r ≤ L →
      ∃ p : ℝ, IsRegionalLowerEnergyEstimate h l r 0 p)
    (hnode : ∀ (l r : ℕ) (hlr : l ≤ r) (hrL : r ≤ L) (hlong : width < r - l),
      let k := l + (r - l) / 2
      ∀ p1 p2 : ℝ,
        IsRegionalLowerEnergyEstimate h l k (49 / 16) p1 →
        IsRegionalLowerEnergyEstimate h k r (49 / 16) p2 →
        ∃ p : ℝ, IsRegionalLowerEnergyEstimate h l r (49 / 16) p ∧
          R l r hlr hrL hlong p1 p2 p)
 :
    ∃ estimate : ℕ → ℕ → ℝ,
      (∀ (l r : ℕ), l ≤ r → r ≤ L →
        IsRegionalLowerEnergyEstimate h l r (49 / 16) (estimate l r)) ∧
      (∀ (l r : ℕ), l ≤ r → r ≤ L → r - l ≤ width →
        IsRegionalLowerEnergyEstimate h l r 0 (estimate l r)) ∧
      ∀ (l r : ℕ) (hlr : l ≤ r) (hrL : r ≤ L) (hlong : width < r - l),
        let k := l + (r - l) / 2
        R l r hlr hrL hlong (estimate l k) (estimate k r) (estimate l r) := by
  classical
  let values := recursiveEnergy h width hwidth R hleaf hnode
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
    change IsRegionalLowerEnergyEstimate h l r 0
      (recursiveEnergy h width hwidth R hleaf hnode l r hlr hrL).val
    rw [recursiveEnergy]
    split
    · exact Classical.choose_spec (hleaf l r hlr hrL)
    · contradiction
  · intro l r hlr hrL hlong k
    have hpk : l ≤ k := by dsimp only [k]; omega
    have hkr : k ≤ r := by dsimp only [k]; omega
    rw [heval l k hpk (hkr.trans hrL), heval k r hkr hrL, heval l r hlr hrL]
    exact recursiveEnergy_node h width hwidth R hleaf hnode l r hlr hrL hlong

/-- A simultaneous scalar assignment on a fixed balanced interval tree.
Every valid interval has lower error at most 49/16; short leaves use actual
minima, and long nodes realize the same-family update at their actual
balanced children. Corrected auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, line 1631. -/
def IsBalancedRegionalEnergyAssignment {L q ell : ℕ} (hq : 0 < q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (N : LongIntervalIndex L (4 * ell) → ℕ)
    (F : ∀ J : LongIntervalIndex L (4 * ell),
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (operation : IntervalMergeOperation L q) (hwidth : 1 ≤ 4 * ell)
    (estimate : ℕ → ℕ → ℝ) : Prop :=
  (∀ (l r : ℕ), l ≤ r → r ≤ L →
    IsRegionalLowerEnergyEstimate h l r (49 / 16) (estimate l r)) ∧
  (∀ (l r : ℕ), l ≤ r → r ≤ L → r - l ≤ 4 * ell →
    IsRegionalLowerEnergyEstimate h l r 0 (estimate l r)) ∧
  ∀ J : LongIntervalIndex L (4 * ell),
    let l := J.val.1
    let r := J.val.2
    let k := l + (r - l) / 2
    let hpk : l ≤ k := by dsimp only [k]; omega
    let hkr : k ≤ r := by dsimp only [k]; omega
    let S1 := balancedIntervalSpace operation (4 * ell) hwidth l k
    let S2 := balancedIntervalSpace operation (4 * ell) hwidth k r
    IsSoftWordNodeEnergyRealization (u := l + ell) (v := r - ell)
      hq hpk hkr h (F J) S1 S2 (estimate l k) (estimate k r) (estimate l r)

/-- The node update on a fixed physical tree constructs one simultaneous
recursive energy assignment. Actual regional minima are used at all short
leaves. The targets, retained spaces and operator families are not selected
again. Corrected auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, line 1631, and line 1807. -/
theorem exists_balanced_regional_energy_assignment {L q ell : ℕ}
    (hq : 0 < q) (hwidth : 1 ≤ 4 * ell)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
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
      HasSoftWordNodeEnergyUpdate (u := l + ell) (v := r - ell) hq hpk hkr h (F J) S1 S2) :
    ∃ estimate : ℕ → ℕ → ℝ,
      IsBalancedRegionalEnergyAssignment hq h N F operation hwidth estimate := by
  classical
  let R := fun (l r : ℕ) (hlr : l ≤ r) (hrL : r ≤ L) (hlong : 4 * ell < r - l)
      (p1 p2 p : ℝ) ↦
    let J : LongIntervalIndex L (4 * ell) := ⟨(l, r), hlr, hrL, hlong⟩
    let k := l + (r - l) / 2
    let hpk : l ≤ k := by dsimp only [k]; omega
    let hkr : k ≤ r := by dsimp only [k]; omega
    IsSoftWordNodeEnergyRealization (u := l + ell) (v := r - ell) hq hpk hkr h (F J)
      (balancedIntervalSpace operation (4 * ell) hwidth l k)
      (balancedIntervalSpace operation (4 * ell) hwidth k r) p1 p2 p
  have hleaf := exists_leaf_energy hq h hs h0 h1
  have hnode (l r : ℕ) (hlr : l ≤ r) (hrL : r ≤ L) (hlong : 4 * ell < r - l) :
      let k := l + (r - l) / 2
      ∀ p1 p2 : ℝ,
        IsRegionalLowerEnergyEstimate h l k (49 / 16) p1 →
        IsRegionalLowerEnergyEstimate h k r (49 / 16) p2 →
        ∃ p : ℝ, IsRegionalLowerEnergyEstimate h l r (49 / 16) p ∧
          R l r hlr hrL hlong p1 p2 p := by
    intro k p1 p2 hp1 hp2
    exact realize_node_update hq (by dsimp only [k]; omega) (by dsimp only [k]; omega)
      h _ _ _ (hcallbacks ⟨(l, r), hlr, hrL, hlong⟩) p1 p2 hp1 hp2
  obtain ⟨estimate, hgood, hshort, hlong⟩ :=
    exists_energy_with_node_relation h (4 * ell) hwidth R hleaf hnode
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
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
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
      HasSoftWordNodeEnergyUpdate (u := l + ell) (v := r - ell) hq hpk hkr h (F J)
        (balancedIntervalSpace operation (4 * ell) hwidth l k)
        (balancedIntervalSpace operation (4 * ell) hwidth k r)) :
    ∃ estimate : ℕ → ℕ → ℝ,
      IsRegionalLowerEnergyEstimate h p0 r0 (49 / 16) (estimate p0 r0) ∧
      (r0 - p0 ≤ 4 * ell → IsRegionalLowerEnergyEstimate h p0 r0 0 (estimate p0 r0)) ∧
      ∀ J : LongIntervalIndex L (4 * ell),
        J.val ∈ balancedIntervalMergeList (4 * ell) hwidth p0 r0 →
        let l := J.val.1
        let r := J.val.2
        let k := l + (r - l) / 2
        let hpk : l ≤ k := by dsimp only [k]; omega
        let hkr : k ≤ r := by dsimp only [k]; omega
        IsRegionalLowerEnergyEstimate h l r (49 / 16) (estimate l r) ∧
        (k - l ≤ 4 * ell → IsRegionalLowerEnergyEstimate h l k 0 (estimate l k)) ∧
        (r - k ≤ 4 * ell → IsRegionalLowerEnergyEstimate h k r 0 (estimate k r)) ∧
        IsSoftWordNodeEnergyRealization (u := l + ell) (v := r - ell) hq hpk hkr h (F J)
          (balancedIntervalSpace operation (4 * ell) hwidth l k)
          (balancedIntervalSpace operation (4 * ell) hwidth k r)
          (estimate l k) (estimate k r) (estimate l r) := by
  classical
  let rootList := balancedIntervalMergeList (4 * ell) hwidth p0 r0
  let R := fun (l r : ℕ) (hlr : l ≤ r) (hrL : r ≤ L) (hlong : 4 * ell < r - l)
      (p1 p2 p : ℝ) ↦
    let J : LongIntervalIndex L (4 * ell) := ⟨(l, r), hlr, hrL, hlong⟩
    let k := l + (r - l) / 2
    let hpk : l ≤ k := by dsimp only [k]; omega
    let hkr : k ≤ r := by dsimp only [k]; omega
    if (l, r) ∈ rootList then
      IsSoftWordNodeEnergyRealization (u := l + ell) (v := r - ell) hq hpk hkr h (F J)
        (balancedIntervalSpace operation (4 * ell) hwidth l k)
        (balancedIntervalSpace operation (4 * ell) hwidth k r) p1 p2 p
    else IsRegionalLowerEnergyEstimate h l r 0 p
  have hleaf := exists_leaf_energy hq h hs h0 h1
  have hnode (l r : ℕ) (hlr : l ≤ r) (hrL : r ≤ L) (hlong : 4 * ell < r - l) :
      let k := l + (r - l) / 2
      ∀ p1 p2 : ℝ,
        IsRegionalLowerEnergyEstimate h l k (49 / 16) p1 →
        IsRegionalLowerEnergyEstimate h k r (49 / 16) p2 →
        ∃ p : ℝ, IsRegionalLowerEnergyEstimate h l r (49 / 16) p ∧
          R l r hlr hrL hlong p1 p2 p := by
    intro k p1 p2 hp1 hp2
    by_cases hmem : (l, r) ∈ rootList
    · obtain ⟨p, hp, hraw⟩ := realize_node_update hq
        (by dsimp only [k]; omega) (by dsimp only [k]; omega) h _ _ _
        (hcallbacks ⟨(l, r), hlr, hrL, hlong⟩ hmem) p1 p2 hp1 hp2
      exact ⟨p, hp, by simpa only [R, ite_eq_left hmem] using hraw⟩
    · obtain ⟨p, hp0⟩ := hleaf l r hlr hrL
      have hp : IsRegionalLowerEnergyEstimate h l r (49 / 16) p := by
        obtain ⟨e, x, hx, hAx, hA, hplower, hpupper⟩ := hp0
        exact ⟨e, x, hx, hAx, hA, by linarith only [hplower], hpupper⟩
      exact ⟨p, hp, by simpa only [R, ite_eq_right hmem] using hp0⟩
  obtain ⟨estimate, hgood, hshort, hlong⟩ :=
    exists_energy_with_node_relation h (4 * ell) hwidth R hleaf hnode
  refine ⟨estimate, hgood p0 r0 hp0r0 hr0L, hshort p0 r0 hp0r0 hr0L, ?_⟩
  intro J hJ l r k hpk hkr
  refine ⟨hgood l r J.property.1 J.property.2.1,
    hshort l k hpk (hkr.trans J.property.2.1), hshort k r hkr J.property.2.1, ?_⟩
  have hraw := hlong l r J.property.1 J.property.2.1 J.property.2.2
  have hmem : (l, r) ∈ rootList := hJ
  simpa only [R, ite_eq_left hmem] using hraw

end TNLean.MPS.AreaLaw.ALVV
