/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.BalancedRegionalEnergy
import TNLean.MPS.AreaLaw.ALVV.SelectedSoftTerminalNodeEnergy
import TNLean.MPS.AreaLaw.CanonicalIntervalResamplingGood
import TNLean.MPS.AreaLaw.CanonicalHalfSampledIntervalImage
import TNLean.MPS.AreaLaw.BalancedIntervalMergeClosure
import TNLean.MPS.AreaLaw.BalancedIntervalMergeBounds

/-!
# Energy induction on a successful resampling tree

On the joint original-target success event of the actual balanced resampling tree, the
energy estimates of the source's merge procedure can be assigned simultaneously at the root
and every internal interval. At each internal interval the estimate is three below the least
eigenvalue of the compression of the soft regional operator, centred by the two actual child
estimates, to the actual last untrimmed image of that interval's repeated sampling. The
families, images, regional minima and targets are those of the tree; no second family and no
second target is selected.

The per-interval hypotheses are those supplied by the physical soft families: a middle
window with an attained minimum, a target of the dimension of the ground space close to it,
and viability of the terminal image on the literal original-target history of every
`0.04`-viable initial candidate.

Supporting ALVV, arXiv:1602.08828v2, Theorem `t:alg1` and its proof, lines 1779--1818, and
Figure `fig:algo1`, line 1631. The proof requires that the interval energy estimates be within
an additive `3` of their true values, line 1807.

**Local fix (one-sided estimates):** the update is the one-sided estimate of width `49/16`
recorded in `docs/paper-gaps/alvv16_soft_regional_energy_centering.tex`; it is not the
printed two-sided `± 3` estimate.
-/

open ManyBody (interval)

open Matrix
open scoped BigOperators TensorProduct InnerProductSpace ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

/-- A child of an interval in the actual root merge list is either short or itself in the
list. Auxiliary to ALVV, arXiv:1602.08828v2, lines 1777--1817. -/
private theorem child_mem_balancedIntervalMergeList (width : ℕ) (hwidth : 1 ≤ width)
    {p r : ℕ} {J : ℕ × ℕ} (hJ : J ∈ balancedIntervalMergeList width hwidth p r)
    {a b : ℕ} (hab : (a, b) = (J.1, J.1 + (J.2 - J.1) / 2) ∨
      (a, b) = (J.1 + (J.2 - J.1) / 2, J.2))
    (hlong : width < b - a) :
    (a, b) ∈ balancedIntervalMergeList width hwidth p r := by
  have hb := bounds_of_mem_balancedIntervalMergeList width hwidth p r
  refine mem_balancedIntervalMergeList_trans width hwidth hJ ?_
  have hJlong : ¬J.2 - J.1 ≤ width := by
    rcases hab with h | h <;> simp only [Prod.mk.injEq] at h <;> omega
  rw [balancedIntervalMergeList, dite_eq_right hJlong]
  simp only [List.mem_append, List.mem_singleton]
  rcases hab with h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
  · exact Or.inl (Or.inl (self_mem_balancedIntervalMergeList width hwidth _ _ hlong))
  · exact Or.inl (Or.inr (self_mem_balancedIntervalMergeList width hwidth _ _ hlong))

/-- The conclusion of the energy induction on a seed `U` of the actual resampling tree: one
assignment of one-sided regional energy estimates of width `49/16` at the root and every listed
interval, each listed value three below the least eigenvalue of the compression of the
child-centred soft regional operator to that interval's actual terminal untrimmed image.
Supporting ALVV, arXiv:1602.08828v2, Theorem `t:alg1` and its proof, lines 1779--1818. -/
def IsTerminalRitzEnergyAssignment {L q width : ℕ} (hq : 0 < q) (hwidth : 1 ≤ width)
    (Φ : ManyBody.BondInteraction L q)
    (ell : ℕ) (t : ℝ) (m D rounds : ℕ)
    (threshold N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (xi : ℝ) (U : IntervalResamplingChoices L q rounds) : Prop :=
  let regional := fun (a b : ℕ) ↦ ∑ i ∈ Finset.univ.filter
    (fun i : Fin (L - 1) ↦ a ≤ i.val ∧ i.val + 1 < b), Φ.term i
  let S := fun (a b : ℕ) (U : IntervalResamplingChoices L q rounds) ↦
    balancedIntervalSpace (canonicalIntervalResamplingOperation
      D rounds threshold N F xi U) width hwidth a b
  ∃ (u v : LongIntervalIndex L width → ℕ) (estimate : ℕ → ℕ → ℝ),
    IsRegionalLowerEnergyEstimate Φ 0 L (49 / 16) (estimate 0 L) ∧
    (L - 0 ≤ width → IsRegionalLowerEnergyEstimate Φ 0 L 0 (estimate 0 L)) ∧
    ∀ J : LongIntervalIndex L width,
      J.val ∈ balancedIntervalMergeList width hwidth 0 L →
      let l := J.val.1
      let r := J.val.2
      let k := l + (r - l) / 2
      let J' := interval L l r
      let sigma0 : Fin L → Fin q := fun _ ↦ ⟨0, hq⟩
      let y0 := ((ManyBody.cutEquiv (fun _ ↦ Fin q) J') sigma0).2
      let native := fun x : J' → Fin q ↦
        (ManyBody.cutEquiv (fun _ ↦ Fin q) J').symm (x, y0)
      IsRegionalLowerEnergyEstimate Φ l r (49 / 16) (estimate l r) ∧
      (k - l ≤ width → IsRegionalLowerEnergyEstimate Φ l k 0 (estimate l k)) ∧
      (r - k ≤ width → IsRegionalLowerEnergyEstimate Φ k r 0 (estimate k r)) ∧
      l ≤ u J ∧ u J ≤ v J ∧ v J ≤ r ∧ u J - l ≤ 2 * ell ∧ r - v J ≤ 2 * ell ∧
      ∃ eLeft eRight : ℝ,
        IsRegionalLowerEnergyEstimate Φ l (u J) 0 eLeft ∧
        IsRegionalLowerEnergyEstimate Φ (v J) r 0 eRight ∧
        let center := estimate l k + estimate k r - eLeft - eRight - 2
        IsRegionalLowerEnergyEstimate Φ (u J) (v J) 10 center ∧
        let R := regional l r - regional (u J) (v J) + (center : ℂ) • 1 +
          cfc (Real.softTruncation t m) (regional (u J) (v J) - (center : ℂ) • 1)
        let Rnat := R.submatrix native native
        let W := adjacentIntervalMerge L q l k r (Nat.le_add_right l _)
          (by have := J.property.1; omega) (S l k U) (S k r U)
        let Y := canonicalHalfSampledIntervalImage L q l r D (threshold J) rounds (F J) xi W
          (U (LongIntervalIndex.coordinate J))
        ∃ (n : ℕ) (b : OrthonormalBasis (Fin (n + 1)) ℂ Y) (energy : Fin (n + 1) → ℝ),
          Module.finrank ℂ Y = n + 1 ∧
          (∀ j, Y.orthogonalCompression
            (toEuclideanCLM (𝕜 := ℂ) (n := J' → Fin q) Rnat).toLinearMap
              (b j) = (energy j : ℂ) • b j) ∧
          Antitone energy ∧ estimate l r = energy (Fin.last n) - 3

set_option maxHeartbeats 400000 in
-- Matching the terminal image with the family-support form unfolds the half-sampling iterate.
open Classical in
/-- **Energy induction on a successful resampling tree.** Let the actual interval families
of the balanced resampling tree carry, on every long interval, a middle window with an
attained minimum, a target `T` of the dimension of the ground space `G` within directed
squared error `3τ/200` of it, and viability of the terminal untrimmed image for `T` on the
literal original-target history of every `0.04`-viable initial candidate. Then for every seed
in the joint success event there is one energy assignment with the following properties. The
root estimate, and the estimate at every listed internal interval, is a one-sided estimate of
width `49/16` of the actual regional minimum, exact for short children. At every listed
interval it equals three below the least eigenvalue of the compression of the soft regional
operator, centred by the two actual child estimates, to the actual terminal image of that
interval for the actual merged child candidate and the actual seed.

Supporting ALVV, arXiv:1602.08828v2, Theorem `t:alg1` and its proof, lines 1779--1818. -/
theorem exists_successful_tree_energy_induction
    {L q width ell : ℕ} (hq : 0 < q) (hwidth : 1 ≤ width)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (g : ℝ) (hg : 0 < g) (t Tcut : ℝ) (m D : ℕ) (hm : 2 ≤ m) (hD : 2 ≤ D)
    (ht : 156 + 2 * g ≤ t) (hTcut : 156 + 2 * g ≤ Tcut)
    (Delta : ℝ) (hDelta0 : 0 ≤ Delta) (mu : ℝ) (rounds : ℕ)
    (threshold N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (xi : ℝ) :
    let _ : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
    let H := Φ.hamiltonian
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let Msoft := 3 * t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 34
    let tau := 1 / ((D : ℝ) ^ 24 * Msoft ^ 10)
    let loss := Delta / (91 / 100 : ℝ) ^ 2
    let regional := fun (a b : ℕ) ↦ ∑ i ∈ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ a ≤ i.val ∧ i.val + 1 < b), Φ.term i
    mu ∈ spectrum ℝ H →
    (∀ z ∈ spectrum ℝ H, mu ≤ z) →
    Delta ≤ 1 / ((D : ℝ) ^ 12 * Msoft ^ 10) →
    3 * (32 * Real.exp (-(Tcut - 156 - 2 * g) / 8) +
      (t / (m : ℝ)) * (Tcut / t) ^ m) ≤ tau * g / 1000000 →
    (∀ J : LongIntervalIndex L width,
      let l := J.val.1
      let r := J.val.2
      let coords := Entropy.regionTensorCoordinates q (interval L l r)
      ∃ u v : ℕ, l ≤ u ∧ u ≤ v ∧ v ≤ r ∧ u - l ≤ 2 * ell ∧ r - v ≤ 2 * ell ∧
        (∃ (e2 : ℝ) (x2 : (Fin L → Fin q) → ℂ), star x2 ⬝ᵥ x2 = 1 ∧
          regional u v *ᵥ x2 = (e2 : ℂ) • x2 ∧ (regional u v - (e2 : ℂ) • 1).PosSemidef) ∧
        ∃ T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
          Module.finrank ℂ T = Module.finrank ℂ G ∧ Submodule.IsCloseTo (3 * tau / 200) G T ∧
          ∀ W : Submodule ℂ (EuclideanSpace ℂ (interval L l r → Fin q)),
            Submodule.IsViable 0.04 W (G.map coords.toLinearEquiv.toLinearMap) →
            ∀ V ∈ canonicalHalfSampledIntervalHistory L q l r D (threshold J) rounds
              (F J) xi W G,
              Submodule.IsViable loss
                (canonicalHalfSampledIntervalImage L q l r D (threshold J) rounds (F J) xi W V)
                (T.map coords.toLinearEquiv.toLinearMap)) →
    ∀ U ∈ canonicalIntervalResamplingGood D rounds hwidth threshold N F xi G 0 L,
    IsTerminalRitzEnergyAssignment hq hwidth Φ ell t m D rounds threshold N F xi U := by
  classical
  intro config H hH G Msoft tau loss regional hmu hlow hDelta htail hcert U hU
  let S := fun (a b : ℕ) (U : IntervalResamplingChoices L q rounds) ↦
    balancedIntervalSpace (canonicalIntervalResamplingOperation
      D rounds threshold N F xi U) width hwidth a b
  choose u v hlu huv hvr hleft hright hmid T hTdim hTclose hTview using hcert
  -- The viable children of a listed interval and its literal history.
  have hchild : ∀ J : LongIntervalIndex L width,
      J.val ∈ balancedIntervalMergeList width hwidth 0 L →
      let l := J.val.1
      let r := J.val.2
      let k := l + (r - l) / 2
      let W := adjacentIntervalMerge L q l k r (Nat.le_add_right l _)
        (by have := J.property.1; omega) (S l k U) (S k r U)
      Submodule.IsViable 0.04 W
        (G.map (Entropy.regionTensorCoordinates q (interval L l r)).toLinearEquiv.toLinearMap) ∧
      U (LongIntervalIndex.coordinate J) ∈ canonicalHalfSampledIntervalHistory L q l r D
        (threshold J) rounds (F J) xi W G := by
    intro J hJ l r k W
    have hb := bounds_of_mem_balancedIntervalMergeList width hwidth 0 L (Nat.zero_le L) hJ
    have hviable : ∀ a b : ℕ, (a, b) = (l, k) ∨ (a, b) = (k, r) →
        Submodule.IsViable (3 / 200 : ℝ) (S a b U)
          (G.map (Entropy.regionTensorCoordinates q
            (interval L a b)).toLinearEquiv.toLinearMap) := by
      intro a b hab
      have hab' : a ≤ b ∧ b ≤ L := by
        rcases hab with Φ.term | Φ.term <;> simp only [Prod.mk.injEq] at Φ.term <;> obtain ⟨rfl, rfl⟩ := Φ.term <;>
          dsimp only [l, r, k] <;> omega
      by_cases hshort : b - a ≤ width
      · change Submodule.IsViable (3 / 200 : ℝ) (balancedIntervalSpace _ width hwidth a b) _
        rw [balancedIntervalSpace_of_short _ hwidth hshort]
        exact Submodule.isViable_top (3 / 200) (by norm_num) _
      · have hmem := child_mem_balancedIntervalMergeList width hwidth hJ hab (by omega)
        exact (hU.2 ⟨(a, b), hab'.1, hab'.2, by omega⟩ hmem).1
    refine ⟨Submodule.IsCloseTo.of_le
      (isViable_adjacentIntervalMerge _ _ G _ _ (hviable l k (Or.inl rfl))
        (hviable k r (Or.inr rfl))) (by norm_num), ?_⟩
    exact (hU.2 J hJ).2
  -- The node relation: the actual terminal Ritz value of the soft operator.
  let Rel : LongIntervalIndex L width → ℝ → ℝ → ℝ → Prop := fun J p1 p2 p ↦
    let l := J.val.1
    let r := J.val.2
    let k := l + (r - l) / 2
    let J' := interval L l r
    let sigma0 : Fin L → Fin q := fun _ ↦ ⟨0, hq⟩
    let y0 := ((ManyBody.cutEquiv (fun _ ↦ Fin q) J') sigma0).2
    let native := fun x : J' → Fin q ↦
      (ManyBody.cutEquiv (fun _ ↦ Fin q) J').symm (x, y0)
    ∃ eLeft eRight : ℝ,
      IsRegionalLowerEnergyEstimate Φ l (u J) 0 eLeft ∧
      IsRegionalLowerEnergyEstimate Φ (v J) r 0 eRight ∧
      let center := p1 + p2 - eLeft - eRight - 2
      IsRegionalLowerEnergyEstimate Φ (u J) (v J) 10 center ∧
      let R := regional l r - regional (u J) (v J) + (center : ℂ) • 1 +
        cfc (Real.softTruncation t m) (regional (u J) (v J) - (center : ℂ) • 1)
      let Rnat := R.submatrix native native
      let W := adjacentIntervalMerge L q l k r (Nat.le_add_right l _)
        (by have := J.property.1; omega) (S l k U) (S k r U)
      let Y := canonicalHalfSampledIntervalImage L q l r D (threshold J) rounds (F J) xi W
        (U (LongIntervalIndex.coordinate J))
      ∃ (n : ℕ) (b : OrthonormalBasis (Fin (n + 1)) ℂ Y) (energy : Fin (n + 1) → ℝ),
        Module.finrank ℂ Y = n + 1 ∧
        (∀ j, Y.orthogonalCompression
          (toEuclideanCLM (𝕜 := ℂ) (n := J' → Fin q) Rnat).toLinearMap
            (b j) = (energy j : ℂ) • b j) ∧
        Antitone energy ∧ p = energy (Fin.last n) - 3
  have hleaf : ∀ l r : ℕ, l ≤ r → r ≤ L → ∃ p : ℝ, IsRegionalLowerEnergyEstimate Φ l r 0 p := by
    intro l r hlr hrL
    obtain ⟨eA, _eB, _eP, x, _z, hx, hAx, _hBx, hA, _hB, _rest⟩ :=
      exists_adjacent_interval_energy_merge hq hlr le_rfl hrL Φ h0 h1
    exact ⟨eA, eA, x, hx, hAx, hA, by simp, le_rfl⟩
  have hnode : ∀ J : LongIntervalIndex L width,
      J.val ∈ balancedIntervalMergeList width hwidth 0 L →
      let l := J.val.1
      let r := J.val.2
      let k := l + (r - l) / 2
      ∀ p1 p2 : ℝ,
        IsRegionalLowerEnergyEstimate Φ l k (49 / 16) p1 →
        IsRegionalLowerEnergyEstimate Φ k r (49 / 16) p2 →
        ∃ p : ℝ, IsRegionalLowerEnergyEstimate Φ l r (49 / 16) p ∧ Rel J p1 p2 p := by
    intro J hJ l r k p1 p2 hp1 hp2
    have hlr : l ≤ r := J.property.1
    have hrL : r ≤ L := J.property.2.1
    obtain ⟨e2, x2, hx2, hMx2, hMmin⟩ := hmid J
    obtain ⟨eP, xP, hxP, hPxP, hPmin, eLeft, eRight, xLeft, xRight, hxLeft, hLeft, hLeftMin,
        hxRight, hRight, hRightMin, hupdate⟩ :=
      exists_selected_soft_terminal_node_energy_update (ι := Fin (N J)) (ell := ell)
        hq (hlu J) (huv J) (hvr J) hrL (hleft J) (hright J) Φ h0 h1 g hg t Tcut m D hm hD
        ht hTcut Delta hDelta0 mu e2 x2 (F J) hmu hlow hx2 hMx2 hMmin hDelta htail
    obtain ⟨hcenter, _hc0, _hc1, _hRnat, eSoft, w, _hRlift, _hw, _hRw, _hRmin, _hRnorm,
        _heSoft, _heP, hfinal⟩ :=
      hupdate k (Nat.le_add_right l _) (by dsimp only [k]; omega) p1 p2 hp1 hp2
    obtain ⟨hW, hhist⟩ := hchild J hJ
    have hview := hTview J _ hW _ hhist
    obtain ⟨n, b, energy, hY, heig, hanti, _hlo, _hhi, _hlo', hlow', hup'⟩ :=
      hfinal (T J) (hTdim J) (hTclose J) (Fintype.equivFin (interval L l r → Fin q)).symm _ hview
    refine ⟨energy (Fin.last n) - 3, ⟨eP, xP, hxP, hPxP, hPmin, hlow', hup'⟩, ?_⟩
    exact ⟨eLeft, eRight, ⟨eLeft, xLeft, hxLeft, hLeft, hLeftMin, by simp, le_rfl⟩,
      ⟨eRight, xRight, hxRight, hRight, hRightMin, by simp, le_rfl⟩, hcenter,
      n, b, energy, hY, heig, hanti, rfl⟩
  obtain ⟨estimate, hroot, hrootShort, hlisted⟩ :=
    exists_root_energy_with_node_relation Φ width hwidth Rel hleaf 0 L (Nat.zero_le L) le_rfl
      hnode
  refine ⟨u, v, estimate, hroot, hrootShort, ?_⟩
  intro J hJ l r k J' sigma0 y0 native
  obtain ⟨hJest, hshortL, hshortR, hrel⟩ := hlisted J hJ
  refine ⟨hJest, hshortL, hshortR, hlu J, huv J, hvr J, hleft J, hright J, ?_⟩
  exact hrel

end TNLean.MPS.AreaLaw.ALVV
