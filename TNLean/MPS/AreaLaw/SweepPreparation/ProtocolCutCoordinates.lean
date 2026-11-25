/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SweepPreparation.ProtocolSweepPlacement
import TNLean.MPS.AreaLaw.SweepPreparation.ProtocolSweepGeometry
import TNLean.MPS.Tensor.OpenMPS.CutMatrixGrowth
import TNLean.Network.DependentBond.WholeGroupContraction
import TNLean.MPS.Tensor.VaryingBond.OpenMPSRank
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Original-site cuts of the actual terminal physical coordinates

The physical party tensor is pulled back
along the existing mainConfigurationEquiv. Actual party prefixes correspond to
prefixes of the original sites. Both sides of each cut are identified using
owner fibres and the existing block encodings, including scalar physical
factors at parties with no main sites. The last remainder party retains the
entire final suffix. No node or private register is deleted or reassigned.

The final conclusion is conditional on the actual block-prefix ranks. It does
not derive these ranks from a network, construct a circuit or prove an MPS
approximation theorem. The vector is arbitrary, without normalization or
nonvanishing assumptions.

**Local fix (terminal auxiliary registers):** These coordinate statements concern
main physical factors only. Auxiliary copies retain their original labels and
owners in the private output, as recorded in
`docs/paper-gaps/tnlean_one_dimensional_band_sweep_corrections.tex`.

Source: Part II, prop:sweep, lines 355–375, and proof of Theorem B,
part2b_mps_protocol.tex, lines 605–614.

## Polynomial original-site bond bounds from actual physical party cut ranks

The original-site vector is exactly the
pullback of the physical party vector along mainConfigurationEquiv. Its norm
is unchanged. Actual internal party-prefix rank bounds give all original-site
cut ranks by the existing coordinate and cut-growth argument. The existing
internal-cut rank constructor then supplies a matrix product representation
of this same vector, without normalization or replacement of the vector.

The numerical estimate retains both ceiling errors. The logarithmic width
contributes the prefactor q^40; the rounded alphabet bound contributes
(Cp+1)^χ. The natural exponent and prefactor depend only on q,D,Cp,alpha and χ,
not on the length or the vector. No division by log q is used.

These are auxiliary consumers of rank bounds. No circuit, compression output,
physical family, approximation error or complete Theorem B is constructed.

Source: the one-dimensional note, Part II, proof of Theorem B,
part2b_mps_protocol.tex, lines 605–615. The constructor is the existing
open-boundary rank theorem associated with Part IIa, prop:VC, lines 39–62.
-/

section

noncomputable section

open ManyBody (cutMatrix)

namespace TNLean.MPS.AreaLaw.ChainSweep

variable {L w q : ℕ}

/-! Restriction of the existing owner-fibre grouping to one side of a cut. -/

private def cutOwner {S : Fin L → Prop} {T : Party L w → Prop}
    (h : ∀ x, S x ↔ T (mainOwner L w x)) (x : Subtype S) : Subtype T :=
  ⟨mainOwner L w x.val, (h x.val).mp x.property⟩

private def cutOwnerFiberEquiv {S : Fin L → Prop} {T : Party L w → Prop}
    (h : ∀ x, S x ↔ T (mainOwner L w x)) (p : Subtype T) :
    {x : Subtype S // cutOwner h x = p} ≃ MainSites L w p.val where
  toFun x := ⟨x.val.val, congrArg Subtype.val x.property⟩
  invFun x := ⟨⟨x.val, (h x.val).mpr (x.property.symm ▸ p.property)⟩,
    Subtype.ext x.property⟩
  left_inv _x := Subtype.ext (Subtype.ext rfl)
  right_inv _x := Subtype.ext rfl

private def blockCutEquiv {S : Fin L → Prop} {T : Party L w → Prop}
    (h : ∀ x, S x ↔ T (mainOwner L w x)) :
    (Subtype S → Fin q) ≃ ((p : Subtype T) → Fin (physicalDimension L w q p.val)) :=
  Equiv.piCongrFiberwise (f := cutOwner h) fun p ↦
    (Equiv.arrowCongr (cutOwnerFiberEquiv h p) (Equiv.refl (Fin q))).trans
      (blockEncoding L w q p.val)

private theorem blockCutEquiv_apply {S : Fin L → Prop} {T : Party L w → Prop}
    (h : ∀ x, S x ↔ T (mainOwner L w x)) (a : Subtype S → Fin q) (p : Subtype T) :
    blockCutEquiv (q := q) h a p =
      blockEncoding L w q p.val
        (fun x ↦ a ⟨x.val, (h x.val).mpr (x.property.symm ▸ p.property)⟩) := rfl

/-! The configuration square commutes before taking any rank. -/

private theorem mainConfigurationEquiv_glue (S : Finset (Fin L))
    (T : Finset (Party L w)) (h : ∀ x, x ∈ S ↔ mainOwner L w x ∈ T)
    (a : {x : Fin L // x ∈ S} → Fin q) (b : {x : Fin L // x ∉ S} → Fin q) :
    mainConfigurationEquiv L w q ((ManyBody.cutEquiv (fun _ ↦ Fin q) S).symm (a, b)) =
      (Equiv.piEquivPiSubtypeProd (· ∈ T) (fun p ↦ Fin (physicalDimension L w q p))).symm
        (blockCutEquiv h a, blockCutEquiv (fun x ↦ not_congr (h x)) b) := by
  classical
  funext p
  change blockEncoding L w q p
    (fun x ↦ (ManyBody.cutEquiv (fun _ ↦ Fin q) S).symm (a, b) x.val) = _
  by_cases hp : p ∈ T
  · rw [show
      (Equiv.piEquivPiSubtypeProd (· ∈ T) (fun p ↦ Fin (physicalDimension L w q p))).symm
          (blockCutEquiv h a, blockCutEquiv (fun x ↦ not_congr (h x)) b) p =
        blockCutEquiv h a ⟨p, hp⟩ by
          simp only [Equiv.piEquivPiSubtypeProd_symm_apply, dite_eq_left hp]]
    rw [blockCutEquiv_apply]
    apply congrArg (blockEncoding L w q p)
    funext x
    exact ManyBody.cutEquiv_symm_apply_mem (X := fun _ ↦ Fin q) a b
      ((h x.val).mpr (x.property.symm ▸ hp))
  · rw [show
      (Equiv.piEquivPiSubtypeProd (· ∈ T) (fun p ↦ Fin (physicalDimension L w q p))).symm
          (blockCutEquiv h a, blockCutEquiv (fun x ↦ not_congr (h x)) b) p =
        blockCutEquiv (T := fun p : Party L w ↦ p ∉ T)
          (fun x ↦ not_congr (h x)) b ⟨p, hp⟩ by
          simp only [Equiv.piEquivPiSubtypeProd_symm_apply, dite_eq_right hp]]
    rw [blockCutEquiv_apply]
    apply congrArg (blockEncoding L w q p)
    funext x
    exact ManyBody.cutEquiv_symm_apply_not_mem (X := fun _ ↦ Fin q) a b
      ((not_congr (h x.val)).mpr (x.property.symm ▸ hp))

private theorem cutMatrix_eq_flattening_submatrix
    (ψ : EuclideanSpace ℂ ((p : Party L w) → Fin (physicalDimension L w q p)))
    (k : ℕ) (T : Finset (Party L w))
    (h : ∀ x, x ∈ leftBlock L k ↔ mainOwner L w x ∈ T) :
    cutMatrix (leftBlock L k) (WithLp.toLp 2 (fun x ↦ ψ (mainConfigurationEquiv L w q x))) =
      (TNLean.Network.WholeGroup.flattening (fun y ↦ ψ y) T).submatrix
        (blockCutEquiv h) (blockCutEquiv (fun x ↦ not_congr (h x))) := by
  classical
  ext a b
  rw [ManyBody.cutMatrix_apply]
  change ψ (mainConfigurationEquiv L w q
    ((ManyBody.cutEquiv (fun _ ↦ Fin q) (leftBlock L k)).symm (a, b))) = _
  exact congrArg (fun y ↦ ψ y) (mainConfigurationEquiv_glue (leftBlock L k) T h a b)

private theorem partyLevel_mainOwner_lt_iff (r : ℕ) (hr : r ≤ stageCount L w)
    (x : Fin L) : partyLevel (mainOwner L w x) < r ↔ x.val < r * (20 * w) := by
  classical
  unfold mainOwner
  split_ifs with hx
  · have ht : 0 < 20 * w := by
      by_contra ht
      have hz : 20 * w = 0 := Nat.eq_zero_of_not_pos ht
      rw [hz, Nat.mul_zero] at hx
      exact Nat.not_lt_zero _ hx
    change x.val / (20 * w) < r ↔ x.val < r * (20 * w)
    exact Nat.div_lt_iff_lt_mul ht
  · change stageCount L w < r ↔ x.val < r * (20 * w)
    have hm := Nat.mul_le_mul_right (20 * w) hr
    omega

/-- Actual physical party prefixes have the same rank as the original-site cut
at r completed block lengths. Every scalar physical factor is retained.
Source: Part II, prop:sweep, lines 355–375, and Theorem B, lines 605–614. -/
theorem rank_partyPrefix_eq_cutMatrix
    (ψ : EuclideanSpace ℂ ((p : Party L w) → Fin (physicalDimension L w q p)))
    (r : ℕ) (hr : r ≤ stageCount L w) :
    let T := Finset.univ.filter fun p : Party L w ↦ partyLevel p < r
    let Φ := WithLp.toLp 2 (fun x ↦ ψ (mainConfigurationEquiv L w q x))
    (TNLean.Network.WholeGroup.flattening (fun y ↦ ψ y) T).rank =
      (cutMatrix (leftBlock L (r * (20 * w))) Φ).rank := by
  classical
  dsimp only
  let T := Finset.univ.filter fun p : Party L w ↦ partyLevel p < r
  have h : ∀ x, x ∈ leftBlock L (r * (20 * w)) ↔ mainOwner L w x ∈ T := by
    intro x
    simpa only [mem_leftBlock, T, Finset.mem_filter, Finset.mem_univ, true_and] using
      (partyLevel_mainOwner_lt_iff r hr x).symm
  exact (Matrix.rank_submatrix _ _ _).symm.trans
    (congrArg Matrix.rank (cutMatrix_eq_flattening_submatrix ψ (r * (20 * w)) T h).symm)

/-- The prefix after all m+1 levels includes the actual final remainder party,
and corresponds to the original-site full-chain cut. No party is removed.
Source: Part II, prop:sweep, lines 355–375. -/
theorem rank_partyPrefix_last_eq_cutMatrix
    (ψ : EuclideanSpace ℂ ((p : Party L w) → Fin (physicalDimension L w q p))) :
    let T := Finset.univ.filter fun p : Party L w ↦ partyLevel p < stageCount L w + 1
    let Φ := WithLp.toLp 2 (fun x ↦ ψ (mainConfigurationEquiv L w q x))
    (TNLean.Network.WholeGroup.flattening (fun y ↦ ψ y) T).rank =
      (cutMatrix (leftBlock L L) Φ).rank := by
  classical
  dsimp only
  let T := Finset.univ.filter fun p : Party L w ↦ partyLevel p < stageCount L w + 1
  have hlevel (p : Party L w) : partyLevel p < stageCount L w + 1 := by
    cases p with
    | inl p => exact p.isLt
    | inr p => exact p.isLt.trans (Nat.lt_succ_self _)
  have h : ∀ x, x ∈ leftBlock L L ↔ mainOwner L w x ∈ T := by
    intro x
    simp only [mem_leftBlock, x.isLt, T, Finset.mem_filter, Finset.mem_univ, true_and,
      hlevel, iff_self]
  exact (Matrix.rank_submatrix _ _ _).symm.trans
    (congrArg Matrix.rank (cutMatrix_eq_flattening_submatrix ψ L T h).symm)

/-- Actual internal physical party-prefix rank bounds imply the uniform
original-site cut bound. The endpoint ranks are at most one for every vector.
This is an auxiliary coordinate and interpolation theorem, not a network or
physical endpoint-rank theorem. Source: Part II, Theorem B, lines 605–614. -/
theorem rank_cutMatrix_le_of_partyPrefix_bounds
    (ψ : EuclideanSpace ℂ ((p : Party L w) → Fin (physicalDimension L w q p)))
    {R : ℕ} (hq : 1 ≤ q) (hw : 1 ≤ w) (hL : 60 * w ≤ L) (hR : 1 ≤ R)
    (hprefix : ∀ r : ℕ, 0 < r → r ≤ stageCount L w →
      (TNLean.Network.WholeGroup.flattening (fun y ↦ ψ y)
        (Finset.univ.filter fun p : Party L w ↦ partyLevel p < r)).rank ≤ R)
    (k : ℕ) (hk : k ≤ L) :
    let Φ := WithLp.toLp 2 (fun x ↦ ψ (mainConfigurationEquiv L w q x))
    (cutMatrix (leftBlock L k) Φ).rank ≤ q ^ (40 * w) * R := by
  classical
  let Φ : EuclideanSpace ℂ (Fin L → Fin q) :=
    WithLp.toLp 2 (fun x ↦ ψ (mainConfigurationEquiv L w q x))
  change (cutMatrix (leftBlock L k) Φ).rank ≤ _
  let m := stageCount L w
  let t := 20 * w
  have ht : 0 < t := by dsimp [t]; omega
  have hgeometry : 3 * (20 * w) ≤ L := by omega
  have heq := terminal_length_eq L w hgeometry
  change L = m * t + 3 * t + L % t at heq
  have hmL : m * t ≤ L := by omega
  have hterminal := (terminal_length_bounds L w hw hgeometry).2
  change L - m * t < 4 * t at hterminal
  have hcut (r : ℕ) (hr : r ≤ m) : (cutMatrix (leftBlock L (r * t)) Φ).rank ≤ R := by
    by_cases hr0 : r = 0
    · subst r
      rw [Nat.zero_mul]
      exact (rank_cutMatrix_zero_le Φ).trans hR
    · have h := hprefix r (Nat.pos_of_ne_zero hr0) hr
      rw [rank_partyPrefix_eq_cutMatrix ψ r hr] at h
      exact h
  by_cases hmain : k < m * t
  · let r := k / t
    have hr : r < m := (Nat.div_lt_iff_lt_mul ht).mpr hmain
    have ha : r * t ≤ k := Nat.div_mul_le_self k t
    have hkb : k ≤ (r + 1) * t := by
      have hd := Nat.div_add_mod k t
      have hm := Nat.mod_lt k ht
      dsimp [r]
      nlinarith
    have hbL : (r + 1) * t ≤ L :=
      (Nat.mul_le_mul_right t (Nat.succ_le_of_lt hr)).trans hmL
    have hwidth : (r + 1) * t - r * t ≤ 80 * w := by
      dsimp [t]
      simp only [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left]
      omega
    exact rank_cutMatrix_le_pow_forty_mul Φ hq ha hkb hbL hwidth
      (hcut r hr.le) (hcut (r + 1) (Nat.succ_le_of_lt hr))
  · have hmk : m * t ≤ k := Nat.le_of_not_gt hmain
    have hwidth : L - m * t ≤ 80 * w := by dsimp only [t]; dsimp only [t] at hterminal; omega
    exact rank_cutMatrix_le_pow_forty_mul Φ hq hmk hk (le_refl L) hwidth
      (hcut m (le_refl m)) ((rank_cutMatrix_le_one_of_le (le_refl L) Φ).trans hR)

end TNLean.MPS.AreaLaw.ChainSweep
end

end

section

noncomputable section

open ManyBody (cutMatrix)

namespace TNLean.MPS.AreaLaw.ChainSweep

/-- Both ceiling errors give a polynomial bound with constants independent of
L and w. The natural alpha is the exponent of the alphabet bound.
Source: Part II, proof of Theorem B, lines 605–615. -/
theorem polynomial_bond_bound_of_ceil_width
    {q : ℕ} {D Cp : ℝ} {α : ℕ} (χ : ℕ)
    (hq : 1 ≤ q) (hD : 1 ≤ D) (hCp : 0 ≤ Cp) (hα : 0 < α)
    {L w : ℕ} (hL : 2 ≤ L) (hw : w = ⌈D * Real.log L⌉₊) :
    ((q ^ (40 * w) * (max 1 ⌈Cp * (L : ℝ) ^ α⌉₊) ^ χ : ℕ) : ℝ) ≤
      (q : ℝ) ^ 40 * (Cp + 1) ^ χ *
        (L : ℝ) ^ (max 1 (⌈40 * D * Real.log q⌉₊ + χ * α)) := by
  let N := max 1 ⌈Cp * (L : ℝ) ^ α⌉₊
  let u := ⌈40 * D * Real.log q⌉₊
  let n := max 1 (u + χ * α)
  have hqR : 1 ≤ (q : ℝ) := by exact_mod_cast hq
  have hLR : 1 ≤ (L : ℝ) := by exact_mod_cast (by omega : 1 ≤ L)
  have hq0 : 0 < (q : ℝ) := lt_of_lt_of_le zero_lt_one hqR
  have hL0 : 0 < (L : ℝ) := lt_of_lt_of_le zero_lt_one hLR
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hqR
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hLR
  have hwidth : (w : ℝ) ≤ D * Real.log L + 1 := by
    rw [hw]
    exact (Nat.ceil_lt_add_one (mul_nonneg (zero_le_one.trans hD) hlogL)).le
  have hu : 40 * D * Real.log q ≤ (u : ℝ) := Nat.le_ceil _
  have hqfactor : (q : ℝ) ^ (40 * w) ≤ (q : ℝ) ^ 40 * (L : ℝ) ^ u := by
    apply (Real.log_le_log_iff (pow_pos hq0 _) (mul_pos (pow_pos hq0 _) (pow_pos hL0 _))).mp
    rw [Real.log_mul (pow_ne_zero _ hq0.ne') (pow_ne_zero _ hL0.ne')]
    simp only [Real.log_pow, Nat.cast_mul, Nat.cast_ofNat]
    have h₁ := mul_le_mul_of_nonneg_right hwidth
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 40) hlogq)
    have h₂ := mul_le_mul_of_nonneg_right hu hlogL
    nlinarith
  have hLpower : (1 : ℝ) ≤ (L : ℝ) ^ α :=
    hLR.trans (le_self_pow₀ hLR hα.ne')
  have hceil : (⌈Cp * (L : ℝ) ^ α⌉₊ : ℝ) ≤ Cp * (L : ℝ) ^ α + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hCp (pow_nonneg hL0.le _))).le
  have hN : (N : ℝ) ≤ (Cp + 1) * (L : ℝ) ^ α := by
    dsimp only [N]
    rw [Nat.cast_max, Nat.cast_one]
    apply max_le
    · nlinarith [mul_nonneg hCp (pow_nonneg hL0.le α)]
    · nlinarith
  have hNpower := pow_le_pow_left₀ (Nat.cast_nonneg N) hN χ
  simp only [Nat.cast_mul, Nat.cast_pow]
  calc
    (q : ℝ) ^ (40 * w) * (N : ℝ) ^ χ
        ≤ ((q : ℝ) ^ 40 * (L : ℝ) ^ u) * ((Cp + 1) * (L : ℝ) ^ α) ^ χ :=
      mul_le_mul hqfactor hNpower (pow_nonneg (Nat.cast_nonneg N) _)
        (mul_nonneg (pow_nonneg hq0.le _) (pow_nonneg hL0.le _))
    _ = (q : ℝ) ^ 40 * (Cp + 1) ^ χ * (L : ℝ) ^ (u + χ * α) := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm α χ, pow_add]
      ac_rfl
    _ ≤ (q : ℝ) ^ 40 * (Cp + 1) ^ χ * (L : ℝ) ^ n :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hLR (le_max_right 1 (u + χ * α))) (by positivity)

/-- A unit physical party vector with the actual polynomial block-prefix rank
bounds gives a unit original-site MPS with an explicit polynomial bond bound.
The party-prefix rank bounds are auxiliary inputs, not physical conclusions.
Source: Part II, proof of Theorem B, lines 605–615. -/
theorem isOpenMPS_of_polynomial_partyPrefix_bounds
    {q : ℕ} {D Cp : ℝ} {α : ℕ} (χ : ℕ)
    (hq : 1 ≤ q) (hD : 1 ≤ D) (hCp : 0 ≤ Cp) (hα : 0 < α)
    {L w : ℕ} (hL : 2 ≤ L) (hw : w = ⌈D * Real.log L⌉₊)
    (hlarge : 60 * w ≤ L)
    (ψ : EuclideanSpace ℂ ((p : Party L w) → Fin (physicalDimension L w q p)))
    (hψ : ‖ψ‖ = 1)
    (hprefix : ∀ r : ℕ, 0 < r → r ≤ stageCount L w →
      (TNLean.Network.WholeGroup.flattening (fun y ↦ ψ y)
        (Finset.univ.filter fun p : Party L w ↦ partyLevel p < r)).rank ≤
          (max 1 ⌈Cp * (L : ℝ) ^ α⌉₊) ^ χ) :
    let Φ : EuclideanSpace ℂ (Fin L → Fin q) :=
      WithLp.toLp 2 (fun x ↦ ψ (mainConfigurationEquiv L w q x))
    let B := q ^ (40 * w) * (max 1 ⌈Cp * (L : ℝ) ^ α⌉₊) ^ χ
    let n := max 1 (⌈40 * D * Real.log q⌉₊ + χ * α)
    ‖Φ‖ = 1 ∧ (∀ k : ℕ, k ≤ L → (cutMatrix (leftBlock L k) Φ).rank ≤ B) ∧
      IsOpenMPS L q B (fun x ↦ Φ x) ∧ 1 ≤ n ∧
        (B : ℝ) ≤ (q : ℝ) ^ 40 * (Cp + 1) ^ χ * (L : ℝ) ^ n := by
  classical
  let Φ : EuclideanSpace ℂ (Fin L → Fin q) :=
    WithLp.toLp 2 (fun x ↦ ψ (mainConfigurationEquiv L w q x))
  let R := (max 1 ⌈Cp * (L : ℝ) ^ α⌉₊) ^ χ
  let B := q ^ (40 * w) * R
  let n := max 1 (⌈40 * D * Real.log q⌉₊ + χ * α)
  change ‖Φ‖ = 1 ∧ (∀ k : ℕ, k ≤ L → (cutMatrix (leftBlock L k) Φ).rank ≤ B) ∧
    IsOpenMPS L q B (fun x ↦ Φ x) ∧ 1 ≤ n ∧
      (B : ℝ) ≤ (q : ℝ) ^ 40 * (Cp + 1) ^ χ * (L : ℝ) ^ n
  have hw1 : 1 ≤ w := by
    rw [hw]
    apply Nat.one_le_ceil_iff.mpr
    exact mul_pos (lt_of_lt_of_le zero_lt_one hD)
      (Real.log_pos (by exact_mod_cast (by omega : 1 < L)))
  have hR : 1 ≤ R := Nat.one_le_iff_ne_zero.mpr
    (pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _))))
  have hnorm : ‖Φ‖ = 1 := by
    change ‖LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (mainConfigurationEquiv L w q).symm ψ‖ = 1
    rw [LinearIsometryEquiv.norm_map, hψ]
  have hcuts (k : ℕ) (hk : k ≤ L) : (cutMatrix (leftBlock L k) Φ).rank ≤ B :=
    rank_cutMatrix_le_of_partyPrefix_bounds ψ hq hw1 hlarge hR hprefix k hk
  have hmps : IsOpenMPS L q B (fun x ↦ Φ x) :=
    isOpenMPS_of_internal_cutMatrix_rank_le Φ (fun k _ hk ↦ hcuts k hk.le)
  exact ⟨hnorm, hcuts, hmps, le_max_left _ _,
    polynomial_bond_bound_of_ceil_width χ hq hD hCp hα hL hw⟩

end TNLean.MPS.AreaLaw.ChainSweep
end

end
