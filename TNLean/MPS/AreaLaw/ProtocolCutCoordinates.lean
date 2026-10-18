/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolSweepPlacement
import TNLean.MPS.AreaLaw.ProtocolSweepGeometry
import TNLean.MPS.AreaLaw.CutMatrixGrowth
import TNLean.PEPS.Approximation.WholeGroupContraction

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
-/

noncomputable section

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
    mainConfigurationEquiv L w q ((Entropy.cutEquiv (fun _ : Fin L ↦ q) S).symm (a, b)) =
      (Equiv.piEquivPiSubtypeProd (· ∈ T) (fun p ↦ Fin (physicalDimension L w q p))).symm
        (blockCutEquiv h a, blockCutEquiv (fun x ↦ not_congr (h x)) b) := by
  classical
  funext p
  change blockEncoding L w q p
    (fun x ↦ (Entropy.cutEquiv (fun _ : Fin L ↦ q) S).symm (a, b) x.val) = _
  by_cases hp : p ∈ T
  · rw [show
      (Equiv.piEquivPiSubtypeProd (· ∈ T) (fun p ↦ Fin (physicalDimension L w q p))).symm
          (blockCutEquiv h a, blockCutEquiv (fun x ↦ not_congr (h x)) b) p =
        blockCutEquiv h a ⟨p, hp⟩ by
          simp only [Equiv.piEquivPiSubtypeProd_symm_apply, dite_eq_left hp]]
    rw [blockCutEquiv_apply]
    apply congrArg (blockEncoding L w q p)
    funext x
    exact Entropy.cutEquiv_symm_apply_mem (n := fun _ : Fin L ↦ q) a b
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
    exact Entropy.cutEquiv_symm_apply_not_mem (n := fun _ : Fin L ↦ q) a b
      ((not_congr (h x.val)).mpr (x.property.symm ▸ hp))

private theorem cutMatrix_eq_flattening_submatrix
    (ψ : EuclideanSpace ℂ ((p : Party L w) → Fin (physicalDimension L w q p)))
    (k : ℕ) (T : Finset (Party L w))
    (h : ∀ x, x ∈ leftBlock L k ↔ mainOwner L w x ∈ T) :
    cutMatrix (WithLp.toLp 2 (fun x ↦ ψ (mainConfigurationEquiv L w q x))) k =
      (TNLean.PEPS.WholeGroup.flattening (fun y ↦ ψ y) T).submatrix
        (blockCutEquiv h) (blockCutEquiv (fun x ↦ not_congr (h x))) := by
  classical
  ext a b
  rw [cutMatrix_apply]
  change ψ (mainConfigurationEquiv L w q
    ((Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k)).symm (a, b))) = _
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
    (TNLean.PEPS.WholeGroup.flattening (fun y ↦ ψ y) T).rank =
      (cutMatrix Φ (r * (20 * w))).rank := by
  classical
  dsimp only
  let T := Finset.univ.filter fun p : Party L w ↦ partyLevel p < r
  have h : ∀ x, x ∈ leftBlock L (r * (20 * w)) ↔ mainOwner L w x ∈ T := by
    intro x
    simpa only [mem_leftBlock, T, Finset.mem_filter, Finset.mem_univ, true_and] using
      (partyLevel_mainOwner_lt_iff r hr x).symm
  rw [cutMatrix_eq_flattening_submatrix ψ (r * (20 * w)) T h, Matrix.rank_submatrix]

/-- The prefix after all m+1 levels includes the actual final remainder party,
and corresponds to the original-site full-chain cut. No party is removed.
Source: Part II, prop:sweep, lines 355–375. -/
theorem rank_partyPrefix_last_eq_cutMatrix
    (ψ : EuclideanSpace ℂ ((p : Party L w) → Fin (physicalDimension L w q p))) :
    let T := Finset.univ.filter fun p : Party L w ↦ partyLevel p < stageCount L w + 1
    let Φ := WithLp.toLp 2 (fun x ↦ ψ (mainConfigurationEquiv L w q x))
    (TNLean.PEPS.WholeGroup.flattening (fun y ↦ ψ y) T).rank = (cutMatrix Φ L).rank := by
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
  rw [cutMatrix_eq_flattening_submatrix ψ L T h, Matrix.rank_submatrix]

/-- Actual internal physical party-prefix rank bounds imply the uniform
original-site cut bound. The endpoint ranks are at most one for every vector.
This is an auxiliary coordinate and interpolation theorem, not a network or
physical endpoint-rank theorem. Source: Part II, Theorem B, lines 605–614. -/
theorem rank_cutMatrix_le_of_partyPrefix_bounds
    (ψ : EuclideanSpace ℂ ((p : Party L w) → Fin (physicalDimension L w q p)))
    {R : ℕ} (hq : 1 ≤ q) (hw : 1 ≤ w) (hL : 60 * w ≤ L) (hR : 1 ≤ R)
    (hprefix : ∀ r : ℕ, 0 < r → r ≤ stageCount L w →
      (TNLean.PEPS.WholeGroup.flattening (fun y ↦ ψ y)
        (Finset.univ.filter fun p : Party L w ↦ partyLevel p < r)).rank ≤ R)
    (k : ℕ) (hk : k ≤ L) :
    let Φ := WithLp.toLp 2 (fun x ↦ ψ (mainConfigurationEquiv L w q x))
    (cutMatrix Φ k).rank ≤ q ^ (40 * w) * R := by
  classical
  let Φ : EuclideanSpace ℂ (Fin L → Fin q) :=
    WithLp.toLp 2 (fun x ↦ ψ (mainConfigurationEquiv L w q x))
  change (cutMatrix Φ k).rank ≤ _
  let m := stageCount L w
  let t := 20 * w
  have ht : 0 < t := by dsimp [t]; omega
  have hgeometry : 3 * (20 * w) ≤ L := by omega
  have heq := terminal_length_eq L w hgeometry
  change L = m * t + 3 * t + L % t at heq
  have hmL : m * t ≤ L := by omega
  have hterminal := (terminal_length_bounds L w hw hgeometry).2
  change L - m * t < 4 * t at hterminal
  have hcut (r : ℕ) (hr : r ≤ m) : (cutMatrix Φ (r * t)).rank ≤ R := by
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
