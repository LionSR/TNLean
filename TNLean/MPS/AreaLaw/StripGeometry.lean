/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.InitialBuffer

/-!
# Column intervals in a finite strip

The strip is the rectangular induced lattice domain with sites equivalent to
`Fin L × Fin w`. Interactions are the distinct admissible supports of
`TNLean.Lattice.LocalHamiltonian`; columns are never blocked into larger physical sites.

This is geometric input for the extension proposed in issue #9552 of the
one-dimensional note, not a theorem stated in that note. Its counting argument is the
strip counterpart of `part1_arealaw.tex`, lines 29–53, and its separated shells correspond
to Lemma `lem:singlesplit`, lines 388–403.

**Local fix (support size):** issue #9552 claims dimension at most `q^(R+1)` for a
lattice support. A diameter-two cross already has five sites. The valid bound is
`q^(1+2R(R+1))`, independent of strip width; at most `2^(2R(R+1))` distinct supports
contain a specified site. These bounds are supplied by the existing lattice counting
results. They change the constants depending on `q,R`, without changing width scaling.
-/

open TNLean.Lattice

namespace TNLean.MPS.AreaLaw

/-- The rectangular lattice domain `[0,L) × [0,w)`. -/
def stripDomain (L w : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Ico 0 (L : ℤ) ×ˢ Finset.Ico 0 (w : ℤ)

/-- A strip site has nonnegative coordinates below the two side lengths. -/
theorem stripSite_bounds {L w : ℕ} (x : Site (stripDomain L w)) :
    0 ≤ x.1.1 ∧ x.1.1 < L ∧ 0 ≤ x.1.2 ∧ x.1.2 < w := by
  simpa only [stripDomain, Finset.mem_product, Finset.mem_Ico, and_assoc] using x.2

/-- The finite rectangular domain has exactly the requested physical sites. -/
def stripSiteEquiv (L w : ℕ) : (Fin L × Fin w) ≃ Site (stripDomain L w) where
  toFun x := ⟨((x.1 : ℕ), (x.2 : ℕ)), by
    simp only [stripDomain, Finset.mem_product, Finset.mem_Ico]
    exact ⟨⟨by positivity, by exact_mod_cast x.1.isLt⟩,
      ⟨by positivity, by exact_mod_cast x.2.isLt⟩⟩⟩
  invFun x := (⟨x.1.1.toNat, by have := stripSite_bounds x; omega⟩,
    ⟨x.1.2.toNat, by have := stripSite_bounds x; omega⟩)
  left_inv x := by ext <;> simp
  right_inv x := by
    apply Subtype.ext
    have := stripSite_bounds x
    ext <;> simp only <;> omega

/-- The column coordinate of an actual lattice site. -/
def stripColumn {L w : ℕ} (x : Site (stripDomain L w)) : ℕ := x.1.1.toNat

/-- The row coordinate of an actual lattice site. -/
def stripRow {L w : ℕ} (x : Site (stripDomain L w)) : ℕ := x.1.2.toNat

/-- A column interval, clipped by the finite strip domain. -/
def stripInterval (L w a b : ℕ) : Finset (Site (stripDomain L w)) :=
  Finset.univ.filter fun x ↦ a ≤ stripColumn x ∧ stripColumn x < b

/-- Membership in a column interval is determined solely by its column. -/
@[simp] theorem mem_stripInterval {L w a b : ℕ} {x : Site (stripDomain L w)} :
    x ∈ stripInterval L w a b ↔ a ≤ stripColumn x ∧ stripColumn x < b := by
  simp [stripInterval]

/-- At most `w` sites occur in each column of an interval. -/
theorem card_stripInterval_le (L w a b : ℕ) :
    (stripInterval L w a b).card ≤ (b - a) * w := by
  classical
  have hinj : Function.Injective (fun x : Site (stripDomain L w) ↦
      (stripColumn x, stripRow x)) := by
    intro x y h
    have hx := stripSite_bounds x
    have hy := stripSite_bounds y
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    apply Subtype.ext
    simp only [stripColumn, stripRow] at h₁ h₂
    ext <;> omega
  calc (stripInterval L w a b).card ≤
      ((Finset.Ico a b) ×ˢ Finset.range w).card := by
        apply Finset.card_le_card_of_injOn
          (fun x ↦ (stripColumn x, stripRow x)) ?_ hinj.injOn
        intro x hx
        have hx' := mem_stripInterval.mp hx
        have hrow : stripRow x < w := by
          have := stripSite_bounds x
          simp only [stripRow]
          omega
        exact Finset.mem_product.mpr
          ⟨Finset.mem_Ico.mpr hx', Finset.mem_range.mpr hrow⟩
    _ = (b - a) * w := by simp

/-- Enlarging a column interval by `d` adds at most `2dw` sites, including clipped
and empty intervals. This is the strip analogue of the buffer size in Section 5. -/
theorem card_stripInterval_enlargement_sdiff_le (L w a b d : ℕ) :
    (stripInterval L w (a - d) (b + d) \ stripInterval L w a b).card ≤ 2 * d * w := by
  classical
  have hcover : stripInterval L w (a - d) (b + d) \ stripInterval L w a b ⊆
      stripInterval L w (a - d) a ∪ stripInterval L w b (b + d) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_union, mem_stripInterval] at hx ⊢
    omega
  calc _ ≤ _ := Finset.card_le_card hcover
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ (a - (a - d)) * w + ((b + d) - b) * w :=
      Nat.add_le_add (card_stripInterval_le _ _ _ _) (card_stripInterval_le _ _ _ _)
    _ ≤ 2 * d * w := by
      have : a - (a - d) ≤ d := by omega
      simp only [Nat.add_sub_cancel_left]
      nlinarith [Nat.mul_le_mul_right w this]

/-- Bounded lattice diameter bounds the difference of column coordinates. -/
theorem stripColumn_le_add_range {L w R : ℕ} (X : AdmissibleSupport (stripDomain L w) R)
    {x y : Site (stripDomain L w)} (hx : x ∈ X.1) (hy : y ∈ X.1) :
    stripColumn y ≤ stripColumn x + R := by
  obtain ⟨p, hp⟩ := X.2.2 x hx y hy
  have hd := TNLean.PEPS.AreaLaw.supDist_le_of_walk p hp
  have hx' := stripSite_bounds x
  have hy' := stripSite_bounds y
  simp only [TNLean.PEPS.AreaLaw.supDist] at hd
  simp only [stripColumn]
  omega

/-- A split support meets a band of at most `2Rw` sites on the inside of the two cuts. -/
theorem crossingSupport_meets_stripBand {L w R a b : ℕ}
    (X : AdmissibleSupport (stripDomain L w) R)
    (hX : X ∈ Entropy.crossingTerms (fun Y : AdmissibleSupport (stripDomain L w) R ↦ Y.1)
      (stripInterval L w a b)) :
    ∃ x ∈ stripInterval L w a (a + R) ∪ stripInterval L w (b - R) b, x ∈ X.1 := by
  classical
  obtain ⟨⟨x, hx, hxA⟩, y, hy, hyA⟩ := (Finset.mem_filter.mp hX).2
  have hxy := stripColumn_le_add_range X hx hy
  have hyx := stripColumn_le_add_range X hy hx
  refine ⟨x, ?_, hx⟩
  simp only [Finset.mem_union, mem_stripInterval] at hxA hyA ⊢
  omega

/-- The width-independent coefficient in the crossing-support count. -/
def stripCrossConst (R : ℕ) : ℕ := 2 * R * 2 ^ (2 * R * (R + 1))

/-- At most `N_R w` distinct admissible supports cross any column interval. -/
theorem card_crossingTerms_stripInterval_le (L w R a b : ℕ) :
    (Entropy.crossingTerms (fun X : AdmissibleSupport (stripDomain L w) R ↦ X.1)
      (stripInterval L w a b)).card ≤ stripCrossConst R * w := by
  classical
  let band := stripInterval L w a (a + R) ∪ stripInterval L w (b - R) b
  have hcover : Entropy.crossingTerms
      (fun X : AdmissibleSupport (stripDomain L w) R ↦ X.1) (stripInterval L w a b) ⊆
      band.biUnion (fun v ↦ Finset.univ.filter fun X ↦ v ∈ X.1) := by
    intro X hX
    obtain ⟨x, hx, hxX⟩ := crossingSupport_meets_stripBand X hX
    exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_filter.mpr ⟨Finset.mem_univ X, hxX⟩⟩
  have hband : band.card ≤ 2 * R * w := by
    calc _ ≤ _ := Finset.card_union_le _ _
      _ ≤ ((a + R) - a) * w + (b - (b - R)) * w :=
        Nat.add_le_add (card_stripInterval_le _ _ _ _) (card_stripInterval_le _ _ _ _)
      _ ≤ 2 * R * w := by
        have : b - (b - R) ≤ R := by omega
        simp only [Nat.add_sub_cancel_left]
        nlinarith [Nat.mul_le_mul_right w this]
  calc _ ≤ _ := Finset.card_le_card hcover
    _ ≤ band.card * 2 ^ ((1 + 2 * R * (R + 1)) - 1) :=
      Finset.card_biUnion_le_card_mul _ _ _ fun v _ ↦
        TNLean.PEPS.AreaLaw.card_admissibleSupport_containing_le v
    _ ≤ (2 * R * w) * 2 ^ ((1 + 2 * R * (R + 1)) - 1) :=
      Nat.mul_le_mul_right _ hband
    _ = stripCrossConst R * w := by
      simp only [stripCrossConst, Nat.add_sub_cancel_left]
      ring

/-- The strip cut budget has linear width dependence and corrected support dimension. -/
theorem cutLogBudget_stripInterval_le {q : ℕ} (hq : 1 ≤ q) (L w R a b : ℕ) :
    Entropy.cutLogBudget
      (Entropy.crossingTerms (fun X : AdmissibleSupport (stripDomain L w) R ↦ X.1)
        (stripInterval L w a b))
      (Entropy.supportDim (fun _ : Site (stripDomain L w) ↦ q) ∘ fun X ↦ X.1) ≤
      1 + (stripCrossConst R * w : ℕ) *
        Real.log (Real.exp 1 * (q : ℝ) ^ (1 + 2 * R * (R + 1))) ^ 2 := by
  refine (TNLean.PEPS.AreaLaw.cutLogBudget_le_card hq _).trans ?_
  have hc : ((Entropy.crossingTerms
      (fun X : AdmissibleSupport (stripDomain L w) R ↦ X.1)
      (stripInterval L w a b)).card : ℝ) ≤ (stripCrossConst R * w : ℕ) := by
    exact_mod_cast card_crossingTerms_stripInterval_le L w R a b
  gcongr

/-- Column intervals grow when either endpoint moves outwards. -/
theorem stripInterval_mono {L w a b c d : ℕ} (hca : c ≤ a) (hbd : b ≤ d) :
    stripInterval L w a b ⊆ stripInterval L w c d := by
  intro x hx
  simp only [mem_stripInterval] at hx ⊢
  omega

/-- A support splits at most one of the column shells spaced by `R`.
This is the actual support geometry required by the finite-site buffered discount. -/
theorem strip_single_splitting {L w R a b : ℕ}
    (X : AdmissibleSupport (stripDomain L w) R) {i j : ℕ}
    (hi : (∃ x ∈ X.1, x ∈ stripInterval L w (a - (i + 1) * R) (b + (i + 1) * R)) ∧
      ∃ x ∈ X.1, x ∉ stripInterval L w (a - (i + 1) * R) (b + (i + 1) * R))
    (hj : (∃ x ∈ X.1, x ∈ stripInterval L w (a - (j + 1) * R) (b + (j + 1) * R)) ∧
      ∃ x ∈ X.1, x ∉ stripInterval L w (a - (j + 1) * R) (b + (j + 1) * R)) : i = j := by
  have hnot {k l : ℕ} (hkl : k < l)
      (hk : ∃ x ∈ X.1,
        x ∈ stripInterval L w (a - (k + 1) * R) (b + (k + 1) * R))
      (hl : ∃ x ∈ X.1,
        x ∉ stripInterval L w (a - (l + 1) * R) (b + (l + 1) * R)) : False := by
    obtain ⟨x, hxX, hx⟩ := hk
    obtain ⟨y, hyX, hy⟩ := hl
    have hxy := stripColumn_le_add_range X hxX hyX
    have hyx := stripColumn_le_add_range X hyX hxX
    have hstep : (k + 1) * R + R ≤ (l + 1) * R := by
      simpa only [Nat.succ_mul] using
        Nat.mul_le_mul_right R (Nat.succ_le_succ (Nat.succ_le_of_lt hkl))
    simp only [mem_stripInterval] at hx hy
    omega
  rcases lt_trichotomy i j with h | h | h
  · exact (hnot h hi.1 hj.2).elim
  · exact h
  · exact (hnot h hj.1 hi.2).elim

/-- A region between two consecutive whole-column prefixes has only linearly many
crossing supports, regardless of the order chosen inside the last column. -/
theorem card_crossingTerms_stripPrefix_le {L w R c : ℕ}
    (A : Finset (Site (stripDomain L w)))
    (hleft : stripInterval L w 0 c ⊆ A)
    (hright : A ⊆ stripInterval L w 0 (c + 1)) :
    (Entropy.crossingTerms (fun X : AdmissibleSupport (stripDomain L w) R ↦ X.1) A).card ≤
      ((R + 1) * 2 ^ (2 * R * (R + 1))) * w := by
  classical
  let band := stripInterval L w (c - R) (c + 1)
  have hcover : Entropy.crossingTerms
      (fun X : AdmissibleSupport (stripDomain L w) R ↦ X.1) A ⊆
      band.biUnion (fun v ↦ Finset.univ.filter fun X ↦ v ∈ X.1) := by
    intro X hX
    obtain ⟨⟨x, hx, hxA⟩, y, hy, hyA⟩ := (Finset.mem_filter.mp hX).2
    have hxcol := mem_stripInterval.mp (hright hxA)
    have hycol : c ≤ stripColumn y := by
      by_contra hn
      exact hyA (hleft (mem_stripInterval.mpr ⟨Nat.zero_le _, by omega⟩))
    have hdist := stripColumn_le_add_range X hx hy
    have hxband : x ∈ band := by simp only [band, mem_stripInterval]; omega
    exact Finset.mem_biUnion.mpr
      ⟨x, hxband, Finset.mem_filter.mpr ⟨Finset.mem_univ X, hx⟩⟩
  have hband : band.card ≤ (R + 1) * w := by
    refine (card_stripInterval_le L w (c - R) (c + 1)).trans ?_
    exact Nat.mul_le_mul_right w (by omega)
  calc _ ≤ _ := Finset.card_le_card hcover
    _ ≤ band.card * 2 ^ ((1 + 2 * R * (R + 1)) - 1) :=
      Finset.card_biUnion_le_card_mul _ _ _ fun v _ ↦
        TNLean.PEPS.AreaLaw.card_admissibleSupport_containing_le v
    _ ≤ ((R + 1) * w) * 2 ^ ((1 + 2 * R * (R + 1)) - 1) :=
      Nat.mul_le_mul_right _ hband
    _ = _ := by simp only [Nat.add_sub_cancel_left]; ring

end TNLean.MPS.AreaLaw
