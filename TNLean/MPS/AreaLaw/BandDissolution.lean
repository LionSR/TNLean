/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Basic
import TNLean.PEPS.Approximation.FrameBoundedChanges
import TNLean.PEPS.Approximation.SheetStackSourceBoundedChange

/-!
# One corrected band dissolution on a chain

The hole-free frames in the band operation satisfy the stated final ownership identities.
Eight primitive mutual-information estimates yield the eight actual circuit steps, with their
source and error bounds, in any surrounding stack of spectator frames. This is a conditional
intermediate construction: deriving the information estimates from logarithmic separation and
assembling the full sweep are separate results.

Integer-ended bands are half-open. The exchange window remains open, including at odd widths.
The main sheet is restored outside its original band, which passes to the right-hand party.
The auxiliary sheet is retained at its actual final owners.

**Local fix (half-open lattice bands):** The printed open integer-ended moves miss the site
`a - 3 * w`: it passes from C to A to B, but lies in neither final open band and would remain
at B. Half-open integer-ended bands restore C at that site. The open real exchange window is
unchanged. The retired auxiliary retains A on `[a - 3*w, a - 2*w)`, B on
`[a - 2*w, a - w)`, and C elsewhere; it is not an all-C copy. The distinguished physical
outputs belong to the main sheet, while the auxiliary registers retain their actual owners.
These corrections are documented in
`docs/paper-gaps/tnlean_one_dimensional_band_sweep_corrections.tex`.

Source: the one-dimensional note, Part II, `part2b_mps_protocol.tex`, `con:band`, lines 248–276;
the corrected endpoint convention in
`docs/paper-gaps/tnlean_one_dimensional_band_sweep_corrections.tex`.
The construction uses a particular adjacent main/auxiliary occurrence in a stack. It never
identifies auxiliary copies by their geometric centre: a repeated centre at a different stage
or side is a different stack occurrence, preserved among the spectators until activated.
-/

noncomputable section

open Matrix
open TNLean.PEPS TNLean.PEPS.EncodedFrame TNLean.PEPS.PairEffect
open scoped InnerProductSpace

namespace TNLean.MPS.AreaLaw.OneBand

variable {L q : ℕ} {Party : Type} {pos : Fin L → ℝ × ℝ}

/-- The initial main sheet, with its actual ownership outside the local band unchanged. -/
def main₀ (own : Fin L → Party) : Frame pos q Party := Frame.raw own

/-- A fresh auxiliary copy held privately by the left-hand party. -/
def aux₀ (C : Party) : Frame pos q Party := Frame.raw fun _ ↦ C

def aux₁ (B C : Party) (a w : ℕ) : Frame pos q Party :=
  (aux₀ C).changeOwner (interval L (a - 6 * w) (a - w)) B

def aux₂ (A B C : Party) (a w : ℕ) : Frame pos q Party :=
  (aux₁ B C a w).changeOwner (interval L (a - 5 * w) (a - 2 * w)) A

def aux₃ (A B C : Party) (a w : ℕ) : Frame pos q Party :=
  (aux₂ A B C a w).changeOwner (interval L (a - 4 * w) (a - 3 * w)) C

/-- The open exchange window, with no integer rounding or parity premise. -/
def exchangeRegion (L a w : ℕ) : Finset (Fin L) :=
  Finset.univ.filter fun x ↦
    (a : ℝ) - 7 * w < x.val ∧ (x.val : ℝ) < a - (7 / 2 : ℝ) * w

/-- The existing two-sheet exchange applied to these two actual hole-free frames. -/
def exchange (own : Fin L → Party) (A B C : Party) (a w : ℕ) :
    TwoSheetExchange pos q Party :=
  TwoSheetExchange.ofFrames (main₀ own) (aux₃ A B C a w) (exchangeRegion L a w)
    (fun _ ↦ true)
    (by
      intro h hh
      simp [main₀, aux₃, aux₂, aux₁, aux₀, Frame.raw, Frame.changeOwner] at hh)
    (by
      intro h hh
      simp [main₀, aux₃, aux₂, aux₁, aux₀, Frame.raw, Frame.changeOwner] at hh)

def main₄ (own : Fin L → Party) (A B C : Party) (a w : ℕ) : Frame pos q Party :=
  (exchange own A B C a w).newFrame₁

/-- This sheet is retired immediately after the exchange; later events do not change it. -/
def aux₄ (own : Fin L → Party) (A B C : Party) (a w : ℕ) : Frame pos q Party :=
  (exchange own A B C a w).newFrame₂

/-- Death of the C-owned band into A. Its information frame is this after-death frame. -/
def main₅ (own : Fin L → Party) (A B C : Party) (a w : ℕ) : Frame pos q Party :=
  (main₄ own A B C a w).changeOwner (interval L (a - 4 * w) a) A

/-- Death of the A-owned band into B, again using the after-death environment. -/
def main₆ (own : Fin L → Party) (A B C : Party) (a w : ℕ) : Frame pos q Party :=
  (main₅ own A B C a w).changeOwner (interval L (a - 5 * w) (a + w)) B

def main₇ (own : Fin L → Party) (A B C : Party) (a w : ℕ) : Frame pos q Party :=
  (main₆ own A B C a w).changeOwner (interval L (a - 3 * w) a) C

def main₈ (own : Fin L → Party) (A B C : Party) (a w : ℕ) : Frame pos q Party :=
  (main₇ own A B C a w).changeOwner (interval L (a - 6 * w) (a - 3 * w)) C

/-- The actual nine frame pairs. Only the selected auxiliary occurrence is modified. -/
def frames (own : Fin L → Party) (A B C : Party) (a w : ℕ) :
    ℕ → List (Frame pos q Party)
  | 0 => [main₀ own, aux₀ C]
  | 1 => [main₀ own, aux₁ B C a w]
  | 2 => [main₀ own, aux₂ A B C a w]
  | 3 => [main₀ own, aux₃ A B C a w]
  | 4 => [main₄ own A B C a w, aux₄ own A B C a w]
  | 5 => [main₅ own A B C a w, aux₄ own A B C a w]
  | 6 => [main₆ own A B C a w, aux₄ own A B C a w]
  | 7 => [main₇ own A B C a w, aux₄ own A B C a w]
  | _ => [main₈ own A B C a w, aux₄ own A B C a w]

def participants (A B C : Party) (j : Fin 8) : Set Party :=
  match j.val with
  | 0 => {C, B}
  | 1 => {B, A}
  | 2 => {A, C}
  | 3 => {C}
  | 4 => {C, A}
  | 5 => {A, B}
  | 6 => {B, C}
  | _ => {B, C}

/-! ## Exact geometric obligations, not additional hypotheses on the construction -/

/-- Equality of hole-free frames reduces to their actual raw ownership functions. -/
private theorem holeFree_ext {F G : Frame pos q Party} (hF : F.holes = [])
    (hG : G.holes = []) (howner : ∀ x, F.owner x = G.owner x) : F = G := by
  rcases F with ⟨fo, fh, fd⟩
  rcases G with ⟨go, gh, gd⟩
  dsimp at hF hG howner
  subst fh
  subst gh
  have ho : fo = go := funext howner
  subst go
  rfl

/-- The auxiliary ownership function on its four assigned A/B intervals. -/
private theorem aux₃_owner_normal_form (A B C : Party) (a w : ℕ) (x : Fin L) :
    (aux₃ (pos := pos) (q := q) A B C a w).owner x =
      if x ∈ interval L (a - 6 * w) (a - 5 * w) then B
      else if x ∈ interval L (a - 5 * w) (a - 4 * w) then A
      else if x ∈ interval L (a - 3 * w) (a - 2 * w) then A
      else if x ∈ interval L (a - 2 * w) (a - w) then B else C := by
  classical
  simp only [aux₃, aux₂, aux₁, aux₀, Frame.changeOwner, Frame.raw, mem_interval]
  split_ifs <;> first | rfl | omega

/-- The open exchange window lies strictly below the surviving right auxiliary intervals. -/
private theorem exchangeRegion_subset_window (a w : ℕ) (hleft : 8 * w ≤ a) :
    exchangeRegion L a w ⊆ interval L (a - 7 * w) (a - 3 * w) := by
  intro x hx
  have hx' : (a : ℝ) - 7 * w < x.val ∧
      (x.val : ℝ) < a - (7 / 2 : ℝ) * w := by
    simpa only [exchangeRegion, Finset.mem_filter, Finset.mem_univ, true_and] using hx
  have h7 : ((a - 7 * w : ℕ) : ℝ) = (a : ℝ) - 7 * w := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat]
  have h3 : ((a - 3 * w : ℕ) : ℝ) = (a : ℝ) - 3 * w := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat]
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  have hl : ((a - 7 * w : ℕ) : ℝ) ≤ x.val := by
    rw [h7]
    linarith [hx'.1]
  have hu : (x.val : ℝ) < ((a - 3 * w : ℕ) : ℝ) := by
    rw [h3]
    linarith [hx'.2]
  simp only [mem_interval]
  exact ⟨by exact_mod_cast hl, by exact_mod_cast hu⟩

/-- Both left auxiliary intervals are exchanged, including their half-open endpoints. -/
private theorem left_changes_subset_exchangeRegion (a w : ℕ) (hw : 1 ≤ w)
    (hleft : 8 * w ≤ a) :
    interval L (a - 6 * w) (a - 4 * w) ⊆ exchangeRegion L a w := by
  intro x hx
  have hx' := mem_interval.mp hx
  have h6 : ((a - 6 * w : ℕ) : ℝ) = (a : ℝ) - 6 * w := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat]
  have h4 : ((a - 4 * w : ℕ) : ℝ) = (a : ℝ) - 4 * w := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat]
  have hw0 : (0 : ℝ) < w := by exact_mod_cast (show 0 < w by omega)
  have hl : ((a - 6 * w : ℕ) : ℝ) ≤ x.val := by exact_mod_cast hx'.1
  have hu : (x.val : ℝ) < ((a - 4 * w : ℕ) : ℝ) := by exact_mod_cast hx'.2
  rw [h6] at hl
  rw [h4] at hu
  simp only [exchangeRegion, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> linarith

/-- Only the two left auxiliary intervals can change the main ownership in the exchange. -/
private theorem main₄_owner_normal_form (own : Fin L → Party) (A B C : Party) (a w : ℕ)
    (hw : 1 ≤ w) (hleft : 8 * w ≤ a)
    (hC : ∀ x ∈ interval L (a - 8 * w) a, own x = C) (x : Fin L) :
    (main₄ (pos := pos) (q := q) own A B C a w).owner x =
      if x ∈ interval L (a - 6 * w) (a - 5 * w) then B
      else if x ∈ interval L (a - 5 * w) (a - 4 * w) then A else own x := by
  classical
  change (if x ∈ exchangeRegion L a w then
    (aux₃ (pos := pos) (q := q) A B C a w).owner x else own x) = _
  by_cases hxY : x ∈ exchangeRegion L a w
  · have hxwin := exchangeRegion_subset_window (L := L) a w hleft hxY
    have hown : own x = C := hC x (by
      simp only [mem_interval] at hxwin ⊢
      omega)
    have hrightA : x ∉ interval L (a - 3 * w) (a - 2 * w) := by
      simp only [mem_interval] at hxwin ⊢
      omega
    have hrightB : x ∉ interval L (a - 2 * w) (a - w) := by
      simp only [mem_interval] at hxwin ⊢
      omega
    rw [ite_eq_left hxY, aux₃_owner_normal_form]
    simp only [hrightA, hrightB, ite_false, hown]
  · have hnotLeft : x ∉ interval L (a - 6 * w) (a - 4 * w) := by
      intro hx
      exact hxY (left_changes_subset_exchangeRegion (L := L) a w hw hleft hx)
    have hleftB : x ∉ interval L (a - 6 * w) (a - 5 * w) := by
      simp only [mem_interval] at hnotLeft ⊢
      omega
    have hleftA : x ∉ interval L (a - 5 * w) (a - 4 * w) := by
      simp only [mem_interval] at hnotLeft ⊢
      omega
    simp only [hxY, hleftB, hleftA, ite_false]

/-- The main ownership identity, with no restriction on ownership away from the local window. -/
theorem main₈_eq_changeOwner (own : Fin L → Party) (A B C : Party) (a w : ℕ)
    (hw : 1 ≤ w) (hleft : 8 * w ≤ a) (_hright : a + 2 * w ≤ L)
    (hC : ∀ x ∈ interval L (a - 8 * w) a, own x = C)
    (_hA : ∀ x ∈ interval L a (a + w), own x = A)
    (_hB : ∀ x ∈ interval L (a + w) (a + 2 * w), own x = B) :
    main₈ (pos := pos) (q := q) own A B C a w =
      (main₀ own).changeOwner (interval L a (a + w)) B := by
  classical
  apply holeFree_ext (by rfl) (by rfl)
  intro x
  change (main₈ (pos := pos) (q := q) own A B C a w).owner x =
    if x ∈ interval L a (a + w) then B else own x
  simp only [main₈, main₇, main₆, main₅, Frame.changeOwner]
  rw [main₄_owner_normal_form own A B C a w hw hleft hC]
  by_cases hxC : x ∈ interval L (a - 8 * w) a
  · have hown := hC x hxC
    rw [hown]
    simp only [mem_interval] at hxC ⊢
    split_ifs <;> first | rfl | omega
  · simp only [mem_interval] at hxC ⊢
    split_ifs <;> first | rfl | omega

/-- The retired auxiliary retains A and B registers, even after A loses its main band. -/
theorem aux₄_eq_raw (own : Fin L → Party) (A B C : Party) (a w : ℕ)
    (hw : 1 ≤ w) (hleft : 8 * w ≤ a) (_hright : a + 2 * w ≤ L)
    (hC : ∀ x ∈ interval L (a - 8 * w) a, own x = C) :
    aux₄ (pos := pos) (q := q) own A B C a w = Frame.raw (fun x ↦
      if x ∈ interval L (a - 3 * w) (a - 2 * w) then A
      else if x ∈ interval L (a - 2 * w) (a - w) then B else C) := by
  classical
  apply holeFree_ext (by rfl) (by rfl)
  intro x
  change (if x ∈ exchangeRegion L a w then own x else
    (aux₃ (pos := pos) (q := q) A B C a w).owner x) =
      if x ∈ interval L (a - 3 * w) (a - 2 * w) then A
      else if x ∈ interval L (a - 2 * w) (a - w) then B else C
  rw [aux₃_owner_normal_form]
  by_cases hxY : x ∈ exchangeRegion L a w
  · have hxwin := exchangeRegion_subset_window (L := L) a w hleft hxY
    have hown : own x = C := hC x (by
      simp only [mem_interval] at hxwin ⊢
      omega)
    rw [ite_eq_left hxY, hown]
    simp only [mem_interval] at hxwin ⊢
    split_ifs <;> first | rfl | omega
  · have hnotLeft : x ∉ interval L (a - 6 * w) (a - 4 * w) := by
      intro hx
      exact hxY (left_changes_subset_exchangeRegion (L := L) a w hw hleft hx)
    rw [ite_eq_right hxY]
    simp only [mem_interval] at hnotLeft ⊢
    split_ifs <;> first | rfl | omega

/-- The information sets of the exchange. The common-C interval across the upper
boundary of Y belongs to neither information set. Source: Part II, lines 305–309. -/
theorem exchange_regions (own : Fin L → Party) (A B C : Party) (a w : ℕ)
    (hAC : A ≠ C) (hBC : B ≠ C) (hw : 1 ≤ w) (hleft : 8 * w ≤ a)
    (hC : ∀ x ∈ interval L (a - 8 * w) a, own x = C) :
    (exchange (pos := pos) (q := q) own A B C a w).tSet C =
        interval L (a - 6 * w) (a - 4 * w) ∧
      (exchange (pos := pos) (q := q) own A B C a w).eSet C =
        interval L (a - 3 * w) (a - w) ∪ (main₀ (pos := pos) (q := q) own).birthEnv C := by
  classical
  have hY : exchangeRegion L a w ⊆ interval L (a - 7 * w) (a - 3 * w) :=
    exchangeRegion_subset_window a w hleft
  have hleftY : interval L (a - 6 * w) (a - 4 * w) ⊆ exchangeRegion L a w :=
    left_changes_subset_exchangeRegion a w hw hleft
  have hYowner : ∀ x ∈ exchangeRegion L a w, own x = C := by
    intro x hx
    have hxwin := hY hx
    exact hC x (by
      simp only [mem_interval] at hxwin ⊢
      omega)
  have hrightNotY : ∀ x ∈ interval L (a - 3 * w) (a - w),
      x ∉ exchangeRegion L a w := by
    intro x hx hxY
    have hxwin := hY hxY
    simp only [mem_interval] at hx hxwin
    omega
  have hZ : ∀ x, x ∈ (exchange (pos := pos) (q := q) own A B C a w).exchangeEnv C ↔
      x ∈ interval L (a - 6 * w) (a - 4 * w) ∨
        x ∈ interval L (a - 3 * w) (a - w) ∨ own x ≠ C := by
    intro x
    unfold exchange
    rw [TwoSheetExchange.mem_ofFrames_exchangeEnv]
    have hmainH : (main₀ (pos := pos) (q := q) own).outerHoles = ∅ := by
      simp [main₀, Frame.raw, Frame.outerHoles, Frame.patches, footprint]
    have hauxH : (aux₃ (pos := pos) (q := q) A B C a w).outerHoles = ∅ := by
      simp [aux₃, aux₂, aux₁, aux₀, Frame.raw, Frame.changeOwner,
        Frame.outerHoles, Frame.patches, footprint]
    rw [hmainH, hauxH]
    simp only [Set.mem_empty_iff_false, or_false]
    change ¬(own x = C ∧ (aux₃ (pos := pos) (q := q) A B C a w).owner x = C) ↔ _
    rw [aux₃_owner_normal_form]
    simp only [mem_interval]
    split_ifs <;> simp_all <;> try omega
    constructor
    · exact fun h ↦ Or.inr (Or.inr h)
    · rintro (h | h | h)
      · omega
      · omega
      · exact h
  constructor
  · ext x
    simp only [TwoSheetExchange.tSet, Finset.mem_inter]
    change (x ∈ (exchange (pos := pos) (q := q) own A B C a w).exchangeEnv C ∧
      x ∈ exchangeRegion L a w) ↔ x ∈ interval L (a - 6 * w) (a - 4 * w)
    rw [hZ]
    constructor
    · rintro ⟨hx | hx | hx, hxY⟩
      · exact hx
      · exact (hrightNotY x hx hxY).elim
      · exact (hx (hYowner x hxY)).elim
    · intro hx
      exact ⟨Or.inl hx, hleftY hx⟩
  · ext x
    simp only [TwoSheetExchange.eSet, Finset.mem_sdiff, Finset.mem_union]
    change (x ∈ (exchange (pos := pos) (q := q) own A B C a w).exchangeEnv C ∧
      x ∉ exchangeRegion L a w) ↔
        x ∈ interval L (a - 3 * w) (a - w) ∨
          x ∈ (main₀ (pos := pos) (q := q) own).birthEnv C
    have hbirth : x ∈ (main₀ (pos := pos) (q := q) own).birthEnv C ↔ own x ≠ C := by
      simp [Frame.birthEnv, main₀, Frame.raw, Frame.outerHoles, Frame.patches, footprint]
    rw [hZ, hbirth]
    constructor
    · rintro ⟨hx | hx | hx, hxNotY⟩
      · exact (hxNotY (hleftY hx)).elim
      · exact Or.inl hx
      · exact Or.inr hx
    · rintro (hx | hx)
      · exact ⟨Or.inr (Or.inl hx), hrightNotY x hx⟩
      · exact ⟨Or.inr (Or.inr hx), fun hxY ↦ hx (hYowner x hxY)⟩

/-! ## Reusing the existing primitive circuits and stack lifts -/

variable [NeZero q]

omit [NeZero q] in
private theorem no_outerHoles (F : Frame pos q Party) (hF : F.holes = [])
    (T : Finset (Fin L)) : Disjoint (T : Set (Fin L)) F.outerHoles := by
  simp [Frame.outerHoles, Frame.patches, hF, footprint]

private theorem birth_liftOne (F : Frame pos q Party) (T : Finset (Fin L)) (P Q : Party)
    (hTP : ∀ x ∈ T, F.owner x = P) (hF : F.holes = [])
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΩ : ‖Ω‖ = 1)
    (hI : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω T (F.birthEnv P) ≤
      (L : ℝ) ^ (-60 : ℤ))
    (pre post : List (Frame pos q Party)) {ℓ : Layout Party} (ξ : Mem ℓ) (hξ : ‖ξ‖ ≤ 1) :
    HasSourceBoundedChange Ω (pre ++ F :: post) (pre ++ F.changeOwner T Q :: post)
      ξ {P, Q} 1 1 1 ((L : ℝ) ^ (-30 : ℤ)) := by
  obtain ⟨_, _, _, v, hv, hu, hs, _, herr⟩ :=
    F.birth_bounded (Q := Q) hTP (no_outerHoles F hF T) hΩ hI
  exact hasSourceBoundedChange_liftOne pre post
    (Word.isBoundedChange_toOriginalCircuit hv hu hs le_rfl (by
      simpa only [Frame.regRef] using herr))
    (v.isSourceBounded_toOriginalCircuit hv) hΩ.le hξ

/-- The MI hypothesis is explicitly evaluated AFTER the death. -/
private theorem death_liftOne (F : Frame pos q Party) (T : Finset (Fin L)) (P Q : Party)
    (hTP : ∀ x ∈ T, F.owner x = P) (hF : F.holes = [])
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΩ : ‖Ω‖ = 1)
    (hI : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω T
      ((F.changeOwner T Q).birthEnv Q) ≤ (L : ℝ) ^ (-60 : ℤ))
    (pre post : List (Frame pos q Party)) {ℓ : Layout Party} (ξ : Mem ℓ) (hξ : ‖ξ‖ ≤ 1) :
    HasSourceBoundedChange Ω (pre ++ F :: post) (pre ++ F.changeOwner T Q :: post)
      ξ {Q, P} 1 1 1 ((L : ℝ) ^ (-30 : ℤ)) := by
  let G := F.changeOwner T Q
  have hback : G.changeOwner T P = F := by
    apply holeFree_ext (F := G.changeOwner T P) (G := F) hF hF
    intro x
    change (if x ∈ T then P else if x ∈ T then Q else F.owner x) = F.owner x
    by_cases hx : x ∈ T
    · simpa only [hx, ↓reduceIte] using (hTP x hx).symm
    · simp only [hx, ↓reduceIte]
  have hGT : ∀ x ∈ T, G.owner x = Q := by
    intro x hx
    simp [G, hx]
  have hG : G.holes = [] := hF
  obtain ⟨_, _, _, M, hM, hu, hs, he, _, herr⟩ :=
    G.death_bounded (Q := P) hGT (no_outerHoles G hG T) hΩ hI
  have hc := PartyChain.isBoundedChange_toOriginalCircuit hM hu hs he le_rfl le_rfl
    (by simpa only [Frame.regRef] using herr)
  simpa only [hback] using hasSourceBoundedChange_liftOne pre post hc
    (M.isSourceBounded_toOriginalCircuit hM) hΩ.le hξ

/-- The exchange is an actual private original circuit, with no non-private gate. -/
private theorem exchange_circuit (own : Fin L → Party) (A B C : Party) (a w : ℕ)
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΩ : ‖Ω‖ = 1)
    (hI : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω
      ((exchange (pos := pos) (q := q) own A B C a w).tSet C)
      ((exchange (pos := pos) (q := q) own A B C a w).eSet C) ≤
      (L : ℝ) ^ (-60 : ℤ)) :
    ∃ c : OriginalCircuit
        ((main₀ (pos := pos) (q := q) own).regs ++ (aux₃ (pos := pos) (q := q) A B C a w).regs)
        ((main₄ (pos := pos) (q := q) own A B C a w).regs ++
          (aux₄ (pos := pos) (q := q) own A B C a w).regs),
      c.IsBoundedChange {C} 1 1 (4 * (L : ℝ) ^ (-30 : ℤ))
        (pairRef (main₀ (pos := pos) (q := q) own) (aux₃ (pos := pos) (q := q) A B C a w) Ω)
        (pairRef (main₄ (pos := pos) (q := q) own A B C a w)
          (aux₄ (pos := pos) (q := q) own A B C a w) Ω) ∧
      c.IsSourceBounded 1 ∧ c.nonprivateCount = 0 := by
  obtain ⟨_, _, _, _, _, _, _, v, hv, hu, hs, _, herr⟩ :=
    TwoSheetExchange.exchange_ofFrames_bounded (main₀ own) (aux₃ A B C a w)
      (exchangeRegion L a w) (fun _ ↦ true) _ _ C hΩ hI
  refine ⟨v.toOriginalCircuit hv,
    Word.isBoundedChange_toOriginalCircuit hv hu (by omega) le_rfl ?_,
    v.isSourceBounded_toOriginalCircuit hv, ?_⟩
  · simpa only [pairRef_eq_twoLayoutIso_symm, main₄, aux₄, exchange] using herr
  · exact (v.nonprivateCount_toOriginalCircuit hv).trans hs

/-- An INTERMEDIATE one-band construction from exactly the primitive information bounds.
It constructs every map; no circuit, output vector or evolving-state information bound is supplied.
The eventual source theorem must derive the eight estimates from logarithmic separation. -/
theorem circuits_of_primitive_information
    (own : Fin L → Party) (A B C : Party) (a w : ℕ)
    (_hAB : A ≠ B) (_hAC : A ≠ C) (_hBC : B ≠ C)
    (hw : 1 ≤ w) (hleft : 8 * w ≤ a) (_hright : a + 2 * w ≤ L)
    (hC : ∀ x ∈ interval L (a - 8 * w) a, own x = C)
    (hA : ∀ x ∈ interval L a (a + w), own x = A)
    (_hB : ∀ x ∈ interval L (a + w) (a + 2 * w), own x = B)
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΩ : ‖Ω‖ = 1)
    (hI₀ : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω
      (interval L (a - 6 * w) (a - w)) ((aux₀ (pos := pos) (q := q) C).birthEnv C) ≤
      (L : ℝ) ^ (-60 : ℤ))
    (hI₁ : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω
      (interval L (a - 5 * w) (a - 2 * w)) ((aux₁ (pos := pos) (q := q) B C a w).birthEnv B) ≤
      (L : ℝ) ^ (-60 : ℤ))
    (hI₂ : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω
      (interval L (a - 4 * w) (a - 3 * w)) ((aux₂ (pos := pos) (q := q) A B C a w).birthEnv A) ≤
      (L : ℝ) ^ (-60 : ℤ))
    (hI₃ : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω
      ((exchange (pos := pos) (q := q) own A B C a w).tSet C)
      ((exchange (pos := pos) (q := q) own A B C a w).eSet C) ≤
      (L : ℝ) ^ (-60 : ℤ))
    (hI₄ : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω
      (interval L (a - 4 * w) a) ((main₅ (pos := pos) (q := q) own A B C a w).birthEnv A) ≤
      (L : ℝ) ^ (-60 : ℤ))
    (hI₅ : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω
      (interval L (a - 5 * w) (a + w)) ((main₆ (pos := pos) (q := q) own A B C a w).birthEnv B) ≤
      (L : ℝ) ^ (-60 : ℤ))
    (hI₆ : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω
      (interval L (a - 3 * w) a) ((main₆ (pos := pos) (q := q) own A B C a w).birthEnv B) ≤
      (L : ℝ) ^ (-60 : ℤ))
    (hI₇ : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω
      (interval L (a - 6 * w) (a - 3 * w))
      ((main₈ (pos := pos) (q := q) own A B C a w).birthEnv C) ≤
      (L : ℝ) ^ (-60 : ℤ))
    (pre post : List (Frame pos q Party)) {ℓ : Layout Party} (ξ : Mem ℓ) (hξ : ‖ξ‖ ≤ 1) :
    ∃ c : (j : Fin 8) →
        OriginalCircuit
          (stackRegs (pre ++ frames (pos := pos) (q := q) own A B C a w j.val ++ post) ℓ)
          (stackRegs (pre ++ frames (pos := pos) (q := q) own A B C a w (j.val + 1) ++ post) ℓ),
      ∀ j, (c j).IsBoundedChange (participants A B C j) 1 1
          (if j.val = 3 then 4 * (L : ℝ) ^ (-30 : ℤ) else (L : ℝ) ^ (-30 : ℤ))
          (stackVec Ω (pre ++ frames (pos := pos) (q := q) own A B C a w j.val ++ post) ξ)
          (stackVec Ω (pre ++ frames (pos := pos) (q := q) own A B C a w (j.val + 1) ++ post) ξ) ∧
        (c j).IsSourceBounded 1 ∧ (j.val = 3 → (c j).nonprivateCount = 0) := by
  classical
  -- These are geometric consequences to prove, not assumptions supplied by the caller.
  have h₁ : ∀ x ∈ interval L (a - 5 * w) (a - 2 * w),
      (aux₁ (pos := pos) (q := q) B C a w).owner x = B := by
    intro x hx
    have hx' : x ∈ interval L (a - 6 * w) (a - w) := by
      simp only [mem_interval] at hx ⊢
      omega
    exact ite_eq_left hx'
  have h₂ : ∀ x ∈ interval L (a - 4 * w) (a - 3 * w),
      (aux₂ (pos := pos) (q := q) A B C a w).owner x = A := by
    intro x hx
    have hx' : x ∈ interval L (a - 5 * w) (a - 2 * w) := by
      simp only [mem_interval] at hx ⊢
      omega
    exact ite_eq_left hx'
  have h₄ : ∀ x ∈ interval L (a - 4 * w) a,
      (main₄ (pos := pos) (q := q) own A B C a w).owner x = C := by
    intro x hx
    rw [main₄_owner_normal_form own A B C a w hw hleft hC]
    have hown : own x = C := hC x (by
      simp only [mem_interval] at hx ⊢
      omega)
    rw [hown]
    simp only [mem_interval] at hx ⊢
    split_ifs <;> first | rfl | omega
  have h₅ : ∀ x ∈ interval L (a - 5 * w) (a + w),
      (main₅ (pos := pos) (q := q) own A B C a w).owner x = A := by
    intro x hx
    simp only [main₅, Frame.changeOwner]
    rw [main₄_owner_normal_form own A B C a w hw hleft hC]
    by_cases hxA : x ∈ interval L a (a + w)
    · have hown := hA x hxA
      rw [hown]
      simp only [mem_interval] at hx hxA ⊢
      split_ifs <;> first | rfl | omega
    · simp only [mem_interval] at hx hxA ⊢
      split_ifs <;> first | rfl | omega
  have h₆ : ∀ x ∈ interval L (a - 3 * w) a,
      (main₆ (pos := pos) (q := q) own A B C a w).owner x = B := by
    intro x hx
    have hx' : x ∈ interval L (a - 5 * w) (a + w) := by
      simp only [mem_interval] at hx ⊢
      omega
    exact ite_eq_left hx'
  have h₇ : ∀ x ∈ interval L (a - 6 * w) (a - 3 * w),
      (main₇ (pos := pos) (q := q) own A B C a w).owner x = B := by
    intro x hx
    simp only [main₇, main₆, main₅, Frame.changeOwner]
    rw [main₄_owner_normal_form own A B C a w hw hleft hC]
    simp only [mem_interval] at hx ⊢
    split_ifs <;> first | rfl | omega
  have hsteps : ∀ j : Fin 8, ∃ c :
      OriginalCircuit (stackRegs (pre ++ frames own A B C a w j.val ++ post) ℓ)
        (stackRegs (pre ++ frames own A B C a w (j.val + 1) ++ post) ℓ),
      c.IsBoundedChange (participants A B C j) 1 1
          (if j.val = 3 then 4 * (L : ℝ) ^ (-30 : ℤ) else (L : ℝ) ^ (-30 : ℤ))
          (stackVec Ω (pre ++ frames own A B C a w j.val ++ post) ξ)
          (stackVec Ω (pre ++ frames own A B C a w (j.val + 1) ++ post) ξ) ∧
        c.IsSourceBounded 1 ∧ (j.val = 3 → c.nonprivateCount = 0) := by
    intro j
    fin_cases j
    · rw [frames.eq_1, frames.eq_2]
      have hop := birth_liftOne (aux₀ C)
        (interval L (a - 6 * w) (a - w)) C B (by intro x hx; rfl) rfl hΩ hI₀
        (pre ++ [main₀ own]) post ξ hξ
      have hn : HasSourceBoundedChange Ω
          (pre ++ [main₀ own, aux₀ C] ++ post)
          (pre ++ [main₀ own, aux₁ B C a w] ++ post)
          ξ {C, B} 1 1 1 ((L : ℝ) ^ (-30 : ℤ)) := by
        simpa only [aux₁, List.append_assoc, List.cons_append, List.nil_append] using hop
      obtain ⟨c, hc, hs⟩ := hn
      refine ⟨c, ?_, hs, ?_⟩
      · simpa [participants] using hc
      · norm_num
    · rw [frames.eq_2, frames.eq_3]
      have hop := birth_liftOne (aux₁ B C a w)
        (interval L (a - 5 * w) (a - 2 * w)) B A h₁ rfl hΩ hI₁
        (pre ++ [main₀ own]) post ξ hξ
      have hn : HasSourceBoundedChange Ω
          (pre ++ [main₀ own, aux₁ B C a w] ++ post)
          (pre ++ [main₀ own, aux₂ A B C a w] ++ post)
          ξ {B, A} 1 1 1 ((L : ℝ) ^ (-30 : ℤ)) := by
        simpa only [aux₂, List.append_assoc, List.cons_append, List.nil_append] using hop
      obtain ⟨c, hc, hs⟩ := hn
      refine ⟨c, ?_, hs, ?_⟩
      · simpa [participants] using hc
      · norm_num
    · rw [frames.eq_3, frames.eq_4]
      have hop := birth_liftOne (aux₂ A B C a w)
        (interval L (a - 4 * w) (a - 3 * w)) A C h₂ rfl hΩ hI₂
        (pre ++ [main₀ own]) post ξ hξ
      have hn : HasSourceBoundedChange Ω
          (pre ++ [main₀ own, aux₂ A B C a w] ++ post)
          (pre ++ [main₀ own, aux₃ A B C a w] ++ post)
          ξ {A, C} 1 1 1 ((L : ℝ) ^ (-30 : ℤ)) := by
        simpa only [aux₃, List.append_assoc, List.cons_append, List.nil_append] using hop
      obtain ⟨c, hc, hs⟩ := hn
      refine ⟨c, ?_, hs, ?_⟩
      · simpa [participants] using hc
      · norm_num
    · rw [frames.eq_4, frames.eq_5]
      rw [show pre ++ [main₀ own, aux₃ A B C a w] ++ post =
          pre ++ main₀ own :: aux₃ A B C a w :: post by
            simp only [List.append_assoc, List.cons_append, List.nil_append],
        show pre ++ [main₄ own A B C a w, aux₄ own A B C a w] ++ post =
          pre ++ main₄ own A B C a w :: aux₄ own A B C a w :: post by
            simp only [List.append_assoc, List.cons_append, List.nil_append]]
      obtain ⟨cx, hx, hsx, hzero⟩ := exchange_circuit own A B C a w hΩ hI₃
      have hwith : ∃ c : OriginalCircuit
          (stackRegs (pre ++ main₀ own :: aux₃ A B C a w :: post) ℓ)
          (stackRegs (pre ++ main₄ own A B C a w :: aux₄ own A B C a w :: post) ℓ),
          c.IsBoundedChange {C} 1 1 (4 * (L : ℝ) ^ (-30 : ℤ))
            (stackVec Ω (pre ++ main₀ own :: aux₃ A B C a w :: post) ξ)
            (stackVec Ω (pre ++ main₄ own A B C a w :: aux₄ own A B C a w :: post) ξ) ∧
          c.IsSourceBounded 1 ∧ ((3 : ℕ) = 3 → c.nonprivateCount = 0) := by
        refine ⟨liftTwo post ℓ cx pre, isBoundedChange_liftTwo pre post hx hΩ.le hξ,
          isSourceBounded_liftTwo post ℓ cx hsx pre, ?_⟩
        intro _
        simpa only [nonprivateCount_liftTwo] using hzero
      simpa [participants] using hwith
    · rw [frames.eq_5, frames.eq_6]
      rw [show pre ++ [main₄ own A B C a w, aux₄ own A B C a w] ++ post =
          pre ++ main₄ own A B C a w :: aux₄ own A B C a w :: post by
            simp only [List.append_assoc, List.cons_append, List.nil_append],
        show pre ++ [main₅ own A B C a w, aux₄ own A B C a w] ++ post =
          pre ++ main₅ own A B C a w :: aux₄ own A B C a w :: post by
            simp only [List.append_assoc, List.cons_append, List.nil_append]]
      have hop := death_liftOne (main₄ own A B C a w)
        (interval L (a - 4 * w) a) C A h₄ rfl hΩ hI₄ pre
        (aux₄ own A B C a w :: post) ξ hξ
      simpa [HasSourceBoundedChange, participants, main₅, Set.pair_comm]
        using hop
    · rw [frames.eq_6, frames.eq_7]
      rw [show pre ++ [main₅ own A B C a w, aux₄ own A B C a w] ++ post =
          pre ++ main₅ own A B C a w :: aux₄ own A B C a w :: post by
            simp only [List.append_assoc, List.cons_append, List.nil_append],
        show pre ++ [main₆ own A B C a w, aux₄ own A B C a w] ++ post =
          pre ++ main₆ own A B C a w :: aux₄ own A B C a w :: post by
            simp only [List.append_assoc, List.cons_append, List.nil_append]]
      have hop := death_liftOne (main₅ own A B C a w)
        (interval L (a - 5 * w) (a + w)) A B h₅ rfl hΩ hI₅ pre
        (aux₄ own A B C a w :: post) ξ hξ
      simpa [HasSourceBoundedChange, participants, main₆, Set.pair_comm]
        using hop
    · rw [frames.eq_7, frames.eq_8]
      rw [show pre ++ [main₆ own A B C a w, aux₄ own A B C a w] ++ post =
          pre ++ main₆ own A B C a w :: aux₄ own A B C a w :: post by
            simp only [List.append_assoc, List.cons_append, List.nil_append],
        show pre ++ [main₇ own A B C a w, aux₄ own A B C a w] ++ post =
          pre ++ main₇ own A B C a w :: aux₄ own A B C a w :: post by
            simp only [List.append_assoc, List.cons_append, List.nil_append]]
      have hop := birth_liftOne (main₆ own A B C a w)
        (interval L (a - 3 * w) a) B C h₆ rfl hΩ hI₆ pre
        (aux₄ own A B C a w :: post) ξ hξ
      simpa [HasSourceBoundedChange, participants, main₇] using hop
    · rw [frames.eq_8, show frames (pos := pos) (q := q) own A B C a w 8 =
          [main₈ own A B C a w, aux₄ own A B C a w] from rfl]
      rw [show pre ++ [main₇ own A B C a w, aux₄ own A B C a w] ++ post =
          pre ++ main₇ own A B C a w :: aux₄ own A B C a w :: post by
            simp only [List.append_assoc, List.cons_append, List.nil_append],
        show pre ++ [main₈ own A B C a w, aux₄ own A B C a w] ++ post =
          pre ++ main₈ own A B C a w :: aux₄ own A B C a w :: post by
            simp only [List.append_assoc, List.cons_append, List.nil_append]]
      have hop := death_liftOne (main₇ own A B C a w)
        (interval L (a - 6 * w) (a - 3 * w)) B C h₇ rfl hΩ hI₇ pre
        (aux₄ own A B C a w :: post) ξ hξ
      simpa [HasSourceBoundedChange, participants, main₈, Set.pair_comm]
        using hop
  choose c hc using hsteps
  exact ⟨c, hc⟩

/-- The boundary alternative in the last sentence of con:band. No left-hand C party
and no auxiliary copy are introduced. This is again conditional on the primitive MI estimate. -/
theorem boundary_change_of_primitive_information
    (own : Fin L → Party) (A B : Party) (w : ℕ)
    (hA : ∀ x ∈ interval L 0 w, own x = A)
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΩ : ‖Ω‖ = 1)
    (hI : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω
      (interval L 0 w) (((main₀ (pos := pos) (q := q) own).changeOwner
        (interval L 0 w) B).birthEnv B) ≤ (L : ℝ) ^ (-60 : ℤ))
    (pre post : List (Frame pos q Party)) {ℓ : Layout Party} (ξ : Mem ℓ) (hξ : ‖ξ‖ ≤ 1) :
    HasSourceBoundedChange Ω (pre ++ main₀ own :: post)
      (pre ++ (main₀ own).changeOwner (interval L 0 w) B :: post)
      ξ {B, A} 1 1 1 ((L : ℝ) ^ (-30 : ℤ)) :=
  death_liftOne (main₀ own) (interval L 0 w) A B hA rfl hΩ hI pre post ξ hξ

end TNLean.MPS.AreaLaw.OneBand
