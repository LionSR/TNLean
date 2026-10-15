/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicProtocolFinalReadout
import TNLean.PEPS.Approximation.DyadicProtocolInitialStep
import TNLean.PEPS.Approximation.OriginalCircuitSourceBound
import TNLean.PEPS.Approximation.SheetStackChange

/-!
# A dyadic protocol from a bounded trajectory of sheets

The protocol of Proposition 7.1 of the polynomial-PEPS manuscript has three parts
(`06-geometry.tex`, lines 572–681): the private initialization of the copies of `Ω` at their
holders, the changes of the schedule, each a bounded change of the sheets, and the final
regrouping of the main sheet into the physical registers. This file assembles these three parts
into a `DyadicProtocol` and proves the bounds `DyadicProtocol.IsDistributionProtocol` consumed by
§8, from the following data on the parties of the hierarchy:

* a list of encoded frames `st t` at every stage, the initial frames raw and each held by one
  party;
* one original circuit for each change of the schedule, a bounded change in the sense of
  `PairEffect.OriginalCircuit.IsBoundedChange` from the reference vector of `st t` to that of
  `st (t + 1)`, whose participants are parties the event of the change uses;
* at the end of the schedule, a main frame read by the unit-square parties, with trivial holes,
  followed by other sheets whose holes satisfy the frame constraint and are at most `C L³` in
  number.

The construction of these frames along the schedule is not done here.

## Main definitions

* `PairEffect.OriginalCircuit.chainLayout`, `PairEffect.OriginalCircuit.chainStep`,
  `PairEffect.OriginalCircuit.chainVec`: one circuit, then a sequence of circuits, then one
  more circuit, as a sequence of circuits on a sequence of layouts.

## Main results

* `card_eventUses_le`: an event of the hierarchy uses at most `19` parties.
* `exists_isDistributionProtocol_of_frames`: the assembled protocol satisfies the bounds of §8,
  and every change is source bounded when the changes of the schedule are.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 7.1 `prop:protocol`,
  `06-geometry.tex`, lines 12–53 (statement), and its proof: the counts (lines 572–583 and
  649–652), the lifetime and locality of the parties (lines 585–647), the initial copies
  (lines 658–667) and the final reference (lines 669–681); Theorem 5.2, item 3,
  `04-compression.tex`, lines 143–147.
-/

noncomputable section

open Finset

namespace TNLean.PEPS

namespace PairEffect.OriginalCircuit

variable {P : Type}

/-! ### Three stages of circuits in a row -/

/-- The layouts of a sequence of circuits made of a first circuit into `B 0`, the circuits from
`B t` to `B (t + 1)` for `t < n`, and a last circuit from `B n` to `Z`, after which the layout
stays `Z`. -/
def chainLayout (A : Layout P) (B : ℕ → Layout P) (n : ℕ) (Z : Layout P) : ℕ → Layout P
  | 0 => A
  | t + 1 => if t ≤ n then B t else Z

variable {A : Layout P} {B : ℕ → Layout P} {n : ℕ} {Z : Layout P}

theorem chainLayout_succ_of_le {t : ℕ} (h : t ≤ n) : chainLayout A B n Z (t + 1) = B t := by
  simp [chainLayout, h]

theorem chainLayout_succ_of_lt {t : ℕ} (h : n < t) : chainLayout A B n Z (t + 1) = Z := by
  simp [chainLayout, show ¬t ≤ n by omega]

/-- The circuits of the sequence: the first circuit, the middle circuits, the last circuit, and
then identities. -/
def chainStep (c₀ : OriginalCircuit A (B 0)) (c : ∀ t, OriginalCircuit (B t) (B (t + 1)))
    (e : OriginalCircuit (B n) Z) :
    ∀ t, OriginalCircuit (chainLayout A B n Z t) (chainLayout A B n Z (t + 1))
  | 0 => c₀.castLayouts rfl (chainLayout_succ_of_le (Nat.zero_le n)).symm
  | t + 1 =>
    if h : t < n then
      (c t).castLayouts (chainLayout_succ_of_le h.le).symm (chainLayout_succ_of_le h).symm
    else if h' : t = n then
      e.castLayouts (by rw [chainLayout_succ_of_le h'.le, h']) (chainLayout_succ_of_lt (by omega)).symm
    else
      (OriginalCircuit.id Z).castLayouts (chainLayout_succ_of_lt (by omega)).symm
        (chainLayout_succ_of_lt (by omega)).symm

section Equations

variable (c₀ : OriginalCircuit A (B 0)) (c : ∀ t, OriginalCircuit (B t) (B (t + 1)))
  (e : OriginalCircuit (B n) Z)

theorem chainStep_zero :
    chainStep c₀ c e 0 =
      c₀.castLayouts rfl (chainLayout_succ_of_le (A := A) (Z := Z) (Nat.zero_le n)).symm :=
  rfl

theorem chainStep_succ_of_lt {t : ℕ} (h : t < n) :
    chainStep c₀ c e (t + 1) =
      (c t).castLayouts (chainLayout_succ_of_le h.le).symm (chainLayout_succ_of_le h).symm := by
  simp only [chainStep, h, dite_true]

theorem chainStep_succ_self :
    chainStep c₀ c e (n + 1) =
      e.castLayouts (chainLayout_succ_of_le le_rfl).symm
        (chainLayout_succ_of_lt (Nat.lt_succ_self n)).symm := by
  simp only [chainStep, lt_irrefl, dite_false, dite_true]

theorem chainStep_succ_of_gt {t : ℕ} (h : n < t) :
    chainStep c₀ c e (t + 1) =
      (OriginalCircuit.id Z).castLayouts (chainLayout_succ_of_lt h).symm
        (chainLayout_succ_of_lt (h.trans (Nat.lt_succ_self t))).symm := by
  simp only [chainStep, show ¬t < n by omega, show t ≠ n by omega, dite_false]

end Equations

/-- Every property of circuits holds for a circuit with its layouts identified with equal ones. -/
theorem castLayouts_induction (Q : ∀ {a b : Layout P}, OriginalCircuit a b → Prop)
    {a b a' b' : Layout P} {w : OriginalCircuit a b} (ha : a = a') (hb : b = b') (h : Q w) :
    Q (w.castLayouts ha hb) := by
  cases ha
  cases hb
  exact h

/-- **Properties of the sequence of circuits.** A property, possibly depending on the position,
that holds for the first circuit, the middle circuits, the last circuit and the identities holds
for every circuit of the sequence. -/
theorem chainStep_induction (Q : ℕ → ∀ {a b : Layout P}, OriginalCircuit a b → Prop)
    {c₀ : OriginalCircuit A (B 0)} {c : ∀ t, OriginalCircuit (B t) (B (t + 1))}
    {e : OriginalCircuit (B n) Z} (h₀ : Q 0 c₀) (hc : ∀ t < n, Q (t + 1) (c t))
    (he : Q (n + 1) e) (hid : ∀ t, n < t → Q (t + 1) (OriginalCircuit.id Z)) :
    ∀ t, Q t (chainStep c₀ c e t)
  | 0 => by rw [chainStep_zero]; exact castLayouts_induction (Q 0) _ _ h₀
  | t + 1 => by
    rcases lt_trichotomy t n with h | rfl | h
    · rw [chainStep_succ_of_lt c₀ c e h]
      exact castLayouts_induction (Q (t + 1)) _ _ (hc t h)
    · rw [chainStep_succ_self]
      exact castLayouts_induction (Q (t + 1)) _ _ he
    · rw [chainStep_succ_of_gt c₀ c e h]
      exact castLayouts_induction (Q (t + 1)) _ _ (hid t h)

/-- The vectors of the sequence: a vector `x₀` of `A`, vectors `y t` of `B t` for `t ≤ n`, and a
vector `z` of `Z` from the stage `n + 2` on. -/
def chainVec (x₀ : Mem A) (y : ∀ t, Mem (B t)) (z : Mem Z) :
    ∀ t, Mem (chainLayout A B n Z t)
  | 0 => x₀
  | t + 1 =>
    if h : t ≤ n then Layout.memCongr (chainLayout_succ_of_le h).symm (y t)
    else Layout.memCongr (chainLayout_succ_of_lt (by omega)).symm z

section Vectors

variable (x₀ : Mem A) (y : ∀ t, Mem (B t)) (z : Mem Z)

theorem chainVec_succ_of_le {t : ℕ} (h : t ≤ n) :
    chainVec x₀ y z (t + 1) = Layout.memCongr (chainLayout_succ_of_le h).symm (y t) := by
  simp only [chainVec, h, dite_true]

theorem chainVec_succ_of_lt {t : ℕ} (h : n < t) :
    chainVec x₀ y z (t + 1) = Layout.memCongr (chainLayout_succ_of_lt h).symm z := by
  simp only [chainVec, show ¬t ≤ n by omega, dite_false]

end Vectors

theorem eval_castLayouts_memCongr {a b a' b' : Layout P} (w : OriginalCircuit a b) (ha : a = a')
    (hb : b = b') (x : Mem a) :
    (w.castLayouts ha hb).eval (Layout.memCongr ha x) = Layout.memCongr hb (w.eval x) := by
  cases ha
  cases hb
  rfl

theorem norm_memCongr_sub {a b : Layout P} (h : a = b) (x y : Mem a) :
    ‖Layout.memCongr h x - Layout.memCongr h y‖ = ‖x - y‖ := by
  rw [← map_sub, LinearIsometryEquiv.norm_map]

/-- **Errors along the sequence.** If the first circuit takes `x₀` within `ε 0` of `y 0`, each
middle circuit takes `y t` within `ε (t + 1)` of `y (t + 1)`, and the last circuit takes `y n`
within `ε (n + 1)` of `z`, then every circuit of the sequence takes the vector of its stage within
the corresponding error of the next one. -/
theorem norm_chainStep_eval_sub_le {c₀ : OriginalCircuit A (B 0)}
    {c : ∀ t, OriginalCircuit (B t) (B (t + 1))} {e : OriginalCircuit (B n) Z} {x₀ : Mem A}
    {y : ∀ t, Mem (B t)} {z : Mem Z} (ε : ℕ → ℝ) (h₀ : ‖c₀.eval x₀ - y 0‖ ≤ ε 0)
    (hc : ∀ t < n, ‖(c t).eval (y t) - y (t + 1)‖ ≤ ε (t + 1))
    (he : ‖e.eval (y n) - z‖ ≤ ε (n + 1)) (hid : ∀ t, n < t → 0 ≤ ε (t + 1)) :
    ∀ t, ‖(chainStep c₀ c e t).eval (chainVec x₀ y z t) - chainVec x₀ y z (t + 1)‖ ≤ ε t
  | 0 => by
    have h : (c₀.castLayouts rfl
        (chainLayout_succ_of_le (A := A) (Z := Z) (Nat.zero_le n)).symm).eval x₀ = _ :=
      eval_castLayouts_memCongr c₀ rfl _ x₀
    rw [chainStep_zero, chainVec_succ_of_le x₀ y z (Nat.zero_le n)]
    change ‖(c₀.castLayouts rfl _).eval x₀ - _‖ ≤ _
    rw [h, norm_memCongr_sub]
    exact h₀
  | t + 1 => by
    rcases lt_trichotomy t n with h | rfl | h
    · rw [chainStep_succ_of_lt c₀ c e h, chainVec_succ_of_le x₀ y z h.le,
        chainVec_succ_of_le x₀ y z h, eval_castLayouts_memCongr, norm_memCongr_sub]
      exact hc t h
    · rw [chainStep_succ_self, chainVec_succ_of_le x₀ y z le_rfl,
        chainVec_succ_of_lt x₀ y z (Nat.lt_succ_self t), eval_castLayouts_memCongr,
        norm_memCongr_sub]
      exact he
    · rw [chainStep_succ_of_gt c₀ c e h, chainVec_succ_of_lt x₀ y z h,
        chainVec_succ_of_lt x₀ y z (h.trans (Nat.lt_succ_self t)), eval_castLayouts_memCongr,
        norm_memCongr_sub]
      change ‖z - z‖ ≤ _
      rw [sub_self, norm_zero]
      exact hid t h

end PairEffect.OriginalCircuit

namespace Approximation

open EncodedFrame PairEffect

/-! ### The parties an event uses -/

variable {k : ℕ}

open Classical in
/-- **An event uses a bounded number of parties.** The repainting of a square uses at most
eighteen block parties, those of the blocks next to it at its level and at the level above, and
its placeholder; a junction resize uses at most nine block parties.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol`, item 2, `06-geometry.tex`,
lines 29–30, and lines 585–596. -/
theorem card_eventUses_le (e : ProtocolEvent k) :
    #{p : ProtocolParty k | EventUses e p} ≤ 19 := by
  let g : ProtocolParty k → (ℕ × ℕ × ℕ) ⊕ Unit := Sum.elim (fun Q => .inl Q.toTriple) fun _ => .inr ()
  have hg : Set.InjOn g {p | EventUses e p} := by
    rintro (Q | S) hp (Q' | S') hp' h
    · exact congrArg Sum.inl (DyadicSquare.toTriple_injective k (Sum.inl_injective h))
    · exact absurd h Sum.inl_ne_inr
    · exact absurd h Sum.inr_ne_inl
    · change e = .inl S.1 at hp
      change e = .inl S'.1 at hp'
      exact congrArg Sum.inr (Subtype.ext (Sum.inl_injective (hp.symm.trans hp')))
  rcases e with S | J
  · let f : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ := fun x =>
      if x.1 = 0 then ((S.1 : ℕ), (S.2.1 : ℕ) + x.2.1 - 1, (S.2.2 : ℕ) + x.2.2 - 1)
      else ((S.1 : ℕ) + 1, ((S.2.1 : ℕ) + x.2.1 - 1) / 2, ((S.2.2 : ℕ) + x.2.2 - 1) / 2)
    let T : Finset ((ℕ × ℕ × ℕ) ⊕ Unit) :=
      ((range 2 ×ˢ range 3 ×ˢ range 3).image f).disjSum {()}
    refine (card_le_card_of_injOn g (t := T) (fun p hp => ?_) fun p hp p' hp' h =>
      hg (by simpa using hp) (by simpa using hp') h).trans ?_
    · rcases p with Q | S'
      · obtain ⟨a, b, ha1, ha2, hb1, hb2, hown⟩ := (mem_filter.1 (mem_coe.1 hp)).2
        refine mem_coe.2 (inl_mem_disjSum.2 (mem_image.2 ?_))
        rcases hown with h | h
        · refine ⟨(0, a + 1 - S.2.1, b + 1 - S.2.2), ?_, ?_⟩
          · simp only [mem_product, mem_range]; omega
          · simp only [f, ite_true, h]; congr 2 <;> omega
        · refine ⟨(1, a + 1 - S.2.1, b + 1 - S.2.2), ?_, ?_⟩
          · simp only [mem_product, mem_range]; omega
          · simp only [f, one_ne_zero, ite_false, h]; congr 3 <;> omega
      · exact mem_coe.2 (inr_mem_disjSum.2 (mem_singleton_self _))
    · rw [card_disjSum, card_singleton]
      have := card_image_le (s := range 2 ×ˢ range 3 ×ˢ range 3) (f := f)
      simp only [card_product, card_range] at this
      omega
  · let f : ℕ × ℕ → ℕ × ℕ × ℕ := fun x => ((J.1 : ℕ), (J.2.1 : ℕ) + x.1 - 2, (J.2.2 : ℕ) + x.2 - 2)
    refine (card_le_card_of_injOn g (t := ((range 3 ×ˢ range 3).image f).disjSum ∅)
      (fun p hp => ?_) fun p hp p' hp' h =>
        hg (by simpa using hp) (by simpa using hp') h).trans ?_
    · rcases p with Q | S'
      · obtain ⟨h0, h1, h2, h3, h4⟩ := (mem_filter.1 (mem_coe.1 hp)).2
        refine mem_coe.2 (inl_mem_disjSum.2 (mem_image.2
          ⟨(Q.toTriple.2.1 + 2 - J.2.1, Q.toTriple.2.2 + 2 - J.2.2), ?_, ?_⟩))
        · simp only [mem_product, mem_range]; omega
        · simp only [f]
          ext <;> simp only <;> omega
      · exact absurd (mem_filter.1 (mem_coe.1 hp)).2 Sum.inr_ne_inl
    · rw [card_disjSum, card_empty, add_zero]
      exact card_image_le.trans (by simp)

end Approximation

end TNLean.PEPS
