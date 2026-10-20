/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.OriginalCircuitLift

/-!
# Sequences of original circuits in three stages

A distributed construction of the polynomial-PEPS manuscript is cut into changes, the change
number `t` an original circuit from the layout at stage `t` to the layout at stage `t + 1`
(`04-compression.tex`, lines 21–43). The protocol of Proposition 7.1 has three stages: a first
circuit, then the changes of its schedule, then a last circuit (`06-geometry.tex`,
lines 658–681). This file joins three such stages into one sequence of layouts and circuits,
with no operation added: the layouts are identified along equalities only.

## Main definitions

* `PairEffect.OriginalCircuit.chainLayout`, `PairEffect.OriginalCircuit.chainStep`: a first
  circuit into `B 0`, circuits from `B t` to `B (t + 1)` for `t < n`, and a last circuit from
  `B n` to `Z`, as one sequence, followed by identities on `Z`.
* `PairEffect.OriginalCircuit.chainVec`: the vectors of the stages.

## Main results

* `PairEffect.OriginalCircuit.chainStep_induction`: a property of the three kinds of circuits
  holds for every circuit of the sequence.
* `PairEffect.OriginalCircuit.norm_chainStep_eval_sub_le`: the errors of the circuits on the
  vectors of the stages.

## References

* Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 21–43, and
  Proposition 7.1 `prop:protocol`, `06-geometry.tex`, lines 25–41 and 658–681.
-/

noncomputable section

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
      e.castLayouts (by rw [chainLayout_succ_of_le h'.le, h'])
        (chainLayout_succ_of_lt (by omega)).symm
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
theorem castLayouts_induction (Q : ∀ a b : Layout P, OriginalCircuit a b → Prop)
    {a b a' b' : Layout P} {w : OriginalCircuit a b} (ha : a = a') (hb : b = b') (h : Q a b w) :
    Q a' b' (w.castLayouts ha hb) := by
  cases ha
  cases hb
  exact h

/-- **Properties of the sequence of circuits.** A property, possibly depending on the position,
that holds for the first circuit, the middle circuits, the last circuit and the identities holds
for every circuit of the sequence. -/
theorem chainStep_induction (Q : ℕ → ∀ a b : Layout P, OriginalCircuit a b → Prop)
    {c₀ : OriginalCircuit A (B 0)} {c : ∀ t, OriginalCircuit (B t) (B (t + 1))}
    {e : OriginalCircuit (B n) Z} (h₀ : Q 0 _ _ c₀) (hc : ∀ t < n, Q (t + 1) _ _ (c t))
    (he : Q (n + 1) _ _ e) (hid : ∀ t, n < t → Q (t + 1) _ _ (OriginalCircuit.id Z)) :
    ∀ t, Q t _ _ (chainStep c₀ c e t)
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

end TNLean.PEPS
