/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicProtocolSegments
import TNLean.PEPS.Approximation.DyadicProtocolStateTransitions

/-!
# The dyadic protocol from its large-scale repaintings

The memory of the protocol of Proposition 7.1 of the polynomial-PEPS manuscript is the main frame
followed by one copy of `Ω` for each change of the schedule that initializes an auxiliary sheet:
idle before the repainting that uses it and frozen after it (`06-geometry.tex`, lines 183–186 and
653–667). The resizes and the direct repaintings change only the main frame, by one small-patch
rewrite each (`TNLean.PEPS.Approximation.DyadicLevelEvents`). This file assembles the protocol
from these changes and from the changes of the large-scale repaintings, which are hypotheses here:

* `auxIndices`, `auxState`, `protocolState` : the auxiliary indices, the auxiliary frames before
  each event, and the memory before each event;
* `exists_isDistributionProtocol_of_largeRepaintings` : if every large-scale repainting passes the
  memory from its state before to its state after by `189` bounded changes whose participants the
  repainting uses, and the frozen frames satisfy the frame constraint and carry at most `C L³`
  holes, then there is a protocol with the bounds of §8.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 7.1 `prop:protocol`,
  `06-geometry.tex`, lines 12–53, and its proof, lines 82–241, 507–541 and 572–681.
-/

noncomputable section

open Set

namespace TNLean.PEPS.Approximation

open EncodedFrame PairEffect

variable {k : ℕ}

/-! ### The auxiliary sheets -/

/-- The auxiliary indices: the changes of the schedule that initialize an auxiliary sheet.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 183–186 and 649–652. -/
abbrev auxIndices (k : ℕ) (large : DyadicSquare k → Bool) : List (ProtocolEvent k × RepaintOp) :=
  (protocolSchedule k large).filter fun x => x.2.IsAuxInit

/-- An auxiliary index belongs to a large-scale repainting. -/
theorem exists_large_of_mem_auxIndices {large : DyadicSquare k → Bool}
    {x : ProtocolEvent k × RepaintOp} (hx : x ∈ auxIndices k large) :
    ∃ S, x.1 = .inl S ∧ large S = true := by
  obtain ⟨hx, hax⟩ := List.mem_filter.1 hx
  obtain ⟨e, -, hx⟩ := List.mem_flatMap.1 hx
  obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hx
  rcases e with S | J
  · refine ⟨S, rfl, ?_⟩
    by_contra hS
    simp only [eventOps, hS, ite_false, List.mem_singleton] at ho
    subst ho
    simp [RepaintOp.IsAuxInit] at hax
  · simp only [eventOps, List.mem_singleton] at ho
    subst ho
    simp [RepaintOp.IsAuxInit] at hax

open Classical in
/-- **The auxiliary frames before an event.** Before the event number `i`, the auxiliary sheet of
the index `x` is frozen if its repainting is among the first `i` events, and idle otherwise.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 183–186 and 653–667. -/
def auxState {X : Type*} (frozen idle : ProtocolEvent k × RepaintOp → X) (i : ℕ)
    (x : ProtocolEvent k × RepaintOp) : X :=
  if x.1 ∈ (eventSchedule k).take i then frozen x else idle x

/-- An event other than a large-scale repainting freezes no auxiliary sheet. -/
theorem auxState_succ {X : Type*} {large : DyadicSquare k → Bool}
    (frozen idle : ProtocolEvent k × RepaintOp → X) {i : ℕ}
    (hi : i < (eventSchedule k).length)
    (hne : ∀ S, (eventSchedule k)[i] = .inl S → large S = false) :
    (auxIndices k large).map (auxState frozen idle (i + 1)) =
      (auxIndices k large).map (auxState frozen idle i) := by
  classical
  refine List.map_congr_left fun x hx => ?_
  obtain ⟨S, hS, hlS⟩ := exists_large_of_mem_auxIndices hx
  have hne' : x.1 ≠ (eventSchedule k)[i] := by
    intro h
    rw [hS] at h
    have := hne S h.symm
    rw [hlS] at this
    exact Bool.noConfusion this
  simp only [auxState, take_succ_eventSchedule hi, List.mem_append, List.mem_singleton, hne',
    or_false]

/-- An auxiliary index belongs to an event of the schedule. -/
theorem mem_eventSchedule_of_mem_auxIndices {large : DyadicSquare k → Bool}
    {x : ProtocolEvent k × RepaintOp} (hx : x ∈ auxIndices k large) :
    x.1 ∈ eventSchedule k := by
  obtain ⟨e, he, hx⟩ := List.mem_flatMap.1 (List.mem_filter.1 hx).1
  obtain ⟨o, -, rfl⟩ := List.mem_map.1 hx
  exact he

/-- The squares repainted by the edge construction: those of side larger than `K₀ t`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 135–140. -/
def largeSquare (K₀ t : ℝ) (S : DyadicSquare k) : Bool :=
  open Classical in decide (K₀ * t < (2 : ℝ) ^ (S.1 : ℕ))

/-! ### The memory before each event -/

section State

variable {L q : ℕ} {Ω : StateSpace L q} {B₀ C c : ℝ}
  (P : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L) (rank : GuideLabel → ℕ)
  (R₀ : RepaintedSquare k) {ε₀ t : ℝ} (hε : 0 < ε₀) (ht : 0 < t)
  (hB : ε₀ * t ≤ B₀ * Real.log L) (large : DyadicSquare k → Bool)
  (frozen : ProtocolEvent k × RepaintOp → Frame (cellCenterPos L) q (ProtocolParty k))
  (auxOwner : ProtocolEvent k × RepaintOp → ProtocolParty k)

/-- **The memory before an event.** Before the event number `i`, the main frame followed by the
auxiliary frames: the frozen frame of every auxiliary sheet whose repainting is done, and the idle
raw copy, held by its future owner, of every other.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 21–23, 39–41 and 653–667. -/
def protocolState (i : ℕ) : List (Frame (cellCenterPos L) q (ProtocolParty k)) :=
  mainState P rank R₀ hε ht hB i ::
    (auxIndices k large).map (auxState frozen (fun x => Frame.raw fun _ => auxOwner x) i)

end State

/-! ### The protocol -/

/-- **The dyadic protocol from its large-scale repaintings.** Fix `0 < ε₀ ≤ 1/16`. There is a
threshold `ν' > 0` such that for every mesh ratio `0 < ν ≤ ν'`, constants of the protocol with an
admissible direct-repainting ratio, `L ≥ 2` with `L ≤ 2 ^ k < 2 L`, `‖Ω‖ = 1`, patches supplied
by Proposition 4.1 at accuracy `L⁻⁶⁰`, frozen auxiliary frames and future owners of the auxiliary
copies, the following holds. Suppose that each repainting of a square of side larger than `K₀ t`,
`t = D log L`, passes the memory from its state before to its state after by `189` bounded changes
whose participants the repainting uses, with the bounds of the small-patch rewrites, that the holes
of the frozen frames satisfy the frame constraint at accuracy `L⁻⁶⁰` and number at most `C₁ L³`,
and that `C₁` dominates the counts. Then there is a dyadic protocol with the bounds of §8, all of
whose changes have at most `2 b` pair sources in each monomial.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol`, `06-geometry.tex`, lines 12–53, and
its proof, lines 82–241, 507–541 and 572–681. -/
theorem exists_isDistributionProtocol_of_largeRepaintings {ε₀ : ℝ} (hε : 0 < ε₀)
    (hε₀ : ε₀ ≤ 1 / 16) :
    ∃ ν' > 0, ∀ ν : ℝ, 0 < ν → ν ≤ ν' → ∀ {K₀ a D B₀ : ℝ},
      IsProtocolConstants K₀ ε₀ ν a D B₀ → IsDirectRepaintingRatio K₀ ε₀ ν →
      ∀ {L q : ℕ} [NeZero q] {Ω : StateSpace L q} {C c : ℝ}
        (P : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L) (hL : 2 ≤ L)
        (hkL : L ≤ 2 ^ k) (hk2 : 2 ^ k < 2 * L) (hΩ : ‖Ω‖ = 1) (rank : GuideLabel → ℕ)
        (R₀ : RepaintedSquare k) (ht : 0 < D * Real.log L)
        (hB : ε₀ * (D * Real.log L) ≤ B₀ * Real.log L)
        (frozen : ProtocolEvent k × RepaintOp → Frame (cellCenterPos L) q (ProtocolParty k))
        (auxOwner : ProtocolEvent k × RepaintOp → ProtocolParty k) {C' c' kK : ℕ} {C₁ : ℝ},
      C ≤ C' → 1 ≤ C' → c ≤ c' →
      (∀ i (hi : i < (eventSchedule k).length) (S : DyadicSquare k),
        (eventSchedule k)[i] = .inl S → largeSquare K₀ (D * Real.log L) S = true →
        ∃ seg : ℕ → List (Frame (cellCenterPos L) q (ProtocolParty k)),
          seg 0 = protocolState P rank R₀ hε ht hB (largeSquare K₀ (D * Real.log L)) frozen
            auxOwner i ∧
          seg 189 = protocolState P rank R₀ hε ht hB (largeSquare K₀ (D * Real.log L)) frozen
            auxOwner (i + 1) ∧
          ∀ j < 189, HasSourceBoundedChange Ω (seg j) (seg (j + 1)) (ℓ := []) (1 : ℂ)
            {p | EventUses (.inl S) p} (2 * protocolPatchBound ε₀ ν)
            (rewriteGateBound C' c' (protocolPatchBound ε₀ ν) L) (2 * protocolPatchBound ε₀ ν)
            ((2 * protocolPatchBound ε₀ ν + 1) * ((L : ℝ) ^ 20)⁻¹)) →
      (∀ x ∈ auxIndices k (largeSquare K₀ (D * Real.log L)), ∀ h ∈ (frozen x).holes,
        ‖act h.patch.proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹) →
      (((auxIndices k (largeSquare K₀ (D * Real.log L))).map fun x =>
        ((frozen x).holes.length : ℝ)).sum ≤ C₁ * (L : ℝ) ^ 3) →
      5042 ≤ C₁ → (rewriteGateBound C' c' (protocolPatchBound ε₀ ν) L : ℝ) ≤ C₁ * (L : ℝ) ^ kK →
      (2 * protocolPatchBound ε₀ ν + 1 : ℝ) ≤ C₁ →
      ∃ D' : DyadicProtocol L q (ProtocolParty k),
        D'.IsDistributionProtocol Ω C₁ (64 * 189) kK (2 * protocolPatchBound ε₀ ν) ∧
          ∀ t < D'.changes, (D'.step t).IsSourceBounded (2 * protocolPatchBound ε₀ ν) := by
  obtain ⟨ν', hν', Hres⟩ := exists_resize_hasSourceBoundedChange (B₀ := 0) hε hε₀
  sorry

end TNLean.PEPS.Approximation
