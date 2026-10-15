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
  obtain ⟨ν', hν', Hres⟩ := exists_resize_hasSourceBoundedChange (k := k) hε hε₀
  refine ⟨ν', hν', fun ν hν hνν' {K₀ a D B₀} hc hm {L q} _ {Ω C c} P hL hkL hk2 hΩ rank R₀ ht hB
    frozen auxOwner {C' c' kK C₁} hC hC' hcc hlarge hfε hfh hC₁ hK hεC => ?_⟩
  classical
  have hk : 1 ≤ k := by
    by_contra h
    have : k = 0 := by omega
    subst this
    simp at hk2
    omega
  set t := D * Real.log L with ht_def
  set large := largeSquare (k := k) K₀ t with hlarge_def
  set b := protocolPatchBound ε₀ ν with hb_def
  set st := protocolState P rank R₀ hε ht hB large frozen auxOwner with hst_def
  set idle : ProtocolEvent k × RepaintOp → Frame (cellCenterPos L) q (ProtocolParty k) :=
    fun x => Frame.raw fun _ => auxOwner x
  have hε0 : (0 : ℝ) ≤ (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ := by positivity
  -- the changes of each event
  have hseg : ∀ i (hi : i < (eventSchedule k).length),
      ∃ seg : ℕ → List (Frame (cellCenterPos L) q (ProtocolParty k)), seg 0 = st i ∧
        seg (eventOps large ((eventSchedule k)[i])).length = st (i + 1) ∧
        ∀ j < (eventOps large ((eventSchedule k)[i])).length,
          HasSourceBoundedChange Ω (seg j) (seg (j + 1)) (ℓ := []) (1 : ℂ)
            {p | EventUses ((eventSchedule k)[i]) p} (2 * b) (rewriteGateBound C' c' b L)
            (2 * b) ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹) := by
    intro i hi
    -- one change between the states before and after the event
    have hone : HasSourceBoundedChange Ω (st i) (st (i + 1)) (ℓ := []) (1 : ℂ)
        {p | EventUses ((eventSchedule k)[i]) p} (2 * b) (rewriteGateBound C' c' b L)
        (2 * b) ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹) →
        (eventOps large ((eventSchedule k)[i])).length = 1 →
        ∃ seg : ℕ → List (Frame (cellCenterPos L) q (ProtocolParty k)), seg 0 = st i ∧
          seg (eventOps large ((eventSchedule k)[i])).length = st (i + 1) ∧
          ∀ j < (eventOps large ((eventSchedule k)[i])).length,
            HasSourceBoundedChange Ω (seg j) (seg (j + 1)) (ℓ := []) (1 : ℂ)
              {p | EventUses ((eventSchedule k)[i]) p} (2 * b) (rewriteGateBound C' c' b L)
              (2 * b) ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹) := fun h h1 =>
      ⟨fun j => if j = 0 then st i else st (i + 1), by simp, by rw [h1]; simp, fun j hj => by
        rw [h1] at hj
        obtain rfl : j = 0 := by omega
        simpa using h⟩
    rcases he : (eventSchedule k)[i] with S | J
    · by_cases hlS : large S = true
      · obtain ⟨seg, h0, h1, h2⟩ := hlarge i hi S he hlS
        refine ⟨seg, h0, ?_, ?_⟩
        · simp only [eventOps, hlS, ite_true, length_largeRepaintingOps]; exact h1
        · simp only [eventOps, hlS, ite_true, length_largeRepaintingOps]; exact h2
      · have hS : (S.1 : ℕ) < k := by
          have := isScheduled_getElem hi; rw [he] at this; exact this
        have hKS : (2 : ℝ) ^ (S.1 : ℕ) ≤ K₀ * t := by
          by_contra h
          exact hlS (by simp only [hlarge_def, largeSquare, decide_eq_true_eq]; exact not_le.1 h)
        rw [← he]
        refine hone ?_ (by simp [he, eventOps, hlS])
        have haux := auxState_succ frozen idle hi (large := large) fun S' h => by
          rw [he] at h; obtain rfl := Sum.inl_injective h; simpa using hlS
        simp only [hst_def, protocolState]
        rw [haux, mainState_of_lt _ _ _ _ _ _ hi, he,
          ← eventMain_inl_succ P rank R₀ hε ht hB hk hi he]
        simp only [eventMain]
        exact directRepainting_hasSourceBoundedChange hc hm hL hkL hΩ P rank R₀ ⟨S, hS⟩
          hKS _ _ hC hC' hcc _
    · have hJ0 : 0 < (J.1 : ℕ) := by
        have := isScheduled_getElem hi; rw [he] at this; exact this
      rw [← he]
      refine hone ?_ (by simp [he, eventOps])
      have haux := auxState_succ frozen idle hi (large := large) fun S' h => by
        rw [he] at h; exact absurd h Sum.inr_ne_inl
      simp only [hst_def, protocolState]
      rw [haux, mainState_of_lt _ _ _ _ _ _ hi, he,
        ← eventMain_inr_succ P rank R₀ hε ht hB hk hi he]
      simp only [eventMain]
      exact Hres ν hν hνν' hc hL hkL hΩ P rank R₀ J hJ0 _ _ _ hC hC' hcc _
  -- the trajectory
  choose seg hseg0 hsegm hsegs using hseg
  obtain ⟨tr, htr0, htrm, htrs⟩ := exists_frames_of_segments (Ω := Ω) (ℓ := []) (ξ := (1 : ℂ))
    (fun e : ProtocolEvent k => {p | EventUses e p}) (eventOps large) (eventSchedule k) st
    (fun i => if h : i < (eventSchedule k).length then seg i h else fun _ => st i)
    (fun i => by split_ifs with h; exacts [hseg0 i h, rfl])
    (fun i hi => by simp only [hi, dite_true]; exact hsegm i hi)
    (fun i hi j hj => by simp only [hi, dite_true]; exact hsegs i hi j hj)
  -- the endpoints
  have hall : ∀ x ∈ auxIndices k large, x.1 ∈ (eventSchedule k).take (eventSchedule k).length :=
    fun x hx => by rw [List.take_length]; exact mem_eventSchedule_of_mem_auxIndices hx
  have hfin : tr (protocolSchedule k large).length = finalMain P rank R₀ hε ht hB ::
      (auxIndices k large).map frozen := by
    change tr ((eventSchedule k).flatMap fun e => (eventOps large e).map (e, ·)).length = _
    rw [htrm, hst_def, protocolState, mainState_of_le _ _ _ _ _ _ le_rfl]
    congr 1
    exact List.map_congr_left fun x hx => by simp only [auxState, hall x hx, ite_true]
  have hst0 : tr 0 = Frame.raw (fun _ => .inl (rootSquare k)) :: (auxIndices k large).map idle := by
    rw [htr0, hst_def, protocolState, mainState_zero P rank R₀ hε ht hB hk hkL]
    congr 1
  have hL0 : 0 < L := by omega
  have hε4 : 4 * ε₀ < 1 := by have := hc.ε₀_lt; linarith
  refine exists_isDistributionProtocol_of_hasSourceBoundedChange hL hkL hk2 large hΩ tr
    (fun F => F.owner (⟨0, hL0⟩, ⟨0, hL0⟩)) (fun F hF => ?_) (fun F hF x => ?_)
    (fun t ht => htrs t ht) _ _ hfin
    (finalMain_owner P rank R₀ hε ht hB hkL hε4) (finalMain_holes P rank R₀ hε ht hB hε4)
    (fun F hF h hh => ?_) (by simpa [List.map_map, Function.comp_def] using hfh) hC₁ hK
    (by rw [div_eq_mul_inv]; gcongr)
  · rw [hst0] at hF
    rcases List.mem_cons.1 hF with rfl | hF
    · rfl
    · obtain ⟨x, -, rfl⟩ := List.mem_map.1 hF; rfl
  · rw [hst0] at hF
    rcases List.mem_cons.1 hF with rfl | hF
    · rfl
    · obtain ⟨x, -, rfl⟩ := List.mem_map.1 hF; rfl
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hF
    exact hfε x hx h hh

end TNLean.PEPS.Approximation
