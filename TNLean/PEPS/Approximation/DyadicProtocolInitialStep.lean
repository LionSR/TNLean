/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AdaptivePatchSupply
import TNLean.PEPS.Approximation.DyadicProtocol
import TNLean.PEPS.Approximation.DyadicProtocolParties
import TNLean.PEPS.Approximation.SheetStackRawInitial

/-!
# The initial step of the dyadic protocol

In the protocol of Proposition 7.1 of the polynomial-PEPS manuscript every copy of `Ω` is
initialized privately at its future owner: the main copy at the root party, and each auxiliary
copy at the party that will use it. At the beginning the main guide carries only the root label
and the exterior placeholder, so every initial sheet is a raw frame, without holes and held by
one party (`06-geometry.tex`, lines 21–23 and 658–667). This file instantiates the initial step
`EncodedFrame.exists_originalCircuit_initial_of_holes_eq_nil` on these frames.

* `DyadicProtocol.exists_originalCircuit_initial`: if the initial memory of every party of a
  protocol is the memory of the raw frames it holds and its initial vector is their reference
  vector, then one private map per party followed by a reordering, with no nonprivate gate,
  carries the initial reference vector exactly to the reference vector of the frames.
* `initialFrames`: the main raw frame at the root party followed by one raw frame for each change
  of the schedule that initializes an auxiliary sheet, held by an arbitrary assigned future owner;
  `length_initialFrames_le` counts them by `countP_isAuxInit_protocolSchedule_le`.
* `DyadicProtocol.exists_originalCircuit_initialFrames`: the initial step for these frames.

The future owners of the auxiliary copies are arbitrary here; the trajectory of the protocol is
not fixed.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 7.1 `prop:protocol`, item 1,
  `06-geometry.tex`, lines 21–23, and its proof, lines 576, 649–652 and 658–667.
-/

noncomputable section

namespace TNLean.PEPS

namespace Approximation

open EncodedFrame TNLean.Lattice.PartyCircuit

/-! ### The initial step of a protocol -/

namespace DyadicProtocol

variable {L q : ℕ} {P : Type} [Fintype P] (D : DyadicProtocol L q P)

/-- **The initial step of a protocol from raw copies.** Let `‖Ω‖ = 1` and let every frame of the
list `Fs` have no hole and be held entirely by the party `holder F`. If the whole initial memory
of each party of a protocol is the memory of the frames it holds and its initial vector is the
product of their reference vectors, then one private map per party followed by a reordering,
with no nonprivate gate, carries the initial reference vector exactly to the reference vector of
`Fs`.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol`, item 1, `06-geometry.tex`,
lines 21–23, and its proof, lines 658–667. -/
theorem exists_originalCircuit_initial [DecidableEq P] [NeZero q] {ι : Type} [Fintype ι]
    [DecidableEq ι] {pos : ι → ℝ × ℝ} {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    (Fs : List (Frame pos q P)) (holder : Frame pos q P → P) (hraw : ∀ F ∈ Fs, F.holes = [])
    (hown : ∀ F ∈ Fs, ∀ x, F.owner x = holder F)
    (hspace : D.initialSpace = fun p => framesSpace (Fs.filter fun F => holder F = p))
    (hvec : HEq D.initialVector fun p => framesVec Ω (Fs.filter fun F => holder F = p)) :
    ∃ c : OriginalCircuit (D.layout 0) (stackRegs Fs []),
      c.nonprivateCount = 0 ∧ (∀ (S : Set P) g, (↑(c.participants g) : Set P) ⊆ S) ∧
        (∀ r s, c.IsExpansionBounded r s) ∧ (∀ K, c.IsMonomialBounded K) ∧
          c.eval (D.reference 0) = framesVec Ω Fs := by
  obtain ⟨hx, c, h0, h1, h2, h3, h4⟩ :=
    exists_originalCircuit_initial_of_holes_eq_nil hΩ Fs holder hraw hown
  obtain ⟨placement, initialSpace, finite_initialSpace, initialVector, norm_initialVector,
    changes, layout, layout_zero, step, reference, reference_zero⟩ := D
  dsimp only at hspace hvec reference_zero ⊢
  subst hspace
  obtain rfl := eq_of_heq hvec
  refine ⟨c.castLayouts layout_zero.symm rfl, by rw [OriginalCircuit.nonprivateCount_castLayouts,
    h0], fun S => OriginalCircuit.participants_castLayouts_subset _ _ _ (h1 S),
    fun r s => OriginalCircuit.isExpansionBounded_castLayouts _ _ _ (h2 r s),
    fun K => OriginalCircuit.isMonomialBounded_castLayouts _ _ _ (h3 K), ?_⟩
  rw [OriginalCircuit.eval_castLayouts, reference_zero]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.isoL_apply,
    LinearIsometryEquiv.symm_apply_apply]
  exact h4

/-- **The two descriptions of the initial reference vector agree.** For a protocol with the
bounds of §8 and `‖Ω‖ = 1`, the initial product vector `r_0` across the parties is carried by one
private map per party followed by a reordering, with no nonprivate gate, exactly to the reference
vector of the initial encoded frames: the main copy of `Ω` followed by the auxiliary copies.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol`, item 1, `06-geometry.tex`,
lines 21–23, and item 4, lines 38–40. -/
theorem IsDistributionProtocol.exists_originalCircuit_initialCopies [NeZero q]
    {Ω : StateSpace L q} {C_N C_K C_E : ℝ} {b k r : ℕ}
    (h : D.IsDistributionProtocol Ω C_N C_K C_E b k r)
    (hΩ : ‖Ω‖ = 1) :
    ∃ c : OriginalCircuit (D.layout 0) (stackRegs (D.frames 0) []),
      c.nonprivateCount = 0 ∧ c.eval (D.reference 0) = framesVec Ω (D.frames 0) := by
  classical
  obtain ⟨-, holder, hF, hsv⟩ := h.initialCopies
  obtain ⟨hs, hv⟩ := hsv
  obtain ⟨c, h0, -, -, -, hc⟩ := D.exists_originalCircuit_initial hΩ (D.frames 0) holder
    (fun F hF' => (hF F hF').1) (fun F hF' => (hF F hF').2) hs hv
  exact ⟨c, h0, hc⟩

end DyadicProtocol

/-! ### The raw copies of the dyadic protocol -/

variable {L q k : ℕ}

/-- The root square of the hierarchy of `[0, 2 ^ k] ^ 2`. -/
def rootSquare (k : ℕ) : DyadicSquare k :=
  ⟨Fin.last k, ⟨0, by simp⟩, ⟨0, by simp⟩⟩

/-- **The initial sheets.** The main raw frame, held by the party of the root square, followed by
one raw frame for each change of the schedule that initializes an auxiliary sheet, held by the
future owner `auxOwner x` of that copy.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 21–23, 127–131 and 658–667. -/
def initialFrames (k : ℕ) (large : DyadicSquare k → Bool)
    (auxOwner : ProtocolEvent k × RepaintOp → ProtocolParty k) :
    List (Frame (cellCenterPos L) q (ProtocolParty k)) :=
  Frame.raw (fun _ => .inl (rootSquare k)) ::
    ((protocolSchedule k large).filter fun x => x.2.IsAuxInit).map fun x =>
      Frame.raw (fun _ => auxOwner x)

/-- **Count of the initial sheets.** There is one main copy and at most four auxiliary copies for
each square and junction of the hierarchy.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 576 and 649–652. -/
theorem length_initialFrames_le (k : ℕ) (large : DyadicSquare k → Bool)
    (auxOwner : ProtocolEvent k × RepaintOp → ProtocolParty k) :
    (initialFrames (L := L) (q := q) k large auxOwner).length ≤
      1 + 4 * (Fintype.card (DyadicSquare k) + Fintype.card (DyadicJunction k)) := by
  have h := countP_isAuxInit_protocolSchedule_le k large
  rw [List.countP_eq_length_filter] at h
  rw [initialFrames, List.length_cons, List.length_map]
  omega

/-- The party holding a raw frame on the square of side `L > 0`: the owner of its first site. -/
def rawHolder (hL : 0 < L) (F : Frame (cellCenterPos L) q (ProtocolParty k)) : ProtocolParty k :=
  F.owner (⟨0, hL⟩, ⟨0, hL⟩)

theorem mem_initialFrames {large : DyadicSquare k → Bool}
    {auxOwner : ProtocolEvent k × RepaintOp → ProtocolParty k}
    {F : Frame (cellCenterPos L) q (ProtocolParty k)} (hF : F ∈ initialFrames k large auxOwner) :
    ∃ p, F = Frame.raw (fun _ => p) := by
  rcases List.mem_cons.1 (by simpa only [initialFrames] using hF) with rfl | hF
  · exact ⟨_, rfl⟩
  · obtain ⟨x, -, rfl⟩ := List.mem_map.1 hF
    exact ⟨_, rfl⟩

/-- **The initial step of the dyadic protocol.** Let `‖Ω‖ = 1` on the square of side `L > 0`. If
the whole initial memory of each party of a protocol on the parties of the hierarchy is the
memory of the initial sheets it holds, the main copy at the root party and every auxiliary copy
at its future owner, and its initial vector is the product of their reference vectors, then the
initial reference vector is carried exactly to the reference vector of the initial sheets, by one
private map per party and a reordering, with no nonprivate gate.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol`, item 1, `06-geometry.tex`,
lines 21–23, and its proof, lines 658–667. -/
theorem DyadicProtocol.exists_originalCircuit_initialFrames [NeZero q]
    (D : DyadicProtocol L q (ProtocolParty k)) (hL : 0 < L) {Ω : StateSpace L q}
    (hΩ : ‖Ω‖ = 1) (large : DyadicSquare k → Bool)
    (auxOwner : ProtocolEvent k × RepaintOp → ProtocolParty k)
    (hspace : D.initialSpace = fun p =>
      framesSpace ((initialFrames (q := q) k large auxOwner).filter fun F => rawHolder hL F = p))
    (hvec : HEq D.initialVector fun p =>
      framesVec Ω ((initialFrames (q := q) k large auxOwner).filter fun F => rawHolder hL F = p)) :
    ∃ c : OriginalCircuit (D.layout 0) (stackRegs (initialFrames (q := q) k large auxOwner) []),
      c.nonprivateCount = 0 ∧ (∀ (S : Set (ProtocolParty k)) g,
        (↑(c.participants g) : Set (ProtocolParty k)) ⊆ S) ∧
        (∀ r s, c.IsExpansionBounded r s) ∧ (∀ K, c.IsMonomialBounded K) ∧
          c.eval (D.reference 0) = framesVec Ω (initialFrames (q := q) k large auxOwner) :=
  D.exists_originalCircuit_initial hΩ _ (rawHolder hL)
    (fun F hF => by obtain ⟨p, rfl⟩ := mem_initialFrames hF; rfl)
    (fun F hF x => by obtain ⟨p, rfl⟩ := mem_initialFrames hF; rfl) hspace hvec

end Approximation

end TNLean.PEPS
