/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.NestedPatches.AdaptivePatchSupply
import TNLean.PEPS.Approximation.Protocol.DyadicProtocol
import TNLean.PEPS.Approximation.Guides.DyadicProtocolParties
import TNLean.PEPS.Approximation.Frames.SheetStackRawInitial

/-!
# The initial step of the dyadic protocol

In the protocol of Proposition 7.1 of the polynomial-PEPS manuscript every copy of `Ω` is
initialized privately at its future owner: the main copy at the root party, and each auxiliary
copy at the party that will use it. At the beginning the main guide carries only the root label
and the exterior placeholder, so every initial sheet is a raw frame, without holes and held by
one party (`06-geometry.tex`, lines 21–23 and 658–667). Such a reference vector is a product
across the parties (`QuantumCircuit.Party.exists_productVector_eq_framesVec`), so the initial
memory of a protocol can be the memory of the frames itself.

* `DyadicProtocol.exists_originalCircuit_initial`: if the initial memory of a protocol is the
  memory of a list of frames and its initial reference vector is their reference vector, then an
  original circuit with no nonprivate gate carries the initial reference vector exactly to the
  reference vector of the frames: the identification of the two memories.
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

open EncodedFrame ManyBody QuantumCircuit.Party

/-! ### The initial step of a protocol -/

namespace DyadicProtocol

variable {L q : ℕ} {P : Type} [Fintype P] [DecidableEq P] (D : DyadicProtocol L q P)

/-- **The initial step of a protocol from copies.** If the whole initial memory of each party of a
protocol is its memory on the frames of the list `Fs`, and the initial reference vector is the
reference vector of `Fs`, then an original circuit with no nonprivate gate, whose participant
conditions hold vacuously, carries the initial reference vector exactly to the reference vector
of `Fs`.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol`, item 1, `06-geometry.tex`,
lines 21–23, and its proof, lines 658–667. -/
theorem exists_originalCircuit_initial [NeZero q] {ι : Type} [Fintype ι] [DecidableEq ι]
    {pos : ι → ℝ × ℝ} (Ω : EuclideanSpace ℂ (ι → Fin q)) (Fs : List (Frame pos q P))
    (hsys : D.system 0 = framesSystem q pos Fs fun _ ↦ Unit)
    (href : D.reference 0 = OriginalCircuit.castVector hsys.symm (framesRef Ω Fs)) :
    ∃ c : OriginalCircuit (D.system 0) (framesSystem q pos Fs fun _ ↦ Unit),
      c.nonprivateCount = 0 ∧ (∀ (S : Set P) g, (↑(c.participants g) : Set P) ⊆ S) ∧
        (∀ r s, c.IsExpansionBounded r s) ∧ (∀ K, c.IsMonomialBounded K) ∧
          Matrix.toEuclideanLin c.op (D.reference 0) = framesRef Ω Fs := by
  have h0 : ((OriginalCircuit.done _).castSystems hsys.symm rfl :
      OriginalCircuit (D.system 0) (framesSystem q pos Fs fun _ ↦ Unit)).nonprivateCount = 0 := by
    simp
  refine ⟨(OriginalCircuit.done _).castSystems hsys.symm rfl, h0,
    fun S g ↦ OriginalCircuit.forall_participants_of_nonprivateCount_eq_zero
      (Q := fun T ↦ (↑T : Set P) ⊆ S) h0 g,
    fun r s ↦ OriginalCircuit.isExpansionBounded_of_nonprivateCount_eq_zero h0 r s,
    fun K ↦ OriginalCircuit.isMonomialBounded_of_nonprivateCount_eq_zero h0 K, ?_⟩
  rw [href, OriginalCircuit.toEuclideanLin_op_castSystems, OriginalCircuit.op_done,
    OriginalCircuit.castVector_rfl]
  simp

/-- **The two descriptions of the initial reference vector agree.** For a protocol with the
bounds of §8 and `‖Ω‖ = 1`, the initial product vector `r_0` across the parties is carried by an
original circuit with no nonprivate gate exactly to the reference vector of the initial encoded
frames: the main copy of `Ω` followed by the auxiliary copies.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol`, item 1, `06-geometry.tex`,
lines 21–23, and item 4, lines 38–40. -/
theorem IsDistributionProtocol.exists_originalCircuit_initialCopies [NeZero q]
    {Ω : StateSpace L q} {C_N C_K C_E : ℝ} {b k r : ℕ}
    (h : D.IsDistributionProtocol Ω C_N C_K C_E b k r) :
    ∃ c : OriginalCircuit (D.system 0)
        (framesSystem q (cellCenterPos L) (D.frames 0) fun _ ↦ Unit),
      c.nonprivateCount = 0 ∧
        Matrix.toEuclideanLin c.op (D.reference 0) = framesRef Ω (D.frames 0) := by
  obtain ⟨-, -, -, hsys, href⟩ := h.initialCopies
  obtain ⟨c, h0, -, -, -, hc⟩ := D.exists_originalCircuit_initial Ω (D.frames 0) hsys href
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

/-- **The initial step of the dyadic protocol.** Let the whole initial memory of each party of a
protocol on the parties of the hierarchy be its memory on the initial sheets, the main copy at the
root party and every auxiliary copy at its future owner, and let the initial reference vector be
the reference vector of the initial sheets. Then an original circuit with no nonprivate gate
carries the initial reference vector exactly to the reference vector of the initial sheets.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol`, item 1, `06-geometry.tex`,
lines 21–23, and its proof, lines 658–667. -/
theorem DyadicProtocol.exists_originalCircuit_initialFrames [NeZero q]
    (D : DyadicProtocol L q (ProtocolParty k)) (Ω : StateSpace L q)
    (large : DyadicSquare k → Bool)
    (auxOwner : ProtocolEvent k × RepaintOp → ProtocolParty k)
    (hsys : D.system 0 =
      framesSystem q (cellCenterPos L) (initialFrames (q := q) k large auxOwner) fun _ ↦ Unit)
    (href : D.reference 0 = OriginalCircuit.castVector hsys.symm
      (framesRef Ω (initialFrames (q := q) k large auxOwner))) :
    ∃ c : OriginalCircuit (D.system 0)
        (framesSystem q (cellCenterPos L) (initialFrames (q := q) k large auxOwner) fun _ ↦ Unit),
      c.nonprivateCount = 0 ∧ (∀ (S : Set (ProtocolParty k)) g,
        (↑(c.participants g) : Set (ProtocolParty k)) ⊆ S) ∧
        (∀ r s, c.IsExpansionBounded r s) ∧ (∀ K, c.IsMonomialBounded K) ∧
          Matrix.toEuclideanLin c.op (D.reference 0) =
            framesRef Ω (initialFrames (q := q) k large auxOwner) :=
  D.exists_originalCircuit_initial Ω _ hsys href

end Approximation

end TNLean.PEPS
