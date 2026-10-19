/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicProtocolFinalReadout
import TNLean.PEPS.Approximation.DyadicProtocolInitialStep
import TNLean.PEPS.Approximation.OriginalCircuitChain
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

## Main results

* `card_eventUses_le`: an event of the hierarchy uses at most `19` parties.
* `exists_isDistributionProtocol_of_frames`: the assembled protocol satisfies the bounds of §8,
  including the pair-source bound when the changes of the schedule are source bounded.

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

namespace Approximation

open EncodedFrame PairEffect PairEffect.OriginalCircuit

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
  let g : ProtocolParty k → (ℕ × ℕ × ℕ) ⊕ Unit :=
    Sum.elim (fun Q => .inl Q.toTriple) fun _ => .inr ()
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

/-! ### The assembled protocol -/

/-- The padded side is at least every power of two below twice the side. -/
theorem pow_le_paddedSide {L k : ℕ} (h : 2 ^ k < 2 * L) : 2 ^ k ≤ paddedSide L := by
  have h1 : 2 ^ k < 2 ^ (Nat.clog 2 L + 1) := by
    have := le_paddedSide L
    rw [paddedSide] at this
    rw [pow_succ]
    omega
  exact Nat.pow_le_pow_right two_pos (Nat.lt_succ_iff.1 ((Nat.pow_lt_pow_iff_right
    (by norm_num)).1 h1))

/-- Every register of a list of frames is finite-dimensional. -/
theorem finiteDimensional_of_mem_stackRegs {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ}
    {pos : ι → ℝ × ℝ} {Party : Type} :
    ∀ (Fs : List (Frame pos q Party)), ∀ r ∈ stackRegs Fs [], FiniteDimensional ℂ r.space
  | [], r, hr => absurd hr List.not_mem_nil
  | F :: Fs, r, hr => by
    rcases List.mem_append.1 hr with hr | hr
    · rcases List.mem_append.1 hr with hr | hr
      · have key : ∀ l : List (Hole pos q Party), ∀ r ∈ tagRegs l,
            FiniteDimensional ℂ r.space := by
          intro l
          induction l with
          | nil => intro r hr; exact absurd hr List.not_mem_nil
          | cons h l ih =>
            intro r hr
            rcases List.mem_cons.1 hr with rfl | hr
            · change FiniteDimensional ℂ (EuclideanSpace ℂ h.patch.Tag)
              infer_instance
            · exact ih r hr
        exact key _ r hr
      · obtain ⟨x, -, rfl⟩ := List.mem_map.1 hr
        change FiniteDimensional ℂ (EuclideanSpace ℂ (Fin q))
        infer_instance
    · exact finiteDimensional_of_mem_stackRegs Fs r hr

/-- The reference vector of equal lists of frames, across the identification of their
registers. -/
theorem memCongr_stackVec {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} [NeZero q]
    {pos : ι → ℝ × ℝ} {Party : Type} (Ω : EuclideanSpace ℂ (ι → Fin q))
    {Fs Fs' : List (Frame pos q Party)} (h : Fs = Fs') {ℓ : Layout Party} (ξ : Mem ℓ) :
    Layout.memCongr (congrArg (stackRegs · ℓ) h) (stackVec Ω Fs ξ) = stackVec Ω Fs' ξ := by
  subst h
  rfl

/-- A square of the padded hierarchy of `[0, 2 ^ k] ^ 2` is a square of the hierarchy of depth
`k`: its scale is at most `k` and its block indices are below `2 ^ (k - j)`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 64–65. -/
theorem HierarchySquare.lt_of_eq_pow {N k : ℕ} (hN : N = 2 ^ k) (S : HierarchySquare N) :
    S.1.1 < k + 1 ∧ S.1.2.1 < 2 ^ (k - S.1.1) ∧ S.1.2.2 < 2 ^ (k - S.1.1) := by
  obtain ⟨⟨j, x, y⟩, hx, hy⟩ := S
  subst hN
  dsimp only at hx hy ⊢
  have hj : j ≤ k := by
    have : 2 ^ j ≤ 2 ^ k := (Nat.le_mul_of_pos_right _ (by omega)).trans hx
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  have hsplit : (2 : ℕ) ^ k = 2 ^ j * 2 ^ (k - j) := by rw [← pow_add, Nat.add_sub_cancel' hj]
  rw [hsplit] at hx hy
  have hx' := Nat.le_of_mul_le_mul_left hx (by positivity)
  have hy' := Nat.le_of_mul_le_mul_left hy (by positivity)
  omega

/-- **Events occupy segments of the schedule.** The changes of one event form a contiguous
segment of the protocol schedule: the events are listed without repetition, and each contributes
its changes in one block.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 82–87. -/
theorem protocolSchedule_fst_eq_of_le {k : ℕ} (large : DyadicSquare k → Bool) {i m j : ℕ}
    (him : i ≤ m) (hmj : m ≤ j) (hj : j < (protocolSchedule k large).length)
    {e : ProtocolEvent k} (hi : ((protocolSchedule k large)[i]'(by omega)).1 = e)
    (hj' : ((protocolSchedule k large)[j]).1 = e) :
    ((protocolSchedule k large)[m]'(by omega)).1 = e := by
  set l := eventSchedule k
  have hl : l.Nodup := nodup_eventSchedule k
  let key : ProtocolEvent k × RepaintOp → ℕ := fun x => l.idxOf x.1
  have hpos : l.Pairwise fun a b => l.idxOf a < l.idxOf b := by
    refine List.pairwise_iff_getElem.2 fun a b ha hb hab => ?_
    rw [hl.idxOf_getElem a ha, hl.idxOf_getElem b hb]
    exact hab
  have hsorted : (protocolSchedule k large).Pairwise fun x y => key x ≤ key y := by
    refine List.pairwise_flatMap.2 ⟨fun a _ => ?_, hpos.imp fun {a b} hab x hx y hy => ?_⟩
    · refine List.pairwise_map.2 (List.pairwise_of_forall fun _ _ => le_rfl)
    · obtain ⟨_, -, rfl⟩ := List.mem_map.1 hx
      obtain ⟨_, -, rfl⟩ := List.mem_map.1 hy
      exact hab.le
  have hle : ∀ {a b : ℕ} (hab : a ≤ b) (hb : b < (protocolSchedule k large).length),
      key ((protocolSchedule k large)[a]'(by omega)) ≤ key ((protocolSchedule k large)[b]) :=
    fun {a b} hab hb => by
      rcases hab.lt_or_eq with hab | rfl
      · exact List.pairwise_iff_getElem.1 hsorted a b _ hb hab
      · exact le_rfl
  have hmem : ∀ x ∈ protocolSchedule k large, x.1 ∈ l := fun x hx => by
    obtain ⟨a, ha, hx⟩ := List.mem_flatMap.1 hx
    obtain ⟨_, -, rfl⟩ := List.mem_map.1 hx
    exact ha
  have h1 := hle him (by omega)
  have h2 := hle hmj hj
  simp only [key, hi, hj'] at h1 h2
  exact (List.idxOf_inj (hmem _ (List.getElem_mem _))).1 (le_antisymm h2 h1)

/-- **The party of each square of the hierarchy.** When the padded side is `2 ^ k`, each aligned
square of the padded square, including the root square, is assigned its block party.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 19–20 and 64–67. -/
def protocolSquareParty {L k : ℕ} (hN : paddedSide L = 2 ^ k)
    (S : HierarchySquare (paddedSide L)) : ProtocolParty k :=
  .inl ⟨⟨S.1.1, (S.lt_of_eq_pow hN).1⟩, ⟨S.1.2.1, (S.lt_of_eq_pow hN).2.1⟩,
    ⟨S.1.2.2, (S.lt_of_eq_pow hN).2.2⟩⟩

/-- The party of a square of the hierarchy is attached to that square.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 19–20 and 64–67. -/
theorem toTriple_protocolSquareParty {L k : ℕ} (hN : paddedSide L = 2 ^ k)
    (S : HierarchySquare (paddedSide L)) :
    (protocolSquareParty hN S).square.toTriple = S.1 := rfl

/-- Distinct squares of the hierarchy have distinct block parties.

Polynomial-PEPS manuscript, `06-geometry.tex`, line 67: “A different party is assigned to each
dyadic square.” -/
theorem protocolSquareParty_injective {L k : ℕ} (hN : paddedSide L = 2 ^ k) :
    Function.Injective (protocolSquareParty hN) := fun S S' h => Subtype.ext (by
  rw [← toTriple_protocolSquareParty hN S, ← toTriple_protocolSquareParty hN S', h])

/-- **Additional parties.** When `L ≤ 2 ^ k < 2 L`, every party other than a block party of
`protocolSquareParty` is the placeholder of a non-root square `S`, placed at `S` and used only by
the repainting of `S`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 19–22, 35–37, and 91–95. -/
theorem exists_eq_inr_of_notMem_range_protocolSquareParty {L k : ℕ} (hN : paddedSide L = 2 ^ k)
    (p : ProtocolParty k) (hp : p ∉ Set.range (protocolSquareParty hN)) :
    ∃ R : RepaintedSquare k, p = .inr R := by
  rcases p with T | R
  · refine (hp ⟨⟨T.toTriple, ?_⟩, ?_⟩).elim
    · rw [hN]; exact (protocolPlacement_inGrid k) (.inl T)
    · exact congrArg Sum.inl (DyadicSquare.toTriple_injective k
        (toTriple_protocolSquareParty hN _))
  · exact ⟨R, rfl⟩

/-- **A protocol from a bounded trajectory of sheets.** Let `L ≥ 2` and `L ≤ 2 ^ k < 2 L`, let
`‖Ω‖ = 1`, and let `st t` be lists of encoded frames on the parties of the hierarchy of
`[0, 2 ^ k] ^ 2`, read at the cell centers, such that:

* the frames of `st 0` have no holes, and each is held entirely by one party `holder F`;
* for every change `t` of the schedule there is an original circuit `c t` from the registers of
  `st t` to those of `st (t + 1)` that is a bounded change from the reference vector of `st t` to
  that of `st (t + 1)`, with participants used by the event of the change, at most `r` pair
  effects and at most `r` pair sources per monomial, at most `K ≤ C L ^ kK` monomials and
  coefficient sum, and error `ε ≤ C L⁻²⁰`;
* at the end of the schedule the frames are `M :: Fs`, where the raw owner of every site in the
  main frame `M` is its unit-square party and the holes of `M` are trivial, every hole of the
  other sheets satisfies the frame constraint at accuracy `L⁻⁶⁰`, and the other sheets carry at
  most `C L³` holes.

If `C ≥ 5042`, there is a dyadic protocol with the bounds of
`DyadicProtocol.IsDistributionProtocol` for `Ω` and the constants `C`, `b = 64 · 189`, `kK` and
`r`, including the bound `r` on the pair sources of each monomial. Its first change is the private
initialization, then come the changes of the schedule, and its last change is the final
regrouping into the physical registers.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol`, `06-geometry.tex`, lines 12–53,
and its proof, lines 572–681; Theorem 5.2, item 3, `04-compression.tex`, lines 143–147. -/
theorem exists_isDistributionProtocol_of_frames {L q k : ℕ} [NeZero q] (hL : 2 ≤ L)
    (hkL : L ≤ 2 ^ k) (hk2 : 2 ^ k < 2 * L) (large : DyadicSquare k → Bool)
    {Ω : StateSpace L q} (hΩ : ‖Ω‖ = 1)
    (st : ℕ → List (Frame (cellCenterPos L) q (ProtocolParty k)))
    (hne : ∀ t ≤ (protocolSchedule k large).length, st t ≠ [])
    (holder : Frame (cellCenterPos L) q (ProtocolParty k) → ProtocolParty k)
    (hraw : ∀ F ∈ st 0, F.holes = []) (hown : ∀ F ∈ st 0, ∀ x, F.owner x = holder F)
    (c : ∀ t, OriginalCircuit (stackRegs (st t) []) (stackRegs (st (t + 1)) []))
    {r K kK : ℕ} {C ε : ℝ}
    (hc : ∀ t (ht : t < (protocolSchedule k large).length),
      (c t).IsBoundedChange {p | EventUses ((protocolSchedule k large)[t]).1 p} r K ε
        (framesVec Ω (st t)) (framesVec Ω (st (t + 1))))
    (hsrc : ∀ t < (protocolSchedule k large).length, (c t).IsSourceBounded r)
    (M : Frame (cellCenterPos L) q (ProtocolParty k))
    (Fs : List (Frame (cellCenterPos L) q (ProtocolParty k)))
    (hfin : st (protocolSchedule k large).length = M :: Fs)
    (hMown : ∀ v, M.owner v = .inl (unitSquare hkL v)) (hM : ∀ h ∈ M.holes, h.patch.outer = ∅)
    (hε : ∀ F ∈ Fs, ∀ h ∈ F.holes, ‖act h.patch.proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hholes : (Fs.map fun F => (F.holes.length : ℝ)).sum ≤ C * (L : ℝ) ^ 3)
    (hC : 5042 ≤ C) (hK : (K : ℝ) ≤ C * (L : ℝ) ^ kK) (hεC : ε ≤ C / (L : ℝ) ^ 20) :
    ∃ D : DyadicProtocol L q (ProtocolParty k),
      D.IsDistributionProtocol Ω C (64 * 189) kK r := by
  classical
  set sch := protocolSchedule k large with hsch
  set n := sch.length with hn
  obtain ⟨hx, c₀, h0, -, -, -, hev0⟩ :=
    exists_originalCircuit_initial_of_holes_eq_nil hΩ (st 0) holder hraw hown
  have hinj : Function.Injective M.owner := fun v w h => by
    rw [hMown, hMown] at h
    exact unitSquare_injective hkL (Sum.inl_injective h)
  let d : ProtocolParty k → ℕ := fun p => if p ∈ Set.range M.owner then q else 1
  have hd : ∀ x, d (M.owner x) = q := fun x => by simp [d]
  have hd1 : ∀ p ∉ Set.range M.owner, d p = 1 := fun p hp => by simp only [d]; exact ite_eq_right hp
  have hrange : Set.range (fun v => (.inl (unitSquare hkL v) : ProtocolParty k)) =
      Set.range M.owner := congrArg Set.range (funext hMown).symm
  let e := (readoutCircuit d M Fs [] hd hd1).castLayouts
    (congrArg (stackRegs · []) hfin).symm rfl
  have he0 : e.nonprivateCount = 0 := by
    simp only [e, OriginalCircuit.nonprivateCount_castLayouts, nonprivateCount_readoutCircuit]
  have hN : paddedSide L = 2 ^ k :=
    le_antisymm (paddedSide_le_of_le_pow hkL) (pow_le_paddedSide hk2)
  let D : DyadicProtocol L q (ProtocolParty k) :=
    { placement := protocolPlacement k
      initialSpace := fun p => framesSpace ((st 0).filter fun F => holder F = p)
      finite_initialSpace := fun p => Layout.finiteDimensional_mem_of_registers _
        (finiteDimensional_of_mem_stackRegs _)
      initialVector := fun p => framesVec Ω ((st 0).filter fun F => holder F = p)
      norm_initialVector := hx
      changes := n + 2
      layout := chainLayout (ProductInput.wholePartyLayout fun p =>
        framesSpace ((st 0).filter fun F => holder F = p)) (fun t => stackRegs (st t) []) n
        (familyPhysicalOutputLayout d (siteOrder M.owner) (readoutPrivate M Fs []))
      layout_zero := rfl
      step := chainStep c₀ c e
      reference := chainVec (ProductInput.ofAllParties _ _ hx).vector
        (fun t => framesVec Ω (st t)) (e.eval (framesVec Ω (st n)))
      reference_zero := rfl
      site := fun v => .inl (unitSquare hkL v)
      site_injective := fun v w h => unitSquare_injective hkL (Sum.inl_injective h)
      placement_site := fun v => ⟨rfl, rfl, rfl⟩
      physicalDimension := d
      physicalDimension_site := fun v => by rw [← hMown]; exact hd v
      physicalDimension_eq_one := fun p hp => hd1 p (by rwa [← hrange])
      physicalOrder := siteOrder M.owner
      physicalOrder_nodup := nodup_siteOrder hinj
      mem_physicalOrder := mem_siteOrder M.owner
      privateOutput := readoutPrivate M Fs []
      finite_privateOutput := fun r hr => by
        rcases List.mem_append.1 hr with hr | hr
        · exact finiteDimensional_of_mem_stackRegs [M] r
            (List.mem_append_left _ (List.mem_append_left _ hr))
        · exact finiteDimensional_of_mem_stackRegs Fs r hr
      layout_changes := chainLayout_succ_of_lt (Nat.lt_succ_self n)
      squareParty := protocolSquareParty hN
      repaintingSquare := fun t => if h : 0 < t ∧ t - 1 < n then
        Sum.elim (fun S => some S.toTriple) (fun _ => none) (sch[t - 1]'h.2).1 else none
      frames := fun t => st (t - 1) }
  -- the event of each change of the protocol
  let ev : ℕ → ProtocolEvent k := fun t =>
    if h : 0 < t ∧ t - 1 < n then (sch[t - 1]'h.2).1 else .inl (rootSquare k)
  have hev : ∀ t (ht : t < n), ev (t + 1) = (sch[t]'ht).1 := fun t ht => by
    simp only [ev, Nat.add_sub_cancel, Nat.succ_pos, ht, and_self, dite_true]
  -- the properties of every change
  have hQ := chainStep_induction (c₀ := c₀) (c := c) (e := e)
    (fun t a b (w : OriginalCircuit a b) => w.nonprivateCount ≤ 1 ∧
      (¬(0 < t ∧ t ≤ n) → w.nonprivateCount = 0) ∧
      (∀ g, (↑(w.participants g) : Set (ProtocolParty k)) ⊆ {p | EventUses (ev t) p}) ∧
      w.IsExpansionBounded r K ∧ w.IsMonomialBounded K ∧ w.IsSourceBounded r)
    ⟨h0.trans_le zero_le_one, fun _ => h0, participants_subset_of_nonprivateCount_eq_zero _ h0 _,
      isExpansionBounded_of_nonprivateCount_eq_zero _ _ _ h0,
      isMonomialBounded_of_nonprivateCount_eq_zero _ _ h0,
      isSourceBounded_of_nonprivateCount_eq_zero h0 _⟩
    (fun t ht => ⟨(hc t ht).nonprivateCount_le, fun h => absurd ⟨Nat.succ_pos t, ht⟩ h,
      fun g => by rw [hev t ht]; exact (hc t ht).participants_subset g,
      (hc t ht).isExpansionBounded, (hc t ht).isMonomialBounded, hsrc t ht⟩)
    ⟨he0.trans_le zero_le_one, fun _ => he0, participants_subset_of_nonprivateCount_eq_zero _ he0 _,
      isExpansionBounded_of_nonprivateCount_eq_zero _ _ _ he0,
      isMonomialBounded_of_nonprivateCount_eq_zero _ _ he0,
      isSourceBounded_of_nonprivateCount_eq_zero he0 _⟩
    (fun t _ => ⟨zero_le_one, fun _ => rfl,
      participants_subset_of_nonprivateCount_eq_zero _ rfl _,
      isExpansionBounded_of_nonprivateCount_eq_zero _ _ _ rfl,
      isMonomialBounded_of_nonprivateCount_eq_zero _ _ rfl,
      isSourceBounded_of_nonprivateCount_eq_zero rfl _⟩)
  -- an additional party is the placeholder of a non-root square, used only by its repainting
  have hadd : ∀ p, p ∉ Set.range D.squareParty → ∃ S : HierarchySquare (paddedSide L),
      2 ^ S.1.1 < paddedSide L ∧
        (D.placement.scale p, D.placement.blockX p, D.placement.blockY p) = S.1 ∧
        ∀ t < D.changes, ∀ g, p ∈ (D.step t).participants g → D.repaintingSquare t = some S.1 := by
    intro p hp
    obtain ⟨R, rfl⟩ := exists_eq_inr_of_notMem_range_protocolSquareParty hN p hp
    refine ⟨⟨R.1.toTriple, by rw [hN]; exact (protocolPlacement_inGrid k) (.inr R)⟩, ?_, rfl,
      fun t _ g hg => ?_⟩
    · change 2 ^ (R.1.1 : ℕ) < paddedSide L
      rw [hN]
      exact Nat.pow_lt_pow_right (by norm_num) R.2
    · have hu : ev t = .inl R.1 := (hQ t).2.2.1 g (mem_coe.2 hg)
      have ht : 0 < t ∧ t - 1 < n := by
        by_contra h
        have h' : ¬(0 < t ∧ t ≤ n) := fun h' => h ⟨h'.1, by omega⟩
        exact (isEmpty_nonprivateLocations_of_nonprivateCount_eq_zero _ ((hQ t).2.1 h')).false g
      simp only [ev, ht, and_self, dite_true] at hu
      change (if h : 0 < t ∧ t - 1 < n then _ else none) = _
      simp only [ht, and_self, dite_true, hu, Sum.elim_inl]
  -- a change recorded as a repainting change of `S` is a change of the repainting event of `S`
  have hrs : ∀ t S, D.repaintingSquare t = some S → ∃ h : 0 < t ∧ t - 1 < n,
      ∃ T : DyadicSquare k, (sch[t - 1]'h.2).1 = .inl T ∧ T.toTriple = S := by
    intro t S hS
    change (if h : 0 < t ∧ t - 1 < n then _ else none) = _ at hS
    split_ifs at hS with h
    refine ⟨h, ?_⟩
    rcases he : (sch[t - 1]'h.2).1 with T | J
    · rw [he] at hS
      exact ⟨T, rfl, Option.some_injective _ hS⟩
    · rw [he] at hS
      exact absurd hS (by simp)
  have hrs_mem : ∀ t S, D.repaintingSquare t = some S →
      ∃ S' : HierarchySquare (paddedSide L), S'.1 = S ∧ 2 ^ S.1 < paddedSide L := by
    intro t S hS
    obtain ⟨h, T, hT, rfl⟩ := hrs t S hS
    have hsch : (.inl T : ProtocolEvent k) ∈ eventSchedule k := by
      rw [← hT]
      obtain ⟨a, ha, hx⟩ := List.mem_flatMap.1 (List.getElem_mem (l := sch) h.2)
      obtain ⟨_, -, hx⟩ := List.mem_map.1 hx
      rw [← hx]
      exact ha
    have hTk : (T.1 : ℕ) < k := mem_eventSchedule.1 hsch
    refine ⟨⟨T.toTriple, by rw [hN]; exact (protocolPlacement_inGrid k) (.inl T)⟩, rfl, ?_⟩
    change 2 ^ (T.1 : ℕ) < paddedSide L
    rw [hN]
    exact Nat.pow_lt_pow_right (by norm_num) hTk
  have hrs_segment : ∀ S t₁ t t₂, t₁ ≤ t → t ≤ t₂ → D.repaintingSquare t₁ = some S →
      D.repaintingSquare t₂ = some S → D.repaintingSquare t = some S := by
    intro S t₁ t t₂ h₁ h₂ hS₁ hS₂
    obtain ⟨g₁, T, hT, rfl⟩ := hrs t₁ S hS₁
    obtain ⟨g₂, T', hT', hTT⟩ := hrs t₂ _ hS₂
    obtain rfl := DyadicSquare.toTriple_injective k hTT
    have ht : 0 < t ∧ t - 1 < n := ⟨by omega, by omega⟩
    have hm := protocolSchedule_fst_eq_of_le large (i := t₁ - 1) (m := t - 1) (by omega)
      (by omega) g₂.2 hT hT'
    change (if h : 0 < t ∧ t - 1 < n then _ else none) = _
    simp only [ht, and_self, dite_true]
    rw [hm]
    rfl
  have hrs_near : ∀ t < D.changes, ∀ S, D.repaintingSquare t = some S →
      ∀ g, ∀ p ∈ (D.step t).participants g,
        S.1 ≤ D.placement.scale p + 1 ∧ D.placement.scale p ≤ S.1 + 1 ∧
          Nat.dist (D.placement.anchor p).1 (dyadicAnchor S.1 S.2.1) ≤ 64 * 189 * 2 ^ S.1 ∧
          Nat.dist (D.placement.anchor p).2 (dyadicAnchor S.1 S.2.2) ≤ 64 * 189 * 2 ^ S.1 := by
    intro t _ S hS g p hp
    obtain ⟨h, T, hT, rfl⟩ := hrs t S hS
    have hu : EventUses (ev t) p := (hQ t).2.2.1 g (mem_coe.2 hp)
    simp only [ev, h, and_self, dite_true, hT] at hu
    obtain ⟨h1, h2, h3, h4⟩ := near_of_eventUses_repaint hu
    have hpow : 6 * 2 ^ (T.1 : ℕ) ≤ 64 * 189 * 2 ^ (T.1 : ℕ) :=
      Nat.mul_le_mul_right _ (by norm_num)
    exact ⟨Nat.le_succ_of_le h1, h2, h3.le.trans hpow, h4.le.trans hpow⟩
  -- the initial copies of `Ω`, each held privately by one party
  have hinit : D.frames 0 ≠ [] ∧ ∃ holder : Frame (cellCenterPos L) q (ProtocolParty k) →
      ProtocolParty k, (∀ F ∈ D.frames 0, F.holes = [] ∧ ∀ x, F.owner x = holder F) ∧
        ∀ [DecidableEq (ProtocolParty k)],
          (D.initialSpace = fun p => framesSpace ((D.frames 0).filter fun F => holder F = p)) ∧
            ∀ [NeZero q], HEq D.initialVector
              fun p => framesVec Ω ((D.frames 0).filter fun F => holder F = p) := by
    refine ⟨hne 0 (Nat.zero_le _), holder, fun F hF => ⟨hraw F hF, hown F hF⟩, fun {inst} => ?_⟩
    obtain rfl : inst = instDecidableEqSum := Subsingleton.elim _ _
    exact ⟨rfl, fun {_} => HEq.rfl⟩
  -- the intermediate reference vectors are the reference vectors of the frames
  have hframes : ∀ [NeZero q], ∀ t, 0 < t → t < D.changes →
      (∀ F ∈ D.frames t, ‖F.refVec Ω‖ ≤ 1) ∧
        ∃ h : D.layout t = stackRegs (D.frames t) [],
          D.reference t = Layout.memCongr h.symm (framesVec Ω (D.frames t)) := by
    intro _ t ht0 htn
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have hs : s ≤ n := by change s + 1 < n + 2 at htn; omega
    have hl : D.layout (s + 1) = stackRegs (st s) [] :=
      chainLayout_succ_of_le (A := ProductInput.wholePartyLayout fun p =>
        framesSpace ((st 0).filter fun F => holder F = p)) (B := fun t => stackRegs (st t) []) hs
    exact ⟨fun F _ => (F.norm_refVec_le Ω).trans hΩ.le, hl,
      chainVec_succ_of_le (x₀ := (ProductInput.ofAllParties _ _ hx).vector)
        (y := fun t => framesVec Ω (st t)) (z := e.eval (framesVec Ω (st n))) hs⟩
  -- every intermediate stage has a frame
  have hnil : ∀ t, 0 < t → t < D.changes → D.frames t ≠ [] := fun t ht0 htn =>
    hne (t - 1) (by change t < n + 2 at htn; omega)
  -- before the readout, the main frame is held by the parties of the sites
  have hmain : ∃ M' Fs', D.frames (D.changes - 1) = M' :: Fs' ∧ ∀ v, M'.owner v = D.site v :=
    ⟨M, Fs, by change st (n + 2 - 1 - 1) = _; simpa using hfin, hMown⟩
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hL0 : (0 : ℝ) < L := by linarith
  have hC0 : 0 ≤ C := by linarith
  -- the gates of the protocol belong to the changes of the schedule
  have hgate : ∀ γ : D.Gate, 0 < (γ.1 : ℕ) ∧ (γ.1 : ℕ) - 1 < n := fun γ => by
    by_contra h
    have h' : ¬(0 < (γ.1 : ℕ) ∧ (γ.1 : ℕ) ≤ n) := fun h' => h ⟨h'.1, by omega⟩
    exact (isEmpty_nonprivateLocations_of_nonprivateCount_eq_zero _ ((hQ γ.1).2.1 h')).false γ.2
  let chg : D.Gate → Fin n := fun γ => ⟨(γ.1 : ℕ) - 1, (hgate γ).2⟩
  have hchg : ∀ t, #{γ | chg γ = t} ≤ 1 := fun t => by
    refine card_le_one.2 fun γ hγ γ' hγ' => ?_
    simp only [mem_filter, mem_univ, true_and, chg, Fin.ext_iff] at hγ hγ'
    obtain ⟨⟨i, hi⟩, g⟩ := γ
    obtain ⟨⟨i', hi'⟩, g'⟩ := γ'
    have h1 := (hgate ⟨⟨i, hi⟩, g⟩).1
    have h2 := (hgate ⟨⟨i', hi'⟩, g'⟩).1
    dsimp only at hγ hγ' h1 h2
    obtain rfl : i = i' := by omega
    have hsub : Subsingleton (D.step i).nonprivateLocations :=
      Fintype.card_le_one_iff_subsingleton.1
        ((card_nonprivateLocations _).trans_le (hQ i).1)
    rw [Subsingleton.elim g g']
  refine ⟨D, ⟨?_, ?_, fun j r s => (protocolPlacement_blockBounded k j r s).trans (by norm_num),
    protocolSquareParty_injective hN, fun _ => rfl, hadd, hrs_mem, hrs_segment, hrs_near, hinit,
    ?_, fun t _ => (hQ t).1.trans (by norm_num), fun t _ g => ?_,
    fun t _ => isMonomialBounded_mono _ (hQ t).2.2.2.2.1 (Nat.le_floor (by exact_mod_cast hK)),
    fun t _ => isExpansionBounded_mono _ (hQ t).2.2.2.1 le_rfl hK, fun p => ?_,
    fun t _ g p hp p' hp' => EventUses.scale_le ((hQ t).2.2.1 g hp) ((hQ t).2.2.1 g hp'),
    fun t _ g p hp p' hp' => ?_, hframes, hnil, hmain, fun t _ => ?_, ?_,
    fun t _ => (hQ t).2.2.2.2.2⟩⟩
  · exact fun p => ⟨((protocolPlacement_inGrid k) p).1.trans (pow_le_paddedSide hk2),
      ((protocolPlacement_inGrid k) p).2.trans (pow_le_paddedSide hk2)⟩
  · have h := three_mul_card_protocolParty_lt hk2
    have h' : (3 * Fintype.card (ProtocolParty k) : ℝ) ≤ 32 * (L : ℝ) ^ 2 := by exact_mod_cast h.le
    nlinarith [sq_nonneg (L : ℝ)]
  · have h := length_protocolSchedule_le_cube hk2 large
    have hL3 : (1 : ℝ) ≤ (L : ℝ) ^ 3 := one_le_pow₀ hL1
    change ((n + 2 : ℕ) : ℝ) ≤ C * (L : ℝ) ^ 3
    push_cast
    nlinarith
  · exact (card_le_card fun p hp => by
      simpa using (hQ t).2.2.1 g (mem_coe.2 hp)).trans ((card_eventUses_le (ev t)).trans
        (by norm_num))
  · rw [DyadicProtocol.participation_eq_card]
    exact participation_le_of_schedule chg hchg p _ fun γ hγ => by
      have h := (hQ γ.1).2.2.1 γ.2 hγ
      have hg := hgate γ
      have : ev γ.1 = (sch[chg γ]).1 := by
        simp only [ev, chg, hg, and_self, dite_true, Fin.getElem_fin]
      rwa [this] at h
  · have h := EventUses.anchor_dist_le ((hQ t).2.2.1 g hp) ((hQ t).2.2.1 g hp')
    exact ⟨h.1.trans (Nat.mul_le_mul_right _ (by norm_num)),
      h.2.trans (Nat.mul_le_mul_right _ (by norm_num))⟩
  · refine (norm_chainStep_eval_sub_le (fun t => if 0 < t ∧ t ≤ n then ε else 0) ?_ ?_ ?_ ?_
      t).trans ?_
    · simp [hev0]
    · intro t ht
      simp only [Nat.succ_pos, true_and, show t + 1 ≤ n from ht, ite_true]
      exact (hc t ht).norm_eval_sub_le
    · simp
    · intro t ht
      simp [show ¬t + 1 ≤ n by omega]
    · split_ifs
      exacts [hεC, by positivity]
  · have key : e.eval (framesVec Ω (st n)) =
        (readoutCircuit d M Fs [] hd hd1).eval (stackVec Ω (M :: Fs) (1 : ℂ)) := by
      have h1 := eval_castLayouts_memCongr (readoutCircuit d M Fs [] hd hd1)
        (congrArg (stackRegs · []) hfin).symm rfl (stackVec Ω (M :: Fs) (1 : ℂ))
      rw [memCongr_stackVec Ω hfin.symm] at h1
      exact h1
    refine D.exists_reference_changes_of_readoutCircuit M Fs [] hinj hM (fun v => (hMown v).symm)
      rfl rfl hΩ (by omega) hε hholes norm_one ?_
    have hz : D.reference D.changes = _ :=
      chainVec_succ_of_lt (ProductInput.ofAllParties _ _ hx).vector
        (fun t => framesVec Ω (st t)) (e.eval (framesVec Ω (st n))) (Nat.lt_succ_self n)
    rw [hz]
    exact eq_of_heq (((Layout.memCongr_apply_heq _ _).trans (Layout.memCongr_apply_heq _ _)).trans
      ((heq_of_eq key).trans (Layout.memCongr_apply_heq _ _).symm))

end Approximation

end TNLean.PEPS
