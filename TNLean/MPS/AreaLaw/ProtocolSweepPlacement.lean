/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolSweepMiddle
import TNLean.Lattice.Compression.DistributedOperatorContraction
import TNLean.Lattice.PartyCircuit.OriginalCircuitChain
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Placement of the actual compressed middle links on the chain

The original middle is the existing chronological circuit. Its gate locality
is derived from the exact local
family and its prescribed participant sets. The compressed links below are
the existing gate-tagged star/sample links. Only the degree and the
common-original-gate conclusion returned by the existing compression theorem
are conditional inputs to the final middle specialization. The generic
full-circuit auxiliary also accepts the per-gate distance conclusion which
a preparation theorem must derive; it introduces no physical assumption.

The library completed party indexed by j is the paper's P_(j+1), and is
placed at physical block j. R_i is placed at block i. Scalar physical outputs
at inactive R_i do not remove their nodes or virtual links; R_m retains the
last physical suffix. Parallel link tags are preserved. No cut rank, MPS,
physical information estimate or complete preparation is constructed here.

Source: the one-dimensional note, Part II, con:sweep, lines 329–342,
thm:compression, lines 454–471, and the routing argument, lines 591–615.
-/

noncomputable section
open scoped BigOperators

namespace TNLean.MPS.AreaLaw.ChainSweep

open TNLean.Lattice TNLean.Lattice.PartyCircuit TNLean.Lattice.Sheet
open TNLean.Lattice.Compression

variable {L w q : ℕ}

/-- Natural block position of each actual party. The completed party indexed
by j is P_(j+1) in the source. Source: Part II, con:sweep, lines 329–342. -/
def partyLevel : Party L w → ℕ
  | .inl i => i.val
  | .inr j => j.val

private theorem partyLevel_le_stageCount (p : Party L w) :
    partyLevel p ≤ stageCount L w := by
  cases p with
  | inl i => exact Nat.le_of_lt_succ i.isLt
  | inr j => exact Nat.le_of_lt j.isLt

/-- Stage positions come from the actual role incidence, without forming a
predecessor at stage zero. Source: Part II, con:sweep, lines 333–342. -/
private theorem stageParticipants_level_bounds (k : Fin (stageCount L w)) (j : Fin 18)
    (p : Party L w) (hp : p ∈ stageParticipants k j) :
    k.val - 1 ≤ partyLevel p ∧ partyLevel p ≤ k.val + 1 := by
  cases p with
  | inl i =>
      have hi := remainder_participating_stage i k j hp
      change k.val - 1 ≤ i.val ∧ i.val ≤ k.val + 1
      omega
  | inr i =>
      have hi := completed_participating_stage i k j hp
      change k.val - 1 ≤ i.val ∧ i.val ≤ k.val + 1
      omega

/-- Any two prescribed participants of one actual stage position are at most
two block positions apart. Source: Part II, routing, lines 591–599. -/
theorem stageParticipants_level_dist_le_two (k : Fin (stageCount L w)) (j : Fin 18)
    (p t : Party L w) (hp : p ∈ stageParticipants k j) (ht : t ∈ stageParticipants k j) :
    Nat.dist (partyLevel p) (partyLevel t) ≤ 2 := by
  have hp' := stageParticipants_level_bounds k j p hp
  have ht' := stageParticipants_level_bounds k j t ht
  unfold Nat.dist
  omega

/-- Four clipped neighbouring levels, retaining both sum constructors.
Source: Part II, routing, lines 596–600. -/
private def nearbyParties (r : ℕ) : Finset (Party L w) := by
  classical
  exact Finset.univ.filter fun p ↦ r - 2 ≤ partyLevel p ∧ partyLevel p < r + 2

private theorem mem_nearbyParties (r : ℕ) (p : Party L w) :
    p ∈ nearbyParties r ↔ r - 2 ≤ partyLevel p ∧ partyLevel p < r + 2 := by
  classical
  simp only [nearbyParties, Finset.mem_filter, Finset.mem_univ, true_and]

private def partyTag : Party L w → Bool
  | .inl _ => false
  | .inr _ => true

private theorem partyLevel_tag_injective :
    Function.Injective (fun p : Party L w ↦ (partyLevel p, partyTag p)) := by
  intro p t h
  have hlevel := congrArg Prod.fst h
  have htag := congrArg Prod.snd h
  cases p with
  | inl i =>
      cases t with
      | inl j => exact congrArg Sum.inl (Fin.ext hlevel)
      | inr _ => cases htag
  | inr i =>
      cases t with
      | inl _ => cases htag
      | inr j => exact congrArg Sum.inr (Fin.ext hlevel)

/-- The nearby-party bound is derived by an injection into four levels times
two constructor tags; no physical dimension or owner injectivity is used.
Source: Part II, routing, lines 596–600. -/
private theorem nearbyParties_card_le_eight (r : ℕ) :
    (nearbyParties (L := L) (w := w) r).card ≤ 8 := by
  classical
  let f : {p : Party L w // p ∈ nearbyParties r} → Fin 4 × Bool := fun p ↦
    (⟨partyLevel p.val - (r - 2), by
      have hp := (mem_nearbyParties r p.val).mp p.property
      omega⟩, partyTag p.val)
  have hf : Function.Injective f := by
    intro p t h
    have hlevel := congrArg (fun z : Fin 4 × Bool ↦ z.1.val) h
    have htag := congrArg Prod.snd h
    have hp := (mem_nearbyParties r p.val).mp p.property
    have ht := (mem_nearbyParties r t.val).mp t.property
    apply Subtype.ext
    apply partyLevel_tag_injective
    apply Prod.ext
    · change partyLevel p.val = partyLevel t.val
      change partyLevel p.val - (r - 2) = partyLevel t.val - (r - 2) at hlevel
      omega
    · exact htag
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool] using Fintype.card_le_of_injective f hf

/-- A finite participant set contained in one actual stage position has at
most eight parties. This deliberately coarse bound suffices for the common
compression constant 40 and is derived from labelled placement.
Source: Part II, con:sweep and routing, lines 333–342 and 591–600. -/
theorem card_le_eight_of_subset_stageParticipants (s : Finset (Party L w))
    (k : Fin (stageCount L w)) (j : Fin 18)
    (hsub : (↑s : Set (Party L w)) ⊆ stageParticipants k j) : s.card ≤ 8 := by
  classical
  have hnear : s ⊆ nearbyParties (k.val + 1) := by
    intro p hp
    have hb := stageParticipants_level_bounds k j p (hsub hp)
    apply (mem_nearbyParties (k.val + 1) p).mpr
    omega
  exact (Finset.card_le_card hnear).trans (nearbyParties_card_le_eight (k.val + 1))

section Links

variable {Gate : Type} [DecidableEq Gate]
variable (gates : Finset Gate) (participants : Gate → Finset (Party L w))
  (root : Gate → Party L w)

/-- Existing tagged links crossing the prefix of block positions below r.
The definition keeps the literal Link subtype, including parallel tags.
Source: Part II, routing, lines 596–603. -/
def prefixCrossingLinks (r : ℕ) :
    Finset (DistributedOperatorContraction.Link gates participants root) := by
  classical
  exact Finset.univ.filter fun e ↦
    (partyLevel (DistributedOperatorContraction.src gates participants root e) < r ∧
      r ≤ partyLevel (DistributedOperatorContraction.tgt gates participants root e)) ∨
    (partyLevel (DistributedOperatorContraction.tgt gates participants root e) < r ∧
      r ≤ partyLevel (DistributedOperatorContraction.src gates participants root e))

private theorem mem_prefixCrossingLinks (r : ℕ)
    (e : DistributedOperatorContraction.Link gates participants root) :
    e ∈ prefixCrossingLinks gates participants root r ↔
      (partyLevel (DistributedOperatorContraction.src gates participants root e) < r ∧
        r ≤ partyLevel (DistributedOperatorContraction.tgt gates participants root e)) ∨
      (partyLevel (DistributedOperatorContraction.tgt gates participants root e) < r ∧
        r ≤ partyLevel (DistributedOperatorContraction.src gates participants root e)) := by
  classical
  simp only [prefixCrossingLinks, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The left endpoint prefix has no crossing links. A loop never satisfies the
strict crossing inequalities either. Source: Part II, routing, lines 596–603. -/
theorem prefixCrossingLinks_zero : prefixCrossingLinks gates participants root 0 = ∅ := by
  classical
  ext e
  simp only [mem_prefixCrossingLinks, Finset.notMem_empty, iff_false]
  omega

/-- Prefixes beyond every actual party level have no crossings, without an
assumption that any physical fibre is nonempty. Source: Part II, routing. -/
theorem prefixCrossingLinks_eq_empty_of_stageCount_lt (r : ℕ)
    (hr : stageCount L w < r) : prefixCrossingLinks gates participants root r = ∅ := by
  classical
  ext e
  have hs := partyLevel_le_stageCount
    (DistributedOperatorContraction.src gates participants root e)
  have ht := partyLevel_le_stageCount
    (DistributedOperatorContraction.tgt gates participants root e)
  simp only [mem_prefixCrossingLinks, Finset.notMem_empty, iff_false]
  omega

private theorem crossing_levels_bounds (a b r : ℕ)
    (hcross : (a < r ∧ r ≤ b) ∨ (b < r ∧ r ≤ a)) (hdist : Nat.dist a b ≤ 2) :
    (r - 2 ≤ a ∧ a < r + 2) ∧ (r - 2 ≤ b ∧ b < r + 2) := by
  unfold Nat.dist at hdist
  omega

/-- This auxiliary count uses geometric endpoint distance. The final middle
specialization below derives that distance from actual local circuits.
Source: Part II, routing, lines 596–603. -/
private theorem prefixCrossingLinks_card_le_of_dist
    (hdist : ∀ e : DistributedOperatorContraction.Link gates participants root,
      Nat.dist (partyLevel (DistributedOperatorContraction.src gates participants root e))
        (partyLevel (DistributedOperatorContraction.tgt gates participants root e)) ≤ 2)
    (degree : ℕ)
    (hdegree : ∀ p : Party L w, (incidentDistributedLinks gates participants root p).card ≤ degree)
    (r : ℕ) : (prefixCrossingLinks gates participants root r).card ≤ 8 * degree := by
  classical
  let crossing := prefixCrossingLinks gates participants root r
  let near := nearbyParties (L := L) (w := w) r
  have hsub : crossing.image Subtype.val ⊆
      near.biUnion (incidentDistributedLinks gates participants root) := by
    intro link hlink
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hlink
    have he' := (mem_prefixCrossingLinks gates participants root r e).mp he
    have hnear := crossing_levels_bounds _ _ r he' (hdist e)
    have hsnear : DistributedOperatorContraction.src gates participants root e ∈ near :=
      (mem_nearbyParties r _).mpr hnear.1
    apply Finset.mem_biUnion.mpr
    refine ⟨DistributedOperatorContraction.src gates participants root e, hsnear, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨e.property, ?_⟩
    rw [← DistributedOperatorContraction.endpoints_eq gates participants root e]
    exact Finset.mem_insert_self _ _
  calc
    crossing.card = (crossing.image Subtype.val).card :=
      (Finset.card_image_of_injective crossing Subtype.val_injective).symm
    _ ≤ (near.biUnion (incidentDistributedLinks gates participants root)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ p ∈ near, (incidentDistributedLinks gates participants root p).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ near, degree := Finset.sum_le_sum fun p _ ↦ hdegree p
    _ = near.card * degree := by simp
    _ ≤ 8 * degree := Nat.mul_le_mul_right degree (nearbyParties_card_le_eight r)

end Links

section OriginalGraph

variable {Gate : Type} [DecidableEq Gate]
variable (gates : Finset Gate) (participants : Gate → Finset (Party L w))
  (root : Gate → Party L w)

/-- An auxiliary consequence of the existing compression outputs for an
arbitrary actual original circuit. The per-gate distance premise is to be
DERIVED by its preparation theorem, not added as a physical assumption.
In particular the middle specialization below derives it from c and hc.
Source: Part II, thm:compression and routing, lines 454–471 and 591–603. -/
theorem prefixCrossingLinks_card_le_of_originalCircuit
    {a b : Layout (Party L w)} (d : OriginalCircuit a b)
    (hgate : ∀ (g : d.nonprivateLocations) (p t : Party L w),
      p ∈ d.participants g → t ∈ d.participants g →
        Nat.dist (partyLevel p) (partyLevel t) ≤ 2)
    (degree : ℕ)
    (hdegree : ∀ p : Party L w,
      (incidentDistributedLinks gates participants root p).card ≤ degree)
    (hcommon : ∀ e : DistributedOperatorContraction.Link gates participants root,
      ∀ p t, p ∈ distributedLinkParties root e.1 →
        t ∈ distributedLinkParties root e.1 →
        ∃ g : d.nonprivateLocations, p ∈ d.participants g ∧ t ∈ d.participants g)
    (r : ℕ) : (prefixCrossingLinks gates participants root r).card ≤ 8 * degree := by
  apply prefixCrossingLinks_card_le_of_dist gates participants root ?_ degree hdegree r
  intro e
  have hs : DistributedOperatorContraction.src gates participants root e ∈
      distributedLinkParties root e.1 := by
    rw [← DistributedOperatorContraction.endpoints_eq gates participants root e]
    exact Finset.mem_insert_self _ _
  have ht : DistributedOperatorContraction.tgt gates participants root e ∈
      distributedLinkParties root e.1 := by
    rw [← DistributedOperatorContraction.endpoints_eq gates participants root e]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  obtain ⟨g, hsg, htg⟩ := hcommon e _ _ hs ht
  exact hgate g _ _ hsg htg

end OriginalGraph

/-- The existing equality-transport induction, specialized to a property of
actual participant sets. Source: Part II, routing, lines 591–603. -/
private theorem forall_participants_castLayouts {P : Type}
    (Q : Finset P → Prop) {a b a' b' : Layout P} (d : OriginalCircuit a b)
    (ha : a = a') (hb : b = b') (h : ∀ g, Q (d.participants g)) :
    ∀ g, Q ((d.castLayouts ha hb).participants g) :=
  OriginalCircuit.castLayouts_induction (fun _ _ d ↦ ∀ g, Q (d.participants g)) ha hb h

section Middle

variable (c : (k : Fin (stageCount L w)) → (j : Fin 18) → OriginalCircuit
  (stackRegs (Sheet.regs q) (stageBoundaryFrames L w k j.val) [])
  (stackRegs (Sheet.regs q) (stageBoundaryFrames L w k (j.val + 1)) []))
variable (Ω : EuclideanSpace ℂ (Fin L → Fin q))

/- The literal existing local-family conclusion, curried over stages. Its
geometric participant conclusion is used below; no aggregate locality or
congestion hypothesis is added. -/
variable (hc : ∀ k j, (c k j).IsBoundedChange (stageParticipants k j) 1 1
    (4 * (L : ℝ) ^ (-12 : ℤ))
    (framesVec (Sheet.refFamily Ω) (stageBoundaryFrames L w k j.val))
    (framesVec (Sheet.refFamily Ω) (stageBoundaryFrames L w k (j.val + 1))) ∧
  (c k j).IsSourceBounded 1 ∧ (c k j).nonprivateCount ≤ 1 ∧
  ((k.val = 0 ∧ 3 ≤ j.val ∧ j.val < 10) → (c k j).nonprivateCount = 0 ∧
    ‖(c k j).eval (framesVec (Sheet.refFamily Ω) (stageBoundaryFrames L w k j.val)) -
      framesVec (Sheet.refFamily Ω) (stageBoundaryFrames L w k (j.val + 1))‖ = 0 ∧
    HEq (c k j) (OriginalCircuit.id (stackRegs (Sheet.regs q)
      (stageBoundaryFrames L w k j.val) []))))

include hc

private theorem localCircuit_participants_subset_stage
    (k : Fin (stageCount L w)) (j : Fin 18) :
    ∀ g : (c k j).nonprivateLocations,
      ∃ k' : Fin (stageCount L w), ∃ j' : Fin 18,
        (↑((c k j).participants g) : Set (Party L w)) ⊆ stageParticipants k' j' := by
  intro g
  exact ⟨k, j, (hc k j).1.participants_subset g⟩

/-- Every actual step's gate retains its original stage/slot support through
Path's proved layout equalities. The identity tail has no gate witness.
Source: Part II, con:sweep and routing, lines 333–342 and 591–599. -/
private theorem middleStep_participants_subset_stage (n : ℕ) :
    ∀ g : (sweepMiddleStep c n).nonprivateLocations,
      ∃ k : Fin (stageCount L w), ∃ j : Fin 18,
        (↑((sweepMiddleStep c n).participants g) : Set (Party L w)) ⊆
          stageParticipants k j := by
  classical
  let Q : Finset (Party L w) → Prop := fun s ↦
    ∃ k : Fin (stageCount L w), ∃ j : Fin 18,
      (↑s : Set (Party L w)) ⊆ stageParticipants k j
  let W {a b : Layout (Party L w)} (d : OriginalCircuit a b) : Prop :=
    ∀ g, Q (d.participants g)
  change W (sweepMiddleStep c n)
  unfold sweepMiddleStep
  split
  · exact forall_participants_castLayouts Q _ _ _
      (localCircuit_participants_subset_stage c Ω hc _ _)
  · exact forall_participants_castLayouts Q _ _ _ (fun g ↦ Empty.elim g)

/-- Each actual middle gate has a derived stage and slot whose prescribed
participants contain its entire participant set. The witness is a conclusion,
not supplied circuit data. This remains vacuous when there are no stages.
Source: Part II, con:sweep and routing, lines 333–342 and 591–599. -/
theorem sweepMiddleCircuit_participants_subset_stage
    (g : (sweepMiddleCircuit c).nonprivateLocations) :
    ∃ k : Fin (stageCount L w), ∃ j : Fin 18,
      (↑((sweepMiddleCircuit c).participants g) : Set (Party L w)) ⊆
        stageParticipants k j := by
  let Q : Finset (Party L w) → Prop := fun s ↦
    ∃ k : Fin (stageCount L w), ∃ j : Fin 18,
      (↑s : Set (Party L w)) ⊆ stageParticipants k j
  have h : ∀ g, Q ((sweepMiddleCircuit c).participants g) := by
    unfold sweepMiddleCircuit
    exact forall_participants_castLayouts Q _ _ _
      (OriginalCircuit.forall_participants_sequence _ _ Q _
        (fun n _ ↦ middleStep_participants_subset_stage c Ω hc n))
  exact h g

/-- Every pair of participants of one actual middle gate is at distance at
most two in block position. This is derived from the given local circuits
and the existing chronological sequence, not supplied as a circuit certificate.
Source: Part II, routing, lines 591–599. -/
theorem sweepMiddleCircuit_participants_level_dist_le_two
    (g : (sweepMiddleCircuit c).nonprivateLocations) (p t : Party L w)
    (hp : p ∈ (sweepMiddleCircuit c).participants g)
    (ht : t ∈ (sweepMiddleCircuit c).participants g) :
    Nat.dist (partyLevel p) (partyLevel t) ≤ 2 := by
  obtain ⟨k, j, hsub⟩ := sweepMiddleCircuit_participants_subset_stage c Ω hc g
  exact stageParticipants_level_dist_le_two k j p t (hsub hp) (hsub ht)

/-- The actual middle-gate arity bound is derived from the same stage/slot
support conclusion as the distance bound. Source: Part II, thm:compression
and routing, lines 454–471 and 591–600. -/
theorem sweepMiddleCircuit_participants_card_le_forty
    (g : (sweepMiddleCircuit c).nonprivateLocations) :
    ((sweepMiddleCircuit c).participants g).card ≤ 40 := by
  obtain ⟨k, j, hsub⟩ := sweepMiddleCircuit_participants_subset_stage c Ω hc g
  exact (card_le_eight_of_subset_stageParticipants _ k j hsub).trans (by norm_num)

variable {Gate : Type} [DecidableEq Gate]
variable (gates : Finset Gate) (participants : Gate → Finset (Party L w))
  (root : Gate → Party L w)

/-- The two conditional graph premises are exactly the degree and
common-original-gate conclusions of the existing distributed compression
theorem. The original middle-gate locality is derived internally from the
local family. No crossing bound or endpoint-distance certificate is supplied.
Source: Part II, thm:compression and routing, lines 454–471 and 591–603. -/
theorem compressedMiddle_prefixCrossingLinks_card_le (degree : ℕ)
    (hdegree : ∀ p : Party L w,
      (incidentDistributedLinks gates participants root p).card ≤ degree)
    (hcommon : ∀ e : DistributedOperatorContraction.Link gates participants root,
      ∀ p t, p ∈ distributedLinkParties root e.1 →
        t ∈ distributedLinkParties root e.1 →
        ∃ g : (sweepMiddleCircuit c).nonprivateLocations,
          p ∈ (sweepMiddleCircuit c).participants g ∧
          t ∈ (sweepMiddleCircuit c).participants g)
    (r : ℕ) : (prefixCrossingLinks gates participants root r).card ≤ 8 * degree := by
  exact prefixCrossingLinks_card_le_of_originalCircuit gates participants root
    (sweepMiddleCircuit c)
    (fun g p t hp ht ↦ sweepMiddleCircuit_participants_level_dist_le_two c Ω hc g p t hp ht)
    degree hdegree hcommon r

/-- The general compression degree at b=40 is 3120, giving this coarser
constant congestion. The source theorem asserts polynomial existence and
fixes no numerical exponent; its proof's sharper congestion 1600 is not
claimed here. Source: Part II, Theorem B and routing, lines 591–615. -/
theorem compressedMiddle_prefixCrossingLinks_card_le_24960
    (hdegree : ∀ p : Party L w,
      (incidentDistributedLinks gates participants root p).card ≤ 3120)
    (hcommon : ∀ e : DistributedOperatorContraction.Link gates participants root,
      ∀ p t, p ∈ distributedLinkParties root e.1 →
        t ∈ distributedLinkParties root e.1 →
        ∃ g : (sweepMiddleCircuit c).nonprivateLocations,
          p ∈ (sweepMiddleCircuit c).participants g ∧
          t ∈ (sweepMiddleCircuit c).participants g)
    (r : ℕ) : (prefixCrossingLinks gates participants root r).card ≤ 24960 := by
  simpa only [show 8 * 3120 = 24960 from by norm_num] using
    compressedMiddle_prefixCrossingLinks_card_le c Ω hc gates participants root
      3120 hdegree hcommon r

end Middle

end TNLean.MPS.AreaLaw.ChainSweep
