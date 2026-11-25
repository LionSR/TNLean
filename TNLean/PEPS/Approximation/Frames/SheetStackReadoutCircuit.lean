/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Original.Density
import QICLean.Circuit.Party.Original.Sequence
import TNLean.PEPS.Approximation.Frames.SheetStack

/-!
# The circuit of the final regrouping of the sheets

At the end of the protocol of Proposition 7.1 of the polynomial-PEPS manuscript the main sheet is
at the unit level: its holes have empty physical outer samples, so their encodings are trivial,
and every raw register of the main sheet is held by the unit-square party of its site
(`06-geometry.tex`, lines 669–681). This file builds the original circuit that turns the final
memory of a stack of sheets into the output system of a protocol: at every party one physical
register, and private registers to be discarded (`EncodedFrame.readoutCircuit`). It is a
relabelling of the bases of the parties and has no nonprivate gate.

* The raw configuration of the site of a party on the main sheet is its physical register; it
  keeps the dimension `q`. A party without a site has a physical register of dimension one
  (`EncodedFrame.physEquiv`).
* The private registers of a party are its tags on the main sheet and its registers on the
  other sheets and on the idle system (`EncodedFrame.readoutPrivate`).

The value of the circuit on a vector is `EncodedFrame.op_readoutCircuit_mulVec`.

## Main definitions

* `EncodedFrame.trivialTag`: the identity tag of holes with empty outer samples.
* `EncodedFrame.physEquiv`, `EncodedFrame.readoutPrivate`, `EncodedFrame.readoutCircuit`.

## Main results

* `EncodedFrame.Frame.regRef_of_outer_eq_empty`: a frame with trivial holes has reference
  vector `Ω` on its raw configurations.
* `EncodedFrame.nonprivateCount_readoutCircuit`, `EncodedFrame.op_readoutCircuit_mulVec`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 7.1 `prop:protocol`, item 4,
  `06-geometry.tex`, lines 48–51 (the physical outputs) and 669–681 (the main reference at level
  one); the empty-outer convention, `05-frames.tex`, lines 67–69; private maps,
  `04-compression.tex`, lines 21–36 and 137–151.
-/

noncomputable section

namespace TNLean.PEPS.EncodedFrame

open ManyBody QuantumCircuit.Party Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {Party : Type} {pos : ι → ℝ × ℝ}

/-! ### Trivial holes -/

/-- The identity tag of a list of holes whose outer samples are empty. -/
def trivialTag : (l : List (Hole pos q Party)) → (∀ h ∈ l, h.patch.outer = ∅) → TagSpace l
  | [], _ => ()
  | h :: l, hl => (Sum.inl ⟨(), hl h List.mem_cons_self⟩,
      trivialTag l fun h' hh' => hl h' (List.mem_cons_of_mem _ hh'))

/-- Holes with empty outer samples have only the identity tag. -/
theorem eq_trivialTag : (l : List (Hole pos q Party)) → (hl : ∀ h ∈ l, h.patch.outer = ∅) →
    (τ : TagSpace l) → τ = trivialTag l hl
  | [], _, () => rfl
  | h :: l, hl, (s, τ) => by
      rcases s with ⟨⟨⟩, hs⟩ | ⟨s, hs⟩
      · exact Prod.ext rfl (eq_trivialTag l _ τ)
      · rw [hl h List.mem_cons_self] at hs
        exact absurd hs Finset.not_nonempty_empty

/-- The raw part of the encoding of holes with empty outer samples is the identity. -/
theorem rawProd_trivialTag [NeZero q] : (l : List (Hole pos q Party)) →
    (hl : ∀ h ∈ l, h.patch.outer = ∅) → rawProd l (trivialTag l hl) = 1
  | [], _ => rfl
  | h :: l, hl => by
      change SquarePatch.branch _ _ * rawProd l (trivialTag l _) = 1
      rw [rawProd_trivialTag l]
      exact one_mul _

/-- **Trivial holes.** If every hole of a frame has empty physical outer sample, then the
reference vector of the frame, read on its registers, is `Ω` on the raw configurations.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 669–673, and the empty-outer convention,
`05-frames.tex`, lines 67–69. -/
theorem Frame.regRef_of_outer_eq_empty [Fintype Party] [DecidableEq Party] [NeZero q]
    (F : Frame pos q Party) (hF : ∀ h ∈ F.holes, h.patch.outer = ∅)
    (Ω : EuclideanSpace ℂ (ι → Fin q)) (z : Config F.system) :
    F.regRef Ω z = Ω (F.configEquiv z).2 := by
  rw [Frame.regRef_apply]
  obtain ⟨τ, c⟩ := F.configEquiv z
  obtain rfl := eq_trivialTag F.holes hF τ
  change (Matrix.mulVec (stack (rawProd F.holes)) Ω.ofLp) (trivialTag F.holes hF, c) = Ω c
  have hrow : (Matrix.mulVec (stack (rawProd F.holes)) Ω.ofLp) (trivialTag F.holes hF, c) =
      (Matrix.mulVec (rawProd F.holes (trivialTag F.holes hF)) Ω.ofLp) c := rfl
  rw [hrow, rawProd_trivialTag, Matrix.one_mulVec]

/-! ### The final regrouping -/

section Readout

variable [DecidableEq Party] (d : Party → ℕ)

/-- **The physical register of a party.** If the owners of the main sheet `M` are injective, a
party owning a site `x` holds the raw configuration of `x` on `M`, of dimension `q = d (M x)`, and
a party owning no site holds a one-point basis, of dimension `d p = 1`. -/
def physEquiv (M : Frame pos q Party) (hinj : Function.Injective M.owner)
    (hd : ∀ x, d (M.owner x) = q) (hd1 : ∀ p ∉ Set.range M.owner, d p = 1) (p : Party) :
    M.sheet.system q p ≃ Fin (d p) :=
  if h : p ∈ Set.range M.owner then
    haveI : Unique {v // v ∈ blockPreimage M.owner {p}} :=
      { default := ⟨h.choose, (mem_blockPreimage_singleton _).mpr h.choose_spec⟩
        uniq := fun v ↦ Subtype.ext (hinj (((mem_blockPreimage_singleton _).mp v.2).trans
          h.choose_spec.symm)) }
    (Equiv.funUnique _ (Fin q)).trans (finCongr (by rw [← h.choose_spec, hd]))
  else
    haveI : IsEmpty {v // v ∈ blockPreimage M.owner {p}} :=
      ⟨fun v ↦ h ⟨v, (mem_blockPreimage_singleton _).mp v.2⟩⟩
    (Equiv.ofUnique _ (Fin 1)).trans (finCongr (hd1 p h).symm)

/-- The physical register of the party of a site is the raw configuration of the site. -/
theorem physEquiv_apply_of_owner (M : Frame pos q Party) (hinj : Function.Injective M.owner)
    (hd : ∀ x, d (M.owner x) = q) (hd1 : ∀ p ∉ Set.range M.owner, d p = 1) (x : ι)
    (c : M.sheet.system q (M.owner x)) :
    (physEquiv d M hinj hd hd1 (M.owner x) c : ℕ) =
      c ⟨x, (mem_blockPreimage_singleton _).mpr rfl⟩ := by
  have h : M.owner x ∈ Set.range M.owner := ⟨x, rfl⟩
  have hx : h.choose = x := hinj h.choose_spec
  simp only [physEquiv, h, ↓reduceDIte, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
    Equiv.funUnique_apply]
  congr 2
  exact Subtype.ext hx

/-- The private registers of the final system at a party: its tags on the main sheet, then its
registers on the other sheets and on the idle system. -/
abbrev readoutPrivate (M : Frame pos q Party) (Fs : List (Frame pos q Party))
    (W : Party → Type) : Party → Type :=
  fun p ↦ tagSystem M.holes p × framesSystem q pos Fs W p

/-- The relabelling of the final regrouping at one party. -/
def readoutEquiv (M : Frame pos q Party) (Fs : List (Frame pos q Party)) (W : Party → Type)
    (hinj : Function.Injective M.owner) (hd : ∀ x, d (M.owner x) = q)
    (hd1 : ∀ p ∉ Set.range M.owner, d p = 1) (p : Party) :
    physicalSystem d (readoutPrivate M Fs W) p ≃ framesSystem q pos (M :: Fs) W p where
  toFun z := ((z.2.1, (physEquiv d M hinj hd hd1 p).symm z.1), z.2.2)
  invFun z := (physEquiv d M hinj hd hd1 p z.1.2, (z.1.1, z.2))
  left_inv z := by simp
  right_inv z := by simp

/-- **The final regrouping.** On the stack with main sheet `M` with injective owners, the raw
configuration of the site of every party on `M` becomes its physical register, every party
without a site receives a physical register of dimension one, and the tags of `M` and the other
sheets become private registers: one relabelling of the bases of the parties.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 48–51 and 669–681. -/
def readoutCircuit (M : Frame pos q Party) (Fs : List (Frame pos q Party)) (W : Party → Type)
    [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)] (hinj : Function.Injective M.owner)
    (hd : ∀ x, d (M.owner x) = q)
    (hd1 : ∀ p ∉ Set.range M.owner, d p = 1) :
    OriginalCircuit (framesSystem q pos (M :: Fs) W) (physicalSystem d (readoutPrivate M Fs W)) :=
  OriginalCircuit.relabel (readoutEquiv d M Fs W hinj hd hd1)

variable {W : Party → Type} [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)]

/-- The final regrouping has no nonprivate gate. -/
theorem nonprivateCount_readoutCircuit (M : Frame pos q Party) (Fs : List (Frame pos q Party))
    (hinj : Function.Injective M.owner) (hd : ∀ x, d (M.owner x) = q)
    (hd1 : ∀ p ∉ Set.range M.owner, d p = 1) :
    (readoutCircuit d M Fs W hinj hd hd1).nonprivateCount = 0 :=
  OriginalCircuit.nonprivateCount_relabel _

/-- **The final regrouping on a vector.** The relabelling reads a vector of the stack at the
configuration regrouped back into the stack. -/
theorem op_readoutCircuit_mulVec [Fintype Party] (M : Frame pos q Party)
    (Fs : List (Frame pos q Party)) (hinj : Function.Injective M.owner)
    (hd : ∀ x, d (M.owner x) = q) (hd1 : ∀ p ∉ Set.range M.owner, d p = 1)
    (v : Config (framesSystem q pos (M :: Fs) W) → ℂ)
    (z : Config (physicalSystem d (readoutPrivate M Fs W))) :
    ((readoutCircuit d M Fs W hinj hd hd1).op *ᵥ v) z =
      v (Equiv.piCongrRight (readoutEquiv d M Fs W hinj hd hd1) z) := by
  rw [readoutCircuit, OriginalCircuit.op_relabel]
  simp [Matrix.mulVec, dotProduct, PEquiv.toMatrix_apply]

end Readout

end TNLean.PEPS.EncodedFrame
