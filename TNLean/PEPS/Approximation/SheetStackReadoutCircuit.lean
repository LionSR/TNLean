/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.FamilyPhysicalReadout
import TNLean.Lattice.Sheet.StackChange
import TNLean.PEPS.Approximation.SheetStackEndpoints

/-!
# The circuit of the final regrouping of the sheets

At the end of the protocol of Proposition 7.1 of the polynomial-PEPS manuscript the main sheet is
at the unit level: its holes have empty physical outer samples, so their encodings are trivial,
and every raw register of the main sheet is held by the unit-square party of its site
(`06-geometry.tex`, lines 669–681). This file builds the original circuit that turns the final
memory of a sheet stack into the output layout of a protocol: one physical register for every
party, followed by the private registers to be discarded (`EncodedFrame.readoutCircuit`). It has
no nonprivate gate.

* The raw registers of the main sheet are moved in front of its tag registers by exchanges of
  tensor factors.
* The raw register of each site is renamed, by a private map at its party, as the physical
  register of that party; it keeps the dimension `q` (`EncodedFrame.siteCircuit`).
* Every party without a site receives a fresh physical register of dimension one, prepared by a
  private map at that party (`EncodedFrame.freshCircuit`).

The physical registers are listed in the order of the sites followed by the parties without a
site (`EncodedFrame.siteOrder`). The private registers are the tags of the main sheet followed
by the registers of the other sheets and of the idle copies (`EncodedFrame.readoutPrivate`).
The value of the circuit on the reference vector is computed in
`TNLean.PEPS.Approximation.SheetStackReadout`.

## Main definitions

* `EncodedFrame.trivialTag`: the identity tag of holes with empty outer samples.
* `EncodedFrame.physVec`: the physical basis vector of a configuration.
* `EncodedFrame.freshCircuit`, `EncodedFrame.siteCircuit`, `EncodedFrame.readoutCircuit`.
* `EncodedFrame.siteOrder`: the order of the physical registers.

## Main results

* `EncodedFrame.Frame.regRef_of_outer_eq_empty`: a frame with trivial holes has reference
  vector `Ω` on its raw registers.
* `EncodedFrame.eval_siteCircuit`, `EncodedFrame.nonprivateCount_readoutCircuit`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 7.1 `prop:protocol`, item 4,
  `06-geometry.tex`, lines 48–51 (the physical outputs) and 669–681 (the main reference at level
  one); the empty-outer convention, `05-frames.tex`, lines 67–69; private maps,
  `04-compression.tex`, lines 21–36 and 137–151.
-/

noncomputable section

open scoped TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.EncodedFrame

open PairEffect

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
reference vector of the frame is `Ω` on its raw registers, with the identity tags:
`Ω_F = ∑_c Ω(c) |τ₀⟩ ⊗ |c⟩`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 669–673, and the empty-outer convention,
`05-frames.tex`, lines 67–69. -/
theorem Frame.regRef_of_outer_eq_empty [NeZero q] (F : Frame pos q Party)
    (hF : ∀ h ∈ F.holes, h.patch.outer = ∅) (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    F.regRef Ω = ∑ c, Ω c • layoutVec F.holes F.owner (trivialTag F.holes hF) c := by
  rw [Frame.regRef, LinearIsometryEquiv.symm_apply_eq, map_sum]
  simp only [map_smul, Frame.regIso, layoutIso_layoutVec]
  ext ⟨τ, c⟩
  obtain rfl := eq_trivialTag F.holes hF τ
  change (Matrix.mulVec (stack (rawProd F.holes)) Ω.ofLp) (trivialTag F.holes hF, c) = _
  have hrow : (Matrix.mulVec (stack (rawProd F.holes)) Ω.ofLp) (trivialTag F.holes hF, c) =
      (Matrix.mulVec (rawProd F.holes (trivialTag F.holes hF)) Ω.ofLp) c := rfl
  rw [hrow, rawProd_trivialTag, Matrix.one_mulVec, WithLp.ofLp_sum]
  simp only [WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, PiLp.ofLp_single,
    Pi.single_apply, Prod.mk.injEq, true_and, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-! ### Physical registers -/

/-- The physical basis vector `⊗_{p ∈ ps} |σ p⟩` of a configuration `σ`. -/
def physVec (d : Party → ℕ) : (ps : List Party) → ((p : Party) → Fin (d p)) →
    Mem (familyPhysicalLayout d ps)
  | [], _ => (1 : ℂ)
  | p :: ps, σ => (EuclideanSpace.single (σ p) (1 : ℂ) : EuclideanSpace ℂ (Fin (d p))) ⊗ₜ
      physVec d ps σ

theorem familyPhysicalListBasis_eq_physVec (d : Party → ℕ) :
    (ps : List Party) → (σ : (p : Party) → Fin (d p)) →
      familyPhysicalListBasis d ps (fun i => σ (ps.get i)) = physVec d ps σ
  | [], σ => familyPhysicalListBasis_nil_apply d _
  | p :: ps, σ => by
      rw [familyPhysicalListBasis]
      erw [OrthonormalBasis.reindex_apply, OrthonormalBasis.tensorProduct_apply']
      simp only [EuclideanSpace.basisFun_apply]
      exact congrArg (fun y => (EuclideanSpace.single (σ p) (1 : ℂ) :
        EuclideanSpace ℂ (Fin (d p))) ⊗ₜ y) (familyPhysicalListBasis_eq_physVec d ps σ)

/-- The physical basis labelled by parties sends a configuration to its physical basis
vector. -/
theorem familyLabelledPhysicalBasis_eq_physVec [Fintype Party] [DecidableEq Party]
    (d : Party → ℕ) (ps : List Party) (hps : ps.Nodup) (hcover : ∀ p, p ∈ ps)
    (σ : (p : Party) → Fin (d p)) :
    familyLabelledPhysicalBasis d ps hps hcover σ = physVec d ps σ := by
  rw [familyLabelledPhysicalBasis]
  erw [OrthonormalBasis.reindex_apply]
  rw [← familyPhysicalListBasis_eq_physVec]
  congr 1

/-- The private map at `p` preparing a fresh register `X` in the vector `v`. -/
def freshMap (p : Party) {X : HSpace} (v : X) :
    Mem ([] : Layout Party) →L[ℂ] Mem [(⟨p, X⟩ : Reg Party)] :=
  ContinuousLinearMap.toSpanSingleton ℂ (v ⊗ₜ (1 : ℂ) : Mem [(⟨p, X⟩ : Reg Party)])

theorem freshMap_apply (p : Party) {X : HSpace} (v : X) (a : ℂ) :
    freshMap p v a = a • (v ⊗ₜ (1 : ℂ) : Mem [(⟨p, X⟩ : Reg Party)]) :=
  rfl

theorem norm_freshMap_le (p : Party) {X : HSpace} {v : X} (hv : ‖v‖ ≤ 1) :
    ‖freshMap p v‖ ≤ 1 := by
  rw [freshMap, ContinuousLinearMap.norm_toSpanSingleton, TensorProduct.norm_tmul]
  simpa using hv

/-- The private map at `p` renaming the register `X` as the register `Y` along `e`. -/
def renameMap (p : Party) {X Y : HSpace} (e : X ≃ₗᵢ[ℂ] Y) :
    Mem [(⟨p, X⟩ : Reg Party)] →L[ℂ] Mem [(⟨p, Y⟩ : Reg Party)] :=
  isoL (e.rTensor (Mem ([] : Layout Party)))

theorem renameMap_tmul (p : Party) {X Y : HSpace} (e : X ≃ₗᵢ[ℂ] Y) (x : X) (a : ℂ) :
    renameMap p e (x ⊗ₜ a : Mem [(⟨p, X⟩ : Reg Party)]) = (e x ⊗ₜ a : Mem [(⟨p, Y⟩ : Reg Party)]) :=
  LinearIsometryEquiv.rTensor_tmul _ _ _

theorem norm_renameMap_le (p : Party) {X Y : HSpace} (e : X ≃ₗᵢ[ℂ] Y) :
    ‖renameMap p e‖ ≤ 1 :=
  LinearIsometry.norm_toContinuousLinearMap_le _

variable (d : Party → ℕ)

/-- The element of a one-point coordinate set. -/
def finOneOf {p : Party} (h : d p = 1) : Fin (d p) := ⟨0, by rw [h]; exact Nat.one_pos⟩

/-- **Fresh physical registers.** Each party of `rs`, of physical dimension one, prepares its
physical register privately, in front of the registers `Z`. -/
def freshCircuit (Z : Layout Party) : (rs : List Party) → (∀ p ∈ rs, d p = 1) →
    OriginalCircuit Z (familyPhysicalLayout d rs ++ Z)
  | [], _ => .id Z
  | p :: rs, h =>
      .comp (freshCircuit Z rs fun p' hp' => h p' (List.mem_cons_of_mem _ hp'))
        (.privateMap p (a := []) (b := [⟨p, euc (Fin (d p))⟩]) (by simp) (by simp)
          (freshMap p (EuclideanSpace.single (finOneOf d (h p List.mem_cons_self)) (1 : ℂ)))
          (norm_freshMap_le p (by simp)) (familyPhysicalLayout d rs ++ Z))

theorem nonprivateCount_freshCircuit (Z : Layout Party) :
    (rs : List Party) → (h : ∀ p ∈ rs, d p = 1) → (freshCircuit d Z rs h).nonprivateCount = 0
  | [], _ => rfl
  | _ :: rs, h => by
      change (freshCircuit d Z rs _).nonprivateCount + 0 = 0
      rw [nonprivateCount_freshCircuit Z rs]

theorem eval_freshCircuit (Z : Layout Party) (σ : (p : Party) → Fin (d p)) (z : Mem Z) :
    (rs : List Party) → (h : ∀ p ∈ rs, d p = 1) →
      (freshCircuit d Z rs h).eval z = (appendIso (familyPhysicalLayout d rs) Z).symm
        (physVec d rs σ ⊗ₜ z)
  | [], _ => by
      change z = (appendIso ([] : Layout Party) Z).symm ((1 : ℂ) ⊗ₜ z)
      rw [appendIso_nil_symm_tmul, one_smul]
  | p :: rs, h => by
      have hσ : σ p = finOneOf d (h p List.mem_cons_self) :=
        Fin.ext (by
          have h1 := h p List.mem_cons_self
          have h2 := (σ p).isLt
          simp only [finOneOf]
          omega)
      change (appendIso [⟨p, euc (Fin (d p))⟩] (familyPhysicalLayout d rs ++ Z)).symm
          ((freshMap p _).rTensor _ (appendIso [] _ ((freshCircuit d Z rs _).eval z))) = _
      rw [eval_freshCircuit Z σ z rs, appendIso_nil_apply, rTensor_tmul, freshMap_apply,
        one_smul, appendIso_one_symm_tmul, ← hσ]
      rfl

/-- **Renaming the raw registers.** The raw register of each site of `xs` is renamed, by a
private map at its party, as the physical register of that party, followed by the fresh physical
registers of the parties of `rs`. -/
def siteCircuit (own : ι → Party) (hd : ∀ x, d (own x) = q) (Z : Layout Party) (rs : List Party)
    (hrs : ∀ p ∈ rs, d p = 1) :
    (xs : List ι) → OriginalCircuit (siteRegs q own xs ++ Z)
      (familyPhysicalLayout d (xs.map own ++ rs) ++ Z)
  | [] => freshCircuit d Z rs hrs
  | x :: xs =>
      .comp (.privateMap (own x) (a := [⟨own x, euc (Fin q)⟩])
          (b := [⟨own x, euc (Fin (d (own x)))⟩]) (by simp) (by simp)
          (renameMap (own x) (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (finCongr (hd x).symm)))
          (norm_renameMap_le _ _) (siteRegs q own xs ++ Z))
        (.frame ⟨own x, euc (Fin (d (own x)))⟩ (siteCircuit own hd Z rs hrs xs))

omit [Fintype ι] [DecidableEq ι] in
theorem nonprivateCount_siteCircuit (own : ι → Party) (hd : ∀ x, d (own x) = q)
    (Z : Layout Party) (rs : List Party) (hrs : ∀ p ∈ rs, d p = 1) :
    (xs : List ι) → (siteCircuit d own hd Z rs hrs xs).nonprivateCount = 0
  | [] => nonprivateCount_freshCircuit d Z rs hrs
  | _ :: xs => by
      change 0 + (siteCircuit d own hd Z rs hrs xs).nonprivateCount = 0
      rw [nonprivateCount_siteCircuit own hd Z rs hrs xs]

omit [Fintype ι] [DecidableEq ι] in
theorem eval_siteCircuit (own : ι → Party) (hd : ∀ x, d (own x) = q) (Z : Layout Party)
    (rs : List Party) (hrs : ∀ p ∈ rs, d p = 1) (c : ι → Fin q) (σ : (p : Party) → Fin (d p))
    (hσ : ∀ x, (σ (own x) : ℕ) = c x) (z : Mem Z) :
    (xs : List ι) → (siteCircuit d own hd Z rs hrs xs).eval
        ((appendIso (siteRegs q own xs) Z).symm (siteVec own xs c ⊗ₜ z)) =
      (appendIso (familyPhysicalLayout d (xs.map own ++ rs)) Z).symm
        (physVec d (xs.map own ++ rs) σ ⊗ₜ z)
  | [] => by
      change (freshCircuit d Z rs hrs).eval ((appendIso ([] : Layout Party) Z).symm
        ((1 : ℂ) ⊗ₜ z)) = _
      rw [appendIso_nil_symm_tmul, one_smul, eval_freshCircuit d Z σ z rs hrs]
      rfl
  | x :: xs => by
      have hx : (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (finCongr (hd x).symm))
          (EuclideanSpace.single (c x) (1 : ℂ)) = EuclideanSpace.single (σ (own x)) (1 : ℂ) := by
        rw [EuclideanSpace.piLpCongrLeft_single]
        congr 1
        exact Fin.ext (by simp [hσ x])
      change (siteCircuit d own hd Z rs hrs xs).eval.lTensor _
          ((appendIso [⟨own x, euc (Fin (d (own x)))⟩] (siteRegs q own xs ++ Z)).symm
            ((renameMap (own x) _).rTensor _ (appendIso [⟨own x, euc (Fin q)⟩] _
              ((EuclideanSpace.single (c x) (1 : ℂ) : EuclideanSpace ℂ (Fin q)) ⊗ₜ
                (appendIso (siteRegs q own xs) Z).symm (siteVec own xs c ⊗ₜ z))))) = _
      rw [appendIso_one_tmul, rTensor_tmul, renameMap_tmul, appendIso_one_symm_tmul,
        ContinuousLinearMap.lTensor_tmul, eval_siteCircuit own hd Z rs hrs c σ hσ z xs, hx]
      rfl

/-! ### The order of the physical registers -/

/-- The parties without a site. -/
def nonsiteParties [Fintype Party] [DecidableEq Party] (own : ι → Party) : List Party :=
  (Finset.univ \ Finset.univ.image own).toList

/-- The order of the physical registers: the parties of the sites, in the order of the sites,
followed by the parties without a site. -/
def siteOrder [Fintype Party] [DecidableEq Party] (own : ι → Party) : List Party :=
  (sites ι).map own ++ nonsiteParties own

omit [DecidableEq ι] in
theorem mem_nonsiteParties [Fintype Party] [DecidableEq Party] {own : ι → Party} {p : Party} :
    p ∈ nonsiteParties own ↔ p ∉ Set.range own := by
  simp [nonsiteParties]

omit [DecidableEq ι] in
theorem nodup_siteOrder [Fintype Party] [DecidableEq Party] {own : ι → Party}
    (hown : Function.Injective own) : (siteOrder own).Nodup := by
  refine List.nodup_append.2 ⟨nodup_sites.map hown, Finset.nodup_toList _, ?_⟩
  intro a ha b hb hab
  subst hab
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 ha
  exact mem_nonsiteParties.1 hb ⟨x, rfl⟩

omit [DecidableEq ι] in
theorem mem_siteOrder [Fintype Party] [DecidableEq Party] (own : ι → Party) (p : Party) :
    p ∈ siteOrder own := by
  by_cases hp : p ∈ Set.range own
  · obtain ⟨x, rfl⟩ := hp
    exact List.mem_append_left _ (List.mem_map_of_mem (mem_sites x))
  · exact List.mem_append_right _ (mem_nonsiteParties.2 hp)

/-! ### The final regrouping -/

section Readout

variable [Fintype Party] [DecidableEq Party]

/-- The private registers of the final layout: the tags of the main sheet, then the registers of
the other sheets and the idle registers. -/
abbrev readoutPrivate (M : Frame pos q Party) (Fs : List (Frame pos q Party))
    (ℓ : Layout Party) : Layout Party :=
  tagRegs M.holes ++ stackRegs Fs ℓ

theorem nonsiteParties_dim (M : Frame pos q Party) (hd1 : ∀ p ∉ Set.range M.owner, d p = 1) :
    ∀ p ∈ nonsiteParties M.owner, d p = 1 :=
  fun p hp => hd1 p (mem_nonsiteParties.1 hp)

/-- **The final regrouping.** On the stack with main sheet `M`, the raw registers of `M` are
moved in front of its tags, each is renamed as the physical register of its party, and every
party without a site prepares a physical register of dimension one. The result is the output
layout: the physical registers in the order `siteOrder M.owner`, then the private registers.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 48–51 and 669–681. -/
def readoutCircuit (M : Frame pos q Party) (Fs : List (Frame pos q Party)) (ℓ : Layout Party)
    (hd : ∀ x, d (M.owner x) = q) (hd1 : ∀ p ∉ Set.range M.owner, d p = 1) :
    OriginalCircuit (stackRegs (M :: Fs) ℓ)
      (familyPhysicalOutputLayout d (siteOrder M.owner) (readoutPrivate M Fs ℓ)) :=
  .comp (((Word.exchangeBlocks (tagRegs M.holes) (siteRegs q M.owner (sites ι))
      (stackRegs Fs ℓ)).toOriginalCircuit (Word.isAllowed_exchangeBlocks _ _ _)).castLayouts
      (List.append_assoc _ _ _).symm rfl)
    (siteCircuit d M.owner hd _ (nonsiteParties M.owner) (nonsiteParties_dim d M hd1) (sites ι))

theorem nonprivateCount_readoutCircuit (M : Frame pos q Party) (Fs : List (Frame pos q Party))
    (ℓ : Layout Party) (hd : ∀ x, d (M.owner x) = q) (hd1 : ∀ p ∉ Set.range M.owner, d p = 1) :
    (readoutCircuit d M Fs ℓ hd hd1).nonprivateCount = 0 := by
  change OriginalCircuit.nonprivateCount (OriginalCircuit.castLayouts _ _ _) +
    (siteCircuit d M.owner hd _ _ _ (sites ι)).nonprivateCount = 0
  rw [OriginalCircuit.nonprivateCount_castLayouts,
    Word.nonprivateCount_toOriginalCircuit_of_isReordering
      (Word.isReordering_exchangeBlocks _ _ _), nonprivateCount_siteCircuit]

end Readout

end TNLean.PEPS.EncodedFrame
