/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolInitialization
import TNLean.Algebra.CyclicInsertion
import TNLean.PEPS.Approximation.SheetStackReadoutCircuit
import QICLean.Analysis.ProductReferenceDensityError
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup

/-!
# The terminal sheet reference in its original copy coordinates

The specified terminal frames retain the main owner and every labelled
auxiliary copy at its prescribed retired owners. Their raw register list is
identified with the existing main-plus-auxiliary labels, in the same copy order
as the initialization. In these coordinates the reference is the main vector
and the product of its labelled auxiliary copies.

This constructs the auxiliary vector and its normalization. It does not assume
that the auxiliary state is a product across parties. The actual sweep must
still be shown to end at the specified list of frames.

Source: the one-dimensional note, Part II, Proposition `prop:sweep`,
`part2b_mps_protocol.tex`, lines 356–359, and the physical trace in the proof of
Theorem B, lines 575–583.

**Local fix (terminal auxiliary registers):** Auxiliary registers remain at
all their actual retired owners and are all traced out. The correction is
recorded in `docs/paper-gaps/tnlean_one_dimensional_band_sweep_corrections.tex`.
-/

noncomputable section
open scoped TensorProduct

namespace TNLean.MPS.AreaLaw.ChainSweep

open TNLean.PEPS.PairEffect TNLean.PEPS.EncodedFrame

variable {L w q : ℕ} {pos : Fin L → ℝ × ℝ}

/-- The auxiliary configurations, with their original copy and site labels.
Source: Part II, `prop:sweep`, lines 357–359. -/
def auxiliaryReference (L w q : ℕ) (Ω : EuclideanSpace ℂ (Fin L → Fin q)) :
    EuclideanSpace ℂ (AuxiliarySite L w → Fin q) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.curry (AuxiliaryCopy L w) (Fin L) (Fin q)).symm)
      (EuclideanSpace.piTensor (fun _ : AuxiliaryCopy L w ↦ Ω))

/-- Each auxiliary occurrence contributes precisely one copy of the original
amplitude. Source: Part II, `prop:sweep`, lines 357–359. -/
theorem auxiliaryReference_apply (Ω : EuclideanSpace ℂ (Fin L → Fin q))
    (a : AuxiliarySite L w → Fin q) :
    auxiliaryReference L w q Ω a = ∏ c : AuxiliaryCopy L w, Ω (fun x ↦ a (c, x)) := by
  exact EuclideanSpace.piTensor_apply (fun _ : AuxiliaryCopy L w ↦ Ω)
    (fun c x ↦ a (c, x))

/-- The auxiliary reference is normalized by its construction, including the
empty family. Source: Part II, `prop:sweep`, lines 357–359. -/
theorem norm_auxiliaryReference (Ω : EuclideanSpace ℂ (Fin L → Fin q))
    (hΩ : ‖Ω‖ = 1) : ‖auxiliaryReference L w q Ω‖ = 1 := by
  simp [auxiliaryReference, EuclideanSpace.norm_piTensor, hΩ]

/-- Copy-site order induced by the same labelled copy order as initialization.
Source: Part II, `prop:sweep`, lines 350–351 and 357–359. -/
def terminalAuxiliarySiteOrder (L w : ℕ) : List (AuxiliarySite L w) :=
  (initialAuxiliaryOrder L w).product (sites (Fin L))

private theorem terminalAuxiliarySiteOrder_nodup (L w : ℕ) :
    (terminalAuxiliarySiteOrder L w).Nodup := by
  exact List.Nodup.product (Finset.nodup_toList _) nodup_sites

private theorem mem_terminalAuxiliarySiteOrder (a : AuxiliarySite L w) :
    a ∈ terminalAuxiliarySiteOrder L w := by
  exact List.mem_product.2 ⟨by simp [initialAuxiliaryOrder], mem_sites a.2⟩

/-- The complete main list followed by every original auxiliary copy-site label.
Source: Part II, `prop:sweep`, lines 357–359. -/
def terminalRawOrder (L w : ℕ) : List (RawLabel L w) :=
  (sites (Fin L)).map Sum.inl ++ (terminalAuxiliarySiteOrder L w).map Sum.inr

/-- No actual raw label is repeated in the terminal reference order.
Source: Part II, `prop:sweep`, lines 357–359. -/
theorem terminalRawOrder_nodup (L w : ℕ) : (terminalRawOrder L w).Nodup := by
  apply List.Nodup.append
    (List.Nodup.map Sum.inl_injective nodup_sites)
    (List.Nodup.map Sum.inr_injective (terminalAuxiliarySiteOrder_nodup L w))
  apply List.disjoint_left.2
  intro r hr hs
  obtain ⟨x, _, rfl⟩ := List.mem_map.1 hr
  obtain ⟨a, _, h⟩ := List.mem_map.1 hs
  cases h

/-- Every actual raw label is retained in the terminal reference order.
Source: Part II, `prop:sweep`, lines 357–359. -/
theorem mem_terminalRawOrder (r : RawLabel L w) : r ∈ terminalRawOrder L w := by
  cases r with
  | inl x => exact List.mem_append_left _ (List.mem_map.2 ⟨x, mem_sites x, rfl⟩)
  | inr a =>
      exact List.mem_append_right _
        (List.mem_map.2 ⟨a, mem_terminalAuxiliarySiteOrder a, rfl⟩)

/-- The specified retired auxiliary frames, in the same copy order used at
initialization. Source: Part II, `prop:sweep`, lines 357–359. -/
def terminalAuxiliaryFrames (L w q : ℕ) (pos : Fin L → ℝ × ℝ) :
    List (Frame pos q (Party L w)) :=
  (initialAuxiliaryOrder L w).map fun c ↦
    Frame.raw (fun x ↦ auxiliaryOwner L w (c, x))

/-- The specified terminal main frame followed by all retired auxiliary frames.
This definition does not assert that a sweep has reached it.
Source: Part II, `prop:sweep`, lines 357–360. -/
def terminalFrames (L w q : ℕ) (pos : Fin L → ℝ × ℝ) :
    List (Frame pos q (Party L w)) :=
  Frame.raw (mainOwner L w) :: terminalAuxiliaryFrames L w q pos

private theorem stackRegs_auxiliaryCopies (cs : List (AuxiliaryCopy L w)) :
    stackRegs (cs.map fun c ↦
      (Frame.raw (fun x ↦ auxiliaryOwner L w (c, x)) : Frame pos q (Party L w))) [] =
      siteRegs q (auxiliaryOwner L w) (cs.product (sites (Fin L))) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      change siteRegs q (fun x ↦ auxiliaryOwner L w (c, x)) (sites (Fin L)) ++
        stackRegs (cs.map fun c ↦
          (Frame.raw (fun x ↦ auxiliaryOwner L w (c, x)) : Frame pos q (Party L w))) [] = _
      rw [ih]
      simp [siteRegs, List.product, List.flatMap_cons, List.map_append,
        List.map_map, Function.comp_def]

/-- Flattening the specified terminal frames retains exactly the original raw
labels and owners. Source: Part II, `prop:sweep`, lines 357–360. -/
theorem stackRegs_terminalFrames (L w q : ℕ) (pos : Fin L → ℝ × ℝ) :
    stackRegs (terminalFrames L w q pos) [] =
      siteRegs q (rawOwner L w) (terminalRawOrder L w) := by
  change siteRegs q (mainOwner L w) (sites (Fin L)) ++
    stackRegs ((initialAuxiliaryOrder L w).map fun c ↦
      (Frame.raw (fun x ↦ auxiliaryOwner L w (c, x)) : Frame pos q (Party L w))) [] = _
  rw [stackRegs_auxiliaryCopies]
  simp [terminalRawOrder, terminalAuxiliarySiteOrder, siteRegs, List.map_append,
    List.map_map, Function.comp_def, rawOwner]

private theorem cons_tensor_heq {P : Type} (r : Reg P) {a b : Layout P}
    (h : a = b) (x : r.space) (y : Mem a) (z : Mem b) (hy : HEq y z) :
    HEq (x ⊗ₜ y : Mem (r :: a)) (x ⊗ₜ z : Mem (r :: b)) := by
  cases h
  cases hy
  rfl

private theorem append_tensor_heq {P : Type} {a a' b b' : Layout P}
    (ha : a = a') (hb : b = b') (x : Mem a) (y : Mem b)
    (x' : Mem a') (y' : Mem b') (hx : HEq x x') (hy : HEq y y') :
    HEq ((appendIso a b).symm (x ⊗ₜ y))
      ((appendIso a' b').symm (x' ⊗ₜ y')) := by
  cases ha
  cases hb
  cases hx
  cases hy
  rfl

private theorem mapped_siteVec_heq {ι κ P : Type} (own : κ → P) (f : ι → κ)
    (xs : List ι) (c : κ → Fin q) :
    HEq (siteVec own (xs.map f) c)
      (siteVec (fun x ↦ own (f x)) xs (fun x ↦ c (f x))) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have ht : siteRegs q own (xs.map f) = siteRegs q (fun x ↦ own (f x)) xs := by
        simp [siteRegs, List.map_map, Function.comp_def]
      exact cons_tensor_heq ⟨own (f x), euc (Fin q)⟩ ht
        (EuclideanSpace.single (c (f x)) (1 : ℂ)) _ _ ih

private theorem append_siteVec_transport {ι P : Type} (own : ι → P)
    (a b : List ι) (tail : Layout P) (ht : tail = siteRegs q own b)
    (h : siteRegs q own a ++ tail = siteRegs q own (a ++ b)) (c : ι → Fin q) :
    (Layout.memCongr h).symm (siteVec own (a ++ b) c) =
      (appendIso (siteRegs q own a) tail).symm
        (siteVec own a c ⊗ₜ (Layout.memCongr ht).symm (siteVec own b c)) := by
  subst tail
  induction a with
  | nil =>
      change siteVec own b c =
        (appendIso ([] : Layout P) (siteRegs q own b)).symm
          ((1 : ℂ) ⊗ₜ siteVec own b c)
      simpa only [one_smul] using
        (appendIso_nil_symm_tmul (siteRegs q own b) (1 : ℂ) (siteVec own b c)).symm
  | cons x a ih =>
      let h' : siteRegs q own a ++ siteRegs q own b = siteRegs q own (a ++ b) := by
        simp [siteRegs, List.map_append]
      rw [← Layout.memCongr_symm h]
      change Layout.memCongr (congrArg (⟨own x, euc (Fin q)⟩ :: ·) h'.symm)
        (EuclideanSpace.single (c x) (1 : ℂ) ⊗ₜ siteVec own (a ++ b) c) = _
      rw [Layout.memCongr_cons_tmul _ h'.symm, Layout.memCongr_symm h', ih h']
      exact (appendIso_symm_cons_tmul _ _ _ _ _ _).symm

private theorem append_siteVec_heq {ι P : Type} (own : ι → P)
    (a b : List ι) (c : ι → Fin q) :
    HEq (siteVec own (a ++ b) c)
      ((appendIso (siteRegs q own a) (siteRegs q own b)).symm
        (siteVec own a c ⊗ₜ siteVec own b c)) := by
  let h : siteRegs q own a ++ siteRegs q own b = siteRegs q own (a ++ b) := by
    simp [siteRegs, List.map_append]
  have ht : HEq ((Layout.memCongr h).symm (siteVec own (a ++ b) c))
      (siteVec own (a ++ b) c) := by
    rw [← Layout.memCongr_symm h]
    exact Layout.memCongr_apply_heq _ _
  exact ht.symm.trans (heq_of_eq (append_siteVec_transport own a b _ rfl h c))

private theorem inner_siteVec_regRef_raw [NeZero q] (own : Fin L → Party L w)
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (c : Fin L → Fin q) :
    inner ℂ (siteVec own (sites (Fin L)) c)
      ((Frame.raw own : Frame pos q (Party L w)).regRef Ω) = Ω c := by
  let g := groupIso (q := q) own (sites (Fin L)) (sitesEquiv (Fin L))
  have hb (b : Fin L → Fin q) :
      inner ℂ (siteVec own (sites (Fin L)) c) (siteVec own (sites (Fin L)) b) =
        if b = c then 1 else 0 := by
    rw [← g.inner_map_map]
    rw [groupIso_siteVec own _ _ id (fun _ ↦ rfl) c,
      groupIso_siteVec own _ _ id (fun _ ↦ rfl) b]
    simp [EuclideanSpace.inner_single_left, eq_comm]
  rw [Frame.regRef_of_outer_eq_empty _ (by simp [Frame.raw]) Ω]
  change inner ℂ (siteVec own (sites (Fin L)) c)
    (∑ b, Ω b • (appendIso ([] : Layout (Party L w))
      (siteRegs q own (sites (Fin L)))).symm
        ((1 : ℂ) ⊗ₜ siteVec own (sites (Fin L)) b)) = Ω c
  have he (b : Fin L → Fin q) :
      (appendIso ([] : Layout (Party L w)) (siteRegs q own (sites (Fin L)))).symm
        ((1 : ℂ) ⊗ₜ siteVec own (sites (Fin L)) b) =
        siteVec own (sites (Fin L)) b := by
    exact (appendIso_nil_symm_tmul _ (1 : ℂ) _).trans (one_smul ℂ _)
  have hs : (∑ b, Ω b • (appendIso ([] : Layout (Party L w))
      (siteRegs q own (sites (Fin L)))).symm
        ((1 : ℂ) ⊗ₜ siteVec own (sites (Fin L)) b)) =
      ∑ b, Ω b • siteVec own (sites (Fin L)) b :=
    Finset.sum_congr rfl fun b _ ↦ congrArg (Ω b • ·) (he b)
  exact (congrArg (inner ℂ (siteVec own (sites (Fin L)) c)) hs).trans
    (by simp only [inner_sum, inner_smul_right, hb]; simp)

private def auxiliaryReferenceBasis (a : AuxiliarySite L w → Fin q) :
    (cs : List (AuxiliaryCopy L w)) →
      Mem (stackRegs (cs.map fun c ↦
        (Frame.raw (fun x ↦ auxiliaryOwner L w (c, x)) : Frame pos q (Party L w))) [])
  | [] => (1 : ℂ)
  | c :: cs =>
      (appendIso (siteRegs q (fun x ↦ auxiliaryOwner L w (c, x)) (sites (Fin L)))
        (stackRegs (cs.map fun c ↦
          (Frame.raw (fun x ↦ auxiliaryOwner L w (c, x)) : Frame pos q (Party L w)))
            [])).symm
        (siteVec (fun x ↦ auxiliaryOwner L w (c, x)) (sites (Fin L))
          (fun x ↦ a (c, x)) ⊗ₜ auxiliaryReferenceBasis a cs)

private theorem auxiliaryReferenceBasis_flatten (a : AuxiliarySite L w → Fin q)
    (cs : List (AuxiliaryCopy L w)) :
    HEq (auxiliaryReferenceBasis (pos := pos) a cs)
      (siteVec (auxiliaryOwner L w) (cs.product (sites (Fin L))) a) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      have hh : siteRegs q (fun x ↦ auxiliaryOwner L w (c, x)) (sites (Fin L)) =
          siteRegs q (auxiliaryOwner L w) ((sites (Fin L)).map (fun x ↦ (c, x))) := by
        simp [siteRegs, List.map_map, Function.comp_def]
      have ht := stackRegs_auxiliaryCopies (q := q) (pos := pos) cs
      have hx := (mapped_siteVec_heq (auxiliaryOwner L w) (fun x ↦ (c, x))
        (sites (Fin L)) a).symm
      exact (append_tensor_heq hh ht _ _ _ _ hx ih).trans
        (append_siteVec_heq (auxiliaryOwner L w)
          ((sites (Fin L)).map (fun x ↦ (c, x))) (cs.product (sites (Fin L))) a).symm

private theorem inner_appendIso_symm_tmul (a b : Layout (Party L w))
    (x x' : Mem a) (y y' : Mem b) :
    inner ℂ ((appendIso a b).symm (x ⊗ₜ y))
      ((appendIso a b).symm (x' ⊗ₜ y')) = inner ℂ x x' * inner ℂ y y' := by
  rw [LinearIsometryEquiv.inner_map_map, TensorProduct.inner_tmul]

private theorem auxiliaryReferenceBasis_inner [NeZero q]
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (a : AuxiliarySite L w → Fin q)
    (cs : List (AuxiliaryCopy L w)) :
    inner ℂ (auxiliaryReferenceBasis (pos := pos) a cs)
      (framesVec Ω (cs.map fun c ↦
        (Frame.raw (fun x ↦ auxiliaryOwner L w (c, x)) : Frame pos q (Party L w)))) =
      (cs.map fun c ↦ Ω (fun x ↦ a (c, x))).prod := by
  induction cs with
  | nil =>
      change inner ℂ (1 : ℂ) (1 : ℂ) = 1
      simp
  | cons c cs ih =>
      exact (inner_appendIso_symm_tmul
        (siteRegs q (fun x ↦ auxiliaryOwner L w (c, x)) (sites (Fin L)))
        (stackRegs (cs.map fun c ↦
          (Frame.raw (fun x ↦ auxiliaryOwner L w (c, x)) : Frame pos q (Party L w))) [])
        (siteVec (fun x ↦ auxiliaryOwner L w (c, x)) (sites (Fin L)) (fun x ↦ a (c, x)))
        ((Frame.raw (fun x ↦ auxiliaryOwner L w (c, x)) : Frame pos q (Party L w)).regRef Ω)
        (auxiliaryReferenceBasis a cs) (framesVec Ω _)).trans
        (congrArg₂ (· * ·) (inner_siteVec_regRef_raw _ Ω _) ih)

/-- The actual stack memory in the already specified main/auxiliary coordinates.
No terminal readout or factorization is supplied as a hypothesis.
Source: Part II, `prop:sweep`, lines 357–360. -/
def terminalStackReadout (L w q : ℕ) (pos : Fin L → ℝ × ℝ) :
    Mem (stackRegs (terminalFrames L w q pos) []) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((Fin L → Fin q) × (AuxiliarySite L w → Fin q)) :=
  (Layout.memCongr (stackRegs_terminalFrames L w q pos)).trans
    (sheetReadout (terminalRawOrder L w) (terminalRawOrder_nodup L w)
      mem_terminalRawOrder)

/-- The specified frame product has the exact original main vector and the
constructed auxiliary product in the literal copy coordinates.
Source: Part II, `prop:sweep`, lines 357–359. -/
theorem terminalStackReadout_framesVec [NeZero q]
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) :
    terminalStackReadout L w q pos (framesVec Ω (terminalFrames L w q pos)) =
      Matrix.euclideanTensorVector Ω (auxiliaryReference L w q Ω) := by
  classical
  ext z
  rcases z with ⟨b, a⟩
  let cs := initialAuxiliaryOrder L w
  let ξ : Mem (stackRegs (terminalFrames L w q pos) []) :=
    (appendIso (siteRegs q (mainOwner L w) (sites (Fin L)))
      (stackRegs (terminalAuxiliaryFrames L w q pos) [])).symm
      (siteVec (mainOwner L w) (sites (Fin L)) b ⊗ₜ
        auxiliaryReferenceBasis (pos := pos) a cs)
  have hflat : HEq ξ
      (siteVec (rawOwner L w) (terminalRawOrder L w) (Sum.elim b a)) := by
    have hh : siteRegs q (mainOwner L w) (sites (Fin L)) =
        siteRegs q (rawOwner L w) ((sites (Fin L)).map Sum.inl) := by
      simp [siteRegs, List.map_map, Function.comp_def, rawOwner]
    have ht : stackRegs (terminalAuxiliaryFrames L w q pos) [] =
        siteRegs q (rawOwner L w) ((terminalAuxiliarySiteOrder L w).map Sum.inr) := by
      exact (stackRegs_auxiliaryCopies (q := q) (pos := pos) cs).trans
        (by simp [cs, terminalAuxiliarySiteOrder, siteRegs, List.map_map,
          Function.comp_def, rawOwner])
    have hx : HEq (siteVec (mainOwner L w) (sites (Fin L)) b)
        (siteVec (rawOwner L w) ((sites (Fin L)).map Sum.inl) (Sum.elim b a)) :=
      (mapped_siteVec_heq (rawOwner L w) Sum.inl (sites (Fin L)) (Sum.elim b a)).symm
    have hy : HEq (auxiliaryReferenceBasis (pos := pos) a cs)
        (siteVec (rawOwner L w) ((terminalAuxiliarySiteOrder L w).map Sum.inr)
          (Sum.elim b a)) :=
      (auxiliaryReferenceBasis_flatten (pos := pos) a cs).trans
        (mapped_siteVec_heq (rawOwner L w) Sum.inr
          (terminalAuxiliarySiteOrder L w) (Sum.elim b a)).symm
    exact (append_tensor_heq hh ht _ _ _ _ hx hy).trans
      (append_siteVec_heq (rawOwner L w) ((sites (Fin L)).map Sum.inl)
        ((terminalAuxiliarySiteOrder L w).map Sum.inr) (Sum.elim b a)).symm
  have htransport : Layout.memCongr (stackRegs_terminalFrames L w q pos) ξ =
      siteVec (rawOwner L w) (terminalRawOrder L w) (Sum.elim b a) :=
    eq_of_heq ((Layout.memCongr_apply_heq _ _).trans hflat)
  have hread : terminalStackReadout L w q pos ξ =
      EuclideanSpace.single (b, a) (1 : ℂ) := by
    change sheetReadout (terminalRawOrder L w) (terminalRawOrder_nodup L w)
      mem_terminalRawOrder (Layout.memCongr (stackRegs_terminalFrames L w q pos) ξ) = _
    rw [htransport]
    change (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (Equiv.sumArrowEquivProdArrow (Fin L) (AuxiliarySite L w) (Fin q)))
        (groupIso (rawOwner L w) (terminalRawOrder L w)
          (List.Nodup.getEquivOfForallMemList _ (terminalRawOrder_nodup L w)
            mem_terminalRawOrder)
          (siteVec (rawOwner L w) (terminalRawOrder L w) (Sum.elim b a))) = _
    rw [groupIso_siteVec (rawOwner L w) _ _ id (fun _ ↦ rfl) (Sum.elim b a),
      EuclideanSpace.piLpCongrLeft_single]
    rfl
  calc
    terminalStackReadout L w q pos (framesVec Ω (terminalFrames L w q pos)) (b, a) =
        inner ℂ (EuclideanSpace.single (b, a) (1 : ℂ))
          (terminalStackReadout L w q pos (framesVec Ω (terminalFrames L w q pos))) := by
      simp [EuclideanSpace.inner_single_left]
    _ = inner ℂ ξ (framesVec Ω (terminalFrames L w q pos)) := by
      rw [← hread, LinearIsometryEquiv.inner_map_map]
    _ = Ω b * (cs.map fun c ↦ Ω (fun x ↦ a (c, x))).prod := by
      exact (inner_appendIso_symm_tmul
        (siteRegs q (mainOwner L w) (sites (Fin L)))
        (stackRegs (terminalAuxiliaryFrames L w q pos) [])
        (siteVec (mainOwner L w) (sites (Fin L)) b)
        ((Frame.raw (mainOwner L w) : Frame pos q (Party L w)).regRef Ω)
        (auxiliaryReferenceBasis a cs) (framesVec Ω _)).trans
        (congrArg₂ (· * ·) (inner_siteVec_regRef_raw _ Ω _)
          (auxiliaryReferenceBasis_inner Ω a cs))
    _ = Matrix.euclideanTensorVector Ω (auxiliaryReference L w q Ω) (b, a) := by
      rw [Matrix.euclideanTensorVector_apply, auxiliaryReference_apply]
      simp [cs, initialAuxiliaryOrder]

/-- The reference density after tracing all auxiliary labels is the original
pure main density. Source: Part II, Theorem B, lines 575–583. -/
theorem partialTrace_terminalStackReference [NeZero q]
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1) :
    Matrix.partialTraceRight (Matrix.euclideanOuterProduct
      (terminalStackReadout L w q pos (framesVec Ω (terminalFrames L w q pos)))
      (terminalStackReadout L w q pos (framesVec Ω (terminalFrames L w q pos)))) =
        Matrix.euclideanOuterProduct Ω Ω := by
  rw [terminalStackReadout_framesVec, Matrix.partialTraceRight_tensorVector_eq_smul,
    norm_auxiliaryReference Ω hΩ]
  simp

/-- The existing absolute density estimate applied to this actual terminal
stack readout. The norm of the auxiliary reference is derived, not assumed.
Source: Part II, Theorem B, lines 575–583. This conditional error lemma does
not construct a sweep vector or prove its vector-error bound. -/
theorem rectangularTraceNorm_terminalStackReadout_sub_le [NeZero q]
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1)
    (Ψ : Mem (stackRegs (terminalFrames L w q pos) [])) (hΨ : ‖Ψ‖ ≤ 1)
    {ε : ℝ} (herror : ‖Ψ - framesVec Ω (terminalFrames L w q pos)‖ ≤ ε) :
    Matrix.rectangularTraceNorm
      (Matrix.partialTraceRight (Matrix.euclideanOuterProduct
        (terminalStackReadout L w q pos Ψ) (terminalStackReadout L w q pos Ψ)) -
          Matrix.euclideanOuterProduct Ω Ω) ≤ 2 * ε := by
  have hn : ‖auxiliaryReference L w q Ω‖ = 1 := norm_auxiliaryReference Ω hΩ
  have hv : ‖terminalStackReadout L w q pos Ψ‖ ≤ 1 := by
    simpa only [LinearIsometryEquiv.norm_map] using hΨ
  have he : ‖terminalStackReadout L w q pos Ψ -
      Matrix.euclideanTensorVector Ω (auxiliaryReference L w q Ω)‖ ≤ ε := by
    rw [← terminalStackReadout_framesVec Ω, ← map_sub, LinearIsometryEquiv.norm_map]
    exact herror
  simpa only [mul_zero, add_zero] using
    Matrix.rectangularTraceNorm_partialTraceRight_sub_product_reference_le_of_norm_sub_le
      (terminalStackReadout L w q pos Ψ) Ω (auxiliaryReference L w q Ω)
      hv hΩ hn.le he (show 1 - (0 : ℝ) ≤ ‖auxiliaryReference L w q Ω‖ by simp [hn])

end TNLean.MPS.AreaLaw.ChainSweep
