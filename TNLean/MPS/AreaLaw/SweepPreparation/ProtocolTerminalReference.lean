/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SweepPreparation.ProtocolInitialization
import QICLean.Analysis.TensorProduct.CyclicInsertion
import QICLean.Channel.PartialTrace.ProductReferenceDensityError
import Mathlib.Data.List.Nodup

/-!
# The terminal sheet reference in its original copy coordinates

The specified terminal sheets retain the main owner and every labelled
auxiliary copy at its prescribed retired owners. The sites of a list of sheets,
read at their owners, give coordinates of the system of the list at every party;
for the terminal sheets these sites are the existing main-plus-auxiliary labels.
In these coordinates the reference is the main vector and the product of its
labelled auxiliary copies.

This constructs the auxiliary vector and its normalization. It does not assume
that the auxiliary state is a product across parties. The actual sweep must
still be shown to end at the specified list of sheets.

Source: the one-dimensional note, Part II, Proposition `prop:sweep`,
`part2b_mps_protocol.tex`, lines 356–359, and the physical trace in the proof of
Theorem B, lines 575–583.

**Local fix (terminal auxiliary registers):** Auxiliary registers remain at
all their actual retired owners and are all traced out. The correction is
recorded in `docs/paper-gaps/tnlean_one_dimensional_band_sweep_corrections.tex`.
-/

noncomputable section
namespace TNLean.MPS.AreaLaw.ChainSweep

open Matrix QuantumCircuit.Party
open ManyBody (Config mem_blockPreimage_singleton blockConfigEquiv)

/-! ### Coordinates of a list of sheets -/

section StackCoordinates

variable {ι P : Type} [Fintype ι] [DecidableEq ι] [DecidableEq P] {q : ℕ}

/-- The sites of a list of sheets: the sites of each sheet in turn. -/
@[reducible] def stackSites (ι : Type) : List (Sheet ι P) → Type
  | [] => Empty
  | _ :: Fs => ι ⊕ stackSites ι Fs

/-- The owner of a site of a list of sheets: its owner in its own sheet. -/
def stackSiteOwner : (Fs : List (Sheet ι P)) → stackSites ι Fs → P
  | [], a => a.elim
  | S :: _, .inl x => S.owner x
  | _ :: Fs, .inr a => stackSiteOwner Fs a

/-- The basis of a party on one sheet: the configurations of the sites it owns. -/
private def sheetPartyEquiv (S : Sheet ι P) (p : P) :
    S.system q p ≃ ({x : ι // S.owner x = p} → Fin q) :=
  Equiv.arrowCongr (Equiv.subtypeEquivRight fun _ ↦ mem_blockPreimage_singleton S.owner)
    (Equiv.refl (Fin q))

/-- The basis of a party on a list of sheets, followed by the trivial idle system: the
configurations of the sites of the list that it owns. -/
def stackPartyEquiv : (Fs : List (Sheet ι P)) → (p : P) →
    stackSystem (Sheet.system q) Fs (fun _ ↦ Unit) p ≃
      ({a : stackSites ι Fs // stackSiteOwner Fs a = p} → Fin q)
  | [], _ =>
    { toFun := fun _ a ↦ a.1.elim
      invFun := fun _ ↦ ()
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ funext fun a ↦ a.1.elim }
  | S :: Fs, p =>
    ((sheetPartyEquiv S p).prodCongr (stackPartyEquiv Fs p)).trans
      ((Equiv.sumArrowEquivProdArrow _ _ _).symm.trans
        (Equiv.arrowCongr
          (Equiv.subtypeSum (p := fun a ↦ stackSiteOwner (S :: Fs) a = p)).symm
          (Equiv.refl (Fin q))))

/-- The configurations of the system of a list of sheets are those of its sites. -/
def stackConfigEquiv (Fs : List (Sheet ι P)) :
    Config (stackSystem (Sheet.system q) Fs (fun _ ↦ Unit)) ≃ (stackSites ι Fs → Fin q) :=
  (Equiv.piCongrFiberwise (γ₁ := fun _ ↦ Fin q) (f := stackSiteOwner Fs)
    fun p ↦ (stackPartyEquiv Fs p).symm).symm

/-- The value of the product of the copies of `Ω` on the sheets of a list at a configuration of
its sites. -/
def sheetsValue (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    (Fs : List (Sheet ι P)) → (stackSites ι Fs → Fin q) → ℂ
  | [], _ => 1
  | _ :: Fs, g => Ω (fun x ↦ g (.inl x)) * sheetsValue Ω Fs fun a ↦ g (.inr a)

/-- The reference vector of a list of sheets, read on the sites of the list, is the product of
one copy of `Ω` for each sheet. -/
theorem framesVec_apply [Fintype P] (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    (Fs : List (Sheet ι P)) → (z : Config (stackSystem (Sheet.system q) Fs (fun _ ↦ Unit))) →
      framesVec (fun S ↦ S.refVec Ω) Fs z = sheetsValue Ω Fs (stackConfigEquiv Fs z)
  | [], z => by
    rw [show z = fun _ ↦ () from Subsingleton.elim _ _]
    simp [framesVec, stackVec, sheetsValue]
  | S :: Fs, z => by
    change prodVec (S.refVec Ω) (framesVec (fun S ↦ S.refVec Ω) Fs) z = _
    rw [prodVec_apply, framesVec_apply Ω Fs, Sheet.refVec_apply]
    rfl

end StackCoordinates

/-! ### The terminal sheets -/

variable {L w q : ℕ}
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

/-- The specified retired auxiliary sheets, in the same copy order used at
initialization. Source: Part II, `prop:sweep`, lines 357–359. -/
def terminalAuxiliaryFrames (L w : ℕ) :
    List (Sheet (Fin L) (Party L w)) :=
  (initialAuxiliaryOrder L w).map fun c ↦
    Sheet.mk (fun x ↦ auxiliaryOwner L w (c, x))

/-- The specified terminal main sheet followed by all retired auxiliary sheets.
This definition does not assert that a sweep has reached it.
Source: Part II, `prop:sweep`, lines 357–360. -/
def terminalFrames (L w : ℕ) :
    List (Sheet (Fin L) (Party L w)) :=
  Sheet.mk (mainOwner L w) :: terminalAuxiliaryFrames L w

/-- The auxiliary label of a site of a list of copies of sheets. -/
private def mapSite {κ : Type} (sh : κ → Sheet (Fin L) (Party L w)) :
    (cs : List κ) → stackSites (Fin L) (cs.map sh) → κ × Fin L
  | [], a => a.elim
  | c :: _, .inl x => (c, x)
  | _ :: cs, .inr a => mapSite sh cs a

private theorem owner_mapSite {κ : Type} (sh : κ → Sheet (Fin L) (Party L w)) :
    (cs : List κ) → (a : stackSites (Fin L) (cs.map sh)) →
      (sh (mapSite sh cs a).1).owner (mapSite sh cs a).2 = stackSiteOwner (cs.map sh) a
  | [], a => a.elim
  | _ :: _, .inl _ => rfl
  | _ :: cs, .inr a => owner_mapSite sh cs a

private theorem mapSite_fst_mem {κ : Type} (sh : κ → Sheet (Fin L) (Party L w)) :
    (cs : List κ) → (a : stackSites (Fin L) (cs.map sh)) → (mapSite sh cs a).1 ∈ cs
  | [], a => a.elim
  | _ :: _, .inl _ => List.mem_cons_self
  | _ :: cs, .inr a => List.mem_cons_of_mem _ (mapSite_fst_mem sh cs a)

private theorem mapSite_injective {κ : Type} (sh : κ → Sheet (Fin L) (Party L w)) :
    (cs : List κ) → cs.Nodup → Function.Injective (mapSite sh cs)
  | [], _, a, _, _ => a.elim
  | c :: cs, hn, a, b, h => by
    obtain ⟨hc, hn⟩ := List.nodup_cons.mp hn
    rcases a with x | a <;> rcases b with y | b
    · exact congrArg Sum.inl (congrArg Prod.snd h)
    · have h1 : c = (mapSite sh cs b).1 := congrArg Prod.fst h
      exact (hc (h1 ▸ mapSite_fst_mem sh cs b)).elim
    · have h1 : (mapSite sh cs a).1 = c := congrArg Prod.fst h
      exact (hc (h1 ▸ mapSite_fst_mem sh cs a)).elim
    · exact congrArg Sum.inr (mapSite_injective sh cs hn h)

private theorem exists_mapSite_eq {κ : Type}
    (sh : κ → Sheet (Fin L) (Party L w)) :
    (cs : List κ) → ∀ b : κ × Fin L, b.1 ∈ cs → ∃ a, mapSite sh cs a = b
  | [], _, hb => (List.not_mem_nil hb).elim
  | c :: cs, b, hb => by
    classical
    by_cases hbc : b.1 = c
    · exact ⟨.inl b.2, Prod.ext hbc.symm rfl⟩
    · obtain ⟨a, ha⟩ := exists_mapSite_eq sh cs b ((List.mem_cons.mp hb).resolve_left hbc)
      exact ⟨.inr a, ha⟩

/-- The sites of the terminal auxiliary sheets are the auxiliary labels.
Source: Part II, `prop:sweep`, lines 357–359. -/
def auxiliarySitesEquiv (L w : ℕ) :
    stackSites (Fin L) (terminalAuxiliaryFrames L w) ≃ AuxiliarySite L w :=
  Equiv.ofBijective (mapSite _ (initialAuxiliaryOrder L w))
    ⟨mapSite_injective _ _ (Finset.nodup_toList _), fun b ↦
      exists_mapSite_eq _ _ b (by simp [initialAuxiliaryOrder])⟩

/-- The sites of the terminal sheets are the raw labels: the main sites, then the auxiliary
labels. Source: Part II, `prop:sweep`, lines 357–360. -/
def terminalSitesEquiv (L w : ℕ) : stackSites (Fin L) (terminalFrames L w) ≃ RawLabel L w :=
  Equiv.sumCongr (Equiv.refl (Fin L)) (auxiliarySitesEquiv L w)

/-- Every terminal site keeps its actual owner. Source: Part II, `prop:sweep`, lines 357–360. -/
theorem rawOwner_terminalSitesEquiv (a : stackSites (Fin L) (terminalFrames L w)) :
    rawOwner L w (terminalSitesEquiv L w a) = stackSiteOwner (terminalFrames L w) a := by
  rcases a with x | a
  · rfl
  · exact owner_mapSite _ (initialAuxiliaryOrder L w) a

/-- The basis of a party on the terminal sheets is that of its labelled registers.
Source: Part II, `prop:sweep`, lines 357–360. -/
def terminalPartyEquiv (L w q : ℕ) (p : Party L w) :
    stackSystem (Sheet.system q) (terminalFrames L w) (fun _ ↦ Unit) p ≃ rawSystem L w q p :=
  (stackPartyEquiv (terminalFrames L w) p).trans
    (Equiv.arrowCongr ((terminalSitesEquiv L w).subtypeEquiv fun a ↦ by
      rw [rawOwner_terminalSitesEquiv]) (Equiv.refl (Fin q)))

private theorem stackConfigEquiv_terminalPartyEquiv_symm (g : RawLabel L w → Fin q) :
    stackConfigEquiv (terminalFrames L w)
        ((Equiv.piCongrRight (terminalPartyEquiv L w q)).symm ((rawConfigEquiv L w q).symm g)) =
      fun a ↦ g (terminalSitesEquiv L w a) := by
  funext a
  simp [stackConfigEquiv, terminalPartyEquiv, rawConfigEquiv, Equiv.piCongrFiberwise_symm_apply]

/-- The actual terminal stack in the already specified main/auxiliary coordinates.
No terminal readout or factorization is supplied as a hypothesis.
Source: Part II, `prop:sweep`, lines 357–360. -/
def terminalStackReadout (L w : ℕ) :
    EuclideanSpace ℂ (Config (stackSystem (Sheet.system q) (terminalFrames L w) fun _ ↦ Unit))
      ≃ₗᵢ[ℂ] EuclideanSpace ℂ ((Fin L → Fin q) × (AuxiliarySite L w → Fin q)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.piCongrRight (terminalPartyEquiv L w q))).trans (sheetReadout L w q)

private theorem sheetsValue_auxiliary (Ω : EuclideanSpace ℂ (Fin L → Fin q))
    (a : AuxiliarySite L w → Fin q) :
    (cs : List (AuxiliaryCopy L w)) →
      sheetsValue Ω (cs.map fun c ↦ Sheet.mk fun x ↦ auxiliaryOwner L w (c, x))
          (fun s ↦ a (mapSite _ cs s)) =
        (cs.map fun c ↦ Ω (fun x ↦ a (c, x))).prod
  | [] => rfl
  | c :: cs => by
    exact (congrArg (fun t ↦ Ω (fun x ↦ a (c, x)) * t) (sheetsValue_auxiliary Ω a cs)).trans
      (by rw [List.map_cons, List.prod_cons])

/-- The specified sheet product has the exact original main vector and the
constructed auxiliary product in the literal copy coordinates.
Source: Part II, `prop:sweep`, lines 357–359. -/
theorem terminalStackReadout_framesVec
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) :
    terminalStackReadout L w (framesVec (fun S ↦ S.refVec Ω) (terminalFrames L w)) =
      Matrix.euclideanTensorVector Ω (auxiliaryReference L w q Ω) := by
  ext ⟨b, a⟩
  simp only [terminalStackReadout, sheetReadout, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply, Equiv.symm_trans_apply]
  rw [framesVec_apply, stackConfigEquiv_terminalPartyEquiv_symm,
    Matrix.euclideanTensorVector_apply, auxiliaryReference_apply]
  change Ω b * sheetsValue Ω ((initialAuxiliaryOrder L w).map fun c ↦
    Sheet.mk fun x ↦ auxiliaryOwner L w (c, x))
      (fun s ↦ a (mapSite _ (initialAuxiliaryOrder L w) s)) = _
  rw [sheetsValue_auxiliary]
  simp [initialAuxiliaryOrder, Finset.prod_map_toList]

/-- The reference density after tracing all auxiliary labels is the original
pure main density. Source: Part II, Theorem B, lines 575–583. -/
theorem partialTrace_terminalStackReference
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1) :
    Matrix.partialTraceRight (Matrix.euclideanOuterProduct
      (terminalStackReadout L w (framesVec (fun S ↦ S.refVec Ω) (terminalFrames L w)))
      (terminalStackReadout L w (framesVec (fun S ↦ S.refVec Ω) (terminalFrames L w)))) =
        Matrix.euclideanOuterProduct Ω Ω := by
  rw [terminalStackReadout_framesVec, Matrix.partialTraceRight_tensorVector_eq_smul,
    norm_auxiliaryReference Ω hΩ]
  simp

/-- The existing absolute density estimate applied to this actual terminal
stack readout. The norm of the auxiliary reference is derived, not assumed.
Source: Part II, Theorem B, lines 575–583. This conditional error lemma does
not construct a sweep vector or prove its vector-error bound. -/
theorem rectangularTraceNorm_terminalStackReadout_sub_le
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1)
    (Ψ : EuclideanSpace ℂ
      (Config (stackSystem (Sheet.system q) (terminalFrames L w) fun _ ↦ Unit)))
    (hΨ : ‖Ψ‖ ≤ 1)
    {ε : ℝ} (herror : ‖Ψ - framesVec (fun S ↦ S.refVec Ω) (terminalFrames L w)‖ ≤ ε) :
    Matrix.rectangularTraceNorm
      (Matrix.partialTraceRight (Matrix.euclideanOuterProduct
        (terminalStackReadout L w Ψ) (terminalStackReadout L w Ψ)) -
          Matrix.euclideanOuterProduct Ω Ω) ≤ 2 * ε := by
  have hn : ‖auxiliaryReference L w q Ω‖ = 1 := norm_auxiliaryReference Ω hΩ
  have hv : ‖terminalStackReadout L w Ψ‖ ≤ 1 := by
    simpa only [LinearIsometryEquiv.norm_map] using hΨ
  have he : ‖terminalStackReadout L w Ψ -
      Matrix.euclideanTensorVector Ω (auxiliaryReference L w q Ω)‖ ≤ ε := by
    rw [← terminalStackReadout_framesVec Ω, ← map_sub, LinearIsometryEquiv.norm_map]
    exact herror
  simpa only [mul_zero, add_zero] using
    Matrix.rectangularTraceNorm_partialTraceRight_sub_product_reference_le_of_norm_sub_le
      (terminalStackReadout L w Ψ) Ω (auxiliaryReference L w q Ω)
      hv hΩ hn.le he (show 1 - (0 : ℝ) ≤ ‖auxiliaryReference L w q Ω‖ by simp [hn])

end TNLean.MPS.AreaLaw.ChainSweep
