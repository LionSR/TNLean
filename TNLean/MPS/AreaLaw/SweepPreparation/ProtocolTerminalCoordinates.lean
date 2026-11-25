/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Original.Density
import QICLean.Channel.PartialTrace.BasisInvariance
import QICLean.Analysis.TraceNorm.SubnormalizedPureStateError
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Sort

/-!
# Physical block coordinates of the terminal chain registers

The main registers are grouped at their actual block owners. Every auxiliary
register retains its copy label and its owner. The local coordinate maps separate
the main and auxiliary registers at each party; the physical marginal traces all
auxiliary coordinates, including registers at parties without a main block.

This is an intermediate coordinate construction for the one-dimensional note,
Part II, `part2b_mps_protocol.tex`, `prop:sweep`, lines 355–360, and the
physical trace in the proof of Theorem B, lines 575–583. It does not construct
the sweep or assert that a circuit realizes the final coordinate map.

**Local fix (terminal auxiliary registers):** The block dimension assertion
applies to the main registers. Auxiliary registers remain at their retired
owners, as required by the band construction. The half-open lattice bands and
this distinction are recorded in
`docs/paper-gaps/tnlean_one_dimensional_band_sweep_corrections.tex`.
-/

noncomputable section

open Matrix ManyBody QuantumCircuit.Party

namespace TNLean.MPS.AreaLaw.ChainSweep

/-- The number of completed stages. Source: Part II, `con:sweep`, lines 329–342. -/
def stageCount (L w : ℕ) : ℕ := L / (20 * w) - 3

/-- Remainder parties followed by the distinct completed-block parties.
The last remainder party is the final physical block owner.
Source: Part II, `con:sweep`, lines 329–342. -/
abbrev Party (L w : ℕ) := Fin (stageCount L w + 1) ⊕ Fin (stageCount L w)

/-- Right copies have stages `0,…,m-1`; left copies have stages `1,…,m-1`.
The latter stage is its index plus one. Equal band centres do not identify copies.
Source: Part II, `con:band` and `con:sweep`, lines 248–276 and 329–342. -/
abbrev AuxiliaryCopy (L w : ℕ) := Fin (stageCount L w) ⊕ Fin (stageCount L w - 1)

/-- A raw auxiliary register retains its copy and site labels.
Source: Part II, `con:band`, lines 271–272. -/
abbrev AuxiliarySite (L w : ℕ) := AuxiliaryCopy L w × Fin L

/-- Main labels and auxiliary copy-site labels are disjoint.
Source: Part II, `prop:sweep`, lines 355–360. -/
abbrev RawLabel (L w : ℕ) := Fin L ⊕ AuxiliarySite L w

/-- The terminal main owner: completed blocks have length `20w`; the remaining
suffix belongs to the last remainder party. Source: Part II, `con:sweep`, lines 329–342. -/
def mainOwner (L w : ℕ) (x : Fin L) : Party L w :=
  if hx : x.val < stageCount L w * (20 * w) then
    .inr ⟨x.val / (20 * w),
      Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using hx)⟩
  else .inl (Fin.last (stageCount L w))

private def retiredOwner {L w : ℕ} (a : ℤ) (A B C : Party L w)
    (x : Fin L) : Party L w :=
  if a - 3 * (w : ℤ) ≤ x.val ∧ (x.val : ℤ) < a - 2 * (w : ℤ) then A
  else if a - 2 * (w : ℤ) ≤ x.val ∧ (x.val : ℤ) < a - (w : ℤ) then B
  else C

/-- Retired auxiliary owners for the actual stage and side. In particular,
copies at the same centre remain distinct. Source: Part II, `con:band`,
lines 271–272, with the half-open convention recorded in the module reference. -/
def auxiliaryOwner (L w : ℕ) : AuxiliarySite L w → Party L w
  | (.inl k, x) => retiredOwner (((k.val + 1) * (20 * w) : ℕ) : ℤ)
      (.inl k.castSucc) (.inl k.succ) (.inr k) x
  | (.inr k, x) => retiredOwner (((k.val + 1) * (20 * w) : ℕ) : ℤ)
      (.inl ⟨k.val + 1, by omega⟩) (.inr ⟨k.val + 1, by omega⟩)
      (.inr ⟨k.val, by omega⟩) x

/-- The actual terminal owner of each labelled raw register.
Source: Part II, `prop:sweep`, lines 355–360. -/
def rawOwner (L w : ℕ) : RawLabel L w → Party L w :=
  Sum.elim (mainOwner L w) (auxiliaryOwner L w)

/-- Main sites at one actual terminal owner.
Source: Part II, `prop:sweep`, lines 355–360. -/
abbrev MainSites (L w : ℕ) (p : Party L w) := {x : Fin L // mainOwner L w x = p}

/-- Auxiliary labels at one actual terminal owner.
Source: Part II, `con:band`, lines 271–272. -/
abbrev AuxiliarySites (L w : ℕ) (p : Party L w) :=
  {x : AuxiliarySite L w // auxiliaryOwner L w x = p}

/-- The physical dimension counts only main sites, not all private registers.
Source: Part II, `prop:sweep`, lines 355–360, and `thm:compression`, lines 459–461. -/
def physicalDimension (L w q : ℕ) (p : Party L w) : ℕ :=
  q ^ Fintype.card (MainSites L w p)

/-- Increasing site order followed by the usual base-`q` block encoding.
Source: Part II, `prop:sweep`, lines 355–360. -/
def blockEncoding (L w q : ℕ) (p : Party L w) :
    (MainSites L w p → Fin q) ≃ Fin (physicalDimension L w q p) :=
  (((Fintype.orderIsoFinOfCardEq (MainSites L w p) rfl).toEquiv.symm).arrowCongr
    (Equiv.refl (Fin q))).trans finFunctionFinEquiv

/-- Restrict a main configuration to its owner fibres and encode each block.
No injectivity of the main-owner map is assumed.
Source: Part II, `prop:sweep`, lines 355–360. -/
def mainConfigurationEquiv (L w q : ℕ) :
    (Fin L → Fin q) ≃ ((p : Party L w) → Fin (physicalDimension L w q p)) :=
  Equiv.piCongrFiberwise (f := mainOwner L w) (blockEncoding L w q)

/-- Split the actual labels, encode the main blocks, and leave every auxiliary
coordinate unchanged. Source: Part II, `prop:sweep`, lines 355–360. -/
def terminalConfigurationEquiv (L w q : ℕ) :
    (RawLabel L w → Fin q) ≃
      (((p : Party L w) → Fin (physicalDimension L w q p)) ×
        (AuxiliarySite L w → Fin q)) :=
  (Equiv.sumArrowEquivProdArrow (Fin L) (AuxiliarySite L w) (Fin q)).trans
    (Equiv.prodCongr (mainConfigurationEquiv L w q)
      (Equiv.refl (AuxiliarySite L w → Fin q)))

/-- The same split at a single owner. Both factors use only that owner's
registers. Source: Part II, `prop:sweep`, lines 355–360. -/
def localConfigurationEquiv (L w q : ℕ) (p : Party L w) :
    ({r : RawLabel L w // rawOwner L w r = p} → Fin q) ≃
      (Fin (physicalDimension L w q p) × (AuxiliarySites L w p → Fin q)) :=
  ((Equiv.subtypeSum (p := fun r : RawLabel L w ↦ rawOwner L w r = p)).arrowCongr
    (Equiv.refl (Fin q))).trans
      ((Equiv.sumArrowEquivProdArrow (MainSites L w p) (AuxiliarySites L w p)
        (Fin q)).trans
          (Equiv.prodCongr (blockEncoding L w q p)
            (Equiv.refl (AuxiliarySites L w p → Fin q))))

/-- The global coordinates are the product of the specified owner-local maps;
no auxiliary coordinate is reassigned or omitted. This is a coordinate
assertion, not yet the construction of a private circuit.
Source: Part II, `prop:sweep`, lines 355–360. -/
theorem localConfigurationEquiv_restrict (L w q : ℕ)
    (c : RawLabel L w → Fin q) (p : Party L w) :
    localConfigurationEquiv L w q p (fun r ↦ c r.val) =
      ((terminalConfigurationEquiv L w q c).1 p,
        fun a : AuxiliarySites L w p ↦ c (.inr a.val)) := by
  rfl

variable {L w q : ℕ}

/-- The private system: at every party, the auxiliary registers it retains, with their copy and
site labels. Source: Part II, `con:band`, lines 271–272, and `prop:sweep`, lines 355–360. -/
abbrev privateSystem (L w q : ℕ) : Party L w → Type :=
  fun p ↦ AuxiliarySites L w p → Fin q

instance (p : Party L w) : Fintype (privateSystem L w q p) :=
  inferInstanceAs (Fintype (AuxiliarySites L w p → Fin q))

instance (p : Party L w) : DecidableEq (privateSystem L w q p) :=
  inferInstanceAs (DecidableEq (AuxiliarySites L w p → Fin q))

/-- The terminal system before regrouping: at every party, its labelled main and auxiliary
registers. Source: Part II, `prop:sweep`, lines 355–360. -/
abbrev rawSystem (L w q : ℕ) : Party L w → Type :=
  fun p ↦ {r : RawLabel L w // rawOwner L w r = p} → Fin q

instance (p : Party L w) : Fintype (rawSystem L w q p) :=
  inferInstanceAs (Fintype ({r : RawLabel L w // rawOwner L w r = p} → Fin q))

instance (p : Party L w) : DecidableEq (rawSystem L w q p) :=
  inferInstanceAs (DecidableEq ({r : RawLabel L w // rawOwner L w r = p} → Fin q))

/-- A configuration of the terminal system is a configuration of all labelled registers.
Source: Part II, `prop:sweep`, lines 355–360. -/
def rawConfigEquiv (L w q : ℕ) : Config (rawSystem L w q) ≃ (RawLabel L w → Fin q) :=
  (Equiv.piCongrFiberwise (γ₁ := fun _ ↦ Fin q) (f := rawOwner L w)
    fun _ ↦ Equiv.refl _).symm

/-- The auxiliary configurations read at their actual owners.
Source: Part II, `con:band`, lines 271–272. -/
def auxiliaryConfigEquiv (L w q : ℕ) :
    (AuxiliarySite L w → Fin q) ≃ Config (privateSystem L w q) :=
  Equiv.piCongrFiberwise (γ₁ := fun _ ↦ Fin q) (f := auxiliaryOwner L w) fun _ ↦ Equiv.refl _

/-- Coordinates of the actual terminal system before block encoding: one main
configuration and every original auxiliary label.
Source: Part II, `prop:sweep`, lines 355–360. -/
def sheetReadout (L w q : ℕ) :
    EuclideanSpace ℂ (Config (rawSystem L w q)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((Fin L → Fin q) × (AuxiliarySite L w → Fin q)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    ((rawConfigEquiv L w q).trans (Equiv.sumArrowEquivProdArrow _ _ _))

/-- The explicit coordinate identification with one physical block register and the unchanged
auxiliary registers at every party: the owner-local maps `localConfigurationEquiv`.
Source: Part II, `prop:sweep`, lines 355–360, and Theorem B, lines 575–583. -/
def terminalRegrouping (L w q : ℕ) :
    EuclideanSpace ℂ (Config (rawSystem L w q)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Config (physicalSystem (physicalDimension L w q) (privateSystem L w q))) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.piCongrRight (localConfigurationEquiv L w q))

/-- The owner-local maps, read on all parties at once, encode the main configuration and keep
the auxiliary labels. -/
private theorem piCongrRight_localConfigurationEquiv_symm
    (s : (p : Party L w) → Fin (physicalDimension L w q p)) (a : AuxiliarySite L w → Fin q) :
    (Equiv.piCongrRight (localConfigurationEquiv L w q)).symm
        ((Equiv.arrowProdEquivProdArrow _ _ _).symm (s, auxiliaryConfigEquiv L w q a)) =
      (rawConfigEquiv L w q).symm
        ((Equiv.sumArrowEquivProdArrow _ _ _).symm ((mainConfigurationEquiv L w q).symm s, a)) := by
  funext p ⟨r, hr⟩
  subst hr
  cases r <;> rfl

/-- For every actual terminal vector, the standard physical/private readout has
the physical marginal obtained by tracing precisely the original auxiliary
labels, in the constructed block coordinates. No product or normalization
assumption is made on the vector. Source: Part II, Theorem B, lines 575–583.
This is an intermediate coordinate result, not the full sweep theorem. -/
theorem physicalDensity_terminalRegrouping (Ψ : EuclideanSpace ℂ (Config (rawSystem L w q))) :
    let v := toEuclideanLin (physicalReadout (physicalDimension L w q) (privateSystem L w q))
      (terminalRegrouping L w q Ψ)
    partialTraceRight (euclideanOuterProduct v v) =
      reindex (mainConfigurationEquiv L w q) (mainConfigurationEquiv L w q)
        (partialTraceRight (euclideanOuterProduct (sheetReadout L w q Ψ)
          (sheetReadout L w q Ψ))) := by
  intro v
  have hv (s : (p : Party L w) → Fin (physicalDimension L w q p))
      (a : AuxiliarySite L w → Fin q) :
      v (s, auxiliaryConfigEquiv L w q a) =
        sheetReadout L w q Ψ ((mainConfigurationEquiv L w q).symm s, a) := by
    simp only [v, toEuclideanLin_physicalReadout_apply, terminalRegrouping, sheetReadout,
      LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]
    rw [piCongrRight_localConfigurationEquiv_symm]
    rfl
  ext s s'
  simp only [partialTraceRight_apply, reindex_apply, submatrix_apply, euclideanOuterProduct,
    vecMulVec_apply, Pi.star_apply]
  rw [← (auxiliaryConfigEquiv L w q).sum_comp]
  simp only [hv]

end TNLean.MPS.AreaLaw.ChainSweep
