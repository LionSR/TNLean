/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.SiteRegisters
import TNLean.Lattice.PartyCircuit.FamilyPhysicalReadout
import QICLean.Channel.PartialTraceBasisInvariance
import QICLean.Analysis.SubnormalizedPureStateError
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

open scoped TensorProduct

namespace TNLean.MPS.AreaLaw.ChainSweep

open TNLean.Lattice.PartyCircuit TNLean.Lattice.Sheet

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

private def rawReadout (rs : List (RawLabel L w)) (hn : rs.Nodup)
    (hc : ∀ r, r ∈ rs) :
    Mem (siteRegs q (rawOwner L w) rs) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (RawLabel L w → Fin q) :=
  groupIso (rawOwner L w) rs (List.Nodup.getEquivOfForallMemList rs hn hc)

private def auxiliaryList (L w : ℕ) : List (AuxiliarySite L w) := Finset.univ.toList

/-- The discarded layout contains every labelled auxiliary register at its actual
owner. Source: Part II, `con:band`, lines 271–272, and `prop:sweep`, lines 355–360. -/
def privateLayout (L w q : ℕ) : Layout (Party L w) :=
  siteRegs q (auxiliaryOwner L w) (auxiliaryList L w)

private def auxiliaryReadout (L w q : ℕ) :
    Mem (privateLayout L w q) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (AuxiliarySite L w → Fin q) :=
  groupIso (auxiliaryOwner L w) (auxiliaryList L w)
    (List.Nodup.getEquivOfForallMemList _ (Finset.nodup_toList _)
      (by simp [auxiliaryList]))

/-- Every original party occurs once, including parties with scalar physical
output. Source: Part II, `prop:sweep`, lines 349–360. -/
def physicalOrder (L w : ℕ) : List (Party L w) := Finset.univ.toList

private def physicalBasis (L w q : ℕ) :=
  familyLabelledPhysicalBasis (physicalDimension L w q) (physicalOrder L w)
    (Finset.nodup_toList _) (by simp [physicalOrder])

private def auxiliaryBasis (L w q : ℕ) :=
  (EuclideanSpace.basisFun (AuxiliarySite L w → Fin q) ℂ).map
    (auxiliaryReadout L w q).symm

/-- Coordinates of the actual terminal memory before block encoding: one main
configuration and every original auxiliary label.
Source: Part II, `prop:sweep`, lines 355–360. -/
def sheetReadout (rs : List (RawLabel L w)) (hn : rs.Nodup)
    (hc : ∀ r, r ∈ rs) :=
  (rawReadout (q := q) rs hn hc).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (Equiv.sumArrowEquivProdArrow (Fin L) (AuxiliarySite L w) (Fin q)))

/-- The explicit coordinate identification with the physical block layout and
the unchanged auxiliary layout. Its owner-local factorization is specified
by `localConfigurationEquiv_restrict`; realization by a private word is separate.
Source: Part II, `prop:sweep`, lines 355–360, and Theorem B, lines 575–583. -/
def terminalRegrouping (rs : List (RawLabel L w)) (hn : rs.Nodup)
    (hc : ∀ r, r ∈ rs) :
    Mem (siteRegs q (rawOwner L w) rs) ≃ₗᵢ[ℂ]
      Mem (familyPhysicalOutputLayout (physicalDimension L w q)
        (physicalOrder L w) (privateLayout L w q)) :=
  (rawReadout (q := q) rs hn hc).trans
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (terminalConfigurationEquiv L w q)).trans
        (((physicalBasis L w q).tensorProduct (auxiliaryBasis L w q)).repr.symm.trans
          (appendIso _ _).symm))

/-- For every actual terminal vector, the standard physical/private readout has
the physical marginal obtained by tracing precisely the original auxiliary
labels, in the constructed block coordinates. No product or normalization
assumption is made on the vector. Source: Part II, Theorem B, lines 575–583.
This is an intermediate coordinate result, not the full sweep theorem. -/
theorem physicalDensity_terminalRegrouping
    (rs : List (RawLabel L w)) (hn : rs.Nodup) (hc : ∀ r, r ∈ rs)
    (Ψ : Mem (siteRegs q (rawOwner L w) rs)) :
    letI := (auxiliaryReadout L w q).symm.toLinearEquiv.finiteDimensional
    let v := familyLabelledPhysicalReadout (physicalDimension L w q) (physicalOrder L w)
      (Finset.nodup_toList _) (by simp [physicalOrder]) (privateLayout L w q)
      (terminalRegrouping rs hn hc Ψ)
    Matrix.partialTraceRight (Matrix.euclideanOuterProduct v v) =
      Matrix.reindex (mainConfigurationEquiv L w q) (mainConfigurationEquiv L w q)
        (Matrix.partialTraceRight (Matrix.euclideanOuterProduct
          (sheetReadout (q := q) rs hn hc Ψ) (sheetReadout (q := q) rs hn hc Ψ))) := by
  classical
  let := (auxiliaryReadout L w q).symm.toLinearEquiv.finiteDimensional
  let z := appendIso (familyPhysicalLayout (physicalDimension L w q) (physicalOrder L w))
    (privateLayout L w q) (terminalRegrouping rs hn hc Ψ)
  let b := physicalBasis L w q
  let g := auxiliaryBasis L w q
  have hchange := OrthonormalBasis.tensorProduct_rankOne_basisChange b b g
    (stdOrthonormalBasis ℂ (Mem (privateLayout L w q)).carrier) z z
  have htrace := Matrix.partialTraceRight_kronecker_conj_of_right_isometry
    (b.toBasis.toMatrix b)
    ((stdOrthonormalBasis ℂ (Mem (privateLayout L w q)).carrier).toBasis.toMatrix g)
    (OrthonormalBasis.toMatrix_orthonormalBasis_conjTranspose_mul_self
      (stdOrthonormalBasis ℂ (Mem (privateLayout L w q)).carrier) g)
    (Matrix.euclideanOuterProduct ((b.tensorProduct g).repr z) ((b.tensorProduct g).repr z))
  simp only [Matrix.euclideanOuterProduct, Pi.star_def, starRingEnd_apply] at htrace hchange
  rw [hchange] at htrace
  have hself : b.toBasis.toMatrix b = 1 := Module.Basis.toMatrix_self b.toBasis
  simp only [hself, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at htrace
  have hz : (b.tensorProduct g).repr z =
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (terminalConfigurationEquiv L w q))
        (rawReadout rs hn hc Ψ) := by
    exact ((appendIso
      (familyPhysicalLayout (physicalDimension L w q) (physicalOrder L w))
      (privateLayout L w q)).trans (b.tensorProduct g).repr).apply_symm_apply _
  refine htrace.trans ?_
  rw [hz]
  rfl

end TNLean.MPS.AreaLaw.ChainSweep
