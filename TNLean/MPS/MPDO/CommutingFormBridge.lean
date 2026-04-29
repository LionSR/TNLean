/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.CommutingForm

/-!
# Local-to-global commuting-form data

This file records the exact post-extraction output still needed from the
simple-MPDO SAL + ZCL analysis of arXiv:1606.00608 Appendix C.2 in order to
conclude `MPOTensor.HasCommutingForm`.

The current repository already exposes the local entropy-side ingredients

* `MPOTensor.EtaStructure`,
* `MPOTensor.sal_implies_eta_structure`, and
* `MPOTensor.sal_zcl_implies_rank_one_T`,

but the extraction of the explicit neighboring operators `η_{k,h}` from the
Hayashi Markov decomposition is still open. We therefore introduce the exact
local-to-global datum that the future extraction theorem should produce: a
single translation-invariant positive two-site bond whose translated copies
commute on all periodic chains and realize the MPO on every finite length.

This is the strongest unconditional forward step currently available.
Once the explicit `η_{k,h}` operators are available, the intended future
Proposition C.6 proof should first construct `EtaLocalStructureData M`; the
existing theorem `hasCommutingForm_of_etaLocalStructure` will then discharge the
global commuting-form target.

## Main declarations

* `MPOTensor.TranslationInvariantBondData`
* `MPOTensor.EtaLocalStructureData`
* `MPOTensor.hasCommutingForm_of_etaLocalStructure`

## References

* [CPGSV17] arXiv:1606.00608, Appendix C.2, Proposition C.6
-/

open scoped ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- A single positive two-site bond operator whose translated copies commute on
all finite periodic chains.

This is the chain-independent local ingredient appearing in the commuting-form
presentation `ρ⁽ᴺ⁾ = c · ∏ᵢ B_{i,i+1}`.  In the paper proof of Appendix C.2,
this bond is the object eventually assembled from the explicit neighboring
operators `η_{k,h}`. -/
structure TranslationInvariantBondData (d : ℕ) where
  /-- The local positive semidefinite two-site bond. -/
  bond : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ
  /-- Positivity of the local bond. -/
  bond_pos : Matrix.PosSemidef bond
  /-- Pairwise commutativity of the translated copies of the bond on every
  finite periodic chain. -/
  bond_comm :
    ∀ {N : ℕ}, ∀ hN : 2 ≤ N, ∀ i j : Fin N,
      embedLocalOperator (d := d) 2 N hN i bond
        * embedLocalOperator (d := d) 2 N hN j bond
      = embedLocalOperator (d := d) 2 N hN j bond
          * embedLocalOperator (d := d) 2 N hN i bond

namespace TranslationInvariantBondData

variable {d : ℕ}

/-- The translation-invariant bond specializes to commuting-form data at every
chain length `N ≥ 2`. -/
def toCommutingFormData (data : TranslationInvariantBondData d) {N : ℕ}
    (hN : 2 ≤ N) : CommutingFormData d N where
  hN := hN
  bond := data.bond
  bond_pos := data.bond_pos
  bond_comm := fun i j => data.bond_comm hN i j

@[simp] theorem toCommutingFormData_bond (data : TranslationInvariantBondData d)
    {N : ℕ} (hN : 2 ≤ N) :
    (data.toCommutingFormData (N := N) hN).bond = data.bond := rfl

@[simp] theorem toCommutingFormData_hN (data : TranslationInvariantBondData d)
    {N : ℕ} (hN : 2 ≤ N) :
    (data.toCommutingFormData (N := N) hN).hN = hN := rfl

@[simp] theorem toCommutingFormData_bondAt
    (data : TranslationInvariantBondData d) {N : ℕ} (hN : 2 ≤ N) (i : Fin N) :
    (data.toCommutingFormData (N := N) hN).bondAt i =
      embedLocalOperator (d := d) 2 N hN i data.bond := rfl

end TranslationInvariantBondData

/-- The explicit `η`-local structure needed for Appendix C.2 once the abstract
Hayashi decomposition has been converted into concrete neighboring operators.

Concretely, this record stores the single translation-invariant bond extracted
from the local simple-MPDO analysis, together with proofs that it realizes the
finite-chain MPO operators. This is stronger than `HasCommutingForm M`, since
it requires one bond that works for every chain length rather than a separate
commuting-form witness at each length. The future issue-#833 extraction theorem
should construct this data from `EtaStructure` and the rank-one factorization
of the local transfer matrix. -/
structure EtaLocalStructureData (M : MPOTensor d D) where
  /-- The chain-independent nearest-neighbor bond extracted from the local
  `η_{k,h}` operators. -/
  bondData : TranslationInvariantBondData d
  /-- The MPO on every finite periodic chain is a positive scalar multiple of
  the commuting bond product determined by `bondData`. -/
  realizes_mpo :
    ∀ N : ℕ, ∀ hN : 2 ≤ N,
      (bondData.toCommutingFormData (N := N) hN).Realizes (mpo M N)

namespace EtaLocalStructureData

variable {M : MPOTensor d D}

/-- The commuting-form witness at chain length `N` carried by `EtaLocalStructureData`. -/
def formAt (data : EtaLocalStructureData M) (N : ℕ) (hN : 2 ≤ N) :
    CommutingFormData d N :=
  data.bondData.toCommutingFormData (N := N) hN

@[simp] theorem formAt_bond (data : EtaLocalStructureData M) (N : ℕ) (hN : 2 ≤ N) :
    (data.formAt N hN).bond = data.bondData.bond := rfl

/-- The chain-level commuting-form witness obtained from `EtaLocalStructureData`
realizes the MPO operator at that chain length. -/
theorem formAt_realizes (data : EtaLocalStructureData M) (N : ℕ) (hN : 2 ≤ N) :
    (data.formAt N hN).Realizes (mpo M N) :=
  data.realizes_mpo N hN

/-- The chain-level GSNNCH witness induced by the local `η`-structure at a fixed
chain length. -/
theorem isGSNNCHAt (data : EtaLocalStructureData M) (N : ℕ) (hN : 2 ≤ N) :
    IsGSNNCHAt (mpo M N) :=
  (data.formAt N hN).isGSNNCHAt_of_realizes (data.formAt_realizes N hN)

/-- The explicit `η`-local structure yields a GSNNCH witness on every finite
chain. -/
theorem isGSNNCH (data : EtaLocalStructureData M) : IsGSNNCH M := by
  intro N hN
  exact data.isGSNNCHAt N hN

end EtaLocalStructureData

/-- Once the explicit neighboring operators `η_{k,h}` have been assembled into
`EtaLocalStructureData`, the global commuting-form property follows
immediately. -/
theorem hasCommutingForm_of_etaLocalStructure {M : MPOTensor d D}
    (hEta : EtaLocalStructureData M) : HasCommutingForm M := by
  intro N hN
  exact ⟨hEta.bondData.toCommutingFormData (N := N) hN, hEta.realizes_mpo N hN⟩

/-- The explicit local `η`-structure also yields the GSNNCH condition. -/
theorem isGSNNCH_of_etaLocalStructure {M : MPOTensor d D}
    (hEta : EtaLocalStructureData M) : IsGSNNCH M :=
  isGSNNCH_of_hasCommutingForm (hasCommutingForm_of_etaLocalStructure hEta)

end MPOTensor
