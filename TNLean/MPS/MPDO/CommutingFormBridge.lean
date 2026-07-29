/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorBondPairwise

/-!
# Local-to-global commuting-form data

This file defines the eta-local structure used to express the simple-MPDO
commuting product form of arXiv:1606.00608, Appendix C.2. Conditional on a
physical-sector factorization with positive neighboring operators,
`PhysicalSectorFactorization.etaLocalStructureData` gives one positive two-site
bond whose translates commute and whose ordered product realizes every finite
chain.

For an injective tensor `K` satisfying SAL, the inverse-map sector construction
gives a coherently positive physical-sector factorization satisfying
\[
  \widetilde\sigma^{(N)}(K)
    = \bigoplus_{k_1,\ldots,k_N}\bigotimes_{n=1}^N \eta_{k_n,k_{n+1}}.
\]
Consequently, `MPOTensor.nonempty_etaLocalStructureData_of_isSAL` constructs
the eta-local structure from injectivity and SAL alone. Zero correlation length
is not used in Proposition C.8; it enters only in the later
single-bond commuting-form-with-ZCL and RFP consequences. The source GSNNCH
definition is recorded in `GSNNCHData`. Later modules prove generic assembly
of orthogonal sectors with natural multiplicities and a BNT construction from
projector-selection and sectorwise-SAL data. What remains open is an exact
capstone from the five printed blockwise identities of Proposition `prop3to4`
to that assembled family. See
docs/paper-gaps/cpsv16_gsnnch_sector_decomposition.tex.

## Main declarations

* `MPOTensor.TranslationInvariantBondData`
* `MPOTensor.EtaLocalStructureData`
* `MPOTensor.hasCommutingForm_of_etaLocalStructure`
* `MPOTensor.hasCommutingBondProduct_of_etaLocalStructure`
* `MPOTensor.hasGSNNCHForm_of_etaLocalStructure`
* `MPOTensor.hasCommutingBondProductWithZCL_of_etaLocalStructure`

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608, Appendix C.2, Proposition C.8
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

namespace PhysicalSectorFactorization

variable {K : MPOTensor d D}

/-- A physical-sector factorization with positive neighboring operators
determines a positive translation-invariant bond whose cyclic translates
commute at every chain length.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1589--1593. -/
noncomputable def translationInvariantBondData
    (F : PhysicalSectorFactorization K)
    (hη : ∀ k h, (F.neighboringOperator k h).PosSemidef) :
    TranslationInvariantBondData d where
  bond := F.physicalBond
  bond_pos := F.physicalBond_pos hη
  bond_comm := fun hN i j ↦ F.physicalBond_pairwise_comm hN i j

end PhysicalSectorFactorization

/-- The explicit `η`-local structure needed for Appendix C.2 after the
sector-local neighboring operators have been assembled in the original tensor
coordinates.

Concretely, this structure stores the single translation-invariant bond extracted
from the local simple-MPDO analysis, together with proofs that it realizes the
finite-chain MPO operators. This is stronger than `HasCommutingForm M`, since
it requires one bond that works for every chain length rather than a separate
commuting-form witness at each length. For every injective tensor satisfying
SAL, `MPOTensor.nonempty_etaLocalStructureData_of_isSAL` constructs this
structure from the inverse-map sector factorization and its coherently positive
neighboring operators. No zero-correlation-length hypothesis is required.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8, lines 1569--1594. -/
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

/-- The translated nearest-neighbor bonds carried by the `η`-local structure
commute at every finite chain length.

Source: arXiv:1606.00608, Appendix C.2, Proposition 3to4, lines 1571--1593:
the assembled two-site bonds \(B_{n,n+1}\) commute. -/
theorem formAt_bondAt_comm (data : EtaLocalStructureData M) (N : ℕ) (hN : 2 ≤ N)
    (i j : Fin N) :
    (data.formAt N hN).bondAt i * (data.formAt N hN).bondAt j =
      (data.formAt N hN).bondAt j * (data.formAt N hN).bondAt i :=
  (data.formAt N hN).bondAt_comm i j

/-- The `η`-local structure gives the source product form
\(\sigma^{(N)}(\mathcal K) \propto \prod_n B_{n,n+1}\) at every finite chain
length.

Source: arXiv:1606.00608, Appendix C.2, Proposition 3to4, lines 1571--1593:
after assembling the neighboring operators, the MPDO is a positive scalar
multiple of the product of the translated nearest-neighbor bonds. -/
theorem exists_positive_scalar_mpo_eq_product
    (data : EtaLocalStructureData M) (N : ℕ) (hN : 2 ≤ N) :
    ∃ c : ℝ, 0 < c ∧ mpo M N = (c : ℂ) • (data.formAt N hN).product :=
  data.formAt_realizes N hN

/-- At a fixed chain length, the `η`-local structure gives precisely the
positive commuting nearest-neighbor product form appearing in Proposition C.8
of arXiv:1606.00608.

Source: arXiv:1606.00608, Appendix C.2, Proposition 3to4, lines 1571--1593:
the MPDO has the form \(\sigma^{(N)}(\mathcal K) \propto \prod_n B_{n,n+1}\),
where the nearest-neighbor factors are positive and commute. -/
theorem positive_commuting_product_form
    (data : EtaLocalStructureData M) (N : ℕ) (hN : 2 ≤ N) :
    (data.formAt N hN).bond.PosSemidef ∧
      (∀ i j : Fin N,
        (data.formAt N hN).bondAt i * (data.formAt N hN).bondAt j =
          (data.formAt N hN).bondAt j * (data.formAt N hN).bondAt i) ∧
      ∃ c : ℝ, 0 < c ∧ mpo M N = (c : ℂ) • (data.formAt N hN).product :=
  ⟨(data.formAt N hN).bond_pos, data.formAt_bondAt_comm N hN,
    data.exists_positive_scalar_mpo_eq_product N hN⟩

/-- The chain-level single-bond commuting-product witness induced by the
local `η`-structure at a fixed chain length. -/
theorem hasCommutingBondProductAt
    (data : EtaLocalStructureData M) (N : ℕ) (hN : 2 ≤ N) :
    HasCommutingBondProductAt (mpo M N) :=
  (data.formAt N hN).hasCommutingBondProductAt_of_realizes
    (data.formAt_realizes N hN)

/-- The explicit `η`-local structure yields a single-bond commuting-product
witness on every finite chain. -/
theorem hasCommutingBondProduct (data : EtaLocalStructureData M) :
    HasCommutingBondProduct M := fun N hN ↦
  data.hasCommutingBondProductAt N hN

/-- The explicit `η`-local structure yields the one-sector instance of the
source GSNNCH sector form on every finite chain. -/
theorem hasGSNNCHForm (data : EtaLocalStructureData M) : HasGSNNCHForm M :=
  hasGSNNCHForm_of_hasCommutingBondProduct data.hasCommutingBondProduct

/-- The explicit `η`-local structure yields the global commuting-form property. -/
theorem hasCommutingForm (data : EtaLocalStructureData M) : HasCommutingForm M :=
  fun N hN => ⟨data.formAt N hN, data.formAt_realizes N hN⟩

/-- The explicit `η`-local structure, together with ZCL, gives the
single-bond commuting-product condition with ZCL.

Source: arXiv:1606.00608, Appendix C.2, Proposition 3to4, lines 1571--1593:
the assembled neighboring operators give a commuting nearest-neighbor product
form.

**Scope restriction (single-bond presentation):** This file proves only the
one-sector presentation. Later modules assemble supplied orthogonal sectors
with natural multiplicities, but no theorem derives that family from exactly
the five printed blockwise identities of Proposition `prop3to4`. See
docs/paper-gaps/cpsv16_gsnnch_sector_decomposition.tex. -/
theorem hasCommutingBondProductWithZCL
    (data : EtaLocalStructureData M) (hZCL : IsZCL M) :
    HasCommutingBondProductWithZCL M :=
  (hasCommutingBondProductWithZCL_iff_hasCommutingForm_and_isZCL M).2
    ⟨data.hasCommutingForm, hZCL⟩

end EtaLocalStructureData

/-- Once the explicit neighboring operators `η_{k,h}` have been assembled into
`EtaLocalStructureData`, the global commuting-form property follows
immediately. -/
theorem hasCommutingForm_of_etaLocalStructure {M : MPOTensor d D}
    (hEta : EtaLocalStructureData M) : HasCommutingForm M :=
  hEta.hasCommutingForm

/-- The explicit local `η`-structure also yields the single-bond
commuting-product condition.

**Scope restriction (single-bond presentation):** See
docs/paper-gaps/cpsv16_gsnnch_sector_decomposition.tex. -/
theorem hasCommutingBondProduct_of_etaLocalStructure {M : MPOTensor d D}
    (hEta : EtaLocalStructureData M) : HasCommutingBondProduct M :=
  hEta.hasCommutingBondProduct

/-- The explicit local `η`-structure gives the one-sector instance of the
source GSNNCH sector form. -/
theorem hasGSNNCHForm_of_etaLocalStructure {M : MPOTensor d D}
    (hEta : EtaLocalStructureData M) : HasGSNNCHForm M :=
  hEta.hasGSNNCHForm

/-- Once the explicit local `η`-structure has been assembled, adding ZCL gives
the single-bond commuting-product condition with ZCL.

**Scope restriction (single-bond presentation):** See
docs/paper-gaps/cpsv16_gsnnch_sector_decomposition.tex. -/
theorem hasCommutingBondProductWithZCL_of_etaLocalStructure
    {M : MPOTensor d D} (hEta : EtaLocalStructureData M) (hZCL : IsZCL M) :
    HasCommutingBondProductWithZCL M :=
  hEta.hasCommutingBondProductWithZCL hZCL

end MPOTensor
