/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.RFP
import TNLean.MPS.ParentHamiltonian.Defs

/-!
# Commuting-form and GSNNCH data for simple MPDOs

This file records the commuting-form side of the simple MPDO story from
arXiv:1606.00608 §4.4 and Appendix C.2.

For an `N`-site operator `ρ`, a commuting-form witness consists of a positive
semidefinite two-site matrix `B`, together with proofs that its translated
copies on the periodic chain pairwise commute and that their product
reproduces `ρ` up to a positive scalar. This is the projector-limit version of
the GSNNCH definition, source label `defrhoNComm`. The actual entropy-side derivation
`SAL ⟹ HasCommutingForm` is not yet formalized here; it is isolated as the
upstream missing theorem recorded in the accompanying audit for issue #782.

## Main declarations

* `MPOTensor.ChainOperator`
* `MPOTensor.AgreesOutsideWindow`
* `MPOTensor.embedLocalOperator`
* `MPOTensor.CommutingFormData`
* `MPOTensor.HasCommutingForm`
* `MPOTensor.GSNNCHData`
* `MPOTensor.IsGSNNCH`
* `MPOTensor.isGSNNCH_iff_hasCommutingForm`
* `MPOTensor.IsGSNNCHWithZCL`

## References

* [CPGSV17] arXiv:1606.00608, source labels `defrhoNComm` and `propsimple`
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix Finset

namespace MPOTensor

attribute [local instance] Classical.decEq Classical.propDecidable

variable {d D N : ℕ}

/-- The matrix algebra on an `N`-site chain with local dimension `d`. -/
abbrev ChainOperator (d N : ℕ) :=
  Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ

/-- Two chain configurations agree outside the translated length-`L` window
starting at `i` when replacing the window of `τ` by that of `σ` recovers `σ`.
This is the matrix-entry side condition used to embed an `L`-site operator into
an `N`-site periodic chain. -/
def AgreesOutsideWindow (L : ℕ) {N : ℕ} (hLN : L ≤ N) (i : Fin N)
    (σ τ : Fin N → Fin d) : Prop :=
  MPSTensor.replaceWindow L hLN i τ (MPSTensor.extractWindow L i σ) = σ

/-- Embed an `L`-site operator into the periodic `N`-site chain at position `i`,
acting as the given local matrix on the window and as the identity on the
complement. -/
noncomputable def embedLocalOperator (L N : ℕ) (hLN : L ≤ N) (i : Fin N)
    (B : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) : ChainOperator d N := by
  classical
  exact Matrix.of fun σ τ =>
    if AgreesOutsideWindow (d := d) L hLN i σ τ then
      B (MPSTensor.extractWindow L i σ) (MPSTensor.extractWindow L i τ)
    else 0

@[simp] theorem embedLocalOperator_apply (L N : ℕ) (hLN : L ≤ N) (i : Fin N)
    (B : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) (σ τ : Fin N → Fin d) :
    embedLocalOperator (d := d) L N hLN i B σ τ =
      if AgreesOutsideWindow (d := d) L hLN i σ τ then
        B (MPSTensor.extractWindow L i σ) (MPSTensor.extractWindow L i τ)
      else 0 := by
  classical
  rfl

/-- Chain-level commuting-form data for source label `propsimple`.

The current record stores the translation-invariant two-site factor `B` together
with chain-level commutativity of its translated copies. The intended
nearest-neighbor support is encoded by `embedLocalOperator`; no separate
factorization API is required downstream. -/
structure CommutingFormData (d N : ℕ) where
  /-- The theorem only makes sense for genuine nearest-neighbor chains. -/
  hN : 2 ≤ N
  /-- The positive semidefinite two-site factor `B`. -/
  bond : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ
  /-- Positivity of the local factor. -/
  bond_pos : Matrix.PosSemidef bond
  /-- Pairwise commutativity of the translated factors on the `N`-site chain. -/
  bond_comm :
    ∀ i j : Fin N,
      embedLocalOperator (d := d) 2 N hN i bond
        * embedLocalOperator (d := d) 2 N hN j bond
      = embedLocalOperator (d := d) 2 N hN j bond
          * embedLocalOperator (d := d) 2 N hN i bond

namespace CommutingFormData

variable {N : ℕ}

/-- The translated copy of the local bond operator at site `i`. -/
noncomputable def bondAt (data : CommutingFormData d N) (i : Fin N) :
    ChainOperator d N :=
  embedLocalOperator (d := d) 2 N data.hN i data.bond

@[simp] theorem bondAt_apply (data : CommutingFormData d N) (i : Fin N)
    (σ τ : Fin N → Fin d) :
    data.bondAt i σ τ =
      if AgreesOutsideWindow (d := d) 2 data.hN i σ τ then
        data.bond (MPSTensor.extractWindow 2 i σ) (MPSTensor.extractWindow 2 i τ)
      else 0 := by
  classical
  rfl

theorem bondAt_comm (data : CommutingFormData d N) (i j : Fin N) :
    data.bondAt i * data.bondAt j = data.bondAt j * data.bondAt i :=
  data.bond_comm i j

/-- The commuting product `∏_i B_{i,i+1}` on the periodic chain, taken in the
natural order of `Fin N`. -/
noncomputable def product (data : CommutingFormData d N) : ChainOperator d N :=
  (List.ofFn fun i : Fin N => data.bondAt i).prod

/-- The commuting-form datum realizes `ρ` when `ρ` equals the commuting product
up to a positive real normalization factor. -/
def Realizes (data : CommutingFormData d N) (ρ : ChainOperator d N) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ρ = (c : ℂ) • data.product

end CommutingFormData

/-- Global commuting-form property for an MPO tensor: each finite chain of
length at least `2` admits a commuting-form witness for the corresponding MPO
operator. -/
def HasCommutingForm (M : MPOTensor d D) : Prop :=
  ∀ N : ℕ, 2 ≤ N →
    ∃ data : CommutingFormData d N, data.Realizes (mpo M N)

/-- A GSNNCH witness at chain length `N`: a commuting-form datum together with
its positive normalization constant.

This records source label `defrhoNComm` in the equivalent positive-operator form
`ρ⁽ᴺ⁾ = c ∏ᵢ B_{i,i+1}`, where `c > 0` and the translated bond operators
commute pairwise. The paper's exponential form is recovered by taking
`B_{i,i+1} = e^{-h_{i,i+1}}` or, more generally, by the projector-limit
convention explained immediately after `defrhoNComm`. -/
structure GSNNCHData (d N : ℕ) where
  /-- The underlying commuting-form data. -/
  form : CommutingFormData d N
  /-- Positive normalization constant. -/
  normalization : ℝ
  /-- The normalization constant is strictly positive. -/
  normalization_pos : 0 < normalization

namespace GSNNCHData

variable {N : ℕ}

/-- The chain operator represented by a GSNNCH witness. -/
noncomputable def state (data : GSNNCHData d N) : ChainOperator d N :=
  (data.normalization : ℂ) • data.form.product

/-- Every GSNNCH witness gives back the underlying commuting-form realization. -/
theorem realizes_form_state (data : GSNNCHData d N) :
    data.form.Realizes data.state := by
  refine ⟨data.normalization, data.normalization_pos, ?_⟩
  rfl

end GSNNCHData

/-- Chain-level GSNNCH predicate. -/
def IsGSNNCHAt {d N : ℕ} (ρ : ChainOperator d N) : Prop :=
  ∃ data : GSNNCHData d N, ρ = data.state

/-- Global GSNNCH predicate for an MPO tensor: every chain length `N ≥ 2`
produces a GSNNCH operator in the sense of source label `defrhoNComm`. -/
def IsGSNNCH (M : MPOTensor d D) : Prop :=
  ∀ N : ℕ, 2 ≤ N → IsGSNNCHAt (mpo M N)

namespace CommutingFormData

variable {N : ℕ}

/-- A commuting-form witness together with a positive normalization constant
induces GSNNCH data. -/
def toGSNNCHData (data : CommutingFormData d N) (c : ℝ) (hc : 0 < c) :
    GSNNCHData d N where
  form := data
  normalization := c
  normalization_pos := hc

/-- Any commuting-form realization yields a GSNNCH witness for the same chain
operator. -/
theorem isGSNNCHAt_of_realizes (data : CommutingFormData d N)
    {ρ : ChainOperator d N} (hρ : data.Realizes ρ) : IsGSNNCHAt ρ := by
  rcases hρ with ⟨c, hc, hρ⟩
  refine ⟨data.toGSNNCHData c hc, ?_⟩
  simpa [GSNNCHData.state] using hρ

end CommutingFormData

theorem isGSNNCHAt_iff_exists_commutingForm {d N : ℕ} (ρ : ChainOperator d N) :
    IsGSNNCHAt ρ ↔ ∃ data : CommutingFormData d N, data.Realizes ρ := by
  constructor
  · rintro ⟨data, hρ⟩
    refine ⟨data.form, ?_⟩
    rw [hρ]
    exact data.realizes_form_state
  · rintro ⟨data, hρ⟩
    exact data.isGSNNCHAt_of_realizes hρ

theorem isGSNNCH_of_hasCommutingForm {M : MPOTensor d D}
    (hM : HasCommutingForm M) : IsGSNNCH M := by
  intro N hN
  obtain ⟨data, hdata⟩ := hM N hN
  exact data.isGSNNCHAt_of_realizes hdata

theorem hasCommutingForm_of_isGSNNCH {M : MPOTensor d D}
    (hM : IsGSNNCH M) : HasCommutingForm M := by
  intro N hN
  rcases (isGSNNCHAt_iff_exists_commutingForm (mpo M N)).mp (hM N hN) with
    ⟨data, hdata⟩
  exact ⟨data, hdata⟩

theorem isGSNNCH_iff_hasCommutingForm (M : MPOTensor d D) :
    IsGSNNCH M ↔ HasCommutingForm M := by
  constructor
  · exact hasCommutingForm_of_isGSNNCH
  · exact isGSNNCH_of_hasCommutingForm

/-- The GSNNCH-with-zero-correlation-length branch of the simple-MPDO
equivalence, matching source label `thm:main-simple`. -/
def IsGSNNCHWithZCL (M : MPOTensor d D) : Prop :=
  IsGSNNCH M ∧ IsZCL M

theorem isGSNNCHWithZCL_iff_hasCommutingForm_and_isZCL (M : MPOTensor d D) :
    IsGSNNCHWithZCL M ↔ HasCommutingForm M ∧ IsZCL M := by
  rw [IsGSNNCHWithZCL, isGSNNCH_iff_hasCommutingForm]

end MPOTensor
