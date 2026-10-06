/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentBondNetwork
import TNLean.PEPS.TorusProjectorExtraction

/-!
# Coherent coefficients with independently sized bonds

Regrouping the actual site incidence coordinates gives one head/tail pair per
labelled edge. Products of arbitrary edge matrix functionals then act on actual
physical vectors. For semi-regular edge representations, the source's trace
pairings extract every coefficient of a coherent bond-product expansion.

All edge alphabets and representations may differ. No assumption on graph
geometry, parallel edges, self edges, or unitarity is made.
Source: SCP10, arXiv:1001.3807, Lemma 4.6 and Theorem 5.5, lines 1488–1513.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS.DependentBondNetwork

variable {Vertex Edge : Type*} (tail head : Edge → Vertex) (D : Edge → Type*)

/-- Regroup all physical incidence coordinates into head/tail pairs per edge. -/
def siteBondEquiv : ((v : Vertex) → LocalConfig tail head D v) ≃ ((e : Edge) → D e × D e) :=
  (endpointSiteEquiv tail head D).symm.trans (endpointPairEquiv D)

/-- The physical coefficient permutation from sites to the actual labelled bonds. -/
def bondRegrouping : (((v : Vertex) → LocalConfig tail head D v) → ℂ) ≃ₗ[ℂ]
    (((e : Edge) → D e × D e) → ℂ) :=
  LinearEquiv.piCongrLeft' ℂ (fun _ => ℂ) (siteBondEquiv tail head D)

@[simp]
theorem bondRegrouping_apply
    (ψ : ((v : Vertex) → LocalConfig tail head D v) → ℂ) (β : (e : Edge) → D e × D e) :
    bondRegrouping tail head D ψ β = ψ ((siteBondEquiv tail head D).symm β) := rfl

variable [Fintype Edge]

/-- The physical product of separately assigned edge matrices, with head rows. -/
def matrixBondProduct (B : (e : Edge) → Matrix (D e) (D e) ℂ)
    (σ : (v : Vertex) → LocalConfig tail head D v) : ℂ :=
  ∏ e, B e (siteBondEquiv tail head D σ e).1 (siteBondEquiv tail head D σ e).2

/-- In regrouped coordinates a bond product is the literal product of matrix entries. -/
@[simp]
theorem bondRegrouping_matrixBondProduct (B : (e : Edge) → Matrix (D e) (D e) ℂ)
    (β : (e : Edge) → D e × D e) :
    bondRegrouping tail head D (matrixBondProduct tail head D B) β =
      ∏ e, B e (β e).1 (β e).2 := by
  simp only [bondRegrouping_apply, matrixBondProduct, Equiv.apply_symm_apply]

variable [DecidableEq Edge] [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]

/-- The product of arbitrary edge functionals on the actual physical coefficients. -/
def outputBondPairing (K : (e : Edge) → Matrix (D e) (D e) ℂ →ₗ[ℂ] ℂ) :
    (((v : Vertex) → LocalConfig tail head D v) → ℂ) →ₗ[ℂ] ℂ :=
  Fintype.linearCombination ℂ (fun β : (e : Edge) → D e × D e =>
    ∏ e, K e (Matrix.single (β e).1 (β e).2 1)) ∘ₗ
      (bondRegrouping tail head D).toLinearMap

/-- Pairing a matrix product factors over all independently sized labelled edges. -/
theorem outputBondPairing_matrixBondProduct
    (K : (e : Edge) → Matrix (D e) (D e) ℂ →ₗ[ℂ] ℂ)
    (B : (e : Edge) → Matrix (D e) (D e) ℂ) :
    outputBondPairing tail head D K (matrixBondProduct tail head D B) =
      ∏ e, K e (B e) := by
  simp only [outputBondPairing, LinearMap.comp_apply, Fintype.linearCombination_apply,
    LinearEquiv.coe_coe, bondRegrouping_matrixBondProduct, smul_eq_mul,
    ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (e : Edge) (b : D e × D e) =>
    B e b.1 b.2 * K e (Matrix.single b.1 b.2 1))]
  apply Finset.prod_congr rfl
  intro e _
  rw [matrixLinearFunctional_eq_sum, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

variable {G : Type*} [Group G] [Fintype G]

/-- One independent group-representation matrix per actual edge. -/
def representationBondProduct (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (p : Edge → G) : ((v : Vertex) → LocalConfig tail head D v) → ℂ :=
  matrixBondProduct tail head D (fun e => U e (p e))

/-- Simultaneous trace-dual extraction for independently semi-regular edges. -/
def bondCoefficientExtraction (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (p : Edge → G) : (((v : Vertex) → LocalConfig tail head D v) → ℂ) →ₗ[ℂ] ℂ :=
  outputBondPairing tail head D (fun e => torusDeltaPairing (U e) (p e))

open Classical in
/-- Trace-dual pairing distinguishes complete bond configurations, including
labels on parallel edges. Source: SCP10, Lemma 4.6. -/
theorem bondCoefficientExtraction_bondProduct
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (p q : Edge → G) :
    bondCoefficientExtraction tail head D U p (representationBondProduct tail head D U q) =
      if p = q then 1 else 0 := by
  rw [bondCoefficientExtraction, representationBondProduct, outputBondPairing_matrixBondProduct]
  simp only [torusDeltaPairing_apply_rep _ (hU _), Fintype.prod_boole, ← funext_iff]

/-- Applying the same trace-dual functional to a coherent sum extracts its
coefficient, without any termwise inference about the labels. -/
theorem bondCoefficientExtraction_sum
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (c : (Edge → G) → ℂ) (p : Edge → G) :
    bondCoefficientExtraction tail head D U p
      (∑ q, c q • representationBondProduct tail head D U q) = c p := by
  classical
  simp [map_sum, bondCoefficientExtraction_bondProduct tail head D U hU]

/-- Equality of coherent sums is equality of their trace-dual coefficients. -/
theorem sum_representationBondProduct_eq_iff
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (c d : (Edge → G) → ℂ) :
    (∑ q, c q • representationBondProduct tail head D U q) =
      (∑ q, d q • representationBondProduct tail head D U q) ↔ c = d := by
  constructor
  · intro h
    funext p
    have hp := congrArg (bondCoefficientExtraction tail head D U p) h
    simpa only [bondCoefficientExtraction_sum tail head D U hU] using hp
  · rintro rfl
    rfl

end TNLean.PEPS.DependentBondNetwork
