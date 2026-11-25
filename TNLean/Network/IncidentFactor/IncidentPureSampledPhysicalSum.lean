/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Compression.SourceSampling.ExteriorFactor
import TNLean.Network.IncidentFactor.IncidentSampledPhysicalFactor

/-!
# Replacing sampled party factors by their incident constructions

In the sampled physical sum of the source-replaced circuit on a product input, each local factor
of an original party is constructed from the two incident gate-label assignments and the
restriction of the common sample assignment to the slots incident to that party. The outer
branch sums and the joint sample sum remain the original sums, and neither incident labels nor
samples are extended to unrelated positions. The exterior party contributes the partial trace of
its readout as a separate tensor factor, and the exterior scalar is retained without
cancellation.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267, 351–381 and 565–588.
-/

noncomputable section

open Matrix ManyBody
open scoped Kronecker ComplexConjugate

namespace QuantumCircuit.Party.SourceCircuit

variable {P : Type} [DecidableEq P] [Fintype P]

/-- The configurations of a family of bases on the blocks of all parties: the configuration of
the exterior block and the configurations of the blocks of the original parties. -/
def exteriorConfigEquiv (Phys : Option {_p : P // true = true} → Type) :
    (∀ q, Phys q) ≃ Phys none × ∀ p : P, Phys (some ⟨p, rfl⟩) where
  toFun x := (x none, fun p ↦ x (some ⟨p, rfl⟩))
  invFun y q := match q with
    | none => y.1
    | some p => y.2 p.1
  left_inv x := by
    funext q
    rcases q with _ | ⟨p, hp⟩ <;> rfl
  right_inv _ := rfl

/-- A product of local matrices on the blocks of all parties with a prescribed exterior factor is
that factor times the product over the original parties. -/
private theorem piKronecker_update_none_apply {Phys : Option {_p : P // true = true} → Type}
    (f : ∀ q, Matrix (Phys q) (Phys q) ℂ) (C : Matrix (Phys none) (Phys none) ℂ)
    (x y : ∀ q, Phys q) :
    piKronecker (Function.update f none C) x y =
      C (x none) (y none) * ∏ p : P, f (some ⟨p, rfl⟩) (x (some ⟨p, rfl⟩)) (y (some ⟨p, rfl⟩)) := by
  rw [piKronecker_apply, Fintype.prod_option]
  simp only [Function.update_self, ne_eq, reduceCtorEq, not_false_eq_true,
    Function.update_of_ne]
  exact congrArg _ (Fintype.prod_equiv (Equiv.subtypeUnivEquiv (fun _ ↦ rfl)) _ _ fun _ ↦ rfl)

variable {X Y : P → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)] {Phys Env : Option {_p : P // true = true} → Type}
  [∀ q, Fintype (Env q)]

/-- **The sampled physical density on a product input is the sum of products of the incident
physical matrices.** For each fixed array of Gaussian samples and every product readout `K` on
the blocks of all parties, the density is `(1/k)^n |emptyGateScalar|²` times the partial trace
`partialTraceRight (K none * (K none)ᴴ)` of the exterior readout, tensored with the double branch
sum of the sample sums of the products over the original parties of the matrices constructed
from the incident labels and incident samples. The sampling coefficient and the exterior scalar
are unchanged, including when they vanish or the original party type is empty. Source:
polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267, 351–381 and 565–588. -/
theorem physicalSourceReplacedDensity_pure_sampled_eq_scalar_smul_incidentPhysicalSum
    (K : ∀ q, Matrix (Phys q × Env q) (blockSystem (affectedOwner fun _ ↦ true) Y q) ℂ)
    (w : SourceCircuit X Y) (φ : ∀ s, EuclideanSpace ℂ (X s)) (k : ℕ)
    (lam : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Fin (min (w.sourceDims e).1 (w.sourceDims e).2) → ℝ)
    (E : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.leftBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (F : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.rightBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (ω : SourceGaussianSamples w k) :
    let e := Equiv.arrowProdEquivProdArrow (Option {_p : P // true = true}) Phys Env
    let b := blockConfigEquiv (affectedOwner fun _ ↦ true) Y
    let ψ : EuclideanSpace ℂ (Config X) := WithLp.toLp 2 (productVector fun p x ↦ φ p x)
    let M := fun (ξ ζ : Choices (fun _ ↦ true) w)
      (a : Fin (partialSlots (fun _ ↦ true) w).length → Fin k) (p : P) ↦
      incidentSampledPhysicalFactor K w φ k lam E F p (originalGateLabelsAtOfAllChoices w p ξ)
        (originalGateLabelsAtOfAllChoices w p ζ) ω
        (fun i ↦ a ((allSourceSlotEquiv w).symm (partialSlotEquiv
          (fun t ↦ partySelector (some ⟨p, rfl⟩) (affectedOwner (fun _ ↦ true) t)) w i).1))
    physicalSourceReplacedDensity w (fun s ξ ζ ↦ sampledSourceMatrix w k lam E F s ξ ζ ω)
        ((piKronecker K).submatrix e.symm b.symm) (euclideanOuterProduct ψ ψ) =
      (((k : ℂ)⁻¹ ^ (partialSlots (fun _ ↦ true) w).length) *
        (w.emptyGateScalar * conj w.emptyGateScalar)) •
        reindex (exteriorConfigEquiv Phys).symm (exteriorConfigEquiv Phys).symm
          (partialTraceRight (K none * (K none)ᴴ) ⊗ₖ
            ∑ ξ, ∑ ζ, (coefficient (fun _ ↦ true) w ξ * conj (coefficient (fun _ ↦ true) w ζ)) •
              ∑ a, piKronecker (M ξ ζ a)) := by
  intro e b ψ M
  refine (physicalSourceReplacedDensity_pure_sampled_eq_scalar_smul_physicalSum w K φ k lam E F
    ω).trans (congrArg (_ • ·) ?_)
  ext x y
  simp only [reindex_apply, submatrix_apply, kroneckerMap_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, piKronecker_update_none_apply,
    Equiv.symm_symm, exteriorConfigEquiv, Equiv.coe_fn_mk]
  refine Finset.sum_congr rfl fun ξ _ ↦ Finset.sum_congr rfl fun ζ _ ↦
    Finset.sum_congr rfl fun a _ ↦ ?_
  rw [mul_left_comm, piKronecker_apply]
  refine congrArg (_ * ·) (congrArg (_ * ·) (Finset.prod_congr rfl fun p _ ↦ ?_))
  exact congrFun (congrFun (sampledPhysicalFactor_eq_incidentSampledPhysicalFactor K w φ k lam
    E F p ξ ζ ω a) _) _

end QuantumCircuit.Party.SourceCircuit
