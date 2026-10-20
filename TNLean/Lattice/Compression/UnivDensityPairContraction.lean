/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.DistributedOperatorContraction
import TNLean.Lattice.Compression.ActiveGateLabelSum
import TNLean.Lattice.Compression.WeightedGateLabelPairSum

/-! # The density contraction over all original gate occurrences

When all recorded gate occurrences are active, the contraction of the ordered
ket and bra tensors equals the double sum over their original label functions.
The local matrices receive their incident ket and bra labels independently and
one common sample assignment restricted to each party. A gatewise weight occurs
once per original occurrence, and the exterior scalar stays outside the network.

No coefficient is cancelled. Empty label types, zero weights, zero sample size
and empty families are included. The physical matrix indices are arbitrary.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–588.
-/

namespace TNLean.PEPS.Approximation.DistributedOperatorContraction
open scoped ComplexConjugate
variable {Party G : Type} [Fintype Party] [Fintype G]
variable {Ket Bra : G → Type} [∀ g, Fintype (Ket g)] [∀ g, Fintype (Bra g)]
variable {Out In : Party → Type}

open Classical in
/-- Evaluate the density network using independent original ket and bra label
functions and the same shared samples at every incident endpoint.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–588. -/
theorem contractedOperator_densityPair_univ_eq_double_sum
    (participants : G → Finset Party) (root : G → Party)
    (hroot : ∀ g ∈ (Finset.univ : Finset G), root g ∈ participants g)
    (k : ℕ) (a : (g : G) → Ket g → ℂ) (b : (g : G) → Bra g → ℂ)
    (w : G → ℂ) (γ : ℂ)
    (T : (p : Party) → GateLabelsAt (Finset.univ : Finset G) participants Ket p →
      GateLabelsAt (Finset.univ : Finset G) participants Bra p →
      (SampleAt (Finset.univ : Finset G) participants p → Fin k) →
        Matrix (Out p) (In p) ℂ) :
    γ • contractedOperator (Finset.univ : Finset G) participants root hroot
        (fun g ↦ Ket g × Bra g) k (densityPairCoefficient Ket Bra a b w)
        (fun p ξζ j ↦ T p (fun h ↦ (ξζ h).1) (fun h ↦ (ξζ h).2) j) =
      ((∏ g : G, w g) * γ) •
        ∑ η : (g : G) → Ket g, ∑ θ : (g : G) → Bra g,
          (∏ g : G, a g (η g) * conj (b g (θ g))) •
            ∑ j : Sample (Finset.univ : Finset G) participants → Fin k,
              dependentPhysicalProductFamilyMatrix (fun p ↦
                T p (restrictGates (Finset.univ : Finset G) participants Ket
                    (fun h ↦ η h.1) p)
                  (restrictGates (Finset.univ : Finset G) participants Bra
                    (fun h ↦ θ h.1) p)
                  (restrictSamples (Finset.univ : Finset G) participants k j p)) := by
  let pairedT (p : Party)
      (ξζ : GateLabelsAt (Finset.univ : Finset G) participants (fun g ↦ Ket g × Bra g) p)
      (j : SampleAt (Finset.univ : Finset G) participants p → Fin k) :
      Matrix (Out p) (In p) ℂ :=
    T p (fun h ↦ (ξζ h).1) (fun h ↦ (ξζ h).2) j
  let K (η : (g : G) → Ket g) (θ : (g : G) → Bra g) :
      Matrix ((p : Party) → Out p) ((p : Party) → In p) ℂ :=
    ∑ j : Sample (Finset.univ : Finset G) participants → Fin k,
      dependentPhysicalProductFamilyMatrix (fun p ↦
        T p (restrictGates (Finset.univ : Finset G) participants Ket (fun h ↦ η h.1) p)
          (restrictGates (Finset.univ : Finset G) participants Bra (fun h ↦ θ h.1) p)
          (restrictSamples (Finset.univ : Finset G) participants k j p))
  have hCoefficient (ξζ : GateLabels (Finset.univ : Finset G) (fun g ↦ Ket g × Bra g)) :
      (∏ g : G, w g * a g (ξζ ⟨g, Finset.mem_univ g⟩).1 *
        conj (b g (ξζ ⟨g, Finset.mem_univ g⟩).2)) =
      ∏ h : ActiveGate (Finset.univ : Finset G),
        w h.1 * a h.1 (ξζ h).1 * conj (b h.1 (ξζ h).2) :=
    (Equiv.subtypeUnivEquiv (fun g : G ↦ Finset.mem_univ g)).symm.prod_comp
      (fun h ↦ w h.1 * a h.1 (ξζ h).1 * conj (b h.1 (ξζ h).2))
  have hReindex := sum_eq_sum_gateLabels_univ
    (fun ξζ : (g : G) → Ket g × Bra g ↦
      (∏ g : G, w g * a g (ξζ g).1 * conj (b g (ξζ g).2)) •
        K (fun g ↦ (ξζ g).1) (fun g ↦ (ξζ g).2))
  have hReindex' :
      (∑ ξζ : (g : G) → Ket g × Bra g,
        (∏ g : G, w g * a g (ξζ g).1 * conj (b g (ξζ g).2)) •
          K (fun g ↦ (ξζ g).1) (fun g ↦ (ξζ g).2)) =
      ∑ ξζ : GateLabels (Finset.univ : Finset G) (fun g ↦ Ket g × Bra g),
        (∏ h : ActiveGate (Finset.univ : Finset G),
          w h.1 * a h.1 (ξζ h).1 * conj (b h.1 (ξζ h).2)) •
          ∑ j : Sample (Finset.univ : Finset G) participants → Fin k,
            dependentPhysicalProductFamilyMatrix (fun p ↦
              pairedT p (restrictGates (Finset.univ : Finset G) participants
                (fun g ↦ Ket g × Bra g) ξζ p)
                (restrictSamples (Finset.univ : Finset G) participants k j p)) := by
    refine hReindex.trans ?_
    apply Finset.sum_congr rfl
    intro ξζ _
    rw [hCoefficient ξζ]
    rfl
  have hDensity := contractedOperator_densityPair_eq
    (gates := (Finset.univ : Finset G)) (participants := participants)
    (root := root) (hroot := hroot) (Ket := Ket) (Bra := Bra) (k := k) a b w pairedT
  have hNetwork := hDensity.trans hReindex'.symm
  have hAveraging := weighted_sum_gateLabels_eq_exterior_smul_orderedGateLabelPairs w γ a b K
  have h := (congrArg (fun Z : Matrix ((p : Party) → Out p) ((p : Party) → In p) ℂ ↦
    γ • Z) hNetwork).trans hAveraging.symm
  exact h

end TNLean.PEPS.Approximation.DistributedOperatorContraction
