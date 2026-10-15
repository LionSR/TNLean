/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DistributedOperatorContraction
import TNLean.PEPS.Approximation.PartyColumnRouting

/-!
# Finite coordinates for a distributed operator network

Enumerating each existing virtual alphabet gives a party network on the same
links, with the same endpoints and dimensions. Its physical coordinates are
read through prescribed maps at each party. This is an algebraic change of
coordinates; a protocol must separately identify these maps with its physical
site coordinates and establish the spatial placement required for routing.

Auxiliary to polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–579,
and Lemma 8.2, `07-assembly.tex`, lines 96–177. Source revision:
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open scoped BigOperators
namespace TNLean.PEPS.Approximation.DistributedOperatorContraction

variable {Party Gate : Type*} [Fintype Party]
  [DecidableEq Party] [DecidableEq Gate]
variable (gates : Finset Gate) (participants : Gate → Finset Party)
  (root : Gate → Party) (hroot : ∀ g ∈ gates, root g ∈ participants g)
  (Label : Gate → Type) [∀ g, Fintype (Label g)] (k : ℕ)
variable {Out In : Party → Type*} {q : ℕ}

/-- Enumerate the actual virtual alphabets while retaining their links and
endpoints. The two physical coordinates at each party are prescribed readouts.
Auxiliary to polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–579,
and Lemma 8.2, `07-assembly.tex`, lines 96–177. -/
def toPartyNetwork (c : (g : Gate) → Label g → ℂ)
    (T : (p : Party) → GateLabelsAt gates participants Label p →
      (SampleAt gates participants p → Fin k) → Matrix (Out p) (In p) ℂ)
    (out : (p : Party) → Fin q → Out p)
    (inp : (p : Party) → Fin q → In p) :
    PartyNetwork Party (Link gates participants root) (q * q) where
  dim e := Fintype.card (alphabet gates participants root Label k e)
  src := src gates participants root
  tgt := tgt gates participants root
  tensor p η s := localTensor gates participants root hroot Label k c T p
    (fun e ↦ (Fintype.equivFin (alphabet gates participants root Label k e.1)).symm
      (η ⟨e.1, by
        have he := e.2
        rw [← endpoints_eq gates participants root e.1] at he
        simpa only [Finset.mem_insert, Finset.mem_singleton, eq_comm] using he⟩))
    (out p (finProdFinEquiv.symm s).1, inp p (finProdFinEquiv.symm s).2)

/-- The enumerated party network contracts to the original distributed
operator read through the prescribed physical coordinates. No injectivity or
surjectivity of the physical readouts is needed for this identity.
Auxiliary to polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–579,
and Lemma 8.2, `07-assembly.tex`, lines 96–177. -/
theorem operatorCoeff_toPartyNetwork {V : Type*}
    (c : (g : Gate) → Label g → ℂ)
    (T : (p : Party) → GateLabelsAt gates participants Label p →
      (SampleAt gates participants p → Fin k) → Matrix (Out p) (In p) ℂ)
    (out : (p : Party) → Fin q → Out p)
    (inp : (p : Party) → Fin q → In p)
    (site : Party → V) (x y : V → Fin q) :
    (toPartyNetwork gates participants root hroot Label k c T out inp).operatorCoeff
      site x y = contractedOperator gates participants root hroot Label k c T
        (fun p ↦ out p (x (site p))) (fun p ↦ inp p (y (site p))) := by
  classical
  rw [PartyNetwork.operatorCoeff, PartyNetwork.coeff,
    contractedOperator_eq_linkSum]
  let E : LinkLabels gates participants root Label k ≃
      ((e : Link gates participants root) →
        Fin (Fintype.card (alphabet gates participants root Label k e))) :=
    Equiv.piCongrRight fun e ↦ Fintype.equivFin _
  erw [← E.sum_comp]
  refine Finset.sum_congr rfl fun η _ ↦ Finset.prod_congr rfl fun p _ ↦ ?_
  change localTensor gates participants root hroot Label k c T p
    (fun e ↦ (Fintype.equivFin _).symm (Fintype.equivFin _ (η e.1)))
    (out p (finProdFinEquiv.symm (finProdFinEquiv (x (site p), y (site p)))).1,
      inp p (finProdFinEquiv.symm (finProdFinEquiv (x (site p), y (site p)))).2) = _
  simp only [Equiv.symm_apply_apply]
  rfl

end TNLean.PEPS.Approximation.DistributedOperatorContraction
