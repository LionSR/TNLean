/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentCutCoefficientSupport

/-!
# Dependent-dimensional complementary-cut regressions

Two parallel labelled edges have dimensions two and three. Complementary
single-edge cuts force the complete coherent bond expansion, and trace pairing
extracts its coefficients when both edge representations are semi-regular.
-/

noncomputable section
open scoped BigOperators Matrix
open TNLean.PEPS TNLean.PEPS.DependentBondNetwork
namespace TNLeanTest.DependentCutBondSupport

private abbrev edgeDim (e : Bool) := Fin (if e then 3 else 2)
private def edgeTail (_ : Bool) : Bool := false
private def edgeHead (_ : Bool) : Bool := true
private def cuts (i : Bool) : Finset Bool := {i}

private theorem covers (e : Bool) : ∃ i, e ∉ cuts i := by
  refine ⟨!e, ?_⟩
  cases e <;> simp [cuts]

example : Fintype.card (edgeDim false) = 2 := rfl
example : Fintype.card (edgeDim true) = 3 := rfl
example : Fintype.card ((e : Bool) → edgeDim e × edgeDim e) = 36 := by decide

section Group
variable {G : Type*} [Group G] [Fintype G]
variable (U : (e : Bool) → G →* Matrix (edgeDim e) (edgeDim e) ℂ)

-- Complementary cuts force a coherent expansion without semi-regularity.
example {ψ : ((v : Bool) → LocalConfig edgeTail edgeHead edgeDim v) → ℂ}
    (hψ : ∀ i, ψ ∈ cutSpace edgeTail edgeHead edgeDim
      (DependentBondNetwork.averagingSite edgeTail edgeHead edgeDim U) (cuts i)) :
    ∃ c : (Bool → G) → ℂ,
      ψ = ∑ p, c p • representationBondProduct edgeTail edgeHead edgeDim U p :=
  exists_bondCoefficients_of_mem_cutSpaces edgeTail edgeHead edgeDim U cuts covers hψ

-- Independent trace pairings extract one coefficient of the entire coherent sum.
example
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (c : (Bool → G) → ℂ) (p : Bool → G) :
    bondCoefficientExtraction edgeTail edgeHead edgeDim U p
      (∑ q, c q • representationBondProduct edgeTail edgeHead edgeDim U q) = c p :=
  bondCoefficientExtraction_sum edgeTail edgeHead edgeDim U hU c p

-- Reconstruction follows from literal joint-boundary cut membership.
example
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    {ψ : ((v : Bool) → LocalConfig edgeTail edgeHead edgeDim v) → ℂ}
    (hψ : ∀ i, ψ ∈ cutSpace edgeTail edgeHead edgeDim
      (DependentBondNetwork.averagingSite edgeTail edgeHead edgeDim U) (cuts i)) :
    ψ = ∑ p, bondCoefficientExtraction edgeTail edgeHead edgeDim U p ψ •
      representationBondProduct edgeTail edgeHead edgeDim U p :=
  eq_sum_extracted_bondProducts_of_mem_cutSpaces edgeTail edgeHead edgeDim U hU cuts covers hψ

-- Arbitrary edge insertions remain in the extracted coherent vertex sum.
example (B : (e : Bool) → Matrix (edgeDim e) (edgeDim e) ℂ) (p : Bool → G) :
    bondCoefficientExtraction edgeTail edgeHead edgeDim U p
      (network edgeTail edgeHead edgeDim
        (DependentBondNetwork.averagingSite edgeTail edgeHead edgeDim U) B) =
      (Fintype.card G : ℂ)⁻¹ ^ 2 * ∑ q : Bool → G, ∏ e,
        torusDeltaPairing (U e) (p e)
          (U e (q true) * B e * U e ((q false)⁻¹)) := by
  simpa only [Fintype.card_bool, edgeHead, edgeTail] using
    bondCoefficientExtraction_network_averagingSite edgeTail edgeHead edgeDim U B p

-- When both parallel edges are uncut, their relative labels must agree.
example
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (p : Bool → G) (hp : p false ≠ p true)
    {ψ : ((v : Bool) → LocalConfig edgeTail edgeHead edgeDim v) → ℂ}
    (hψ : ψ ∈ cutSpace edgeTail edgeHead edgeDim
      (DependentBondNetwork.averagingSite edgeTail edgeHead edgeDim U) ∅) :
    bondCoefficientExtraction edgeTail edgeHead edgeDim U p ψ = 0 := by
  apply bondCoefficientExtraction_eq_zero_of_mem_cutSpace_of_incompatible
    edgeTail edgeHead edgeDim U hU ∅ p hψ
  rintro ⟨q, hq⟩
  exact hp ((hq false (by simp)).trans (hq true (by simp)).symm)

-- Nonzero coefficients provide one simultaneous label on all vertices.
example
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (C : Finset Bool) (p : Bool → G)
    {ψ : ((v : Bool) → LocalConfig edgeTail edgeHead edgeDim v) → ℂ}
    (hψ : ψ ∈ cutSpace edgeTail edgeHead edgeDim
      (DependentBondNetwork.averagingSite edgeTail edgeHead edgeDim U) C)
    (hne : bondCoefficientExtraction edgeTail edgeHead edgeDim U p ψ ≠ 0) :
    ∃ q : Bool → G, ∀ e, e ∉ C → p e = q true * (q false)⁻¹ :=
  exists_vertexLabels_of_bondCoefficientExtraction_ne_zero
    edgeTail edgeHead edgeDim U hU C p hψ hne

end Group

-- With no edges and no cuts, the universal empty product spans the coefficient
-- space; no nonemptiness assumption has been smuggled into the coverage premise.
example {G : Type*} [Group G] [Fintype G]
    (U : (e : Empty) → G →* Matrix (Fin 0) (Fin 0) ℂ)
    (ψ : ((v : Unit) → LocalConfig Empty.elim Empty.elim (fun _ : Empty => Fin 0) v) → ℂ) :
    ∃ c : (Empty → G) → ℂ, ψ = ∑ p, c p •
      representationBondProduct Empty.elim Empty.elim (fun _ : Empty => Fin 0) U p := by
  apply exists_bondCoefficients_of_mem_cutSpaces Empty.elim Empty.elim
    (fun _ : Empty => Fin 0) U (fun i : Empty => i.elim)
  · exact fun e => e.elim
  · exact fun i => i.elim

end TNLeanTest.DependentCutBondSupport

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.DependentBondNetwork.bondCoefficientExtraction_sum' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.DependentBondNetwork.bondCoefficientExtraction_sum

/--
info: 'TNLean.PEPS.DependentBondNetwork.exists_bondCoefficients_of_mem_cutSpaces' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.DependentBondNetwork.exists_bondCoefficients_of_mem_cutSpaces

/--
info: 'TNLean.PEPS.DependentBondNetwork.eq_sum_extracted_bondProducts_of_mem_cutSpaces' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.DependentBondNetwork.eq_sum_extracted_bondProducts_of_mem_cutSpaces

/--
info: 'TNLean.PEPS.DependentBondNetwork.bondCoefficientExtraction_network_averagingSite' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.DependentBondNetwork.bondCoefficientExtraction_network_averagingSite

/--
info: 'TNLean.PEPS.DependentBondNetwork.bondCoefficientExtraction_eq_zero_of_mem_cutSpace_of_incompatible' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms bondCoefficientExtraction_eq_zero_of_mem_cutSpace_of_incompatible

/--
info: 'TNLean.PEPS.DependentBondNetwork.exists_vertexLabels_of_bondCoefficientExtraction_ne_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_vertexLabels_of_bondCoefficientExtraction_ne_zero
