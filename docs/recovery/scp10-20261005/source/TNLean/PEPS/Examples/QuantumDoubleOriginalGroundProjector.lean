/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CommutingMatrixProjectionProduct
import TNLean.PEPS.Examples.QuantumDoubleOriginalGroundSpace

/-!
# The original-spin quantum-double ground projector

SCP10, arXiv:1001.3807v3, Section 7.2, lines 2876–2895: the product of
all normalized B averages and all A product-one projectors is the orthogonal
projection onto the entire original-spin quantum-double ground space.
Its range retains every commuting-pair sector.

**Local fix (normalization):** B averages use |G|⁻¹, rather than the printed
unnormalized sum. See `docs/paper-gaps/scp10_quantum_double_local_hamiltonian.tex`.
**Scope restriction (native even torus):** fine periods are 2w,2h with w,h≥3.
See `docs/paper-gaps/rmp_peps_examples_small_torus.tex`.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
local notation "V" => TorusVertex width height
local notation "F" => TorusVertex (width * 2) (height * 2)
local notation "E" => Edge (torusGraph width height)
local notation "C" => (F → G)
local notation "J" => ((V ⊕ V) ⊕ E)

private def faceList : List J :=
  (Finset.univ.toList.map Sum.inr) ++ (Finset.univ.toList.map Sum.inl)

private theorem mem_faceList (j : J) : j ∈ faceList := by
  cases j <;> simp [faceList]

private theorem constraint_commute (j k : J) :
    Commute (1 - quantumDoubleOriginalTerm (G := G) j) (1 - quantumDoubleOriginalTerm k) :=
  (Commute.one_left _).sub_left
    ((Commute.one_right _).sub_right (quantumDoubleOriginalTerm_commute j k))

/-- All B ground projectors followed by all A ground projectors, with
with their stated normalizations. Every original fine-lattice face occurs once. -/
def quantumDoubleOriginalGroundProjector : Matrix C C ℂ :=
  (faceList.map (fun j => 1 - quantumDoubleOriginalTerm j)).prod

/-- The exact corrected product appearing in the source's ground-space construction. -/
theorem quantumDoubleOriginalGroundProjector_eq_B_prod_A :
    quantumDoubleOriginalGroundProjector (width := width) (height := height) (G := G) =
      ((Finset.univ : Finset E).toList.map (fun e => 1 - quantumDoubleOriginalBTerm e)).prod *
        ((Finset.univ : Finset (V ⊕ V)).toList.map
          (fun j => 1 - quantumDoubleOriginalATerm j)).prod := by
  simp [quantumDoubleOriginalGroundProjector, faceList, List.map_map, quantumDoubleOriginalTerm,
    Function.comp_def]

/-- The corrected complete ground-space product is an orthogonal projection. -/
theorem quantumDoubleOriginalGroundProjector_isStarProjection :
    IsStarProjection
      (quantumDoubleOriginalGroundProjector (width := width) (height := height) (G := G)) :=
  Matrix.isStarProjection_list_prod _
    (fun j => (quantumDoubleOriginalTerm_isStarProjection j).one_sub) constraint_commute _

/-- The corrected product fixes exactly the full physical zero-energy space. -/
theorem quantumDoubleOriginalGroundProjector_mulVec_eq_self_iff (ψ : C → ℂ) :
    quantumDoubleOriginalGroundProjector *ᵥ ψ = ψ ↔ quantumDoubleOriginalHamiltonian *ᵥ ψ = 0 := by
  rw [quantumDoubleOriginalGroundProjector, Matrix.list_prod_mulVec_eq_self_iff _
    (fun j => (quantumDoubleOriginalTerm_isStarProjection j).one_sub) constraint_commute]
  simp only [mem_faceList, forall_const, Matrix.sub_mulVec, Matrix.one_mulVec,
    sub_eq_self, quantumDoubleOriginalHamiltonian_mulVec_eq_zero_iff]

/-- The image of the corrected product equals the kernel of the actual
quantum-double Hamiltonian; in particular it contains all commuting-pair sectors. -/
theorem range_quantumDoubleOriginalGroundProjector :
    (Matrix.mulVecLin
      (quantumDoubleOriginalGroundProjector (width := width) (height := height) (G := G))).range =
      (Matrix.mulVecLin
        (quantumDoubleOriginalHamiltonian (width := width) (height := height))).ker := by
  ext ψ
  constructor
  · rintro ⟨χ, rfl⟩
    apply (quantumDoubleOriginalGroundProjector_mulVec_eq_self_iff _).mp
    change quantumDoubleOriginalGroundProjector *ᵥ (quantumDoubleOriginalGroundProjector *ᵥ χ) = _
    rw [Matrix.mulVec_mulVec,
      quantumDoubleOriginalGroundProjector_isStarProjection.isIdempotentElem.eq]
    rfl
  · intro hψ
    exact ⟨ψ, (quantumDoubleOriginalGroundProjector_mulVec_eq_self_iff ψ).mpr hψ⟩

end TNLean.PEPS
