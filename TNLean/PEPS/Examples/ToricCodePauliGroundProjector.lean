/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CommutingMatrixProjectionProduct
import TNLean.PEPS.Examples.ToricCodePauliGroundSpace

/-!
# The correctly normalized toric-code ground projector

The actual orthogonal ground projector is the product of I−h over all
faces, equivalently the product of (I+X⊗4)/2 and (I+Z⊗4)/2. Its range is
the entire four-dimensional physical Pauli kernel.

Source: SCP10, arXiv:1001.3807v3, Section 7.1, lines 2659–2685.
**Local fix (normalization):** after defining h=(I−S)/2, the source prints
(I−h)/2 in the projector construction. The extra factor must be removed.
See `docs/paper-gaps/scp10_toric_code_projector_normalization.tex`.

**Scope restriction (native even torus):** the full comparison uses fine
periods 2w,2h with w,h≥3. Small periodic lattices are not classified here.
See `docs/paper-gaps/scp10_toric_code_projector_normalization.tex`.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "V" => TorusVertex width height
local notation "F" => TorusVertex (width * 2) (height * 2)
local notation "E" => Edge (torusGraph width height)
local notation "C" => (F → ToricCodeGroup)
local notation "J" => ((V ⊕ V) ⊕ E)

omit [Fact (2 < width)] [Fact (2 < height)] in
/-- The correctly normalized +1 parity projector on an A face. -/
theorem one_sub_toricCodeATerm (j : V ⊕ V) :
    1 - toricCodeATerm j =
      (1 / 2 : ℂ) • (1 + toricCodePlacedZ (toricCodeARegion j)) := by
  ext x y
  simp only [toricCodeATerm, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
    smul_eq_mul]
  ring

/-- The correctly normalized coherent flip average on a B face.
The unnormalized coherent sum is twice this projector, not the penalty h_B. -/
theorem one_sub_toricCodeBTerm (e : E) :
    1 - toricCodeBTerm e =
      (1 / 2 : ℂ) • (1 + toricCodePlacedX (toricCodeBRegion e)) := by
  ext x y
  simp only [toricCodeBTerm, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
    smul_eq_mul]
  ring

private def faceList : List J :=
  (Finset.univ.toList.map Sum.inr) ++ (Finset.univ.toList.map Sum.inl)

private theorem mem_faceList (j : J) : j ∈ faceList := by
  cases j <;> simp [faceList]

private theorem constraint_commute (j k : J) :
    Commute (1 - toricCodePauliTerm j) (1 - toricCodePauliTerm k) :=
  (Commute.one_left _).sub_left
    ((Commute.one_right _).sub_right (toricCodePauliTerm_commute j k))

/-- All B ground projectors followed by all A ground projectors, with
no extra half factors. Every original fine-lattice face occurs once. -/
def toricCodePauliGroundProjector : Matrix C C ℂ :=
  (faceList.map (fun j => 1 - toricCodePauliTerm j)).prod

/-- The exact corrected product appearing in the source's ground-space construction. -/
theorem toricCodePauliGroundProjector_eq_B_prod_A :
    toricCodePauliGroundProjector (width := width) (height := height) =
      ((Finset.univ : Finset E).toList.map (fun e => 1 - toricCodeBTerm e)).prod *
        ((Finset.univ : Finset (V ⊕ V)).toList.map (fun j => 1 - toricCodeATerm j)).prod := by
  simp [toricCodePauliGroundProjector, faceList, List.map_map, toricCodePauliTerm,
    Function.comp_def]

/-- The corrected complete ground-space product is an orthogonal projection. -/
theorem toricCodePauliGroundProjector_isStarProjection :
    IsStarProjection (toricCodePauliGroundProjector (width := width) (height := height)) :=
  Matrix.isStarProjection_list_prod _
    (fun j => (toricCodePauliTerm_isStarProjection j).one_sub) constraint_commute _

/-- The corrected product fixes exactly the full physical zero-energy space. -/
theorem toricCodePauliGroundProjector_mulVec_eq_self_iff (ψ : C → ℂ) :
    toricCodePauliGroundProjector *ᵥ ψ = ψ ↔ toricCodePauliHamiltonian *ᵥ ψ = 0 := by
  rw [toricCodePauliGroundProjector, Matrix.list_prod_mulVec_eq_self_iff _
    (fun j => (toricCodePauliTerm_isStarProjection j).one_sub) constraint_commute]
  simp only [mem_faceList, forall_const, Matrix.sub_mulVec, Matrix.one_mulVec,
    sub_eq_self, toricCodePauliHamiltonian_mulVec_eq_zero_iff]

/-- The image of the corrected product equals the kernel of the actual
Pauli Hamiltonian; in particular it contains all four topological sectors. -/
theorem range_toricCodePauliGroundProjector :
    (Matrix.mulVecLin
      (toricCodePauliGroundProjector (width := width) (height := height))).range =
      (Matrix.mulVecLin (toricCodePauliHamiltonian (width := width) (height := height))).ker := by
  ext ψ
  constructor
  · rintro ⟨χ, rfl⟩
    apply (toricCodePauliGroundProjector_mulVec_eq_self_iff _).mp
    change toricCodePauliGroundProjector *ᵥ (toricCodePauliGroundProjector *ᵥ χ) = _
    rw [Matrix.mulVec_mulVec, toricCodePauliGroundProjector_isStarProjection.isIdempotentElem.eq]
    rfl
  · intro hψ
    exact ⟨ψ, (toricCodePauliGroundProjector_mulVec_eq_self_iff ψ).mpr hψ⟩

end TNLean.PEPS
