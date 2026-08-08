/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.OperatorSystemExtensionDirectSum
import TNLean.Channel.StarSubalgebraConditionalExpectation

/-!
# Extending completely positive maps into matrix star subalgebras

Wolf's proposition on extending completely positive maps from operator systems
(`Notes/WolfNoteTexSource/ch01_deconstructing_quantum.tex`, lines 616--626) allows both the
domain and codomain to be finite-dimensional `C^*`-algebras. The domain is represented as a
finite direct sum of full matrix algebras, while the codomain is represented as a star
subalgebra of a full matrix algebra.

The ambient direct-sum extension is composed with a trace-preserving completely positive
conditional expectation onto the codomain subalgebra. Its range can then be restricted to the
subalgebra. Complete positivity of the restricted map is stated after the canonical inclusion
into the ambient matrix algebra.

## Main results

* `Matrix.IsCPMapDirectSum.comp_isKrausCP`: postcomposition of a completely positive map from a
  direct sum with a Kraus completely positive matrix map preserves complete positivity.
* `Matrix.exists_cp_extension_of_operatorSystem_directSum_starSubalgebra_range`: an ambient
  extension whose range lies in the prescribed matrix star subalgebra.
* `Matrix.exists_cp_extension_of_operatorSystem_directSum_starSubalgebra`: the extension with
  codomain restricted to the matrix star subalgebra.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 1][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

namespace Matrix

variable {r : ℕ} {d : Fin r → ℕ} {p q : ℕ}

/-- Postcomposing a completely positive map from a direct sum of matrix algebras with a Kraus
completely positive map preserves complete positivity. -/
theorem IsCPMapDirectSum.comp_isKrausCP
    {F : (∀ k : Fin r, Matrix (Fin (d k)) (Fin (d k)) ℂ) →ₗ[ℂ]
      Matrix (Fin p) (Fin p) ℂ}
    {E : Matrix (Fin p) (Fin p) ℂ →ₗ[ℂ] Matrix (Fin q) (Fin q) ℂ}
    (hF : IsCPMapDirectSum F) (hE : IsKrausCP E) :
    IsCPMapDirectSum (E ∘ₗ F) := by
  intro j X hX
  have hcomp :
      tensorMapIdDirectSum (E ∘ₗ F) X = tensorMapId E (tensorMapIdDirectSum F X) := by
    ext ⟨a, i⟩ ⟨b, l⟩
    rfl
  rw [hcomp]
  exact tensorMapId_posSemidef_of_isKrausCP hE (hF j X hX)

/-- **Extending cp maps from operator systems, with range in a matrix star subalgebra**
(Wolf Ch. 1, lines 616--626): if a completely positive map on an operator system in a finite
direct sum of matrix algebras takes values in a matrix star subalgebra, then it has a completely
positive ambient-matrix-valued extension whose whole range lies in that subalgebra. -/
theorem exists_cp_extension_of_operatorSystem_directSum_starSubalgebra_range
    [NeZero (∑ k, d k)] [NeZero p]
    {S : Submodule ℂ (∀ k : Fin r, Matrix (Fin (d k)) (Fin (d k)) ℂ)}
    (hS : IsOperatorSystemDirectSum S)
    (B : StarSubalgebra ℂ (Matrix (Fin p) (Fin p) ℂ))
    {T : ↥S →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ}
    (hT : IsCPOnOperatorSystemDirectSum T) (hRange : ∀ x, T x ∈ B) :
    ∃ T' : (∀ k : Fin r, Matrix (Fin (d k)) (Fin (d k)) ℂ) →ₗ[ℂ]
        Matrix (Fin p) (Fin p) ℂ,
      IsCPMapDirectSum T' ∧ (∀ A, T' A ∈ B) ∧ ∀ x : ↥S, T' x.1 = T x := by
  obtain ⟨F, hFcp, hFext⟩ := exists_cp_extension_of_operatorSystem_directSum hS hT
  obtain ⟨E, hEcptp, hE⟩ := B.exists_krausCPTP_conditionalExpectation
  refine ⟨E ∘ₗ F, hFcp.comp_isKrausCP hEcptp.isKrausCP, ?_, ?_⟩
  · exact fun A ↦ hE.range_subset (F A)
  · intro x
    rw [LinearMap.comp_apply, hFext x]
    exact hE.fixes (T x) (hRange x)

/-- **Extending cp maps from operator systems, finite-dimensional matrix-algebra form**
(Wolf Ch. 1, lines 616--626): a completely positive map from an operator system in a finite
direct sum of full matrix algebras to a matrix star subalgebra extends to the whole domain.
Complete positivity is measured after the canonical inclusion of the codomain subalgebra into
its ambient full matrix algebra. -/
theorem exists_cp_extension_of_operatorSystem_directSum_starSubalgebra
    [NeZero (∑ k, d k)] [NeZero p]
    {S : Submodule ℂ (∀ k : Fin r, Matrix (Fin (d k)) (Fin (d k)) ℂ)}
    (hS : IsOperatorSystemDirectSum S)
    (B : StarSubalgebra ℂ (Matrix (Fin p) (Fin p) ℂ))
    {T : ↥S →ₗ[ℂ] ↥B}
    (hT : IsCPOnOperatorSystemDirectSum (B.subtype.toLinearMap ∘ₗ T)) :
    ∃ T' : (∀ k : Fin r, Matrix (Fin (d k)) (Fin (d k)) ℂ) →ₗ[ℂ] ↥B,
      IsCPMapDirectSum (B.subtype.toLinearMap ∘ₗ T') ∧ ∀ x : ↥S, T' x.1 = T x := by
  obtain ⟨G, hGcp, hGrange, hGext⟩ :=
    exists_cp_extension_of_operatorSystem_directSum_starSubalgebra_range hS B hT
      (fun x ↦ (T x).2)
  let T' := LinearMap.codRestrict B.toSubalgebra.toSubmodule G hGrange
  refine ⟨T', ?_, ?_⟩
  · have hinclude : B.subtype.toLinearMap ∘ₗ T' = G := by
      ext A
      rfl
    rw [hinclude]
    exact hGcp
  · intro x
    apply Subtype.ext
    exact hGext x

end Matrix
