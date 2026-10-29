/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.SupportAlgebraCommutation
import TNLean.QCA.SupportAlgebraGeneration
import TNLean.QCA.QuasiLocalCommutant
import QICLean.Algebra.StarSubalgebraFactor

/-!
# Scalar centers and matrix presentations of the QCA support algebras

A central element of one support algebra commutes with that algebra by
centrality, and with every other support algebra by their pairwise
commutation. Norm-closed generation makes it central in the entire
quasi-local algebra, where it is scalar. Faithful finite-region embeddings
transport this conclusion back to the two finite support algebras. The
existing QICLean finite-factor theorem then gives positive full-matrix
presentations, chosen coherently over the sites.

Source: GNVW, arXiv:0910.3675v2, Section 7.2, immediately before equations
(25)--(26), source lines 1276--1282. This is the center and factor argument;
the two adjacent-generation equalities and their size identities are separate.

**Scope restriction (homogeneous chain):** The on-site matrix size is one
fixed positive integer. GNVW also allow site-dependent sizes. See
`docs/paper-gaps/gnvw12_site_dependent_adjacent_generation_scope.tex`.
No translation-covariance hypothesis is used. The finite-factor theorem is
the full-matrix consequence documented at
https://sirui-lu.com/QICLean/paper-gaps/sw04_csform_matrix_scope.pdf.
-/

namespace SpinChain
namespace PropagatesWithin

variable {d : ℕ} [NeZero d]
  {ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d}

/-- Every actual embedded support algebra has scalar center, by generation
and pairwise commutation. Source: GNVW, arXiv:0910.3675v2, lines 1276--1282. -/
theorem embeddedSupportAlgebra_isCentral
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (y : ℤ) :
    Algebra.IsCentral ℂ ↥(embeddedSupportAlgebra hω y) where
  out := by
    intro z hz
    have hcomm (a : QuasiLocalAlgebra d) : Commute (z : QuasiLocalAlgebra d) a := by
      apply commute_of_forall_commute_embeddedSupportAlgebra hω
      intro t r hr
      by_cases hty : t = y
      · subst t
        exact ⟨congrArg Subtype.val ((Subalgebra.mem_center_iff.mp hz) ⟨r, hr⟩).symm⟩
      · exact embeddedSupportAlgebra_pairwise_commute hω y t hty.symm z z.2 r hr
    obtain ⟨c, hc, _⟩ := existsUnique_eq_smul_one_of_commute z hcomm
    rw [Algebra.mem_bot]
    refine ⟨c, Subtype.ext ?_⟩
    change algebraMap ℂ (QuasiLocalAlgebra d) c = (z : QuasiLocalAlgebra d)
    simpa only [Algebra.algebraMap_eq_smul_one] using hc.symm

private theorem finiteSupportAlgebra_isCentral
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1))
    (Λ : Finset ℤ) (S : StarSubalgebra ℂ (Matrix (Config d Λ) (Config d Λ) ℂ))
    (y : ℤ)
    (hS : S.map (matrixToQuasiLocalObservable d Λ) = embeddedSupportAlgebra hω y) :
    Algebra.IsCentral ℂ ↥S := by
  let f := matrixToQuasiLocalObservable d Λ
  have hf : Function.Injective f :=
    (quasiLocalObservable_injective d Λ).comp CStarMatrix.ofMatrixStarAlgEquiv.injective
  let e := S.toSubalgebra.equivMapOfInjective f.toAlgHom hf
  let : Algebra.IsCentral ℂ ↥(S.toSubalgebra.map f.toAlgHom) := by
    change Algebra.IsCentral ℂ ↥(S.map f)
    rw [hS]
    exact embeddedSupportAlgebra_isCentral hω y
  exact Algebra.IsCentral.of_algEquiv ℂ _ _ e.symm

/-- The finite left support algebra has scalar center. Source: GNVW,
arXiv:0910.3675v2, lines 1278--1282. -/
theorem evenSupportAlgebra_isCentral
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    Algebra.IsCentral ℂ ↥(evenSupportAlgebra hω x) := by
  apply finiteSupportAlgebra_isCentral hω (leftPair x) (evenSupportAlgebra hω x) (2 * x)
  exact (embeddedSupportAlgebra_even hω x).symm

/-- The finite right support algebra has scalar center. Source: GNVW,
arXiv:0910.3675v2, lines 1278--1282. -/
theorem oddSupportAlgebra_isCentral
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    Algebra.IsCentral ℂ ↥(oddSupportAlgebra hω x) := by
  apply finiteSupportAlgebra_isCentral hω (rightPair x) (oddSupportAlgebra hω x) (2 * x + 1)
  exact (embeddedSupportAlgebra_odd hω x).symm

/-- The actual left support factor has a positive full-matrix presentation.
Source: GNVW, arXiv:0910.3675v2, lines 1278--1282; the finite classification
is the QICLean full-matrix consequence of Schumacher--Werner, Csform. -/
theorem exists_evenSupportAlgebra_matrix
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    ∃ (r : ℕ) (_ : NeZero r),
      Nonempty (↥(evenSupportAlgebra hω x) ≃⋆ₐ[ℂ] Matrix (Fin r) (Fin r) ℂ) := by
  let : Algebra.IsCentral ℂ ↥(evenSupportAlgebra hω x) := evenSupportAlgebra_isCentral hω x
  exact StarSubalgebra.exists_starAlgEquiv_matrix_of_isCentral (evenSupportAlgebra hω x)

/-- The actual right support factor has a positive full-matrix presentation.
Source: GNVW, arXiv:0910.3675v2, lines 1278--1282. -/
theorem exists_oddSupportAlgebra_matrix
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    ∃ (r : ℕ) (_ : NeZero r),
      Nonempty (↥(oddSupportAlgebra hω x) ≃⋆ₐ[ℂ] Matrix (Fin r) (Fin r) ℂ) := by
  let : Algebra.IsCentral ℂ ↥(oddSupportAlgebra hω x) := oddSupportAlgebra_isCentral hω x
  exact StarSubalgebra.exists_starAlgEquiv_matrix_of_isCentral (oddSupportAlgebra hω x)

/-- The full-matrix sizes can be chosen as one positive site-indexed family,
with the source even/left and odd/right order. Source: GNVW,
arXiv:0910.3675v2, lines 1278--1282. No size identity is asserted here. -/
theorem exists_supportAlgebra_matrixSizes
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) :
    ∃ r : ℤ → ℕ, (∀ y, NeZero (r y)) ∧
      (∀ x, Nonempty (↥(evenSupportAlgebra hω x) ≃⋆ₐ[ℂ]
        Matrix (Fin (r (2 * x))) (Fin (r (2 * x))) ℂ)) ∧
      (∀ x, Nonempty (↥(oddSupportAlgebra hω x) ≃⋆ₐ[ℂ]
        Matrix (Fin (r (2 * x + 1))) (Fin (r (2 * x + 1))) ℂ)) := by
  classical
  choose rE hE eE using exists_evenSupportAlgebra_matrix hω
  choose rO hO eO using exists_oddSupportAlgebra_matrix hω
  let r : ℤ → ℕ := fun y ↦ if y % 2 = 0 then rE (y / 2) else rO (y / 2)
  refine ⟨r, ?_, ?_, ?_⟩
  · intro y
    dsimp only [r]
    split_ifs
    · exact hE (y / 2)
    · exact hO (y / 2)
  · intro x
    simpa [r] using eE x
  · intro x
    have hmod : (2 * x + 1) % 2 ≠ 0 := by omega
    have hdiv : (2 * x + 1) / 2 = x := by omega
    simpa only [r, if_neg hmod, hdiv] using eO x

end PropagatesWithin
end SpinChain
