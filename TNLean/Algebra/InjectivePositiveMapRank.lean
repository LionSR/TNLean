/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.PSDConeAutomorphism.FaceDimension
import QICLean.Channel.Schwarz.PositiveMapProperties
import QICLean.Channel.KrausRank
import QICLean.Channel.LocalizedKrausCPTP
import QICLean.Channel.FixedPoint.DirectSumBlockRetraction
import QICLean.Channel.Semigroup.CPClosure

/-!
# Rank under injective positive maps

An injective positive linear map cannot decrease the rank of a positive
semidefinite matrix. The proof compares the dimensions of the positive faces
supported by the input and output, using Wolf's face-dimension formula.
-/

open scoped Matrix ComplexOrder MatrixOrder

namespace Matrix

/-- An injective positive map on a finite matrix algebra cannot decrease the
rank of a positive semidefinite matrix. The argument uses the dimension of the
span of each support face (Wolf, Proposition 3.6, after equation (3.42)). -/
theorem rank_le_rank_map_of_injective_positive {D : ℕ}
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) (hInjective : Function.Injective T)
    {P : Matrix (Fin D) (Fin D) ℂ} (hP : P.PosSemidef) :
    P.rank ≤ (T P).rank := by
  classical
  let e : Matrix (Fin D) (Fin D) ℂ ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
    LinearEquiv.ofBijective T
      ⟨hInjective, LinearMap.injective_iff_surjective.mp hInjective⟩
  have hTP : (T P).PosSemidef := hT P hP
  have hface : T '' psdConeFace P ⊆ psdConeFace (T P) := by
    rintro X ⟨Y, ⟨c, hc, hzero, hle⟩, rfl⟩
    refine ⟨c, hc, ?_, ?_⟩
    · simpa only [LinearMap.map_smul_of_tower, map_zero] using hT.map_le_map hzero
    · simpa only [LinearMap.map_smul_of_tower] using hT.map_le_map hle
  have hspan :
      (Submodule.span ℂ (psdConeFace P)).map T ≤
        Submodule.span ℂ (psdConeFace (T P)) := by
    rw [Submodule.map_span]
    exact Submodule.span_mono hface
  have hdim := Submodule.finrank_mono hspan
  have heq := e.finrank_map_eq (Submodule.span ℂ (psdConeFace P))
  have he : e.toLinearMap = T := by
    apply LinearMap.ext
    intro X
    exact LinearEquiv.ofBijective_apply T X
  have hrank_sq : P.rank ^ 2 ≤ (T P).rank ^ 2 := by
    rw [finrank_span_psdConeFace_eq_rank_sq (T P) hTP] at hdim
    have heq' :
        Module.finrank ℂ ((Submodule.span ℂ (psdConeFace P)).map T) = P.rank ^ 2 := by
      rw [he, finrank_span_psdConeFace_eq_rank_sq P hP] at heq
      exact heq
    exact heq' ▸ hdim
  nlinarith

/-- The rank inequality is independent of the choice of finite matrix index set. -/
theorem rank_le_rank_map_of_injective_positive_fintype
    {α : Type*} [Fintype α]
    {T : Matrix α α ℂ →ₗ[ℂ] Matrix α α ℂ}
    (hT : IsPositiveMap T) (hInjective : Function.Injective T)
    {P : Matrix α α ℂ} (hP : P.PosSemidef) :
    P.rank ≤ (T P).rank := by
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let E : Matrix α α ℂ ≃ₗ[ℂ]
      Matrix (Fin (Fintype.card α)) (Fin (Fintype.card α)) ℂ :=
    Matrix.reindexLinearEquiv ℂ ℂ e e
  let S := reindexEndomorphism e T
  have hSpos : IsPositiveMap S := Matrix.IsPositiveMap.reindexEndomorphism hT e
  have hSinj : Function.Injective S := by
    intro X Y hXY
    apply E.symm.injective
    apply hInjective
    apply E.injective
    exact hXY
  have hEP : (E P).PosSemidef := hP.submatrix e.symm
  have hRank := rank_le_rank_map_of_injective_positive hSpos hSinj hEP
  have hSP : S (E P) = E (T P) := by
    simp [S, E, reindexEndomorphism_apply, Matrix.reindex_apply]
  rw [hSP] at hRank
  change (Matrix.reindex e e P).rank ≤ (Matrix.reindex e e (T P)).rank at hRank
  simpa only [Matrix.rank_reindex] using hRank

end Matrix

namespace Channel

private theorem tensorMapIdLM_injective {D : ℕ}
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hInjective : Function.Injective T) :
    Function.Injective (Matrix.tensorMapIdLM (δ := Fin D) T) := by
  intro X Y hXY
  ext ⟨a, u⟩ ⟨b, v⟩
  have hslice : T (Matrix.bipartiteSlice X u v) =
      T (Matrix.bipartiteSlice Y u v) := by
    ext i j
    exact congrArg (fun M : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ ↦
      M (i, u) (j, v)) hXY
  exact congrArg (fun M : Matrix (Fin D) (Fin D) ℂ ↦ M a b)
    (hInjective hslice)

/-- Postcomposition by an injective completely positive map cannot lower the
Choi rank of a completely positive map. -/
theorem choiRank_le_comp_of_injective {D : ℕ}
    {F G : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hF : IsCPMap F) (hG : IsCPMap G)
    (hInjective : Function.Injective F) :
    choiRank G ≤ choiRank (F ∘ₗ G) := by
  by_cases hD : D = 0
  · subst D
    have hleft : ChoiRectangular.choiMatrix G = 0 := Subsingleton.elim _ _
    have hright : ChoiRectangular.choiMatrix (F ∘ₗ G) = 0 := Subsingleton.elim _ _
    simp [choiRank, hleft, hright]
  let _ : NeZero D := ⟨hD⟩
  have hGchoi : (ChoiJamiolkowski.choiMatrix G).PosSemidef :=
    (ChoiRectangular.isKrausCP_iff_choiMatrix_posSemidef (T := G)).mp hG
  have hLift : IsPositiveMap (Matrix.tensorMapIdLM (δ := Fin D) F) :=
    (Matrix.tensorMapIdLM_isKrausCP hF).isPositiveMap
  have hRank := Matrix.rank_le_rank_map_of_injective_positive_fintype
    hLift (tensorMapIdLM_injective hInjective) hGchoi
  have hChoi :
      ChoiJamiolkowski.choiMatrix (F ∘ₗ G) =
        Matrix.tensorMapIdLM (δ := Fin D) F (ChoiJamiolkowski.choiMatrix G) := by
    rfl
  change (ChoiJamiolkowski.choiMatrix G).rank ≤
    (ChoiJamiolkowski.choiMatrix (F ∘ₗ G)).rank
  rw [hChoi]
  exact hRank

/-- An injective completely positive map has Choi rank no greater than any
positive power of itself. -/
theorem choiRank_le_pow_of_injective {D : ℕ}
    {F : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hF : IsCPMap F) (hInjective : Function.Injective F)
    {p : ℕ} (hp : 0 < p) :
    choiRank F ≤ choiRank (F ^ p) := by
  have hstep (n : ℕ) : choiRank (F ^ n) ≤ choiRank (F ^ (n + 1)) := by
    simpa only [pow_succ', Module.End.mul_eq_comp] using
      choiRank_le_comp_of_injective hF (hF.pow n) hInjective
  have hbound (n : ℕ) : choiRank F ≤ choiRank (F ^ (n + 1)) := by
    induction n with
    | zero => simp
    | succ n ih => exact ih.trans (hstep (n + 1))
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  rw [hn]
  exact hbound n

end Channel
