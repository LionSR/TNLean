/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.FinitePairSources
import QICLean.Channel.SchmidtDecomposition

/-!
# Schmidt isometries of a normalized pair vector

A normalized algebraic tensor admits a finite Schmidt expansion with probability
weights and isometric embeddings into its actual endpoint spaces. The embeddings
need not span those spaces. This applies in particular to the normalized tensor
product of exact crossing sources after the endpoint registers are regrouped.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 384–434;
Schmidt existence is Wolf Chapter 1, Proposition 1.1.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-exterior-input.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.
-/

noncomputable section
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect.PairSource

private def orthonormalFrame {ι : Type} [Fintype ι] (U : HSpace)
    (u : ι → U) (hu : Orthonormal ℂ u) : EuclideanSpace ℂ ι →ₗᵢ[ℂ] U :=
  by
    let b := EuclideanSpace.basisFun ι ℂ
    let f : EuclideanSpace ℂ ι →ₗ[ℂ] U := b.toBasis.constr ℂ u
    have hf : f ∘ b.toBasis = u := by
      funext i
      exact b.toBasis.constr_basis ℂ u i
    exact f.isometryOfOrthonormal (v := b.toBasis) b.orthonormal (by rw [hf]; exact hu)

private theorem orthonormalFrame_basis {ι : Type} [Fintype ι] (U : HSpace)
    (u : ι → U) (hu : Orthonormal ℂ u) (i : ι) :
    orthonormalFrame U u hu (EuclideanSpace.basisFun ι ℂ i) = u i := by
  change ((EuclideanSpace.basisFun ι ℂ).toBasis.constr ℂ u)
    ((EuclideanSpace.basisFun ι ℂ).toBasis i) = u i
  exact (EuclideanSpace.basisFun ι ℂ).toBasis.constr_basis ℂ u i

/-- A normalized pair vector has a finite Schmidt expansion with probability
weights and actual isometric embeddings into its endpoint spaces.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 384–434;
Wolf Chapter 1, Proposition 1.1. -/
theorem exists_probability_schmidt_isometries (U V : HSpace)
    (z : U ⊗[ℂ] V) (hz : ‖z‖ = 1) :
    ∃ (r : ℕ) (lam : Fin r → ℝ)
      (F : EuclideanSpace ℂ (Fin r) →ₗᵢ[ℂ] U)
      (G : EuclideanSpace ℂ (Fin r) →ₗᵢ[ℂ] V),
      (∀ j, 0 ≤ lam j) ∧ ∑ j, lam j = 1 ∧
        z = ∑ j, (Real.sqrt (lam j) : ℂ) •
          (F (EuclideanSpace.basisFun (Fin r) ℂ j) ⊗ₜ[ℂ]
            G (EuclideanSpace.basisFun (Fin r) ℂ j)) := by
  obtain ⟨m, n, f, g, z₀, hmap, hnorm⟩ :=
    exists_finite_coordinates U V (fun _ : Unit ↦ z)
  let B := (EuclideanSpace.basisFun (Fin m) ℂ).tensorProduct
    (EuclideanSpace.basisFun (Fin n) ℂ)
  obtain ⟨e, h, lam, hnonneg, hrepr, hmass⟩ :=
    Matrix.exists_isSchmidtDecomposition (fun p ↦ B.repr (z₀ ()) p)
  have hmassOne : ∑ j, lam j = 1 := by
    calc
      _ = ‖B.repr (z₀ ())‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        exact hmass
      _ = 1 := by rw [LinearIsometryEquiv.norm_map, hnorm, hz, one_pow]
  have hz₀ : z₀ () = ∑ j : Fin (min m n), (Real.sqrt (lam j) : ℂ) •
      (e (j.castLE (min_le_left m n)) ⊗ₜ[ℂ] h (j.castLE (min_le_right m n))) := by
    apply B.repr.injective
    ext ⟨i, j⟩
    simpa only [B, map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply,
      PiLp.smul_apply, smul_eq_mul, OrthonormalBasis.tensorProduct_repr_tmul_apply,
      EuclideanSpace.basisFun_repr, mul_comm, mul_left_comm, mul_assoc] using hrepr i j
  let F₀ := orthonormalFrame (HSpace.of (EuclideanSpace ℂ (Fin m)))
    (fun j : Fin (min m n) ↦ e (j.castLE (min_le_left m n)))
    (e.orthonormal.comp _ (Fin.castLE_injective _))
  let G₀ := orthonormalFrame (HSpace.of (EuclideanSpace ℂ (Fin n)))
    (fun j : Fin (min m n) ↦ h (j.castLE (min_le_right m n)))
    (h.orthonormal.comp _ (Fin.castLE_injective _))
  refine ⟨min m n, lam, f.comp F₀, g.comp G₀, hnonneg, hmassOne, ?_⟩
  rw [← hmap (), hz₀, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, TensorProduct.mapIsometry_apply, TensorProduct.map_tmul]
  change (Real.sqrt (lam j) : ℂ) • (f _ ⊗ₜ[ℂ] g _) =
    (Real.sqrt (lam j) : ℂ) •
      (f (F₀ (EuclideanSpace.basisFun _ ℂ j)) ⊗ₜ[ℂ]
        g (G₀ (EuclideanSpace.basisFun _ ℂ j)))
  rw [show F₀ (EuclideanSpace.basisFun _ ℂ j) = _ from
    orthonormalFrame_basis _ _ _ j,
    show G₀ (EuclideanSpace.basisFun _ ℂ j) = _ from
    orthonormalFrame_basis _ _ _ j]

end TNLean.PEPS.PairEffect.PairSource
