/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PhysicalAlphabetLocalTerms
import Mathlib.Logic.Equiv.Prod

/-!
# Pair and outside coordinates for dependent physical spaces

Two applications of the standard dependent product splitting separate two
chosen sites from all remaining sites. This coordinate bijection commutes
with arbitrary sitewise physical embeddings. The corresponding Euclidean
coordinate changes therefore commute with actual extension by zero.

These identities retain the differently sized physical spaces after arbitrary
consecutive blocking in PGVWC07, arXiv:quant-ph/0608197, Theorem 9,
source lines 1195–1220.
-/

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Separate two actual physical coordinates and the dependent coordinates at
all other sites, using Mathlib's dependent product splitting twice.
Source: PGVWC07, equation unique-OBC, lines 1213–1220. -/
def pairConfigurationEquiv (β : ι → Type*) (i j : ι) (hji : j ≠ i) :
    ((k : ι) → β k) ≃ (β i × β j) ×
      ((k : {k : {k : ι // k ≠ i} // k ≠ ⟨j, hji⟩}) → β k.val.val) :=
  (Equiv.piSplitAt i β).trans
    (((Equiv.refl (β i)).prodCongr
      (Equiv.piSplitAt ⟨j, hji⟩ (fun k : {k : ι // k ≠ i} ↦ β k.val))).trans
      (Equiv.prodAssoc _ _ _).symm)

/-- The pair/outside bijection reads the original physical coordinates without
relabeling either active site. -/
@[simp] theorem pairConfigurationEquiv_apply (β : ι → Type*) (i j : ι) (hji : j ≠ i)
    (σ : (k : ι) → β k) :
    pairConfigurationEquiv β i j hji σ =
      ((σ i, σ j), fun k ↦ σ k.val.val) := rfl

/-- The coordinate bijection commutes with every sitewise physical embedding.
Source: PGVWC07, arbitrary consecutive blocking and pair sections,
lines 1195–1220. -/
theorem pairConfigurationEquiv_embedding_apply (β γ : ι → Type*)
    (e : ∀ k, β k ↪ γ k) (i j : ι) (hji : j ≠ i) (σ : (k : ι) → β k) :
    pairConfigurationEquiv γ i j hji (Function.Embedding.piCongrRight e σ) =
      (((e i).prodMap (e j)).prodMap
        (Function.Embedding.piCongrRight
          (fun k : {k : {k : ι // k ≠ i} // k ≠ ⟨j, hji⟩} ↦ e k.val.val)))
        (pairConfigurationEquiv β i j hji σ) := rfl

/-- The pair/outside coordinate bijection, acting on actual Euclidean vectors.
Source: PGVWC07, equation unique-OBC, lines 1213–1220. -/
noncomputable def pairConfigurationReindex (β : ι → Type*) [∀ k, Fintype (β k)]
    (i j : ι) (hji : j ≠ i) :
    EuclideanSpace ℂ ((k : ι) → β k) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((β i × β j) ×
        ((k : {k : {k : ι // k ≠ i} // k ≠ ⟨j, hji⟩}) → β k.val.val)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (pairConfigurationEquiv β i j hji)

/-- Physical extension by zero commutes with the actual dependent pair/outside
coordinate changes. No outside-coordinate supplier is assumed.
Source: PGVWC07, equation unique-OBC, lines 1213–1220. -/
theorem pairConfigurationReindex_extendByZero (β γ : ι → Type*)
    [∀ k, Fintype (β k)] [∀ k, Fintype (γ k)]
    (e : ∀ k, β k ↪ γ k) (i j : ι) (hji : j ≠ i)
    (v : EuclideanSpace ℂ ((k : ι) → β k)) :
    pairConfigurationReindex γ i j hji
        ((Function.Embedding.piCongrRight e).euclideanExtendByZero v) =
      (((e i).prodMap (e j)).prodMap
        (Function.Embedding.piCongrRight
          (fun k : {k : {k : ι // k ≠ i} // k ≠ ⟨j, hji⟩} ↦ e k.val.val)))
        .euclideanExtendByZero (pairConfigurationReindex β i j hji v) := by
  classical
  let Q := pairConfigurationEquiv β i j hji
  let Q' := pairConfigurationEquiv γ i j hji
  let E := Function.Embedding.piCongrRight e
  let F := ((e i).prodMap (e j)).prodMap
    (Function.Embedding.piCongrRight
      (fun k : {k : {k : ι // k ≠ i} // k ≠ ⟨j, hji⟩} ↦ e k.val.val))
  have hcomm (σ : (k : ι) → β k) : Q' (E σ) = F (Q σ) := rfl
  apply PiLp.ext
  intro c
  change E.euclideanExtendByZero v (Q'.symm c) =
    F.euclideanExtendByZero (pairConfigurationReindex β i j hji v) c
  by_cases hc : c ∈ Set.range F
  · obtain ⟨a, rfl⟩ := hc
    have hpre : Q'.symm (F a) = E (Q.symm a) := by
      apply Q'.injective
      rw [Q'.apply_symm_apply, hcomm, Q.apply_symm_apply]
    rw [hpre, E.euclideanExtendByZero_apply_image,
      F.euclideanExtendByZero_apply_image]
  · have hpre : Q'.symm c ∉ Set.range E := by
      rintro ⟨σ, hσ⟩
      apply hc
      refine ⟨Q σ, ?_⟩
      have h := congrArg Q' hσ
      rw [hcomm, Q'.apply_symm_apply] at h
      exact h
    rw [E.euclideanExtendByZero_apply_not_mem_range _ _ hpre,
      F.euclideanExtendByZero_apply_not_mem_range _ _ hc]

end Matrix
