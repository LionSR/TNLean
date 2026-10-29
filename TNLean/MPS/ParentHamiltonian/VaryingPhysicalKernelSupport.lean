/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.VaryingPhysicalParentHamiltonian
import QICLean.Analysis.WeightedPositiveKernel

/-!
# Physical support forced by the actual open parent kernel

After physical extension by zero, each actual pair boundary range is supported
on the original two physical alphabets. Positivity derives the local equations
from the actual open Hamiltonian. Every site of a chain of length at least two
belongs to an adjacent pair, so every coefficient outside the original full
physical configuration image vanishes. The vector is therefore the extension
of its actual coefficient pullback, rather than an assumed embedded state.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 9 and equation unique-OBC,
source lines 1195–1220.
-/

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

/-- Each actual fixed-outside pair section has a rectangular trace boundary
when the actual extended local parent term vanishes.
Source: PGVWC07, equation unique-OBC, lines 1213–1220. -/
theorem physicalPairParentTerm_boundary_of_apply_eq_zero
    (β : ι → Type*) [∀ k, Fintype (β k)] (i j : ι) (hji : j ≠ i)
    (A : β i → Matrix a b ℂ) (B : β j → Matrix b c ℂ)
    (ψ : EuclideanSpace ℂ ((k : ι) → β k))
    (hzero : physicalPairParentTerm β i j hji A B ψ = 0)
    (η : (k : {k : {k : ι // k ≠ i} // k ≠ ⟨j, hji⟩}) → β k.val.val) :
    ∃ X : Matrix c a ℂ, ∀ x y,
      ψ ((pairConfigurationEquiv β i j hji).symm ((x, y), η)) =
        Matrix.trace (X * A x * B y) := by
  let U := pairConfigurationReindex β i j hji
  let G := LinearMap.range (rectangularPairBoundary A B)
  have hprod : ContinuousLinearMap.rightFiberwiseMap Gᗮ.starProjection (U ψ) = 0 := by
    rw [← physicalPairParentTerm_in_coordinates, hzero, map_zero]
  have hfiber := (ContinuousLinearMap.mem_ker_rightFiberwiseMap_iff
    Gᗮ.starProjection (U ψ)).mp hprod η
  have hmem : ContinuousLinearMap.rightFiber (U ψ) η ∈ G := by
    have horth := (Submodule.starProjection_apply_eq_zero_iff).mp hfiber
    simpa only [Submodule.orthogonal_orthogonal] using horth
  obtain ⟨X, hX⟩ := LinearMap.mem_range.mp hmem
  refine ⟨X, fun x y ↦ ?_⟩
  have hc := congrArg (fun v ↦ v (x, y)) hX
  change Matrix.trace (X * (A x * B y)) =
    ψ ((pairConfigurationEquiv β i j hji).symm ((x, y), η)) at hc
  rw [← Matrix.mul_assoc] at hc
  exact hc.symm

/-- The actual local equation is equivalent to rectangular boundary
representations on every outside section. Source: PGVWC07,
equation unique-OBC, lines 1213–1220. -/
theorem physicalPairParentTerm_apply_eq_zero_iff_boundary
    (β : ι → Type*) [∀ k, Fintype (β k)] (i j : ι) (hji : j ≠ i)
    (A : β i → Matrix a b ℂ) (B : β j → Matrix b c ℂ)
    (ψ : EuclideanSpace ℂ ((k : ι) → β k)) :
    physicalPairParentTerm β i j hji A B ψ = 0 ↔
      ∀ η : (k : {k : {k : ι // k ≠ i} // k ≠ ⟨j, hji⟩}) → β k.val.val,
        ∃ X : Matrix c a ℂ, ∀ x y,
          ψ ((pairConfigurationEquiv β i j hji).symm ((x, y), η)) =
            Matrix.trace (X * A x * B y) := by
  constructor
  · exact physicalPairParentTerm_boundary_of_apply_eq_zero β i j hji A B ψ
  · intro hboundary
    let U := pairConfigurationReindex β i j hji
    let G := LinearMap.range (rectangularPairBoundary A B)
    apply U.injective
    rw [map_zero, physicalPairParentTerm_in_coordinates]
    apply (ContinuousLinearMap.mem_ker_rightFiberwiseMap_iff Gᗮ.starProjection (U ψ)).mpr
    intro η
    obtain ⟨X, hX⟩ := hboundary η
    have hmem : ContinuousLinearMap.rightFiber (U ψ) η ∈ G := by
      refine ⟨X, ?_⟩
      apply PiLp.ext
      rintro ⟨x, y⟩
      change Matrix.trace (X * (A x * B y)) =
        ψ ((pairConfigurationEquiv β i j hji).symm ((x, y), η))
      rw [← Matrix.mul_assoc]
      exact (hX x y).symm
    apply Submodule.starProjection_apply_eq_zero_iff.mpr
    simpa only [Submodule.orthogonal_orthogonal] using hmem

/-- An actual embedded pair term kills no coefficient at an added physical
letter: any vector in its kernel must vanish there.
Source: PGVWC07, actual pair range in Theorem 9, lines 1201–1220. -/
theorem physicalPairParentTerm_coeff_eq_zero_of_not_mem_range
    (β γ : ι → Type*) [∀ k, Fintype (β k)] [∀ k, Fintype (γ k)]
    (e : ∀ k, β k ↪ γ k) (i j : ι) (hji : j ≠ i)
    (A : β i → Matrix a b ℂ) (B : β j → Matrix b c ℂ)
    (ψ : EuclideanSpace ℂ ((k : ι) → γ k))
    (hzero : physicalPairParentTerm γ i j hji (Function.extend (e i) A 0)
      (Function.extend (e j) B 0) ψ = 0)
    (σ : (k : ι) → γ k)
    (hσ : σ i ∉ Set.range (e i) ∨ σ j ∉ Set.range (e j)) : ψ σ = 0 := by
  classical
  let Q := pairConfigurationEquiv γ i j hji
  obtain ⟨X, hX⟩ := physicalPairParentTerm_boundary_of_apply_eq_zero γ i j hji
    (Function.extend (e i) A 0) (Function.extend (e j) B 0) ψ hzero (Q σ).2
  have hc := hX (σ i) (σ j)
  change ψ (Q.symm (Q σ)) = Matrix.trace
    (X * Function.extend (e i) A 0 (σ i) * Function.extend (e j) B 0 (σ j)) at hc
  rw [Q.symm_apply_apply] at hc
  rcases hσ with hi | hj
  · rw [Function.extend_apply' A 0 (σ i) hi, Matrix.mul_zero,
      Matrix.zero_mul, Matrix.trace_zero] at hc
    exact hc
  · rw [Function.extend_apply' B 0 (σ j) hj, Matrix.mul_zero, Matrix.trace_zero] at hc
    exact hc

/-- Positivity derives every actual adjacent local equation from the full
Hamiltonian equation. Source: PGVWC07, Theorem 9 proof, lines 1213–1217. -/
theorem varyingPhysicalParentHamiltonian_apply_eq_zero_iff_terms {n : ℕ}
    (β : Fin (n + 2) → Type*) [∀ k, Fintype (β k)] (D : ℕ → ℕ)
    (A : ∀ k : Fin (n + 2), β k → Matrix (Fin (D k.val)) (Fin (D (k.val + 1))) ℂ)
    (ψ : EuclideanSpace ℂ ((k : Fin (n + 2)) → β k)) :
    varyingPhysicalParentHamiltonian β D A ψ = 0 ↔
      ∀ j : Fin (n + 1), physicalPairParentTerm β j.castSucc j.succ
        (ne_of_gt j.castSucc_lt_succ) (A j.castSucc) (A j.succ) ψ = 0 := by
  change (∑ j : Fin (n + 1), physicalPairParentTerm β j.castSucc j.succ
    (ne_of_gt j.castSucc_lt_succ) (A j.castSucc) (A j.succ)) ψ = 0 ↔ _
  exact WeightedPositiveKernel.apply_sum_eq_zero_iff
    (fun j ↦ physicalPairParentTerm_isPositive β _ _ _ _ _) ψ

/-- Every nonwrapping adjacent pair satisfies its actual local equation when
the full parent Hamiltonian vanishes. Source: PGVWC07, Theorem 9 proof,
lines 1213–1217. -/
theorem varyingPhysicalParentHamiltonian_pair_apply_eq_zero {N : ℕ}
    (β : Fin N → Type*) [∀ k, Fintype (β k)] (D : ℕ → ℕ)
    (A : ∀ k : Fin N, β k → Matrix (Fin (D k.val)) (Fin (D (k.val + 1))) ℂ)
    (ψ : EuclideanSpace ℂ ((k : Fin N) → β k))
    (hzero : varyingPhysicalParentHamiltonian β D A ψ = 0)
    (p : ℕ) (hp : p + 1 < N) :
    physicalPairParentTerm β ⟨p, by omega⟩ ⟨p + 1, hp⟩
      (fun h ↦ Nat.succ_ne_self p (congrArg Fin.val h))
      (A ⟨p, by omega⟩) (A ⟨p + 1, hp⟩) ψ = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  exact (varyingPhysicalParentHamiltonian_apply_eq_zero_iff_terms β D A ψ).mp hzero
    ⟨p, by omega⟩

/-- Added physical letters have zero coefficients in the actual extended open
parent kernel. Adjacent local equations are derived from the Hamiltonian, and
every site is covered when the chain has at least two sites.
Source: PGVWC07, Theorem 9 and equation unique-OBC, lines 1195–1220. -/
theorem varyingPhysicalParentHamiltonian_coeff_eq_zero_of_not_mem_range {N : ℕ}
    (hN : 2 ≤ N) (β γ : Fin N → Type*)
    [∀ k, Fintype (β k)] [∀ k, Fintype (γ k)]
    (e : ∀ k, β k ↪ γ k) (D : ℕ → ℕ)
    (A : ∀ k : Fin N, β k → Matrix (Fin (D k.val)) (Fin (D (k.val + 1))) ℂ)
    (ψ : EuclideanSpace ℂ ((k : Fin N) → γ k))
    (hzero : varyingPhysicalParentHamiltonian γ D
      (fun k ↦ Function.extend (e k) (A k) 0) ψ = 0)
    (σ : (k : Fin N) → γ k) (k : Fin N) (hk : σ k ∉ Set.range (e k)) : ψ σ = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  have hterms := (varyingPhysicalParentHamiltonian_apply_eq_zero_iff_terms γ D _ ψ).mp hzero
  by_cases hleft : k.val < n + 1
  · let j : Fin (n + 1) := ⟨k.val, hleft⟩
    have hkleft : j.castSucc = k := Fin.ext rfl
    exact physicalPairParentTerm_coeff_eq_zero_of_not_mem_range β γ e _ _ _ _ _ ψ
      (hterms j) σ (Or.inl (by simpa only [hkleft] using hk))
  · have hkright : (Fin.last n).succ = k := by
      apply Fin.ext
      have := k.isLt
      simp only [Fin.val_succ, Fin.val_last]
      omega
    exact physicalPairParentTerm_coeff_eq_zero_of_not_mem_range β γ e _ _ _ _ _ ψ
      (hterms (Fin.last n)) σ (Or.inr (by simpa only [hkright] using hk))

/-- Every actual kernel vector after physical extension is exactly the
extension of its literal coefficient pullback. Embedded-state membership is
derived, not supplied. Source: PGVWC07, Theorem 9, lines 1195–1220. -/
theorem varyingPhysicalParentHamiltonian_eq_extendByZero_pullback_of_eq_zero {N : ℕ}
    (hN : 2 ≤ N) (β γ : Fin N → Type*)
    [∀ k, Fintype (β k)] [∀ k, Fintype (γ k)]
    (e : ∀ k, β k ↪ γ k) (D : ℕ → ℕ)
    (A : ∀ k : Fin N, β k → Matrix (Fin (D k.val)) (Fin (D (k.val + 1))) ℂ)
    (ψ : EuclideanSpace ℂ ((k : Fin N) → γ k))
    (hzero : varyingPhysicalParentHamiltonian γ D
      (fun k ↦ Function.extend (e k) (A k) 0) ψ = 0) :
    ψ = (Function.Embedding.piCongrRight e).euclideanExtendByZero
      (WithLp.toLp 2 fun σ ↦ ψ (Function.Embedding.piCongrRight e σ)) := by
  classical
  let E := Function.Embedding.piCongrRight e
  apply PiLp.ext
  intro σ
  by_cases hσ : σ ∈ Set.range E
  · obtain ⟨τ, rfl⟩ := hσ
    exact (E.euclideanExtendByZero_apply_image _ τ).symm
  · rw [E.euclideanExtendByZero_apply_not_mem_range _ _ hσ]
    have hinvalid : ∃ k, σ k ∉ Set.range (e k) := by
      by_contra hnone
      have hvalid : ∀ k, ∃ x, e k x = σ k := by
        intro k
        by_contra hk
        exact hnone ⟨k, hk⟩
      choose τ hτ using hvalid
      exact hσ ⟨τ, funext hτ⟩
    obtain ⟨k, hk⟩ := hinvalid
    exact varyingPhysicalParentHamiltonian_coeff_eq_zero_of_not_mem_range
      hN β γ e D A ψ hzero σ k hk

end Matrix
