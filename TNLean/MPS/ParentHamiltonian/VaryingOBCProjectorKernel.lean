/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.VaryingOBCReconstruction
import QICLean.Analysis.WeightedPositiveKernel
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Local projector kernels on a varying-bond open chain

The two-site boundary range uses the rectangular matrices at each bond.
Its orthogonal complement defines the local parent projector. Fixing a prefix
and a suffix gives a coordinate restriction to the intervening pair. Summing
the adjoint compressions of the local projector over these outside configurations
extends it by the identity. Each outside configuration occurs once, so there is
no averaging factor and no cyclic interaction across the endpoints.

Positivity identifies the kernel of the resulting finite Hamiltonian with the
adjacent-pair trace sections used in the open-chain reconstruction.
No injectivity or canonical normalization is needed for this kernel identification.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 9 and the first step of its proof,
`Papers/quant-ph_0608197/MPSarchive.tex`, lines 1195–1222.
-/

open scoped BigOperators Matrix InnerProductSpace

namespace Matrix

variable {d : ℕ}

/-- The rectangular two-site boundary map at position \(p\).
Source: PGVWC07, Theorem 9, lines 1201–1205. -/
noncomputable def obcPairBoundary (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ) (p : ℕ) :
    Matrix (Fin (b (p + 2))) (Fin (b p)) ℂ →ₗ[ℂ]
      EuclideanSpace ℂ (Fin 2 → Fin d) :=
  (WithLp.linearEquiv 2 ℂ ((Fin 2 → Fin d) → ℂ)).symm.toLinearMap.comp
    (LinearMap.pi fun σ ↦
      (Matrix.traceLinearMap (Fin (b (p + 2))) ℂ ℂ).comp
        (_root_.mulRightLinearMap (Fin (b (p + 2))) ℂ
          (A p (σ 0) * A (p + 1) (σ 1))))

/-- Coordinates of the pair boundary map are two-site rectangular traces.
Source: PGVWC07, Theorem 9, lines 1201–1205. -/
theorem obcPairBoundary_apply (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ) (p : ℕ)
    (X : Matrix (Fin (b (p + 2))) (Fin (b p)) ℂ) (σ : Fin 2 → Fin d) :
    obcPairBoundary b A p X σ = Matrix.trace (X * A p (σ 0) * A (p + 1) (σ 1)) := by
  simp [obcPairBoundary, Matrix.mul_assoc]

/-- The local parent projector is the orthogonal projection onto the complement
of the pair boundary range. Source: PGVWC07, Theorem 9, lines 1201–1205. -/
noncomputable def obcPairProjector (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ) (p : ℕ) :
    EuclideanSpace ℂ (Fin 2 → Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2 → Fin d) :=
  (LinearMap.range (obcPairBoundary b A p))ᗮ.starProjection.toLinearMap

/-- The pair projector is positive. Source: PGVWC07, Theorem 9,
lines 1201–1217. -/
theorem obcPairProjector_isPositive (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ) (p : ℕ) :
    (obcPairProjector b A p).IsPositive :=
  (Submodule.isSymmetricProjection_starProjection
    (LinearMap.range (obcPairBoundary b A p))ᗮ).isPositive

/-- A pair vector is annihilated precisely when it has a rectangular boundary
representation. Source: PGVWC07, equation unique-OBC, lines 1213–1220. -/
theorem obcPairProjector_apply_eq_zero_iff (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ) (p : ℕ)
    (v : EuclideanSpace ℂ (Fin 2 → Fin d)) :
    obcPairProjector b A p v = 0 ↔
      ∃ X : Matrix (Fin (b (p + 2))) (Fin (b p)) ℂ,
        ∀ σ, v σ = Matrix.trace (X * A p (σ 0) * A (p + 1) (σ 1)) := by
  have hker : obcPairProjector b A p v = 0 ↔
      v ∈ LinearMap.range (obcPairBoundary b A p) := by
    change (LinearMap.range (obcPairBoundary b A p))ᗮ.starProjection v = 0 ↔ _
    rw [Submodule.starProjection_orthogonal_val, sub_eq_zero, eq_comm,
      Submodule.starProjection_eq_self_iff]
  rw [hker, LinearMap.mem_range]
  constructor
  · rintro ⟨X, rfl⟩
    exact ⟨X, obcPairBoundary_apply b A p X⟩
  · rintro ⟨X, hX⟩
    refine ⟨X, ?_⟩
    ext σ
    rw [obcPairBoundary_apply]
    exact (hX σ).symm

/-- Restrict a vector to its pair coordinates after fixing the prefix and
suffix. Source: PGVWC07, equation unique-OBC, lines 1213–1220. -/
noncomputable def obcPairSection {N p q : ℕ} (h : p + 2 + q = N)
    (u : Fin p → Fin d) (w : Fin q → Fin d) :
    EuclideanSpace ℂ (Fin N → Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2 → Fin d) :=
  LinearMap.withLpMap 2
    { toFun := fun ψ σ ↦ ψ (fun i ↦
        Fin.append (Fin.append u σ) w (Fin.cast h.symm i))
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

/-- One outside-coordinate compression of the local projector.
Source: PGVWC07, Theorem 9 proof, lines 1213–1217. -/
private noncomputable def obcPairCompression (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ)
    {N p q : ℕ} (h : p + 2 + q = N) (u : Fin p → Fin d) (w : Fin q → Fin d) :
    EuclideanSpace ℂ (Fin N → Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin N → Fin d) :=
  (obcPairSection h u w).adjoint ∘ₗ obcPairProjector b A p ∘ₗ obcPairSection h u w

private theorem obcPairCompression_isPositive (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ)
    {N p q : ℕ} (h : p + 2 + q = N) (u : Fin p → Fin d) (w : Fin q → Fin d) :
    (obcPairCompression b A h u w).IsPositive :=
  (obcPairProjector_isPositive b A p).adjoint_conj (obcPairSection h u w)

private theorem obcPairCompression_apply_eq_zero_iff (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ)
    {N p q : ℕ} (h : p + 2 + q = N) (u : Fin p → Fin d) (w : Fin q → Fin d)
    (ψ : EuclideanSpace ℂ (Fin N → Fin d)) :
    obcPairCompression b A h u w ψ = 0 ↔
      obcPairProjector b A p (obcPairSection h u w ψ) = 0 := by
  constructor
  · intro hzero
    apply (obcPairProjector_isPositive b A p).apply_eq_zero_of_re_inner_eq_zero
    rw [← LinearMap.adjoint_inner_left (obcPairSection h u w) ψ]
    change Complex.re (⟪obcPairCompression b A h u w ψ, ψ⟫_ℂ) = 0
    rw [hzero]
    simp
  · intro hzero
    change (obcPairSection h u w).adjoint
      (obcPairProjector b A p (obcPairSection h u w ψ)) = 0
    rw [hzero, map_zero]

/-- The open parent Hamiltonian sums the pair projector extended by the identity
on its prefix and suffix. Every outside configuration is counted once.
Source: PGVWC07, Theorem 9, lines 1201–1217. -/
noncomputable def obcParentHamiltonian (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ) (N : ℕ) :
    EuclideanSpace ℂ (Fin N → Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin N → Fin d) :=
  ∑ s : {s : Fin (N + 1) × Fin (N + 1) // s.1.val + 2 + s.2.val = N},
    ∑ u : Fin s.val.1.val → Fin d, ∑ w : Fin s.val.2.val → Fin d,
      obcPairCompression b A s.property u w

/-- The varying-bond open parent Hamiltonian is positive.
Source: PGVWC07, Theorem 9 proof, lines 1213–1217. -/
theorem obcParentHamiltonian_isPositive (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ) (N : ℕ) :
    (obcParentHamiltonian b A N).IsPositive := by
  classical
  exact LinearMap.isPositive_sum Finset.univ fun s _ ↦
    LinearMap.isPositive_sum Finset.univ fun u _ ↦
      LinearMap.isPositive_sum Finset.univ fun w _ ↦
        obcPairCompression_isPositive b A s.property u w

/-- The Hamiltonian vanishes exactly when every fixed-outside pair
section belongs to the two-site boundary range. Source: PGVWC07,
equation unique-OBC, lines 1213–1220. -/
theorem obcParentHamiltonian_apply_eq_zero_iff (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ) (N : ℕ)
    (ψ : EuclideanSpace ℂ (Fin N → Fin d)) :
    obcParentHamiltonian b A N ψ = 0 ↔
      ∀ (p q : ℕ) (h : p + 2 + q = N) (u : Fin p → Fin d) (w : Fin q → Fin d),
        obcPairProjector b A p (obcPairSection h u w ψ) = 0 := by
  classical
  have hpos := fun (s : {s : Fin (N + 1) × Fin (N + 1) //
      s.1.val + 2 + s.2.val = N}) ↦
    LinearMap.isPositive_sum Finset.univ fun u _ ↦
      LinearMap.isPositive_sum Finset.univ fun w _ ↦
        obcPairCompression_isPositive b A s.property u w
  rw [obcParentHamiltonian, WeightedPositiveKernel.apply_sum_eq_zero_iff hpos]
  constructor
  · intro hzero p q h u w
    let s : {s : Fin (N + 1) × Fin (N + 1) // s.1.val + 2 + s.2.val = N} :=
      ⟨(⟨p, by omega⟩, ⟨q, by omega⟩), h⟩
    have hu := (WeightedPositiveKernel.apply_sum_eq_zero_iff
      (fun u ↦ LinearMap.isPositive_sum Finset.univ fun w _ ↦
        obcPairCompression_isPositive b A s.property u w) ψ).mp (hzero s)
    have hw := (WeightedPositiveKernel.apply_sum_eq_zero_iff
      (fun w ↦ obcPairCompression_isPositive b A s.property u w) ψ).mp (hu u)
    exact (obcPairCompression_apply_eq_zero_iff b A h u w ψ).mp (hw w)
  · intro hzero s
    apply (WeightedPositiveKernel.apply_sum_eq_zero_iff
      (fun u ↦ LinearMap.isPositive_sum Finset.univ fun w _ ↦
        obcPairCompression_isPositive b A s.property u w) ψ).mpr
    intro u
    apply (WeightedPositiveKernel.apply_sum_eq_zero_iff
      (fun w ↦ obcPairCompression_isPositive b A s.property u w) ψ).mpr
    intro w
    exact (obcPairCompression_apply_eq_zero_iff b A s.property u w ψ).mpr
      (hzero s.val.1.val s.val.2.val s.property u w)

/-- The kernel of the open Hamiltonian gives the list-indexed pair
sections needed for reconstruction along the whole chain. The coefficient
identification only changes the representation of a physical word.
Source: PGVWC07, equation unique-OBC, lines 1213–1220. -/
theorem obcParentHamiltonian_pair_sections_of_apply_eq_zero (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ) {N : ℕ}
    (ψ : EuclideanSpace ℂ (Fin N → Fin d)) (f : List (Fin d) → ℂ)
    (hf : ∀ w : Fin N → Fin d, f (List.ofFn w) = ψ w)
    (hzero : obcParentHamiltonian b A N ψ = 0) :
    ∀ u v : List (Fin d), u.length + 2 + v.length = N →
      ∃ X : Matrix (Fin (b (u.length + 2))) (Fin (b u.length)) ℂ,
        ∀ i j, f (u ++ i :: j :: v) =
          Matrix.trace (X * A u.length i * A (u.length + 1) j) := by
  intro u v huv
  have hlocal := (obcParentHamiltonian_apply_eq_zero_iff b A N ψ).mp hzero
    u.length v.length huv u.get v.get
  obtain ⟨X, hX⟩ := (obcPairProjector_apply_eq_zero_iff b A u.length _).mp hlocal
  refine ⟨X, fun i j ↦ ?_⟩
  let σ : Fin 2 → Fin d := ![i, j]
  let w : Fin (u.length + 2 + v.length) → Fin d := Fin.append (Fin.append u.get σ) v.get
  have hw : List.ofFn (fun k : Fin N ↦ w (Fin.cast huv.symm k)) = u ++ i :: j :: v := by
    rw [← List.ofFn_congr huv w]
    simp only [w, List.ofFn_fin_append, List.ofFn_get]
    simp [σ, List.ofFn_succ]
  rw [← hw, hf]
  exact hX σ

/-- The open Hamiltonian kernel is exactly the adjacent-pair trace-section
condition, in list coordinates. Source: PGVWC07, equation unique-OBC,
lines 1213–1220. -/
theorem obcParentHamiltonian_apply_eq_zero_iff_pair_sections (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ) {N : ℕ}
    (ψ : EuclideanSpace ℂ (Fin N → Fin d)) (f : List (Fin d) → ℂ)
    (hf : ∀ w : Fin N → Fin d, f (List.ofFn w) = ψ w) :
    obcParentHamiltonian b A N ψ = 0 ↔
      ∀ u v : List (Fin d), u.length + 2 + v.length = N →
        ∃ X : Matrix (Fin (b (u.length + 2))) (Fin (b u.length)) ℂ,
          ∀ i j, f (u ++ i :: j :: v) =
            Matrix.trace (X * A u.length i * A (u.length + 1) j) := by
  constructor
  · exact obcParentHamiltonian_pair_sections_of_apply_eq_zero b A ψ f hf
  · intro hpair
    apply (obcParentHamiltonian_apply_eq_zero_iff b A N ψ).mpr
    intro p q h u v
    have key : ∀ m : ℕ, m = (List.ofFn u).length →
        ∃ X : Matrix (Fin (b (m + 2))) (Fin (b m)) ℂ,
          ∀ i j, f (List.ofFn u ++ i :: j :: List.ofFn v) =
            Matrix.trace (X * A m i * A (m + 1) j) := by
      intro m hm
      subst hm
      exact hpair (List.ofFn u) (List.ofFn v) (by simp only [List.length_ofFn]; omega)
    obtain ⟨X, hX⟩ := key p List.length_ofFn.symm
    apply (obcPairProjector_apply_eq_zero_iff b A p _).mpr
    refine ⟨X, fun σ ↦ ?_⟩
    change ψ (fun k : Fin N ↦
      Fin.append (Fin.append u σ) v (Fin.cast h.symm k)) = _
    rw [← hf, ← List.ofFn_congr h (Fin.append (Fin.append u σ) v)]
    simp only [List.ofFn_fin_append]
    simpa [List.ofFn_succ, List.append_assoc] using hX (σ 0) (σ 1)

end Matrix
