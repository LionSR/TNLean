/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.OpenBoundary.VaryingOBCReconstruction
import QICLean.ManyBody.Hamiltonian.FrustrationFree
import QICLean.ManyBody.Hamiltonian.Models
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Local projector kernels on a varying-bond open chain

The two-site boundary range uses the rectangular matrices at each bond.
Its orthogonal complement defines the local parent projector. The parent interaction on the
open chain places the matrix of the projector at each position on the two sites of that
position (`ManyBody.Interaction.ofPlaceAlong`), so each term acts as the identity on the
remaining sites and there is no cyclic interaction across the endpoints. Fixing a prefix
and a suffix gives a coordinate restriction to the intervening pair.

Positivity identifies the kernel of the resulting finite Hamiltonian with the
adjacent-pair trace sections used in the open-chain reconstruction.
No injectivity or canonical normalization is needed for this kernel identification.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 9 and the first step of its proof,
`Papers/quant-ph_0608197/MPSarchive.tex`, lines 1195–1222.
-/

open scoped BigOperators ComplexOrder Matrix InnerProductSpace

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

/-- The configuration of the chain with prefix `u`, pair `a` and suffix `w`. -/
private def obcPairCfg {N p q : ℕ} (h : p + 2 + q = N) (u : Fin p → Fin d)
    (a : Fin 2 → Fin d) (w : Fin q → Fin d) : Fin N → Fin d :=
  fun i ↦ Fin.append (Fin.append u a) w (Fin.cast h.symm i)

private theorem obcPairCfg_chainWindow {N p q : ℕ} (h : p + 2 + q = N) (u : Fin p → Fin d)
    (a : Fin 2 → Fin d) (w : Fin q → Fin d) (j : Fin 2) :
    obcPairCfg h u a w (ManyBody.chainWindow (N := N) (k := 2) p (by omega) j) = a j := by
  have hj : Fin.cast h.symm (ManyBody.chainWindow (N := N) (k := 2) p (by omega) j) =
      Fin.castAdd q (Fin.natAdd p j) := Fin.ext rfl
  rw [obcPairCfg, hj, Fin.append_left, Fin.append_right]

private theorem obcPairCfg_of_forall_chainWindow_ne {N p q : ℕ} (h : p + 2 + q = N)
    (u : Fin p → Fin d) (a a' : Fin 2 → Fin d) (w : Fin q → Fin d) {v : Fin N}
    (hv : ∀ j, ManyBody.chainWindow (N := N) (k := 2) p (by omega) j ≠ v) :
    obcPairCfg h u a' w v = obcPairCfg h u a w v := by
  have key : ∀ v' : Fin (p + 2 + q), (∀ j : Fin 2, p + j.val ≠ v'.val) →
      Fin.append (Fin.append u a') w v' = Fin.append (Fin.append u a) w v' := by
    intro v' hv'
    induction v' using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left k => simp only [Fin.append_left]
      | right j => exact absurd rfl (hv' j)
    | right k => simp only [Fin.append_right]
  exact key _ fun j hj ↦ hv j (Fin.ext hj)

private theorem obcPairCfg_self {N p q : ℕ} (h : p + 2 + q = N) (σ : Fin N → Fin d) :
    obcPairCfg h (fun i ↦ σ (Fin.cast h (Fin.castAdd q (Fin.castAdd 2 i))))
      (fun j ↦ σ (ManyBody.chainWindow (N := N) (k := 2) p (by omega) j))
      (fun k ↦ σ (Fin.cast h (Fin.natAdd (p + 2) k))) = σ := by
  have key : ∀ v' : Fin (p + 2 + q),
      Fin.append (Fin.append (fun i ↦ σ (Fin.cast h (Fin.castAdd q (Fin.castAdd 2 i))))
        (fun j ↦ σ (ManyBody.chainWindow (N := N) (k := 2) p (by omega) j)))
        (fun k ↦ σ (Fin.cast h (Fin.natAdd (p + 2) k))) v' = σ (Fin.cast h v') := by
    intro v'
    induction v' using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left k => simp only [Fin.append_left]
      | right j =>
        simp only [Fin.append_left, Fin.append_right]
        exact congrArg σ (Fin.ext rfl)
    | right k => simp only [Fin.append_right]
  funext v
  exact (key (Fin.cast h.symm v)).trans (congrArg σ (Fin.ext rfl))

/-- **The parent interaction on the open chain with varying bonds.** On the open chain of `N`
sites, the term at the position `p`, for \(p + 2 \le N\), is the matrix of the pair projector at `p`
placed on the two sites `p` and \(p + 1\) (`ManyBody.Interaction.ofPlaceAlong`); there is no term
across the endpoints. Its Hamiltonian is the open parent Hamiltonian. Source: PGVWC07,
Theorem 9, lines 1201–1217. -/
noncomputable abbrev obcParentInteraction (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ) (N : ℕ) :=
  ManyBody.Interaction.ofPlaceAlong (α := Fin d)
    (fun p : Fin (N - 1) ↦ ManyBody.chainWindow (N := N) (k := 2) p.val (by omega))
    (fun p ↦ Matrix.toEuclideanLin.symm (obcPairProjector b A p.val))

/-- The terms of the parent interaction on the open chain with varying bonds are positive
semidefinite. Source: PGVWC07, Theorem 9 proof, lines 1213–1217. -/
theorem posSemidef_obcParentInteraction_term (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ) (N : ℕ) (p : Fin (N - 1)) :
    ((obcParentInteraction b A N).term p).PosSemidef :=
  ManyBody.posSemidef_placeAlong (X := fun _ ↦ Fin d) _
    (Matrix.isPositive_toEuclideanLin_iff.mp (by
      rw [LinearEquiv.apply_symm_apply]
      exact obcPairProjector_isPositive b A p.val))

/-- The Hamiltonian of the parent interaction on the open chain with varying bonds is positive
semidefinite. Source: PGVWC07, Theorem 9 proof, lines 1213–1217. -/
theorem posSemidef_hamiltonian_obcParentInteraction (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ) (N : ℕ) :
    (obcParentInteraction b A N).hamiltonian.PosSemidef :=
  ManyBody.Interaction.posSemidef_hamiltonian (posSemidef_obcParentInteraction_term b A N)

private theorem placeAlong_chainWindow_obcPairProjector_mulVec_apply (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ) {N p q : ℕ}
    (h : p + 2 + q = N) (ψ : EuclideanSpace ℂ (Fin N → Fin d)) (u : Fin p → Fin d)
    (a : Fin 2 → Fin d) (w : Fin q → Fin d) :
    (ManyBody.placeAlong (X := fun _ ↦ Fin d)
        (ManyBody.chainWindow (N := N) (k := 2) p (by omega))
        (Matrix.toEuclideanLin.symm (obcPairProjector b A p)) *ᵥ ψ.ofLp) (obcPairCfg h u a w) =
      obcPairProjector b A p (obcPairSection h u w ψ) a := by
  rw [ManyBody.placeAlong_mulVec_apply_of _ _ _ _ (fun a' ↦ obcPairCfg h u a' w)
    (fun a' j ↦ obcPairCfg_chainWindow h u a' w j)
    (fun a' v hv ↦ obcPairCfg_of_forall_chainWindow_ne h u a a' w hv)]
  have hT : obcPairProjector b A p (obcPairSection h u w ψ) =
      Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm (obcPairProjector b A p))
        (obcPairSection h u w ψ) := by
    rw [LinearEquiv.apply_symm_apply]
  rw [hT, Matrix.toLpLin_apply]
  simp only [funext (obcPairCfg_chainWindow h u a w)]
  rfl

private theorem placeAlong_chainWindow_obcPairProjector_mulVec_eq_zero_iff (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ) {N p q : ℕ}
    (h : p + 2 + q = N) (ψ : EuclideanSpace ℂ (Fin N → Fin d)) :
    ManyBody.placeAlong (X := fun _ ↦ Fin d)
        (ManyBody.chainWindow (N := N) (k := 2) p (by omega))
        (Matrix.toEuclideanLin.symm (obcPairProjector b A p)) *ᵥ ψ.ofLp = 0 ↔
      ∀ (u : Fin p → Fin d) (w : Fin q → Fin d),
        obcPairProjector b A p (obcPairSection h u w ψ) = 0 := by
  constructor
  · intro hzero u w
    ext a
    rw [← placeAlong_chainWindow_obcPairProjector_mulVec_apply b A h ψ u a w, hzero]
    rfl
  · intro hzero
    funext σ
    rw [← obcPairCfg_self h σ, placeAlong_chainWindow_obcPairProjector_mulVec_apply, hzero]
    rfl

/-- The Hamiltonian vanishes exactly when every fixed-outside pair
section belongs to the two-site boundary range. Source: PGVWC07,
equation unique-OBC, lines 1213–1220. -/
theorem hamiltonian_obcParentInteraction_apply_eq_zero_iff (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ) (N : ℕ)
    (ψ : EuclideanSpace ℂ (Fin N → Fin d)) :
    Matrix.toEuclideanLin (obcParentInteraction b A N).hamiltonian ψ = 0 ↔
      ∀ (p q : ℕ) (h : p + 2 + q = N) (u : Fin p → Fin d) (w : Fin q → Fin d),
        obcPairProjector b A p (obcPairSection h u w ψ) = 0 := by
  rw [Matrix.toLpLin_apply, WithLp.toLp_eq_zero, ManyBody.Interaction.hamiltonian_mulVec_eq_zero_iff
    (posSemidef_obcParentInteraction_term b A N)]
  constructor
  · intro hzero p q h u w
    exact (placeAlong_chainWindow_obcPairProjector_mulVec_eq_zero_iff b A h ψ).mp
      (hzero ⟨p, by omega⟩) u w
  · intro hzero p
    exact (placeAlong_chainWindow_obcPairProjector_mulVec_eq_zero_iff b A
      (show p.val + 2 + (N - (p.val + 2)) = N by omega) ψ).mpr fun u w ↦ hzero _ _ _ u w

/-- The kernel of the open Hamiltonian gives the list-indexed pair
sections needed for reconstruction along the whole chain. The coefficient
identification only changes the representation of a physical word.
Source: PGVWC07, equation unique-OBC, lines 1213–1220. -/
theorem pair_sections_of_hamiltonian_obcParentInteraction_apply_eq_zero (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ) {N : ℕ}
    (ψ : EuclideanSpace ℂ (Fin N → Fin d)) (f : List (Fin d) → ℂ)
    (hf : ∀ w : Fin N → Fin d, f (List.ofFn w) = ψ w)
    (hzero : Matrix.toEuclideanLin (obcParentInteraction b A N).hamiltonian ψ = 0) :
    ∀ u v : List (Fin d), u.length + 2 + v.length = N →
      ∃ X : Matrix (Fin (b (u.length + 2))) (Fin (b u.length)) ℂ,
        ∀ i j, f (u ++ i :: j :: v) =
          Matrix.trace (X * A u.length i * A (u.length + 1) j) := by
  intro u v huv
  have hlocal := (hamiltonian_obcParentInteraction_apply_eq_zero_iff b A N ψ).mp hzero
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
theorem hamiltonian_obcParentInteraction_apply_eq_zero_iff_pair_sections (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ) {N : ℕ}
    (ψ : EuclideanSpace ℂ (Fin N → Fin d)) (f : List (Fin d) → ℂ)
    (hf : ∀ w : Fin N → Fin d, f (List.ofFn w) = ψ w) :
    Matrix.toEuclideanLin (obcParentInteraction b A N).hamiltonian ψ = 0 ↔
      ∀ u v : List (Fin d), u.length + 2 + v.length = N →
        ∃ X : Matrix (Fin (b (u.length + 2))) (Fin (b u.length)) ℂ,
          ∀ i j, f (u ++ i :: j :: v) =
            Matrix.trace (X * A u.length i * A (u.length + 1) j) := by
  constructor
  · exact pair_sections_of_hamiltonian_obcParentInteraction_apply_eq_zero b A ψ f hf
  · intro hpair
    apply (hamiltonian_obcParentInteraction_apply_eq_zero_iff b A N ψ).mpr
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
