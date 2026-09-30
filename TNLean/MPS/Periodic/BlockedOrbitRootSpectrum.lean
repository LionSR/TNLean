/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.BlockedOrbitMicroprojections
import TNLean.Algebra.CyclicShiftSpectrum
import TNLean.Algebra.CyclicOrbitIndex
import QICLean.Channel.Peripheral.AdjointSpectrum

/-!
# Roots of unity in a compressed orbit spectrum

The original cyclic projections, compressed to a blocked shift orbit,
remain independent and rotate under the adjoint transfer map. Their
Fourier combinations give all roots of unity of the orbit length as
eigenvalues.

Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 765--806.
-/

open scoped Matrix

namespace MPSTensor

/-- A full cyclic enumeration of the microsectors in one compressed
orbit forces every root of unity of the orbit length into its adjoint
transfer spectrum. Source: arXiv:1708.00029, Lemma
`lem:blocking-arbitrary`, lines 765--806. -/
theorem compressed_blockTensor_roots_of_unity_eigenvalues
    {d D m r s p n : ℕ} [NeZero m]
    (A : MPSTensor d D) (C : MPSTensor (blockPhysDim d p) n)
    (α : Fin m → Fin r) (P : Fin m → MatrixAlg D)
    (hP : ∀ u, IsOrthogonalProjection (P u))
    (hPne : ∀ u, P u ≠ 0)
    (horth : ∀ u v, u ≠ v → P u * P v = 0)
    (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (hshift : ∀ u i, P u * A i = A i * P (u + 1))
    (j : Fin r) (f : Fin (s + 1) → Fin m)
    (hf : Function.Injective f)
    (hαf : ∀ t, α (f t) = j)
    (hrotate : ∀ t, f (finRotate (s + 1) t) =
      f t + p • (1 : Fin m))
    (V : Matrix (Fin D) (Fin n) ℂ)
    (hVrange : V * Vᴴ = orbitProjection α P j)
    (hC : ∀ I, C I = Vᴴ * blockTensor A p I * V)
    (ζ : ℂ) (hζ : ζ ^ (s + 1) = 1) :
    Module.End.HasEigenvalue (Kraus.mapLM (fun I => (C I)ᴴ)) ζ := by
  let R : Fin (s + 1) → MatrixAlg n :=
    fun t => Vᴴ * P (f t) * V
  have hlin : LinearIndependent ℂ R :=
    linearIndependent_compressed_cyclic_projections α P hP hPne
      horth j f hf hαf V hVrange
  have hshiftR : ∀ t, Kraus.mapLM (fun I => (C I)ᴴ) (R t) =
      R (finRotate (s + 1) t) := by
    intro t
    have hrange : V * Vᴴ = orbitProjection α P (α (f t)) := by
      rw [hαf t]
      exact hVrange
    change Kraus.map (fun I => (C I)ᴴ) (Vᴴ * P (f t) * V) =
      Vᴴ * P (f (finRotate (s + 1) t)) * V
    rw [hrotate]
    exact compressed_blockTensor_cyclic_projection_shift A C α P
      hP horth hTP hshift (f t) V hrange hC
  exact LinearMap.hasEigenvalue_of_cyclic_shift
    (Kraus.mapLM (fun I => (C I)ᴴ)) R hlin hshiftR ζ hζ

/-- The orbit enumeration by repeated blocked shifts supplies the cyclic
index required in the preceding spectrum theorem. Source:
arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 765--806. -/
theorem compressed_blockTensor_roots_of_unity_eigenvalues_of_orbit
    {d D m r s p n : ℕ} [NeZero m]
    (A : MPSTensor d D) (C : MPSTensor (blockPhysDim d p) n)
    (α : Fin m → Fin r) (P : Fin m → MatrixAlg D)
    (hP : ∀ u, IsOrthogonalProjection (P u))
    (hPne : ∀ u, P u ≠ 0)
    (horth : ∀ u v, u ≠ v → P u * P v = 0)
    (hα : ∀ u, α (u + p • (1 : Fin m)) = α u)
    (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (hshift : ∀ u i, P u * A i = A i * P (u + 1))
    (u : Fin m) (hord : addOrderOf (p : ZMod m) = s + 1)
    (V : Matrix (Fin D) (Fin n) ℂ)
    (hVrange : V * Vᴴ = orbitProjection α P (α u))
    (hC : ∀ I, C I = Vᴴ * blockTensor A p I * V)
    (ζ : ℂ) (hζ : ζ ^ (s + 1) = 1) :
    Module.End.HasEigenvalue (Kraus.mapLM (fun I => (C I)ᴴ)) ζ := by
  let e : Fin m ≃+* ZMod m := ZMod.finEquiv m
  let f : Fin (s + 1) → Fin m :=
    fun t => e.symm (e u + t.val • (p : ZMod m))
  have hf : Function.Injective f := by
    intro t v htv
    apply ZMod.orbitIndex_injective (p : ZMod m) (e u) hord
    simpa [f] using congrArg e htv
  have hfstep : ∀ t : Fin (s + 1),
      f (finRotate (s + 1) t) = f t + p • (1 : Fin m) := by
    intro t
    apply e.injective
    simpa [f, map_add, map_nsmul] using
      ZMod.orbitIndex_finRotate (p : ZMod m) (e u) hord t
  have hαpow : ∀ k : ℕ, α (u + k • (p • (1 : Fin m))) = α u := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [succ_nsmul, ← add_assoc, hα, ih]
  have hαf : ∀ t, α (f t) = α u := by
    intro t
    have hft : f t = u + t.val • (p • (1 : Fin m)) := by
      apply e.injective
      simp [f, map_add, map_nsmul]
    rw [hft]
    exact hαpow t.val
  exact compressed_blockTensor_roots_of_unity_eigenvalues
    A C α P hP hPne horth hTP hshift (α u) f hf hαf
      hfstep V hVrange hC ζ hζ

/-- Every root of unity of the shift-orbit length is a peripheral
eigenvalue of the compressed transfer map. Source: arXiv:1708.00029,
Lemma `lem:blocking-arbitrary`, lines 765--806. -/
theorem compressed_blockTensor_roots_subset_peripheral
    {d D m r s p n : ℕ} [NeZero m]
    (A : MPSTensor d D) (C : MPSTensor (blockPhysDim d p) n)
    (α : Fin m → Fin r) (P : Fin m → MatrixAlg D)
    (hP : ∀ u, IsOrthogonalProjection (P u))
    (hPne : ∀ u, P u ≠ 0)
    (horth : ∀ u v, u ≠ v → P u * P v = 0)
    (hα : ∀ u, α (u + p • (1 : Fin m)) = α u)
    (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (hshift : ∀ u i, P u * A i = A i * P (u + 1))
    (u : Fin m) (hord : addOrderOf (p : ZMod m) = s + 1)
    (V : Matrix (Fin D) (Fin n) ℂ)
    (hVrange : V * Vᴴ = orbitProjection α P (α u))
    (hC : ∀ I, C I = Vᴴ * blockTensor A p I * V) :
    {ζ : ℂ | ζ ^ (s + 1) = 1} ⊆
      peripheralEigenvalues (Kraus.mapLM C) := by
  intro ζ hζ
  have hstar : (star ζ) ^ (s + 1) = 1 := by
    rw [← star_pow, hζ, star_one]
  have hEigAdj := compressed_blockTensor_roots_of_unity_eigenvalues_of_orbit
    A C α P hP hPne horth hα hTP hshift u hord V hVrange hC
      (star ζ) hstar
  have hEig : Module.End.HasEigenvalue (Kraus.mapLM C) ζ := by
    simpa only [star_star] using
      (Kraus.hasEigenvalue_mapLM_conjTranspose_iff C (star ζ)).mp hEigAdj
  have hnormpow : ‖ζ‖ ^ (s + 1) = 1 := by
    simpa only [norm_pow, norm_one] using congrArg norm hζ
  have hnorm : ‖ζ‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg ζ) (Nat.succ_ne_zero s)).mp hnormpow
  exact ⟨hEig, hnorm⟩

end MPSTensor
