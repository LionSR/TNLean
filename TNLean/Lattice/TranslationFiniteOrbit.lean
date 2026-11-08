/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Finite-dimensional translation orbits

The characteristic polynomial of a norm-preserving linear map has all roots on the
unit circle. Its constant coefficient has modulus one, and the sum of the moduli of
its remaining coefficients is at most `2^m - 1`, where `m` is the dimension.
Cayley–Hamilton therefore recovers a vector from its first `m` forward iterates,
with a uniform bound on the sum of the coefficient moduli.

For translations on the ground space, apply this calculation to conjugation on its
operator space, of dimension the square of the ground-space dimension. No bound on
momentum denominators is imposed. This is the finite-dimensional step in the
translation argument omitted in Hastings, arXiv:cond-mat/0508554v3, lines 1644–1654.
-/

open Polynomial Finset

namespace TNLean.Lattice

namespace FiniteOrbitProof

private theorem monic_mahlerMeasure_eq_one {p : ℂ[X]} (hp : p.Monic)
    (hr : ∀ z ∈ p.roots, ‖z‖ = 1) : p.mahlerMeasure = 1 := by
  rw [Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots,
    hp.leadingCoeff, norm_one, one_mul]
  have hm : p.roots.map (fun z ↦ max 1 ‖z‖) = p.roots.map (fun _ ↦ (1 : ℝ)) :=
    Multiset.map_congr rfl fun z hz ↦ by rw [hr z hz]; exact max_self 1
  rw [hm]
  simp


private theorem norm_coeff_zero_eq_one {p : ℂ[X]} (hp : p.Monic)
    (hr : ∀ z ∈ p.roots, ‖z‖ = 1) : ‖p.coeff 0‖ = 1 := by
  rw [(IsAlgClosed.splits p).coeff_zero_eq_prod_roots_of_monic hp]
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Multiset.norm_prod]
  have hm : p.roots.map norm = p.roots.map (fun _ ↦ (1 : ℝ)) :=
    Multiset.map_congr rfl fun z hz ↦ hr z hz
  rw [hm]
  simp


variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

private theorem norm_root_charpoly_eq_one (T : Module.End ℂ V)
    (hT : ∀ x, ‖T x‖ = ‖x‖) (z : ℂ) (hz : z ∈ T.charpoly.roots) : ‖z‖ = 1 := by
  have hr := (Polynomial.mem_roots T.charpoly_monic.ne_zero).mp hz
  have hev := (Module.End.hasEigenvalue_iff_isRoot_charpoly T z).mpr hr
  obtain ⟨x, hx⟩ := hev.exists_hasEigenvector
  have hn : ‖x‖ = ‖z‖ * ‖x‖ := by
    calc
      ‖x‖ = ‖T x‖ := (hT x).symm
      _ = ‖z • x‖ := congrArg norm (Module.End.mem_eigenspace_iff.mp hx.1)
      _ = ‖z‖ * ‖x‖ := norm_smul z x
  exact (mul_right_cancel₀ (norm_ne_zero_iff.mpr hx.2)) (by simpa using hn.symm)


private theorem exists_power_recurrence_of_roots_norm_eq_one (T : Module.End ℂ V)
    (hr : ∀ z ∈ T.charpoly.roots, ‖z‖ = 1) :
    ∃ c : Fin (Module.finrank ℂ V) → ℂ,
      (∑ k, ‖c k‖) ≤ (2 : ℝ) ^ Module.finrank ℂ V - 1 ∧
      (1 : Module.End ℂ V) = ∑ k, c k • T ^ ((k : ℕ) + 1) := by
  let m := Module.finrank ℂ V
  let p := T.charpoly
  have hm : p.natDegree = m := T.charpoly_natDegree
  have hmahler : p.mahlerMeasure = 1 := monic_mahlerMeasure_eq_one T.charpoly_monic hr
  have hc0 : ‖p.coeff 0‖ = 1 := norm_coeff_zero_eq_one T.charpoly_monic hr
  have hc0ne : p.coeff 0 ≠ 0 := norm_ne_zero_iff.mp (by rw [hc0]; norm_num)
  let c : Fin m → ℂ := fun k ↦ -((p.coeff 0)⁻¹) * p.coeff ((k : ℕ) + 1)
  refine ⟨c, ?_, ?_⟩
  · have hsum : (∑ k : Fin m, (m.choose ((k : ℕ) + 1) : ℝ)) = (2 : ℝ) ^ m - 1 := by
      have hh := Nat.sum_range_choose m
      rw [Finset.sum_range_succ'] at hh
      simp only [Nat.choose_zero_right] at hh
      have hreal : (∑ k ∈ Finset.range m, (m.choose (k + 1) : ℝ)) + 1 = (2 : ℝ) ^ m := by
        exact_mod_cast hh
      rw [Finset.sum_range] at hreal
      linarith
    refine (Finset.sum_le_sum fun k _ ↦ ?_).trans_eq hsum
    dsimp [c]
    rw [norm_mul, norm_neg, norm_inv, hc0, inv_one, one_mul]
    simpa only [hmahler, mul_one, hm] using p.norm_coeff_le_choose_mul_mahlerMeasure ((k : ℕ) + 1)
  · have hch : (∑ k : Fin m, p.coeff ((k : ℕ) + 1) • T ^ ((k : ℕ) + 1)) +
        p.coeff 0 • (1 : Module.End ℂ V) = 0 := by
      have hh := T.aeval_self_charpoly
      change Polynomial.aeval T p = 0 at hh
      rw [Polynomial.aeval_eq_sum_range, hm, Finset.sum_range_succ',
        Finset.sum_range, pow_zero] at hh
      exact hh
    have hch' : (∑ k : Fin m, p.coeff ((k : ℕ) + 1) • T ^ ((k : ℕ) + 1)) =
        -(p.coeff 0 • (1 : Module.End ℂ V)) := eq_neg_of_add_eq_zero_left hch
    symm
    calc
      _ = -((p.coeff 0)⁻¹) • (∑ k : Fin m, p.coeff ((k : ℕ) + 1) • T ^ ((k : ℕ) + 1)) := by
        simp only [c, Finset.smul_sum, smul_smul]
        rfl
      _ = _ := by
        rw [hch']
        have hs : -((p.coeff 0)⁻¹) * p.coeff 0 = -1 := by
          rw [neg_mul, inv_mul_cancel₀ hc0ne]
        rw [smul_neg, smul_smul, hs, neg_one_smul, neg_neg]


private theorem exists_power_recurrence_of_norm_eq (T : Module.End ℂ V)
    (hT : ∀ x, ‖T x‖ = ‖x‖) :
    ∃ c : Fin (Module.finrank ℂ V) → ℂ,
      (∑ k, ‖c k‖) ≤ (2 : ℝ) ^ Module.finrank ℂ V - 1 ∧
      (1 : Module.End ℂ V) = ∑ k, c k • T ^ ((k : ℕ) + 1) :=
  exists_power_recurrence_of_roots_norm_eq_one T (norm_root_charpoly_eq_one T hT)


private theorem norm_apply_le_of_power_bounds
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (T : Module.End ℂ V) (hT : ∀ x, ‖T x‖ = ‖x‖) (F : V →ₗ[ℂ] W) (x : V)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ k : Fin (Module.finrank ℂ V), ‖F ((T ^ ((k : ℕ) + 1)) x)‖ ≤ B) :
    ‖F x‖ ≤ ((2 : ℝ) ^ Module.finrank ℂ V - 1) * B := by
  obtain ⟨c, hc, hpoly⟩ := exists_power_recurrence_of_norm_eq T hT
  have hx : x = ∑ k, c k • ((T ^ ((k : ℕ) + 1)) x) := by
    simpa only [Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply] using
      congrArg (fun A : Module.End ℂ V ↦ A x) hpoly
  have hF : F x = ∑ k, c k • F ((T ^ ((k : ℕ) + 1)) x) := by
    calc
      F x = F (∑ k, c k • ((T ^ ((k : ℕ) + 1)) x)) := congrArg F hx
      _ = _ := by rw [map_sum]; simp only [map_smul]
  calc
    ‖F x‖ = ‖∑ k, c k • F ((T ^ ((k : ℕ) + 1)) x)‖ := congrArg norm hF
    _ ≤ ∑ k, ‖c k • F ((T ^ ((k : ℕ) + 1)) x)‖ := norm_sum_le _ _
    _ = ∑ k, ‖c k‖ * ‖F ((T ^ ((k : ℕ) + 1)) x)‖ := by simp only [norm_smul]
    _ ≤ ∑ k, ‖c k‖ * B := Finset.sum_le_sum fun k _ ↦
      mul_le_mul_of_nonneg_left (hbound k) (norm_nonneg _)
    _ = (∑ k, ‖c k‖) * B := (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hB


private theorem finrank_operator_space {K : Type*} [NormedAddCommGroup K]
    [NormedSpace ℂ K] [FiniteDimensional ℂ K] :
    Module.finrank ℂ (K →L[ℂ] K) = (Module.finrank ℂ K) ^ 2 := by
  rw [← (LinearMap.toContinuousLinearMap : (K →ₗ[ℂ] K) ≃ₗ[ℂ] (K →L[ℂ] K)).finrank_eq]
  rw [← ((Module.finBasis ℂ K).constr ℂ (M' := K)).finrank_eq]
  simp [Module.finrank_pi_fintype, pow_two]

/-- On a ground space of dimension `n`, commutator bounds along the first `n²` iterates of
an isometric translation orbit control the original commutator, uniformly in all translation
phases. This is the finite-dimensional step omitted in Hastings,
arXiv:cond-mat/0508554v3, lines 1644–1654. -/
theorem _root_.TNLean.Lattice.norm_commutator_le_of_finite_translation_orbit_bounds
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K] [FiniteDimensional ℂ K]
    (T : Module.End ℂ (K →L[ℂ] K)) (hT : ∀ B, ‖T B‖ = ‖B‖)
    (A B : K →L[ℂ] K) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ k : Fin ((Module.finrank ℂ K) ^ 2),
      ‖A * ((T ^ ((k : ℕ) + 1)) B) - ((T ^ ((k : ℕ) + 1)) B) * A‖ ≤ C) :
    ‖A * B - B * A‖ ≤ ((2 : ℝ) ^ ((Module.finrank ℂ K) ^ 2) - 1) * C := by
  let F : (K →L[ℂ] K) →ₗ[ℂ] (K →L[ℂ] K) :=
    LinearMap.mul ℂ (K →L[ℂ] K) A - LinearMap.mulRight ℂ A
  have hb : ∀ k : Fin (Module.finrank ℂ (K →L[ℂ] K)),
      ‖F ((T ^ ((k : ℕ) + 1)) B)‖ ≤ C := by
    rw [finrank_operator_space]
    simpa only [F, LinearMap.sub_apply, LinearMap.mul_apply', LinearMap.mulRight_apply] using hbound
  have hf := norm_apply_le_of_power_bounds T hT F B hC hb
  simpa only [F, finrank_operator_space, LinearMap.sub_apply, LinearMap.mul_apply',
    LinearMap.mulRight_apply] using hf

end FiniteOrbitProof

end TNLean.Lattice
