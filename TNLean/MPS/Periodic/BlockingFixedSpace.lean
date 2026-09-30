/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.BlockingEigenvalues
import TNLean.MPS.Periodic.SectorIrreducibility.HLift
import QICLean.Channel.Schwarz.Closure
import QICLean.Channel.SingleKrausPositivity
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.FieldTheory.Separable
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Periods of fixed points after blocking

The fixed space of a positive power has finite-order dynamics. Its vectors
supported on one step-orbit projection are scalar multiples of that projection.
Lifting invariant projections from a compressed block then proves irreducibility.
Together with the exact peripheral spectrum, this proves the prescribed-blocking
conclusion of arXiv:1708.00029, Lemma `lem:blocking-arbitrary`.

## Main results

* `IsPeriodic.adjoint_pow_fixed_iff_gcd`: the fixed space depends only on the gcd.
* `IsPeriodic.adjoint_pow_fixed_of_pow_fixed`: a fixed point of a positive power
  of the adjoint transfer map is fixed by its `m`-th power.
* `sum_adjoint_pow_stepOrbitProjection`: the adjoint iterates of one step-orbit
  projection resolve the identity.
* `IsPeriodic.adjoint_pow_fixed_eq_smul_stepOrbitProjection`: supported fixed-point rigidity.
* `IsPeriodic.isIrreducibleFamily_compressed_stepOrbit`: the compressed blocks are irreducible.
-/

open scoped Matrix BigOperators
open Fin.NatCast

namespace MPSTensor

private theorem pow_fixed_of_peripheral_roots {M : Type*} [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (f : M →ₗ[ℂ] M) {m p : ℕ} (hp : 0 < p)
    (hroots : ∀ z, Module.End.HasEigenvalue f z → ‖z‖ = 1 → z ^ m = 1)
    {x : M} (hx : (f ^ p) x = x) : (f ^ m) x = x := by
  let S := Module.End.eigenspace (f ^ p) 1
  have hS : ∀ y ∈ S, f y ∈ S := by
    intro y hy
    simp only [S, Module.End.mem_eigenspace_iff, one_smul] at hy ⊢
    rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply, hy]
  let g := f.restrict hS
  have hg : g ^ p = 1 := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    change (((f.restrict hS) ^ p) y : M) = (y : M)
    rw [Module.End.pow_restrict]
    exact (Module.End.mem_eigenspace_iff.mp y.property).trans (one_smul ℂ (y : M))
  have hsemi : Module.End.IsSemisimple g := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      ((Polynomial.X_pow_sub_one_separable_iff.mpr
        (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp) : (p : ℂ) ≠ 0)).squarefree)
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, hg, sub_self]
  have hle : (⨆ z : ℂ, Module.End.eigenspace g z) ≤ Module.End.eigenspace (g ^ m) 1 := by
    apply iSup_le
    intro z y hy
    by_cases hy0 : y = 0
    · subst y
      exact Submodule.zero_mem _
    have hv : Module.End.HasEigenvector g z y :=
      Module.End.hasEigenvector_iff.mpr ⟨hy, hy0⟩
    have hzp : z ^ p = 1 := by
      have he := hv.pow_apply p
      rw [hg, Module.End.one_apply] at he
      exact smul_left_injective ℂ hy0 (he.symm.trans (one_smul ℂ y).symm)
    have hnorm : ‖z‖ = 1 := by
      apply (pow_eq_one_iff_of_nonneg (norm_nonneg z) (Nat.ne_of_gt hp)).mp
      simpa only [norm_pow, norm_one] using congrArg norm hzp
    have hyne : (y : M) ≠ 0 := fun h => hy0 (Subtype.ext h)
    have hfy : f (y : M) = z • (y : M) := congrArg Subtype.val hv.apply_eq_smul
    have hzm := hroots z (hasEigenvalue_of_eigenvector_eq f z y hfy hyne) hnorm
    rw [Module.End.mem_eigenspace_iff, hv.pow_apply m, hzm]
  have hxS : x ∈ S := by
    simpa only [S, Module.End.mem_eigenspace_iff, one_smul] using hx
  have hxg : (⟨x, hxS⟩ : S) ∈ Module.End.eigenspace (g ^ m) 1 :=
    hle (by rw [hsemi.iSup_eigenspace_eq_top]; trivial)
  have he := congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp hxg)
  simp only [one_smul] at he
  change (((f.restrict hS) ^ m) ⟨x, hxS⟩ : M) = x at he
  rw [Module.End.pow_restrict] at he
  exact he

/-- Any vector fixed by a positive power of the adjoint transfer map is fixed
by its m-th power. This is a spectral reduction in the prescribed-blocking argument
of arXiv:1708.00029, Lemma 6. -/
theorem IsPeriodic.adjoint_pow_fixed_of_pow_fixed {d D m : ℕ} {A : MPSTensor d D}
    (hA : IsPeriodic m A) {p : ℕ} (hp : 0 < p)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : (Kraus.transferMap (fun i => (A i)ᴴ) ^ p) X = X) :
    (Kraus.transferMap (fun i => (A i)ᴴ) ^ m) X = X := by
  refine pow_fixed_of_peripheral_roots _ hp ?_ hX
  intro z hz hnorm
  have he := (Kraus.hasEigenvalue_mapLM_conjTranspose_iff A z).mp hz
  have hper : star z ∈ peripheralEigenvalues (Kraus.transferMap A) :=
    ⟨he, by simpa only [norm_star] using hnorm⟩
  rw [hA.peripheral_eq] at hper
  change (star z) ^ m = 1 at hper
  simpa only [star_pow, star_star, star_one] using congrArg star hper

/-- Positive powers have the same adjoint fixed space as the gcd of the power
and the original period. Source: the periodic spectral structure used in
arXiv:1708.00029, Lemma 6. -/
theorem IsPeriodic.adjoint_pow_fixed_iff_gcd {d D m : ℕ} {A : MPSTensor d D}
    (hA : IsPeriodic m A) {p : ℕ} (hp : 0 < p)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    (Kraus.transferMap (fun i => (A i)ᴴ) ^ p) X = X ↔
      (Kraus.transferMap (fun i => (A i)ᴴ) ^ m.gcd p) X = X := by
  let f := Kraus.transferMap (fun i => (A i)ᴴ)
  constructor
  · intro hX
    have hm : Function.IsPeriodicPt f m X := by
      simpa only [Function.IsPeriodicPt, Function.IsFixedPt, f, Module.End.pow_apply]
        using hA.adjoint_pow_fixed_of_pow_fixed hp hX
    have hpX : Function.IsPeriodicPt f p X := by
      simpa only [Function.IsPeriodicPt, Function.IsFixedPt, f, Module.End.pow_apply] using hX
    simpa only [Function.IsPeriodicPt, Function.IsFixedPt, f, Module.End.pow_apply]
      using hm.gcd hpX
  · intro hX
    have hg : Function.IsPeriodicPt f (m.gcd p) X := by
      simpa only [Function.IsPeriodicPt, Function.IsFixedPt, f, Module.End.pow_apply] using hX
    simpa only [Function.IsPeriodicPt, Function.IsFixedPt, f, Module.End.pow_apply]
      using hg.trans_dvd (Nat.gcd_dvd_right m p)

/-- Averaging one grouped projection over gcd(m,p) consecutive adjoint iterates
recovers the identity. Source: the cyclic projections in arXiv:1708.00029, Lemma 6. -/
theorem sum_adjoint_pow_stepOrbitProjection {d D m : ℕ} [NeZero m]
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ) (hsum : ∑ u, P u = 1)
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    (hshift : ∀ u i, P u * A i = A i * P (u + 1))
    (p : ℕ) (a : Fin (m.gcd p)) :
    ∑ j : Fin (m.gcd p), (Kraus.transferMap (fun i => (A i)ᴴ) ^ j.val)
      (stepOrbitProjection P p a) = 1 := by
  let f := Kraus.transferMap (fun i => (A i)ᴴ)
  let e := Fin.stepOrbitEquiv m p (Nat.pos_of_ne_zero (NeZero.ne m))
  have hstep (u : Fin m) : f (P u) = P (u + 1) := by
    simp only [f, Kraus.transferMap_apply, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc, hshift]
    simp only [← Matrix.mul_assoc, ← Finset.sum_mul]
    rw [show (∑ i, (A i)ᴴ * A i) = 1 from hA, Matrix.one_mul]
  have hpow (j : ℕ) (u : Fin m) : (f ^ j) (P u) = P (u + (j : Fin m)) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih, hstep]
      simp only [Nat.cast_add, Nat.cast_one, add_assoc]
  have hcoord (j : Fin (m.gcd p)) (k : Fin (m / m.gcd p)) :
      e (a, k) + (j.val : Fin m) = e (j, k) + (a.val : Fin m) := by
    apply Fin.ext
    change ((a.val + p * k.val) % m + j.val % m) % m =
      ((j.val + p * k.val) % m + a.val % m) % m
    simp only [← Nat.add_mod]
    congr 1
    omega
  change ∑ j : Fin (m.gcd p), (f ^ j.val) (stepOrbitProjection P p a) = 1
  simp only [stepOrbitProjection, map_sum, hpow]
  change ∑ j : Fin (m.gcd p), ∑ k : Fin (m / m.gcd p), P (e (a, k) + (j.val : Fin m)) = 1
  simp_rw [hcoord]
  calc
    ∑ j : Fin (m.gcd p), ∑ k : Fin (m / m.gcd p), P (e (j, k) + (a.val : Fin m)) =
        ∑ u : Fin m, P (u + (a.val : Fin m)) := by
      simpa only [Fintype.sum_prod_type] using e.sum_comp (fun u => P (u + (a.val : Fin m)))
    _ = ∑ u : Fin m, P u := Equiv.sum_comp (Equiv.addRight (a.val : Fin m)) P
    _ = 1 := hsum

/-- An adjoint fixed point of the blocked map supported on one step orbit is scalar
on that orbit. This is the fixed-space rigidity needed for arXiv:1708.00029, Lemma 6. -/
theorem IsPeriodic.adjoint_pow_fixed_eq_smul_stepOrbitProjection
    {d D m : ℕ} [NeZero m] {A : MPSTensor d D} (hA : IsPeriodic m A)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hproj : ∀ u, IsOrthogonalProjection (P u)) (hsum : ∑ u, P u = 1)
    (hshift : ∀ u i, P u * A i = A i * P (u + 1))
    {p : ℕ} (hp : 0 < p) (a : Fin (m.gcd p))
    (X : Matrix (Fin D) (Fin D) ℂ) (hXQ : stepOrbitProjection P p a * X = X)
    (hX : (Kraus.transferMap (fun i => (A i)ᴴ) ^ p) X = X) :
    ∃ c : ℂ, X = c • stepOrbitProjection P p a := by
  let : NeZero D := ⟨hA.bondDim_ne_zero⟩
  let : NeZero (m.gcd p) := ⟨Nat.ne_of_gt (Nat.gcd_pos_of_pos_left p hA.period_pos)⟩
  let f := Kraus.transferMap (fun i => (A i)ᴴ)
  let e := Fin.stepOrbitEquiv m p hA.period_pos
  let Q := stepOrbitProjection P p a
  let R := fun j : Fin (m.gcd p) =>
    ∑ k : Fin (m / m.gcd p), P (e (a, k) + (j.val : Fin m))
  have hmulstep (u : Fin m) (Y : Matrix (Fin D) (Fin D) ℂ) :
      f (P u * Y) = P (u + 1) * f Y := by
    have hs (i : Fin d) : (A i)ᴴ * P u = P (u + 1) * (A i)ᴴ := by
      simpa only [Matrix.conjTranspose_mul, (hproj u).1.eq, (hproj (u + 1)).1.eq]
        using congrArg Matrix.conjTranspose (hshift u i)
    simp only [f, Kraus.transferMap_apply, Matrix.conjTranspose_conjTranspose,
      ← Matrix.mul_assoc, hs]
    simp only [Matrix.mul_assoc, ← Matrix.mul_sum]
  have hiter (j : ℕ) (u : Fin m) (Y : Matrix (Fin D) (Fin D) ℂ) :
      (f ^ j) (P u * Y) = P (u + (j : Fin m)) * (f ^ j) Y := by
    induction j with
    | zero => simp
    | succ j ih =>
      simp only [pow_succ', Module.End.mul_apply, ih, hmulstep, Nat.cast_add,
        Nat.cast_one, add_assoc]
  have hf1 : f 1 = 1 := by
    simpa only [f, Kraus.transferMap_apply, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_one] using (show (∑ i, (A i)ᴴ * A i) = 1 from hA.leftCanonical)
  have hpow1 (j : ℕ) : (f ^ j) 1 = 1 := by
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ', Module.End.mul_apply, ih, hf1]
  have hPj (j : ℕ) (u : Fin m) : (f ^ j) (P u) = P (u + (j : Fin m)) := by
    simpa only [Matrix.mul_one, hpow1] using hiter j u 1
  have hR (j : Fin (m.gcd p)) : (f ^ j.val) Q = R j := by
    simp only [Q, stepOrbitProjection, map_sum, hPj, R, e]
  have hRproj (j : Fin (m.gcd p)) : IsOrthogonalProjection (R j) := by
    apply isOrthogonalProjection_sum_of_pairwise_mul_eq_zero
    · exact fun k => hproj _
    · intro k l hkl
      apply orthogonalProjection_mul_eq_zero_of_sum_eq_one P hproj hsum
      intro he
      exact hkl (congrArg Prod.snd (e.injective (add_right_cancel he)))
  have hRsum : ∑ j, R j = 1 := by
    simpa only [← hR] using
      sum_adjoint_pow_stepOrbitProjection P hsum A hA.leftCanonical hshift p a
  have hR0 : R 0 = Q := by
    simpa only [Fin.val_zero, pow_zero, Module.End.one_apply] using (hR 0).symm
  have hsupport (j : Fin (m.gcd p)) : R j * (f ^ j.val) X = (f ^ j.val) X := by
    have ht : (f ^ j.val) (Q * X) = R j * (f ^ j.val) X := by
      simp only [Q, stepOrbitProjection, Matrix.sum_mul, map_sum, hiter, R, e]
    rw [hXQ] at ht
    exact ht.symm
  have hfix : f (orbitSumProjection (m := m.gcd p) f X) =
      orbitSumProjection (m := m.gcd p) f X :=
    orbitSumProjection_fixed_of_pow_fix ((hA.adjoint_pow_fixed_iff_gcd hp X).mp hX)
  have hUnital : KadisonSchwarz.IsUnitalKraus (fun i => (A i)ᴴ) := by
    simpa only [KadisonSchwarz.IsUnitalKraus, Matrix.conjTranspose_conjTranspose]
      using (show (∑ i, (A i)ᴴ * A i) = 1 from hA.leftCanonical)
  have hIrr : IsIrreducibleMap f := Kraus.isIrreducibleMap_mapLM_conjTranspose A
    (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hA.irreducible)
  obtain ⟨c, hc⟩ := Kraus.fixed_eq_scalar_of_irreducible_unital
    (fun i => (A i)ᴴ) hUnital hIrr (orbitSumProjection (m := m.gcd p) f X) hfix
  have hrecover : Q * orbitSumProjection (m := m.gcd p) f X = X := by
    change Q * (∑ j : Fin (m.gcd p), (f ^ j.val) X) = X
    rw [Matrix.mul_sum, Finset.sum_eq_single 0]
    · simpa only [Fin.val_zero, pow_zero, Module.End.one_apply] using hXQ
    · intro j _ hj
      rw [← hsupport j, ← Matrix.mul_assoc, ← hR0,
        orthogonalProjection_mul_eq_zero_of_sum_eq_one R hRproj hRsum (Ne.symm hj),
        Matrix.zero_mul]
    · simp
  refine ⟨c, ?_⟩
  calc
    X = Q * orbitSumProjection (m := m.gcd p) f X := hrecover.symm
    _ = Q * (c • 1) := by rw [hc]
    _ = c • Q := by simp

/-- Each compressed step-orbit block is irreducible. This completes the
irreducibility assertion of arXiv:1708.00029, Lemma 6. -/
theorem IsPeriodic.isIrreducibleFamily_compressed_stepOrbit
    {d D m n : ℕ} [NeZero m] {A : MPSTensor d D} (hA : IsPeriodic m A)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hproj : ∀ u, IsOrthogonalProjection (P u)) (hsum : ∑ u, P u = 1)
    (hshift : ∀ u i, P u * A i = A i * P (u + 1))
    {p : ℕ} (hp : 0 < p) (a : Fin (m.gcd p))
    (C : MPSTensor (blockPhysDim d p) n) (V : Matrix (Fin D) (Fin n) ℂ)
    (hiso : Vᴴ * V = 1) (hV : V * Vᴴ = stepOrbitProjection P p a)
    (hC : ∀ i, C i = Vᴴ * blockTensor A p i * V) :
    Kraus.IsIrreducibleFamily C := by
  let : NeZero D := ⟨hA.bondDim_ne_zero⟩
  let f := Kraus.transferMap (fun i => (A i)ᴴ)
  let g := Kraus.transferMap (fun i => (C i)ᴴ)
  have hpow : Kraus.transferMap (fun i => (blockTensor A p i)ᴴ) = f ^ p := by
    have h := congrArg Matrix.traceAdjointMap (transferMap_blockTensor A p)
    simpa only [Kraus.transferMap, Matrix.traceAdjointMap_pow,
      Kraus.traceAdjointMap_mapLM_eq_mapLM_conjTranspose] using h
  have hint (i) : (blockTensor A p i)ᴴ * V = V * (C i)ᴴ := by
    have hcomm : (V * Vᴴ) * blockTensor A p i = blockTensor A p i * (V * Vᴴ) := by
      rw [hV]
      exact stepOrbitProjection_mul_blockTensor P A hshift p a i
    have hs := congrArg Matrix.conjTranspose hcomm
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at hs
    calc
      (blockTensor A p i)ᴴ * V = ((blockTensor A p i)ᴴ * (V * Vᴴ)) * V := by
        simp only [Matrix.mul_assoc, hiso, Matrix.mul_one]
      _ = ((V * Vᴴ) * (blockTensor A p i)ᴴ) * V := by rw [hs]
      _ = V * (C i)ᴴ := by
        rw [hC i]
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hlift (Y : Matrix (Fin n) (Fin n) ℂ) :
      (f ^ p) (V * Y * Vᴴ) = V * g Y * Vᴴ := by
    rw [← hpow]
    exact transferMap_conj_of_intertwine _ _ V hint Y
  apply Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM C
  apply (Kraus.isIrreducibleMap_mapLM_conjTranspose_iff C).mp
  intro R hR hInv
  let L := V * R * Vᴴ
  have hLproj : IsOrthogonalProjection L := by
    constructor
    · change (V * R * Vᴴ)ᴴ = V * R * Vᴴ
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hR.1.eq,
        Matrix.mul_assoc]
    · change (V * R * Vᴴ) * (V * R * Vᴴ) = V * R * Vᴴ
      change singleKrausMap V R * singleKrausMap V R =
        singleKrausMap V R
      rw [← Matrix.singleKrausMap_mul_of_isometry V hiso, hR.2]
  have hLinv : PreservesCorner L (f ^ p) := by
    intro Y
    have harg : L * Y * L = V * (R * (Vᴴ * Y * V) * R) * Vᴴ := by
      simp only [L, Matrix.mul_assoc]
    rw [harg, hlift]
    calc
      L * (V * g (R * (Vᴴ * Y * V) * R) * Vᴴ) * L =
          V * (R * g (R * (Vᴴ * Y * V) * R) * R) * Vᴴ := by
        change singleKrausMap V R * singleKrausMap V _ *
          singleKrausMap V R = singleKrausMap V _
        rw [← Matrix.singleKrausMap_mul_of_isometry V hiso,
          ← Matrix.singleKrausMap_mul_of_isometry V hiso]
      _ = V * g (R * (Vᴴ * Y * V) * R) * Vᴴ := by rw [hInv]
  have hLfix : (f ^ p) L = L := hFixUpgrade_of_peripheral hA.leftCanonical
    (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hA.irreducible) hLproj hLinv
  have hLsupport : stepOrbitProjection P p a * L = L := by
    rw [← hV]
    simp only [L, Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc Vᴴ V, hiso, Matrix.one_mul]
  obtain ⟨c, hc⟩ := hA.adjoint_pow_fixed_eq_smul_stepOrbitProjection
    P hproj hsum hshift hp a L hLsupport hLfix
  have hscalar : R = c • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have h := congrArg (fun Z => Vᴴ * Z * V) hc
    rw [← hV] at h
    simp only [L, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc] at h
    simpa only [← Matrix.mul_assoc Vᴴ V, hiso, Matrix.one_mul, Matrix.mul_one] using h
  by_cases hc0 : c = 0
  · left
    simpa only [hc0, zero_smul] using hscalar
  · right
    apply smul_right_injective _ hc0
    calc
      c • R = (c • (1 : Matrix (Fin n) (Fin n) ℂ)) * R := by simp
      _ = R * R := by rw [← hscalar]
      _ = R := hR.2
      _ = c • 1 := hscalar

end MPSTensor
