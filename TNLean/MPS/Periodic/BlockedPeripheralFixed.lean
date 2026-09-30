/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Peripheral.CesaroRecurrence
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Fixed points of a blocked transfer map

A fixed point of a positive power of a trace-preserving positive map belongs
to the peripheral spectral subspace of the original map. This observation is
one step toward identifying the irreducible orbit summands in the blocking
lemma of arXiv:1708.00029, Section 4.1, lines 765--806.
-/

open scoped Matrix Matrix.Norms.Frobenius ComplexOrder MatrixOrder BigOperators
  NNReal ENNReal Topology
open Filter

namespace MPSTensor

private theorem finrank_biSup_le_card_of_finrank_le_one
    {V ι : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (s : Finset ι) (W : ι → Submodule ℂ V)
    (hW : ∀ i ∈ s, Module.finrank ℂ (W i) ≤ 1) :
    Module.finrank ℂ ((⨆ i ∈ s, W i) : Submodule ℂ V) ≤ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.iSup_insert, Finset.card_insert_of_notMem ha]
      have hsup := (W a).finrank_sup_add_finrank_inf_eq
        ((⨆ i ∈ s, W i) : Submodule ℂ V)
      have hsmall : Module.finrank ℂ (W a) ≤ 1 := hW a (Finset.mem_insert_self a s)
      have hrest : Module.finrank ℂ ((⨆ i ∈ s, W i) : Submodule ℂ V) ≤ s.card :=
        ih (fun i hi => hW i (Finset.mem_insert_of_mem hi))
      omega

/-- A fixed point of a positive power has no component in the decaying
spectral subspace. This is the spectral input for the period calculation in
arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 765--806. -/
theorem mem_peripheralSubspace_of_pow_fixed
    {D : ℕ} [NeZero D]
    (T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    {p : ℕ} (hp : 0 < p) (X : Matrix (Fin D) (Fin D) ℂ)
    (hfix : (T ^ p) X = X) : X ∈ T.peripheralSubspace := by
  let Y := X - T.peripheralProjection X
  have hYmem : Y ∈ T.nonPeripheralSubspace := T.sub_peripheralProjection_mem X
  have hcomm := (T.commute_peripheralProjection.pow_right p).eq
  have hYfix : (T ^ p) Y = Y := by
    dsimp [Y]
    rw [map_sub, hfix]
    have hcommX := congrArg (fun f : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) => f X) hcomm
    simp only [Module.End.mul_apply] at hcommX
    rw [← hcommX, hfix]
  have hYpow : ∀ n : ℕ, (T ^ (p * n)) Y = Y := by
    intro n
    rw [pow_mul]
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, ih, hYfix]
  have hb : ∀ μ : ℂ, T.HasEigenvalue μ → ‖μ‖ ≤ 1 :=
    fun μ hμ => (hPos.hasBoundedOrbits_of_tracePreserving hTP).norm_le_one_of_hasEigenvalue hμ
  have hmono : StrictMono (fun n : ℕ => p * n) :=
    strictMono_nat_of_lt_succ (fun n => Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self n) hp)
  have hzero := (T.tendsto_pow_apply_zero_of_mem_nonPeripheralSubspace hb hYmem).comp
    hmono.tendsto_atTop
  have hconst : Tendsto (fun _ : ℕ => Y) atTop
      (𝓝 (0 : Matrix (Fin D) (Fin D) ℂ)) := by
    exact hzero.congr' (Filter.Eventually.of_forall fun n => hYpow n)
  have hYzero : Y = 0 := (tendsto_const_nhds_iff.mp hconst)
  exact (T.peripheralProjection_apply_eq_self_iff X).mp (sub_eq_zero.mp hYzero).symm

/-- The fixed space of a positive power is the span of precisely those
peripheral eigenspaces whose phases become one under that power.
Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 765--806. -/
theorem eigenspace_pow_one_eq_iSup_peripheral
    {D : ℕ} [NeZero D]
    (T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    {p : ℕ} (hp : 0 < p) :
    (T ^ p).eigenspace 1 =
      ⨆ μ ∈ {μ : ℂ | μ ∈ peripheralEigenvalues T ∧ μ ^ p = 1},
        T.eigenspace μ := by
  classical
  apply le_antisymm
  · intro X hX
    have hfix : (T ^ p) X = X := by
      simpa only [Module.End.mem_eigenspace_iff, one_smul] using hX
    have hper := mem_peripheralSubspace_of_pow_fixed T hPos hTP hp X hfix
    rw [hPos.peripheralSubspace_eq_iSup_eigenspace hTP] at hper
    let S := (peripheralEigenvalues_finite T).toFinset
    have hperS : X ∈ ⨆ μ ∈ S, T.eigenspace μ := by
      simpa only [S, Set.Finite.mem_toFinset] using hper
    obtain ⟨v, hv⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ X).mp hperS
    have hcoeff : ∀ μ ∈ S, (μ ^ p - 1) • (v μ : Matrix (Fin D) (Fin D) ℂ) = 0 := by
      have hsum : (∑ μ ∈ S, (μ ^ p - 1) • (v μ : Matrix (Fin D) (Fin D) ℂ)) = 0 := by
        calc
          (∑ μ ∈ S, (μ ^ p - 1) • (v μ : Matrix (Fin D) (Fin D) ℂ)) =
              (T ^ p) X - X := by
                rw [← hv, map_sum, ← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro μ hμ
                rw [T.pow_apply_of_mem_eigenspace (v μ).2]
                simp [sub_smul]
          _ = 0 := sub_eq_zero.mpr hfix
      exact (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero T.eigenspace).mp
        T.eigenspaces_iSupIndep S
        (fun μ => (μ ^ p - 1) • (v μ : Matrix (Fin D) (Fin D) ℂ))
        (fun μ hμ => (T.eigenspace μ).smul_mem _ (v μ).2) hsum
    have hvzero : ∀ μ ∈ S, μ ^ p ≠ 1 →
        (v μ : Matrix (Fin D) (Fin D) ℂ) = 0 := by
      intro μ hμ hne
      exact (smul_eq_zero.mp (hcoeff μ hμ)).resolve_left (sub_ne_zero.mpr hne)
    rw [← hv]
    apply Submodule.sum_mem
    intro μ hμ
    by_cases hμp : μ ^ p = 1
    · exact le_biSup (fun z => T.eigenspace z)
        (show μ ∈ {z : ℂ | z ∈ peripheralEigenvalues T ∧ z ^ p = 1} from
          ⟨(peripheralEigenvalues_finite T).mem_toFinset.mp hμ, hμp⟩) (v μ).2
    · rw [hvzero μ hμ hμp]
      exact Submodule.zero_mem _
  · refine iSup₂_le fun μ hμ => ?_
    intro X hX
    rw [Module.End.mem_eigenspace_iff]
    rw [T.pow_apply_of_mem_eigenspace hX, hμ.2, one_smul]

/-- When the peripheral spectrum is the full period-`m` cyclic group and
each peripheral eigenspace is at most one-dimensional, the fixed space after
`p` steps has dimension at most `gcd(m,p)`.
Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 765--806. -/
theorem finrank_eigenspace_pow_one_le_gcd
    {D m : ℕ} [NeZero D] [NeZero m]
    (T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    (hper : peripheralEigenvalues T = {μ : ℂ | μ ^ m = 1})
    (hsimple : ∀ μ ∈ peripheralEigenvalues T,
      Module.finrank ℂ (T.eigenspace μ) ≤ 1)
    {p : ℕ} (hp : 0 < p) :
    Module.finrank ℂ ((T ^ p).eigenspace 1) ≤ Nat.gcd m p := by
  classical
  let S : Set ℂ := {μ | μ ∈ peripheralEigenvalues T ∧ μ ^ p = 1}
  have hSfin : S.Finite := (peripheralEigenvalues_finite T).subset (fun _ h => h.1)
  have hdim : Module.finrank ℂ ((T ^ p).eigenspace 1) ≤ hSfin.toFinset.card := by
    rw [eigenspace_pow_one_eq_iSup_peripheral T hPos hTP hp]
    have heq : (⨆ μ ∈ S, T.eigenspace μ) =
        ⨆ μ ∈ hSfin.toFinset, T.eigenspace μ := by
      simp only [S, Set.Finite.mem_toFinset]
    rw [heq]
    apply finrank_biSup_le_card_of_finrank_le_one
    intro μ hμ
    exact hsimple μ (hSfin.mem_toFinset.mp hμ).1
  have hS : S = {μ : ℂ | μ ^ (Nat.gcd m p) = 1} := by
    ext μ
    simp only [S, Set.mem_ofPred_eq, hper, pow_gcd_eq_one]
  have hgcd : 0 < Nat.gcd m p := Nat.gcd_pos_of_pos_left p (NeZero.pos m)
  have : NeZero (Nat.gcd m p) := ⟨hgcd.ne'⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ (Nat.gcd m p) :=
    ⟨Complex.exp (2 * Real.pi * Complex.I / (Nat.gcd m p)),
      Complex.isPrimitiveRoot_exp (Nat.gcd m p) (NeZero.ne _)⟩
  have hSroots : hSfin.toFinset =
      Polynomial.nthRootsFinset (Nat.gcd m p) (1 : ℂ) := by
    ext μ
    simp only [Set.Finite.mem_toFinset, hS, Set.mem_ofPred_eq,
      Polynomial.mem_nthRootsFinset hgcd]
  rw [hSroots, hζ.card_nthRootsFinset] at hdim
  exact hdim

end MPSTensor
