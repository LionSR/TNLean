/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.RankOneFactorization
import QICLean.Algebra.RankOneSandwich
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Symmetry eigenvalues of continuous ground lines

A fixed finite-dimensional symmetry operator has a finite spectrum. Thus
its eigenvalue on a continuous invariant line is constant on a connected
parameter interval. The eigenvalue is extracted continuously by the trace
against the rank-one ground projection.

This is a finite-chain ingredient for the character rephasing permitted in
Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.C.2,
lines 440–453, and Appendix B, lines 2614–2632. The projection continuity
must be derived separately from the Hamiltonian path. These results do not
construct canonical tensors across a change of minimal bond dimension.
-/

open scoped Matrix Matrix.Norms.L2Operator

namespace Matrix

/-- An operator commuting with a rank-one idempotent acts on its range by
the trace against that idempotent. Orthogonal ground projections are a
special case. Source context: arXiv:1010.3732, Section II.C.2,
lines 440–453, and Appendix B, lines 2614–2632. -/
theorem mul_rankOne_idempotent_eq_trace_smul
    {n : Type*} [Fintype n]
    (U P : Matrix n n ℂ) (hrank : P.rank = 1) (hid : P * P = P)
    (hComm : Commute P U) : U * P = (U * P).trace • P := by
  classical
  obtain ⟨v, w, _, _, hP⟩ := exists_eq_vecMulVec_of_rank_eq_one P hrank
  have hsand : P * U * P = (U * P).trace • P := by
    simpa only [hP] using vecMulVec_mul_mul_vecMulVec_eq_trace_smul v w U
  simpa only [hComm.eq, Matrix.mul_assoc, hid] using hsand

/-- The scalar action on a nonzero rank-one invariant line belongs to the
spectrum of the fixed symmetry operator. Source context: arXiv:1010.3732,
Section II.C.2, lines 440–453, and Appendix B, lines 2614–2632. -/
theorem trace_mul_mem_spectrum_of_rankOne_idempotent_commute
    {n : Type*} [Fintype n] [DecidableEq n]
    (U P : Matrix n n ℂ) (hrank : P.rank = 1) (hid : P * P = P)
    (hComm : Commute P U) : (U * P).trace ∈ spectrum ℂ U := by
  rw [spectrum.mem_iff]
  intro hunit
  have hzero : (algebraMap ℂ (Matrix n n ℂ) (U * P).trace - U) * P = 0 := by
    rw [Matrix.sub_mul, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul]
    exact sub_eq_zero.mpr (mul_rankOne_idempotent_eq_trace_smul U P hrank hid hComm).symm
  have hPzero : P = 0 := hunit.mul_left_cancel (hzero.trans (Matrix.mul_zero _).symm)
  simp only [hPzero, Matrix.rank_zero, zero_ne_one] at hrank

/-- The eigenvalue of a fixed operator on a continuous invariant rank-one
projection is constant on a connected parameter space. No finiteness
assumption on a symmetry group is involved. Source context:
arXiv:1010.3732, Section II.C.2, lines 440–453, and Appendix B,
lines 2614–2632. -/
theorem trace_mul_constant_of_continuous_rankOne_idempotent
    {T n : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    [Fintype n]
    (U : Matrix n n ℂ) (P : T → Matrix n n ℂ) (hP : Continuous P)
    (hrank : ∀ t, (P t).rank = 1) (hid : ∀ t, P t * P t = P t)
    (hComm : ∀ t, Commute (P t) U) (t t₀ : T) :
    (U * P t).trace = (U * P t₀).trace := by
  classical
  let c : T → spectrum ℂ U := fun t =>
    ⟨(U * P t).trace,
      trace_mul_mem_spectrum_of_rankOne_idempotent_commute U (P t)
        (hrank t) (hid t) (hComm t)⟩
  have hc : Continuous c :=
    ((continuous_const.matrix_mul hP).matrix_trace).subtype_mk _
  exact congrArg Subtype.val (TotallyDisconnectedSpace.eq_of_continuous c hc t t₀)

/-- A one-dimensional invariant range of a group representation carries a
character, extracted by the trace against its idempotent. Source context:
arXiv:1010.3732, Section II.C.2, lines 440–453, and Appendix B,
lines 2614–2632. -/
theorem exists_character_of_rankOne_idempotent_commute
    {G n : Type*} [Group G] [Fintype n] [DecidableEq n]
    (U : G →* Matrix n n ℂ) (P : Matrix n n ℂ)
    (hrank : P.rank = 1) (hid : P * P = P)
    (hComm : ∀ g, Commute P (U g)) :
    ∃ χ : G →* ℂ, ∀ g, χ g = (U g * P).trace := by
  have hPne : P ≠ 0 := by
    intro hzero
    simp only [hzero, Matrix.rank_zero, zero_ne_one] at hrank
  have hcov := fun g => mul_rankOne_idempotent_eq_trace_smul (U g) P hrank hid (hComm g)
  refine ⟨{ toFun := fun g => (U g * P).trace, map_one' := ?_, map_mul' := ?_ }, fun _ => rfl⟩
  · apply smul_left_injective ℂ hPne
    simpa only [map_one, Matrix.one_mul, one_smul] using (hcov 1).symm
  · intro g h
    apply smul_left_injective ℂ hPne
    calc
      (U (g * h) * P).trace • P = U (g * h) * P := (hcov (g * h)).symm
      _ = U g * (U h * P) := by rw [map_mul, Matrix.mul_assoc]
      _ = U g * ((U h * P).trace • P) := congrArg (U g * ·) (hcov h)
      _ = (U h * P).trace • (U g * P) := Matrix.mul_smul _ _ _
      _ = (U h * P).trace • ((U g * P).trace • P) :=
        congrArg ((U h * P).trace • ·) (hcov g)
      _ = ((U g * P).trace * (U h * P).trace) • P := by rw [smul_smul, mul_comm]

/-- Continuous rank-one invariant ground projections carry one fixed unitary
character throughout a connected parameter space. Source context:
arXiv:1010.3732, Section II.C.2, lines 440–453, and Appendix B,
lines 2614–2632. -/
theorem exists_constant_character_of_continuous_rankOne_idempotent
    {T G n : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    [Group G] [Fintype n] [DecidableEq n]
    (U : G →* Matrix n n ℂ) (hU : ∀ g, U g ∈ unitaryGroup n ℂ)
    (P : T → Matrix n n ℂ) (hP : Continuous P)
    (hrank : ∀ t, (P t).rank = 1) (hid : ∀ t, P t * P t = P t)
    (hComm : ∀ t g, Commute (P t) (U g)) (t₀ : T) :
    ∃ χ : G →* ℂ, (∀ g, ‖χ g‖ = 1) ∧
      ∀ t g, U g * P t = χ g • P t := by
  obtain ⟨χ, hχ⟩ := exists_character_of_rankOne_idempotent_commute U (P t₀)
    (hrank t₀) (hid t₀) (hComm t₀)
  refine ⟨χ, ?_, ?_⟩
  · intro g
    rw [hχ g]
    exact spectrum.norm_eq_one_of_unitary (hU g)
      (trace_mul_mem_spectrum_of_rankOne_idempotent_commute (U g) (P t₀)
        (hrank t₀) (hid t₀) (hComm t₀ g))
  · intro t g
    rw [hχ g, mul_rankOne_idempotent_eq_trace_smul (U g) (P t)
      (hrank t) (hid t) (hComm t g)]
    rw [trace_mul_constant_of_continuous_rankOne_idempotent (U g) P hP hrank hid
      (fun t => hComm t g) t t₀]

end Matrix
