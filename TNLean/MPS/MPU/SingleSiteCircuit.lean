/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Overlap.Basic
import QICLean.Algebra.FinCastAddNatAdd
import QICLean.Circuit.Geometry.Graph
import QICLean.Circuit.Model.CleanWorkspace

/-!
# A single-site unitary with one clean padding qudit

A unitary on one physical site acts as one neighboring two-qudit gate
when the second qudit is left unchanged. The initialized-input equality
below retains the exact scalar phase and holds on every logical input.
No unitary extension or circuit is supplied as an additional hypothesis.

Source: the single-site endpoint of Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`; the arbitrary two-qudit
model is specified in arXiv:2508.08160, local `main.tex`, line 820.
-/

open Matrix MPSTensor QuantumCircuit

namespace MPUCircuit

/-- An operator on the logical sites, placed on the logical sites of a register with a workspace
appended in the zero configuration, implements itself cleanly. The identity holds for arbitrary
operators, without a unitarity premise. -/
theorem isCleanImplementation_placeAlong_workspace {d n A : ℕ} [NeZero d]
    (Z : Matrix (Cfg d n) (Cfg d n) ℂ) :
    IsCleanImplementation (basisInclusion (workspaceEmbedding (n := n) (0 : Fin A → Fin d)))
      (ManyBody.placeAlong (X := fun _ ↦ Fin d) (Fin.castAddEmb A) Z) Z := by
  unfold IsCleanImplementation
  ext z x
  rw [mul_basisInclusion_apply, basisInclusion_workspaceEmbedding_mul_apply,
    ManyBody.placeAlong_apply, workspaceEmbedding_apply]
  have hoff : (∀ v, (∀ u, Fin.castAddEmb A u ≠ v) → z v = Fin.append x 0 v) ↔
      ∀ j, z (Fin.natAdd n j) = (0 : Fin A → Fin d) j := by
    constructor
    · intro h j
      have hj := h (Fin.natAdd n j) fun u hu ↦ by
        have hv := congrArg Fin.val hu
        simp only [Fin.castAddEmb_apply, Fin.val_castAdd, Fin.val_natAdd] at hv
        have := u.isLt
        omega
      rwa [Fin.append_right] at hj
    · intro h v hv
      induction v using Fin.addCases with
      | left j => exact (hv j rfl).elim
      | right j => rw [Fin.append_right]; exact h j
  by_cases h : ∀ j, z (Fin.natAdd n j) = (0 : Fin A → Fin d) j
  · rw [ite_eq_left (hoff.mpr h), ite_eq_left h]
    exact congrArg₂ Z rfl (funext fun u ↦ Fin.append_left x 0 u)
  · rw [ite_eq_right (fun h' ↦ h (hoff.mp h')), ite_eq_right h]

variable {d : ℕ}

/-- Apply a single-site operator to the first of two sites and leave the
second site unchanged. Source: the single-site endpoint construction in
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def singleSitePaddedOperator (U : Matrix (Cfg d 1) (Cfg d 1) ℂ) :
    Matrix (Cfg d 2) (Cfg d 2) ℂ :=
  ManyBody.placeAlong (X := fun _ ↦ Fin d) (Fin.castAddEmb 1) U

/-- Padding by an identity preserves actual unitarity, including scalar
phase. Source: the single-site endpoint construction in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem singleSitePaddedOperator_mem_unitary
    {U : Matrix (Cfg d 1) (Cfg d 1) ℂ}
    (hU : U ∈ unitary (Matrix (Cfg d 1) (Cfg d 1) ℂ)) :
    singleSitePaddedOperator U ∈ unitary (Matrix (Cfg d 2) (Cfg d 2) ℂ) :=
  ManyBody.placeAlong_mem_unitaryGroup _ hU

/-- A single-site unitary therefore has a one-gate neighboring-pair
implementation on two qudits: it is a unitary supported on the cell of the
two sites. Source: arXiv:2508.08160, local `main.tex`, line 820, and the
single-site endpoint in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem singleSitePaddedOperator_isGateProduct
    {U : Matrix (Cfg d 1) (Cfg d 1) ℂ}
    (hU : U ∈ unitary (Matrix (Cfg d 1) (Cfg d 1) ℂ)) :
    IsGateProduct (Geometry.graph (SimpleGraph.pathGraph 2)) 1 (singleSitePaddedOperator U) := by
  have hpair : ({0, 1} : Finset (Fin 2)) = Finset.univ := by
    ext i
    fin_cases i <;> simp
  refine IsGateProduct.of_mem_supportedOperators
    (b := Geometry.pathCell (p := (0 : Fin 2)) (p' := 1) (by decide))
    (singleSitePaddedOperator_mem_unitary hU) ?_
  rw [Geometry.pathCell_cell, hpair, ManyBody.supportedOperators_univ]
  exact Submodule.mem_top (R := ℂ)

variable [NeZero d]

/-- Padding leaves the workspace exactly zero on every logical input.
The identity is valid for arbitrary operators, without a unitarity premise.
Source: the initialized-input equality at the single-site endpoint in
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem singleSitePaddedOperator_isCleanImplementation
    (U : Matrix (Cfg d 1) (Cfg d 1) ℂ) :
    IsCleanImplementation
      (basisInclusion (workspaceEmbedding (n := 1) (0 : Fin 1 → Fin d)))
      (singleSitePaddedOperator U) U :=
  isCleanImplementation_placeAlong_workspace U

/-- Every actual single-site unitary in positive physical dimension has an
exact one-pair-gate circuit with one clean padding qudit; no circuit or
unitary extension witness is assumed. The physical assumption `2 ≤ d`
of the general circuit theorem implies the required `NeZero d` instance.
Source: the single-site endpoint of Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_singleSite_clean_pair_circuit
    {U : Matrix (Cfg d 1) (Cfg d 1) ℂ}
    (hU : U ∈ unitary (Matrix (Cfg d 1) (Cfg d 1) ℂ)) :
    ∃ C : Matrix (Cfg d 2) (Cfg d 2) ℂ,
      IsGateProduct (Geometry.graph (SimpleGraph.pathGraph 2)) 1 C ∧
        IsCleanImplementation
          (basisInclusion (workspaceEmbedding (n := 1) (0 : Fin 1 → Fin d)))
          C U := by
  exact ⟨singleSitePaddedOperator U,
    singleSitePaddedOperator_isGateProduct hU,
    singleSitePaddedOperator_isCleanImplementation U⟩

end MPUCircuit
