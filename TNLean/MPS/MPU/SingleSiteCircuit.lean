/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Overlap.Basic
import TNLean.Circuit.CleanImplementationPlacement

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

variable {d : ℕ}

/-- Apply a single-site operator to the first of two sites and leave the
second site unchanged. Source: the single-site endpoint construction in
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def singleSitePaddedOperator (U : Matrix (Cfg d 1) (Cfg d 1) ℂ) :
    Matrix (Cfg d 2) (Cfg d 2) ℂ :=
  embedOp (Fin.castAdd 1) U

/-- Padding by an identity preserves actual unitarity, including scalar
phase. Source: the single-site endpoint construction in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem singleSitePaddedOperator_mem_unitary
    {U : Matrix (Cfg d 1) (Cfg d 1) ℂ}
    (hU : U ∈ unitary (Matrix (Cfg d 1) (Cfg d 1) ℂ)) :
    singleSitePaddedOperator U ∈ unitary (Matrix (Cfg d 2) (Cfg d 2) ℂ) :=
  embedOp_mem_unitary (Fin.castAdd_injective 1 1) hU

/-- The padded operator is one allowed neighboring pair gate. Source:
arXiv:2508.08160, local `main.tex`, line 820, and the single-site endpoint
construction in Section 5 of the circuit audit. -/
theorem singleSitePaddedOperator_isNeighbourGate
    {U : Matrix (Cfg d 1) (Cfg d 1) ℂ}
    (hU : U ∈ unitary (Matrix (Cfg d 1) (Cfg d 1) ℂ)) :
    IsNeighbourGate (singleSitePaddedOperator U) := by
  have hpair : ({0, 1} : Set (Fin 2)) = Set.univ := by
    ext i
    fin_cases i <;> simp
  refine ⟨singleSitePaddedOperator_mem_unitary hU, 0, 1, by decide, ?_⟩
  rw [hpair]
  exact mem_supportedOperators_univ _

/-- A single-site unitary therefore has a one-gate neighboring-pair
implementation on two qudits. Source: the single-site endpoint in Section 5
of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem singleSitePaddedOperator_isPairProduct
    {U : Matrix (Cfg d 1) (Cfg d 1) ℂ}
    (hU : U ∈ unitary (Matrix (Cfg d 1) (Cfg d 1) ℂ)) :
    IsPairProduct d 2 1 (singleSitePaddedOperator U) :=
  IsPairProduct.of_isNeighbourGate (singleSitePaddedOperator_isNeighbourGate hU)

variable [NeZero d]

/-- Padding leaves the workspace exactly zero on every logical input.
The identity is valid for arbitrary operators, without a unitarity premise.
Source: the initialized-input equality at the single-site endpoint in
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem singleSitePaddedOperator_isCleanImplementation
    (U : Matrix (Cfg d 1) (Cfg d 1) ℂ) :
    IsCleanImplementation
      (initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := 1) (a := 1)))
      (singleSitePaddedOperator U) U := by
  classical
  change singleSitePaddedOperator U *
    initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := 1) (a := 1)) = _
  rw [mul_initializedBasisMatrix]
  ext z x
  change embedOp (Fin.castAdd 1) U z (Fin.append x 0) = _
  rw [embedOp_apply, initializedBasisMatrix_zeroWorkspace_mul_apply]
  have hguard : AgreeOff (Fin.castAdd 1) z (Fin.append x 0) ↔
      ∀ j : Fin 1, z (Fin.natAdd 1 j) = 0 := by
    constructor
    · intro h j
      have hj : ∀ i : Fin 1, Fin.castAdd 1 i ≠ Fin.natAdd 1 j := by
        intro i hi
        have := congrArg Fin.val hi
        simp only [Fin.val_castAdd, Fin.val_natAdd] at this
        omega
      simpa only [Fin.append_right, Pi.zero_apply] using h (Fin.natAdd 1 j) hj
    · intro h j
      refine Fin.addCases (fun i hi ↦ ?_) (fun i _ ↦ ?_) j
      · exact False.elim (hi i rfl)
      · simpa only [Fin.append_right, Pi.zero_apply] using h i
  have hrestrict : (Fin.append x (0 : Cfg d 1)) ∘ Fin.castAdd 1 = x := by
    funext i
    exact Fin.append_left _ _ i
  simp only [hguard, hrestrict]
  rfl

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
      IsPairProduct d 2 1 C ∧
        IsCleanImplementation
          (initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := 1) (a := 1)))
          C U := by
  exact ⟨singleSitePaddedOperator U,
    singleSitePaddedOperator_isPairProduct hU,
    singleSitePaddedOperator_isCleanImplementation U⟩

end MPUCircuit
