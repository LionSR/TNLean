/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SingleSiteCircuit
import TNLean.MPS.MPU.FinalCircuitRegisters

/-!
# Complete circuit registers at the one-site endpoint

For a one-site chain, the logical auxiliary register and the common scratch
register are empty. The complete register therefore consists of the physical
site and one initialized padding qudit. The physical unitary acts on these two
sites as one neighboring-pair gate and returns the padding qudit exactly to zero.
The equality below retains its scalar phase on every physical input.

For chains of length at least two, the additional padding register is empty.
A circuit on the global register then has the same gate count and initialized
physical action when written on the complete register. Only the site indices
are transported; no additional gates are introduced.

Source: the single-site endpoint and complete-register convention in Section 5
of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. The arbitrary two-qudit
model is specified in arXiv:2508.08160, local `main.tex`, line 820.
-/

open Matrix MPSTensor MPSPreparation

namespace MPUCircuit

variable {d D N : ℕ}

/-- The complete register of a one-site chain has precisely two sites.
Source: the one-site endpoint in Section 5 of the circuit manuscript. -/
theorem completeCircuitSiteCount_one (d D : ℕ) :
    completeCircuitSiteCount d D 1 = 2 := by
  simp [completeCircuitSiteCount, circuitPaddingCount, globalSiteCount,
    logicalSiteCount, auxiliarySiteCount]

/-- Chains of length at least two have no additional padding register.
Source: the complete-register convention in Section 5 of the circuit manuscript. -/
theorem circuitPaddingCount_eq_zero_of_two_le (hN : 2 ≤ N) :
    circuitPaddingCount N = 0 := by
  simp [circuitPaddingCount, show N ≠ 1 by omega]

/-- For chains of length at least two, the complete and global site counts agree.
Source: the complete-register convention in Section 5 of the circuit manuscript. -/
theorem completeCircuitSiteCount_eq_global_of_two_le (hN : 2 ≤ N) :
    completeCircuitSiteCount d D N = globalSiteCount d D N := by
  rw [completeCircuitSiteCount, circuitPaddingCount_eq_zero_of_two_le hN, Nat.add_zero]

/-- Identifying equal site counts preserves the neighboring-pair gate count and
an exact initialized-input identity. The supplied circuit is induction data;
this lemma introduces no new gates. Source: the complete-register transport in
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_clean_pair_circuit_of_siteCount_eq
    {n m k K : ℕ} (h : n = m)
    (E : Cfg d k ↪ Cfg d n) (F : Cfg d k ↪ Cfg d m)
    (hEF : ∀ x, E x = F x ∘ Fin.cast h)
    (U : Matrix (Cfg d k) (Cfg d k) ℂ)
    (hC : ∃ C : Matrix (Cfg d n) (Cfg d n) ℂ,
      IsPairProduct d n K C ∧
        C * initializedBasisMatrix E = initializedBasisMatrix E * U) :
    ∃ C : Matrix (Cfg d m) (Cfg d m) ℂ,
      IsPairProduct d m K C ∧
        C * initializedBasisMatrix F = initializedBasisMatrix F * U := by
  subst m
  have hEF' : E = F := by
    apply Function.Embedding.ext
    intro x
    simpa only [Fin.cast_refl, Function.comp_id] using hEF x
  subst F
  exact hC

/-- The complete physical embedding is the global physical embedding transported
along the equality of site counts, with every auxiliary still zero.
Source: the complete-register convention in Section 5 of the circuit manuscript. -/
theorem completePhysicalConfigEmbedding_pullback_of_two_le [NeZero d]
    (hN : 2 ≤ N) (x : Cfg d N) :
    physicalGlobalConfigEmbedding (D := D) x =
      completePhysicalConfigEmbedding (D := D) x ∘
        Fin.cast (completeCircuitSiteCount_eq_global_of_two_le (d := d) (D := D) hN).symm := by
  have hc : globalSiteCount d D N = globalSiteCount d D N + circuitPaddingCount N :=
    (completeCircuitSiteCount_eq_global_of_two_le hN).symm
  change physicalGlobalConfigEmbedding (D := D) x =
    Fin.append (physicalGlobalConfigEmbedding (D := D) x)
      (0 : Cfg d (circuitPaddingCount N)) ∘ Fin.cast hc
  rw [Fin.append_right_nil _ _ (circuitPaddingCount_eq_zero_of_two_le hN)]
  funext i
  apply congrArg (physicalGlobalConfigEmbedding (D := D) x)
  apply Fin.ext
  rfl

/-- Every single-site unitary has an exact one-gate neighboring-pair circuit on
the complete register, including exact erasure of its padding qudit. There is
no supplied circuit or initialized-column witness. The dimension assumption
`2 ≤ d` of the general circuit theorem supplies the `NeZero d` instance.
Source: the one-site endpoint in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_singleSite_complete_clean_pair_circuit
    [NeZero d] {U : Matrix (Cfg d 1) (Cfg d 1) ℂ}
    (hU : U ∈ unitary (Matrix (Cfg d 1) (Cfg d 1) ℂ)) :
    ∃ C : Matrix (Cfg d (completeCircuitSiteCount d D 1))
        (Cfg d (completeCircuitSiteCount d D 1)) ℂ,
      IsPairProduct d (completeCircuitSiteCount d D 1) 1 C ∧
        C * initializedBasisMatrix (completePhysicalConfigEmbedding (D := D)) =
          initializedBasisMatrix (completePhysicalConfigEmbedding (D := D)) * U := by
  apply exists_clean_pair_circuit_of_siteCount_eq
    (completeCircuitSiteCount_one d D).symm
    (zeroWorkspaceEmbedding (d := d) (n := 1) (a := 1))
    (completePhysicalConfigEmbedding (D := D))
  · intro x
    have hc : 2 = 1 + auxiliarySiteCount d D 1 + auxiliarySiteCount d D 1 +
        circuitPaddingCount 1 := (completeCircuitSiteCount_one d D).symm
    change Fin.append x (0 : Cfg d 1) =
      Fin.append (Fin.append (Fin.append x (0 : Cfg d (auxiliarySiteCount d D 1)))
        (0 : Cfg d (auxiliarySiteCount d D 1))) (0 : Cfg d (circuitPaddingCount 1)) ∘
          Fin.cast hc
    funext i
    fin_cases i
    · have hi : Fin.cast hc (0 : Fin 2) =
          Fin.castAdd (circuitPaddingCount 1)
            (Fin.castAdd (auxiliarySiteCount d D 1)
              (Fin.castAdd (auxiliarySiteCount d D 1) (0 : Fin 1))) := by
        apply Fin.ext
        rfl
      change Fin.append x (0 : Cfg d 1) (0 : Fin 2) =
        Fin.append (Fin.append (Fin.append x (0 : Cfg d (auxiliarySiteCount d D 1)))
          (0 : Cfg d (auxiliarySiteCount d D 1))) (0 : Cfg d (circuitPaddingCount 1))
            (Fin.cast hc (0 : Fin 2))
      rw [hi, Fin.append_left, Fin.append_left, Fin.append_left]
      rfl
    · have hi : Fin.cast hc (1 : Fin 2) =
          Fin.natAdd (1 + auxiliarySiteCount d D 1 + auxiliarySiteCount d D 1)
            (⟨0, by simp [circuitPaddingCount]⟩ : Fin (circuitPaddingCount 1)) := by
        apply Fin.ext
        change 1 = 1 + auxiliarySiteCount d D 1 + auxiliarySiteCount d D 1
        simp [auxiliarySiteCount]
      change Fin.append x (0 : Cfg d 1) (1 : Fin 2) =
        Fin.append (Fin.append (Fin.append x (0 : Cfg d (auxiliarySiteCount d D 1)))
          (0 : Cfg d (auxiliarySiteCount d D 1))) (0 : Cfg d (circuitPaddingCount 1))
            (Fin.cast hc (1 : Fin 2))
      rw [hi, Fin.append_right]
      rfl
  · exact exists_singleSite_clean_pair_circuit hU

/-- An actual circuit on the global register transfers to the complete register
without increasing its gate count when the chain has at least two sites.
Its exact physical action and exact auxiliary erasure are retained.
Source: the complete-register transport in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_complete_clean_pair_circuit_of_global [NeZero d]
    (hN : 2 ≤ N) {K : ℕ} (U : Matrix (Cfg d N) (Cfg d N) ℂ)
    (C : Matrix (Cfg d (globalSiteCount d D N)) (Cfg d (globalSiteCount d D N)) ℂ)
    (hC : IsPairProduct d (globalSiteCount d D N) K C)
    (hcolumns : C * initializedBasisMatrix (physicalGlobalConfigEmbedding (D := D)) =
      initializedBasisMatrix (physicalGlobalConfigEmbedding (D := D)) * U) :
    ∃ W : Matrix (Cfg d (completeCircuitSiteCount d D N))
        (Cfg d (completeCircuitSiteCount d D N)) ℂ,
      IsPairProduct d (completeCircuitSiteCount d D N) K W ∧
        W * initializedBasisMatrix (completePhysicalConfigEmbedding (D := D)) =
          initializedBasisMatrix (completePhysicalConfigEmbedding (D := D)) * U :=
  exists_clean_pair_circuit_of_siteCount_eq
    (completeCircuitSiteCount_eq_global_of_two_le hN).symm
    (physicalGlobalConfigEmbedding (D := D)) (completePhysicalConfigEmbedding (D := D))
    (completePhysicalConfigEmbedding_pullback_of_two_le hN) U ⟨C, hC, hcolumns⟩

end MPUCircuit
