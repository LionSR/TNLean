/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.SupportProjectionOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import TNLean.Circuit.EntropySupport
import QICLean.ManyBody.Sites.Twirl

/-!
# The range projection of a supported Hermitian operator

Functional calculus preserves the sites on which a Hermitian operator acts.
In particular, replacement by its range projection preserves its physical
support. This is the local support assertion in the range-projection reduction
of ALVV, arXiv:1602.08828v2, Section 6.1, lines 1457–1460.
-/

open scoped Matrix MatrixOrder ComplexOrder

namespace QuantumCircuit

variable {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The range projection acts on the same sites as the original Hermitian
operator. ALVV, arXiv:1602.08828v2, Section 6.1, lines 1457–1460. -/
theorem supportProj_mem_supportedOperators (K : Finset ι)
    {A : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hA : A.IsHermitian)
    (hK : A ∈ supportedOperators q (K : Set ι)) :
    hA.supportProj ∈ supportedOperators q (K : Set ι) := by
  rw [hA.supportProj_eq_cfc]
  refine mem_supportedOperators_of_isSupportedOn <|
    ManyBody.mem_supportedOperators_iff_forall_commute.mpr fun Y hY ↦ ?_
  have hY' : Y ∈ supportedOperators q ((K : Set ι)ᶜ) := by
    simpa only [Finset.coe_compl] using mem_supportedOperators_of_isSupportedOn hY
  exact (commute_of_mem_supportedOperators disjoint_compl_right hK hY').cfc_real _

/-- The absolute value of a Hermitian matrix commuting with `B` commutes with `B`. -/
theorem _root_.Commute.cfcAbs_of_isHermitian {X B : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hX : X.IsHermitian) (h : Commute X B) : Commute (CFC.abs X) B := by
  rw [CFC.abs_eq_cfc_norm X hX.isSelfAdjoint]
  exact h.cfc_real _

/-- The square root of a positive matrix acting on `K` acts on `K`. Source: area law,
`03-quasilocal.tex`, lines 386–388 ("commutes with both local square roots"). -/
theorem sqrt_mem_supportedOperators [NeZero q] (K : Finset ι)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k)
    (hk : k ∈ supportedOperators q (K : Set ι)) :
    CFC.sqrt k ∈ supportedOperators q (K : Set ι) :=
  mem_supportedOperators_of_isSupportedOn <|
    ManyBody.mem_supportedOperators_iff_forall_commute.mpr fun Y hY => by
      have hY' : Y ∈ supportedOperators q ((K : Set ι)ᶜ) := by
        simpa only [Finset.coe_compl] using mem_supportedOperators_of_isSupportedOn hY
      rw [CFC.sqrt_eq_real_sqrt _ hk₀, cfcₙ_eq_cfc]
      exact (commute_of_mem_supportedOperators disjoint_compl_right hk hY').cfc_real _

end QuantumCircuit
