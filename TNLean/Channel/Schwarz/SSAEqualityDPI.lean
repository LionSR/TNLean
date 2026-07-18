/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Channel.Schwarz.StrongSubadditivityPosDef

/-!
# Equality in strong subadditivity as equality in data processing

For a positive semidefinite tripartite state $\rho_{ABC}$ of trace one, this
file identifies equality in strong subadditivity with saturation of the
relative-entropy data-processing inequality under the partial trace over $C$.
The reference pair is
\[
  (\mathbf 1_A/d_A)\otimes\rho_{BC}, \qquad
  (\mathbf 1_A/d_A)\otimes\rho_B.
\]

Hayden--Jozsa--Petz--Winter use the product-marginal pair
$\rho_A\otimes\rho_{BC}$ and $\rho_A\otimes\rho_B$ in their equations (5)--(7).
The maximally mixed reference used here gives the same strong-subadditivity
deficit and is covered by the existing singular-support evaluation of relative
entropy. The remaining product-marginal evaluation is recorded in
docs/paper-gaps/hjpw04_ssa_product_marginal_reference.tex.

## Main results

* `isSSAEquality_iff_maximally_mixed_reference_data_processing_eq` gives the
  equality criterion on the full positive semidefinite unit-trace domain.

## Reference

Hayden, Jozsa, Petz, Winter, "Structure of states which satisfy strong
subadditivity of quantum entropy with equality", CMP 246, 359--374 (2004),
arXiv:quant-ph/0304007v2, p. 3, equations (5)--(7).
-/

open scoped Matrix Kronecker ComplexOrder Matrix.Norms.L2Operator
open Matrix

section SSAEqualityDPI

open SSAPosDef

variable {dA dB dC : ℕ}

/-- **SSA equality is saturation of partial-trace data processing for the
maximally mixed reference.** For every tripartite density matrix
$\rho_{ABC}$, equality in strong subadditivity is equivalent to
\[
  D\!\left(\rho_{ABC}\,\middle\|\,
    (\mathbf 1_A/d_A)\otimes\rho_{BC}\right)
  =
  D\!\left(\rho_{AB}\,\middle\|\,
    (\mathbf 1_A/d_A)\otimes\rho_B\right).
\]
The second reference is the image of the first under
$\operatorname{tr}_C$ by `SSAPosDef.traceC_ABC_kronecker_traceA_ABC`.

Hayden--Jozsa--Petz--Winter use instead the exact product-marginal pair
$\rho_A\otimes\rho_{BC}$ and $\rho_A\otimes\rho_B$. Their equation (6) gives
the same strong-subadditivity deficit. The present theorem uses
the maximally mixed state on $A$ because `SSAPosDef.rel_entropy_eval_support`
supplies this singular-reference evaluation without any additional hypothesis.

**Reference substitution:** This is the hypothesis-free maximally mixed-reference
formulation, not the exact product-marginal formulation of HJPW. The missing
product-marginal logarithm evaluation is recorded in
docs/paper-gaps/hjpw04_ssa_product_marginal_reference.tex.

Source: Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2, p. 3,
equations (5)--(7) and the paragraph following equation (7). -/
theorem isSSAEquality_iff_maximally_mixed_reference_data_processing_eq
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC) (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1) :
    IsSSAEquality ρ_ABC hρ_dm.1.isHermitian ↔
      quantumRelativeEntropy ρ_ABC
          (((dA : ℂ)⁻¹ • (1 : Matrix (Fin dA) (Fin dA) ℂ)) ⊗ₖ traceA_ABC ρ_ABC)
        = quantumRelativeEntropy (traceC_ABC ρ_ABC)
          (traceC_ABC
            (((dA : ℂ)⁻¹ • (1 : Matrix (Fin dA) (Fin dA) ℂ))
              ⊗ₖ traceA_ABC ρ_ABC)) := by
  classical
  obtain ⟨hρ, hρtr⟩ := hρ_dm
  have hAne : NeZero dA := by
    refine ⟨fun h ↦ ?_⟩
    subst h
    rw [Matrix.trace_eq_zero_of_isEmpty] at hρtr
    exact zero_ne_one hρtr
  have hBne : NeZero dB := by
    refine ⟨fun h ↦ ?_⟩
    subst h
    rw [Matrix.trace_eq_zero_of_isEmpty] at hρtr
    exact zero_ne_one hρtr
  have hCne : NeZero dC := by
    refine ⟨fun h ↦ ?_⟩
    subst h
    rw [Matrix.trace_eq_zero_of_isEmpty] at hρtr
    exact zero_ne_one hρtr
  have : Nonempty (Fin dB × Fin dC) := ⟨⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne dB)⟩,
    ⟨0, Nat.pos_of_ne_zero (NeZero.ne dC)⟩⟩⟩
  have : Nonempty (Fin dB) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne dB)⟩⟩
  have hfull := rel_entropy_eval_support (ρ := ρ_ABC) hρ hρtr (kron_marginal_support hρ)
  set ρAB := traceC_ABC ρ_ABC with hρAB
  have hρAB_psd : ρAB.PosSemidef := traceC_ABC_posSemidef hρ
  have hρABtr : ρAB.trace = 1 := by
    rw [hρAB, ← Matrix.trace_eq_trace_traceC_ABC]
    exact hρtr
  have himg := rel_entropy_eval_support (ρ := ρAB) hρAB_psd hρABtr
    (kron_marginal_support hρAB_psd)
  have hρB : traceLeftA ρAB = traceAC_ABC ρ_ABC := by
    ext b₁ b₂
    simp only [hρAB, traceLeftA, traceC_ABC, traceAC_ABC]
  have hSρBC :
      vonNeumannEntropy (traceLeftA ρ_ABC) (traceLeftA_posSemidef hρ).isHermitian
        = vonNeumannEntropy (traceA_ABC ρ_ABC)
          (traceA_ABC_isHermitian hρ.isHermitian) :=
    vonNeumannEntropy_congr rfl _ _
  have hSρB : vonNeumannEntropy (traceLeftA ρAB)
      (traceLeftA_posSemidef hρAB_psd).isHermitian
        = vonNeumannEntropy (traceAC_ABC ρ_ABC)
          (traceAC_ABC_isHermitian hρ.isHermitian) :=
    vonNeumannEntropy_congr hρB _ _
  have hSρAB : vonNeumannEntropy ρAB hρAB_psd.isHermitian
      = vonNeumannEntropy (traceC_ABC ρ_ABC)
          (traceC_ABC_isHermitian hρ.isHermitian) :=
    vonNeumannEntropy_congr hρAB _ _
  rw [traceC_ABC_kronecker_traceA_ABC]
  rw [← hρB]
  change IsSSAEquality ρ_ABC hρ.isHermitian ↔
    quantumRelativeEntropy ρ_ABC
        (((dA : ℂ)⁻¹ • (1 : Matrix (Fin dA) (Fin dA) ℂ)) ⊗ₖ traceLeftA ρ_ABC)
      = quantumRelativeEntropy ρAB
        (((dA : ℂ)⁻¹ • (1 : Matrix (Fin dA) (Fin dA) ℂ)) ⊗ₖ traceLeftA ρAB)
  simp only [hfull, himg]
  rw [IsSSAEquality]
  rw [hSρBC, hSρB, hSρAB]
  constructor <;> intro h <;> linarith

end SSAEqualityDPI
