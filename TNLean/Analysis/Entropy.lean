/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import TNLean.Channel.Basic
import TNLean.Channel.PartialTrace

/-!
# Von Neumann entropy, strong subadditivity, and mutual information

This file defines the von Neumann entropy for density matrices and develops
the basic quantum entropy infrastructure needed for MPDO / RFP applications.

## Main definitions

* `vonNeumannEntropy`: `S(ρ) = ∑ᵢ negMulLog(λᵢ)` where `λᵢ` are eigenvalues
* `mutualInformation`: `I(A:B) = S(ρ_A) + S(ρ_B) - S(ρ_AB)`

## Main results

* `vonNeumannEntropy_nonneg`: `S(ρ) ≥ 0` for density matrices
* `vonNeumannEntropy_le_log_dim`: `S(ρ) ≤ log D` for `D × D` density matrices
* `strong_subadditivity`: `S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)` (axiom)
* `subadditivity`: `S(ρ_AB) ≤ S(ρ_A) + S(ρ_B)` (axiom)
* `mutualInformation_nonneg`: `I(A:B) ≥ 0`

## Implementation notes

Strong subadditivity (SSA) and subadditivity are axiomatized following Option B
from issue #239. The full proof from Klein's inequality and Lieb concavity is
deferred; the axioms are marked with TODOs for future replacement.

The entropy definition uses the eigenvalue-based formula via
`Matrix.IsHermitian.eigenvalues` and Mathlib's `Real.negMulLog`. The index
type `n` is kept polymorphic (`[Fintype n] [DecidableEq n]`) so that von
Neumann entropy can be applied to matrices indexed by product types arising
from partial traces.

Tripartite partial traces are defined directly as matrix entry sums, avoiding
dependence on the bipartite `Matrix.traceLeft`/`Matrix.traceRight` which are
specialized to `Fin d × Fin d'` indices.

## References

* Lieb, Ruskai, "Proof of the strong subadditivity of quantum-mechanical
  entropy", JMP 14, 1938 (1973)
* [M. Wolf, *Quantum Channels & Operations: Guided Tour*][Wolf2012QChannels]
* arXiv:1606.00608 §4.4
-/

open scoped Matrix ComplexOrder
open Matrix Finset Real

/-! ## Von Neumann entropy -/

section VonNeumannEntropy

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Von Neumann entropy** of a Hermitian matrix.

For a Hermitian matrix `ρ` with eigenvalues `λᵢ`, the von Neumann entropy is
`S(ρ) = ∑ᵢ negMulLog(λᵢ) = -∑ᵢ λᵢ log(λᵢ)`.

When `ρ` is a density matrix (PSD with trace 1), this gives the standard
quantum entropy `S(ρ) = -tr(ρ log ρ)`. -/
noncomputable def vonNeumannEntropy
    (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) : ℝ :=
  ∑ i, negMulLog (hρ.eigenvalues i)

end VonNeumannEntropy

/-! ### Basic properties for `Fin D` density matrices -/

section VonNeumannEntropyFinD

variable {D : ℕ}

/-- The eigenvalues of a density matrix sum to 1 (real version). -/
theorem densityMatrix_eigenvalues_sum_one [DecidableEq (Fin D)]
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ ∈ densityMatrices D) :
    ∑ i : Fin D, hρ.1.isHermitian.eigenvalues i = 1 := by
  have h := hρ.1.isHermitian.trace_eq_sum_eigenvalues
  have h_tr := hρ.2
  have key : (∑ i : Fin D, (hρ.1.isHermitian.eigenvalues i : ℂ)) = 1 :=
    h ▸ h_tr
  exact_mod_cast key

/-- The eigenvalues of a density matrix lie in `[0, 1]`. -/
theorem densityMatrix_eigenvalues_le_one [DecidableEq (Fin D)]
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ ∈ densityMatrices D)
    (i : Fin D) : hρ.1.isHermitian.eigenvalues i ≤ 1 := by
  have h_nonneg := hρ.1.eigenvalues_nonneg
  have h_sum := densityMatrix_eigenvalues_sum_one hρ
  nlinarith [Finset.single_le_sum (f := fun j => hρ.1.isHermitian.eigenvalues j)
    (fun j _ => h_nonneg j) (Finset.mem_univ i)]

/-- Von Neumann entropy is nonneg for density matrices.

Each eigenvalue `λᵢ` of a density matrix satisfies `0 ≤ λᵢ ≤ 1`, and
`negMulLog` is nonneg on `[0, 1]`. -/
theorem vonNeumannEntropy_nonneg [DecidableEq (Fin D)]
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ ∈ densityMatrices D) :
    0 ≤ vonNeumannEntropy ρ hρ.1.isHermitian := by
  apply Finset.sum_nonneg
  intro i _
  exact negMulLog_nonneg (hρ.1.eigenvalues_nonneg i)
    (densityMatrix_eigenvalues_le_one hρ i)

/-- Von Neumann entropy is bounded above by `log D`.

By Jensen's inequality applied to the concave function `negMulLog`, the entropy
is maximized when all eigenvalues are equal to `1/D` (maximally mixed state),
giving `S(ρ) ≤ D · negMulLog(1/D) = log D`.

TODO: Prove via `ConcaveOn.le_map_sum` applied to `concaveOn_negMulLog`. -/
theorem vonNeumannEntropy_le_log_dim [DecidableEq (Fin D)]
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ ∈ densityMatrices D)
    (hD : 0 < D) :
    vonNeumannEntropy ρ hρ.1.isHermitian ≤ Real.log D := by
  sorry

end VonNeumannEntropyFinD

/-! ## Tripartite partial traces

Partial traces for tripartite systems `A ⊗ B ⊗ C`, defined directly via
summation over the traced-out indices. The tripartite state is indexed by
`Fin dA × Fin dB × Fin dC` (right-associated: `Fin dA × (Fin dB × Fin dC)`). -/

section TripartiteTrace

variable {dA dB dC : ℕ}

/-- Partial trace over A: `ρ_BC = tr_A(ρ_ABC)`.

`(traceA_ABC ρ) (b₁, c₁) (b₂, c₂) = ∑ a, ρ (a, b₁, c₁) (a, b₂, c₂)` -/
noncomputable def traceA_ABC
    (ρ : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ) :
    Matrix (Fin dB × Fin dC) (Fin dB × Fin dC) ℂ :=
  fun bc₁ bc₂ => ∑ a : Fin dA, ρ (a, bc₁) (a, bc₂)

/-- Partial trace over C: `ρ_AB = tr_C(ρ_ABC)`.

`(traceC_ABC ρ) (a₁, b₁) (a₂, b₂) = ∑ c, ρ (a₁, b₁, c) (a₂, b₂, c)` -/
noncomputable def traceC_ABC
    (ρ : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ) :
    Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ :=
  fun ab₁ ab₂ => ∑ c : Fin dC, ρ (ab₁.1, ab₁.2, c) (ab₂.1, ab₂.2, c)

/-- Partial trace over AC: `ρ_B = tr_AC(ρ_ABC)`.

`(traceAC_ABC ρ) b₁ b₂ = ∑ a, ∑ c, ρ (a, b₁, c) (a, b₂, c)` -/
noncomputable def traceAC_ABC
    (ρ : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ) :
    Matrix (Fin dB) (Fin dB) ℂ :=
  fun b₁ b₂ => ∑ a : Fin dA, ∑ c : Fin dC, ρ (a, b₁, c) (a, b₂, c)

end TripartiteTrace

/-! ## Strong subadditivity (axiom)

Strong subadditivity is axiomatized as described in issue #239 (Option B).
The full proof via Klein's inequality and joint convexity of relative entropy
is deferred.

TODO: Replace this axiom with a proof from Klein's inequality and
Lieb concavity (Lieb–Ruskai 1973). This requires:
1. Quantum relative entropy `D(ρ‖σ) = tr(ρ(log ρ - log σ))`
2. Klein's inequality: `D(ρ‖σ) ≥ 0`
3. Joint convexity of relative entropy
4. Monotonicity of relative entropy under partial trace -/

section StrongSubadditivity

variable {dA dB dC : ℕ}

/-- **Strong subadditivity** (Lieb–Ruskai 1973).

For a tripartite density matrix `ρ_ABC` on `A ⊗ B ⊗ C`:
  `S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`

This is axiomatized; see the module docstring for the deferred proof plan.

References:
* Lieb, Ruskai, JMP 14, 1938 (1973) -/
axiom strong_subadditivity
    [DecidableEq (Fin dA × Fin dB × Fin dC)]
    [DecidableEq (Fin dA × Fin dB)]
    [DecidableEq (Fin dB × Fin dC)]
    [DecidableEq (Fin dB)]
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_ABC : ρ_ABC.IsHermitian)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1)
    (hρ_B : (traceAC_ABC ρ_ABC).IsHermitian)
    (hρ_AB : (traceC_ABC ρ_ABC).IsHermitian)
    (hρ_BC : (traceA_ABC ρ_ABC).IsHermitian) :
    vonNeumannEntropy ρ_ABC hρ_ABC
      + vonNeumannEntropy (traceAC_ABC ρ_ABC) hρ_B
    ≤ vonNeumannEntropy (traceC_ABC ρ_ABC) hρ_AB
      + vonNeumannEntropy (traceA_ABC ρ_ABC) hρ_BC

end StrongSubadditivity

/-! ## Subadditivity (axiom)

Subadditivity follows from strong subadditivity with a trivial system C
(dimension 1). We axiomatize it separately for ergonomic use with bipartite
states.

TODO: Prove from `strong_subadditivity` by specializing `dC = 1`. -/

section Subadditivity

variable {dA dB : ℕ}

/-- **Subadditivity** of von Neumann entropy.

For a bipartite density matrix `ρ_AB` on `A ⊗ B`:
  `S(ρ_AB) ≤ S(ρ_A) + S(ρ_B)` -/
axiom subadditivity
    [DecidableEq (Fin dA × Fin dB)]
    [DecidableEq (Fin dA)] [DecidableEq (Fin dB)]
    (ρ_AB : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hρ_AB : ρ_AB.IsHermitian)
    (hρ_dm : ρ_AB.PosSemidef ∧ ρ_AB.trace = 1)
    (hρ_A : (Matrix.traceRight ρ_AB).IsHermitian)
    (hρ_B : (Matrix.traceLeft ρ_AB).IsHermitian) :
    vonNeumannEntropy ρ_AB hρ_AB
    ≤ vonNeumannEntropy (Matrix.traceRight ρ_AB) hρ_A
      + vonNeumannEntropy (Matrix.traceLeft ρ_AB) hρ_B

end Subadditivity

/-! ## SSA equality condition

The Hayashi (2003) characterization of equality in strong subadditivity is
defined as a predicate. The characterization theorem (equality ↔ recovery map
condition) is axiomatized.

TODO: Replace with a proof following Hayashi, "Quantum Information: An
Introduction", Springer 2006, Theorem 5.24. -/

section SSAEquality

variable {dA dB dC : ℕ}

/-- Predicate asserting that equality holds in strong subadditivity for a
tripartite state `ρ_ABC`. -/
def IsSSAEquality
    [DecidableEq (Fin dA × Fin dB × Fin dC)]
    [DecidableEq (Fin dA × Fin dB)]
    [DecidableEq (Fin dB × Fin dC)]
    [DecidableEq (Fin dB)]
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_ABC : ρ_ABC.IsHermitian)
    (hρ_B : (traceAC_ABC ρ_ABC).IsHermitian)
    (hρ_AB : (traceC_ABC ρ_ABC).IsHermitian)
    (hρ_BC : (traceA_ABC ρ_ABC).IsHermitian) : Prop :=
  vonNeumannEntropy ρ_ABC hρ_ABC
    + vonNeumannEntropy (traceAC_ABC ρ_ABC) hρ_B
  = vonNeumannEntropy (traceC_ABC ρ_ABC) hρ_AB
    + vonNeumannEntropy (traceA_ABC ρ_ABC) hρ_BC

end SSAEquality

/-! ## Mutual information -/

section MutualInformation

variable {dA dB : ℕ}

/-- **Quantum mutual information** between subsystems A and B.

`I(A:B) = S(ρ_A) + S(ρ_B) - S(ρ_AB)`

Measures the total correlations (classical + quantum) between A and B. -/
noncomputable def mutualInformation
    [DecidableEq (Fin dA × Fin dB)]
    [DecidableEq (Fin dA)] [DecidableEq (Fin dB)]
    (ρ_AB : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hρ_AB : ρ_AB.IsHermitian)
    (hρ_A : (Matrix.traceRight ρ_AB).IsHermitian)
    (hρ_B : (Matrix.traceLeft ρ_AB).IsHermitian) : ℝ :=
  vonNeumannEntropy (Matrix.traceRight ρ_AB) hρ_A
    + vonNeumannEntropy (Matrix.traceLeft ρ_AB) hρ_B
    - vonNeumannEntropy ρ_AB hρ_AB

/-- Mutual information is nonneg: `I(A:B) ≥ 0`.

This follows directly from subadditivity: `S(ρ_AB) ≤ S(ρ_A) + S(ρ_B)`. -/
theorem mutualInformation_nonneg
    [DecidableEq (Fin dA × Fin dB)]
    [DecidableEq (Fin dA)] [DecidableEq (Fin dB)]
    (ρ_AB : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hρ_AB : ρ_AB.IsHermitian)
    (hρ_dm : ρ_AB.PosSemidef ∧ ρ_AB.trace = 1)
    (hρ_A : (Matrix.traceRight ρ_AB).IsHermitian)
    (hρ_B : (Matrix.traceLeft ρ_AB).IsHermitian) :
    0 ≤ mutualInformation ρ_AB hρ_AB hρ_A hρ_B := by
  unfold mutualInformation
  linarith [subadditivity ρ_AB hρ_AB hρ_dm hρ_A hρ_B]

/-- **Area law** for mutual information of MPDO states.

For an MPDO with bond dimension `D`, the mutual information across any cut
satisfies `I(A:B) ≤ 4 * log D`.

TODO: Prove from the bond-dimension structure of MPDO transfer matrices.

References:
* arXiv:1606.00608 §4.4 -/
theorem mutualInformation_area_law
    [DecidableEq (Fin dA × Fin dB)]
    [DecidableEq (Fin dA)] [DecidableEq (Fin dB)]
    (ρ_AB : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hρ_AB : ρ_AB.IsHermitian)
    (hρ_A : (Matrix.traceRight ρ_AB).IsHermitian)
    (hρ_B : (Matrix.traceLeft ρ_AB).IsHermitian)
    (bondDim : ℕ) (hD : 0 < bondDim) :
    mutualInformation ρ_AB hρ_AB hρ_A hρ_B ≤ 4 * Real.log bondDim := by
  sorry

end MutualInformation
