/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Order.Interval.Finset.Fin
import TNLean.MPS.Tensor.TruncationCommutator

/-!
# Endpoint dependence of the finite-group detector at order two

The finite-group detector of arXiv:2405.00439, Section V, `detectG`
(`Papers/2405.00439/MPU-DW.tex`, lines 2108–2117), uses six truncations at
group-element order two. It is distinct from the four-factor commutator `detecZ2`.
Here the truncations act chronologically in increasing index, so the forward
written product is `T₂₂ T₁₁ T₀₀`, and the undo product is
`T₀₁† T₂₂† T₁₀†`, exactly as written in the source.

For the printed cut order `a₀ < a₂ < a₁ < b₀ < b₂ < b₁`, the left-dressed on-site
truncations `T(a,b) = Zₐ X^[a,b]` give the detector `-1`, although the on-site
symmetry has trivial anomaly. The calculation is for arbitrary chain length and
arbitrarily separated cuts. `FiniteGroupDetectorConstruction` separately proves
a fixed-circuit realization of dressed intervals on paired sites, including the
extension to every positive even cyclic order. See
`docs/audits/2026-11-15_finite_group_detector_endpoints.md` for the scope comparison.

**Scope:** the matrix identity below is a counterexample for an explicit interval
operator family. It does not identify arbitrary source truncations with
canonical domain-wall strings. In particular it does not assert `detectG`.
-/

open scoped Matrix

namespace Matrix

variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The interval truncation `wₐ u^[a,b]`, dressed at its left endpoint.
Source context: arXiv:2405.00439, Section V, lines 2081–2087 and `detectG`.
The dressing is an explicit choice, not a hypothesis implicit in that source. -/
noncomputable def leftDressedOnSiteInterval (u w : Matrix ι ι ℂ) (a b : Fin N) :
    Matrix (Fin N → ι) (Fin N → ι) ℂ :=
  onSiteTruncation w {a} * onSiteTruncation u (Finset.Icc a b)

/-- The six-factor detector at group-element order two, with forward action
`T₀₀`, then `T₁₁`, then `T₂₂` on kets. Source: arXiv:2405.00439, `detectG`,
lines 2108–2117. The order of multiplication is specified explicitly. -/
def cyclicTwoTruncationDetector (T : Fin N → Fin N → Matrix ι ι ℂ)
    (a₀ a₁ a₂ b₀ b₁ b₂ : Fin N) : Matrix ι ι ℂ :=
  (T a₀ b₁)ᴴ * (T a₂ b₂)ᴴ * (T a₁ b₀)ᴴ * T a₂ b₂ * T a₁ b₁ * T a₀ b₀

/-- Every interval in a left-dressed on-site family is unitary if both one-site
matrices are unitary. Source context: arXiv:2405.00439, Section V, lines
2081–2087. This is a property of the explicit family, not a circuit comparison. -/
theorem leftDressedOnSiteInterval_conjTranspose_mul_self {u w : Matrix ι ι ℂ}
    (hu : uᴴ * u = 1) (hw : wᴴ * w = 1) (a b : Fin N) :
    (leftDressedOnSiteInterval u w a b)ᴴ * leftDressedOnSiteInterval u w a b = 1 :=
  dressed_onSiteTruncation_conjTranspose_mul_self hu hw (Finset.Icc a b) a

local notation "σX" => !![(0 : ℂ), 1; 1, 0]
local notation "σZ" => !![(1 : ℂ), 0; 0, -1]

/-- The chronological finite-group detector at order two is `-1` for the coherent
left-endpoint dressings `T(a,b) = Zₐ X^[a,b]` and the printed cut order.

Project counterexample to the arbitrary-truncation reading of arXiv:2405.00439,
`detectG`, lines 2108–2117. The six-factor matrix identity is formalized here;
the fixed-circuit identification and the general even-order extension are separate
claims in `docs/audits/2026-11-15_finite_group_detector_endpoints.md`. -/
theorem cyclicTwoTruncationDetector_leftDressedOnSiteInterval_pauliX
    {a₀ a₁ a₂ b₀ b₁ b₂ : Fin N}
    (h₀ : a₀ < a₂) (h₁ : a₂ < a₁) (h₂ : a₁ < b₀)
    (h₃ : b₀ < b₂) (h₄ : b₂ < b₁) :
    cyclicTwoTruncationDetector (leftDressedOnSiteInterval σX σZ)
      a₀ a₁ a₂ b₀ b₁ b₂ = -1 := by
  simp only [cyclicTwoTruncationDetector, leftDressedOnSiteInterval,
    onSiteTruncation, Matrix.piKronecker_mul, Matrix.conjTranspose_piKronecker]
  rw [← neg_one_smul ℂ (1 : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ),
    ← Matrix.piKronecker_ite_smul_one (ι := fun _ ↦ Fin 2) a₁]
  congr 1
  funext k
  simp only [Finset.mem_singleton, Finset.mem_Icc, Fin.le_def, Fin.ext_iff]
  simp only [Fin.lt_def] at h₀ h₁ h₂ h₃ h₄
  split_ifs <;> first
    | omega
    | (ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two])

/-- The six-factor finite-group detector of the explicit dressed interval family
has expectation `-1` on every normalized state. Source context:
arXiv:2405.00439, `detectG`, lines 2108–2117; this is the matrix counterexample
above, not the claimed anomaly detection theorem. -/
theorem star_dotProduct_cyclicTwoTruncationDetector_leftDressedOnSiteInterval_pauliX
    {a₀ a₁ a₂ b₀ b₁ b₂ : Fin N}
    (h₀ : a₀ < a₂) (h₁ : a₂ < a₁) (h₂ : a₁ < b₀)
    (h₃ : b₀ < b₂) (h₄ : b₂ < b₁)
    {ψ : (Fin N → Fin 2) → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    star ψ ⬝ᵥ (cyclicTwoTruncationDetector (leftDressedOnSiteInterval σX σZ)
      a₀ a₁ a₂ b₀ b₁ b₂ *ᵥ ψ) = -1 := by
  rw [cyclicTwoTruncationDetector_leftDressedOnSiteInterval_pauliX h₀ h₁ h₂ h₃ h₄,
    neg_mulVec, one_mulVec, dotProduct_neg, hψ]

end Matrix
