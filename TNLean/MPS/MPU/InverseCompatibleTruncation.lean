/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.InverseCompatibleSourceTransport
import TNLean.MPS.MPU.TruncatedSymmetryUnitarity

/-!
# Inverse-compatible transport of truncated symmetries

The proved unitary comparison, after the explicit source-rank transport, gives
$S.Y_1=C^\dagger S_0.Y_1$, while $S.Y_2=S_0.Y_2$. Consequently the endpoint
contraction is multiplied on its right source coordinate by $C^\dagger$.
The multiplier is $I_\ell\otimes(I\otimes C^\dagger)$ in the right-associated
row coordinates. Its unitarity transports the existing all-length theorem.
Here $N$ counts bulk sites; the source total length is $L=N+2\geq2$, so the
zero-bulk case has total length two.

Source: arXiv:2502.20257, the unitary comparison and transport of pleasant
properties at lines 5432–5487, applied to `eq:truncsym` (lines 2062–2099).
This is endpoint-coordinate transport after comparison unitarity, not a new
proof of that comparison. It does not establish `eq:UUU`, a packaged gate
phase without rank transport, or the finite-group physical-action assertion.
-/

open scoped ComplexOrder Matrix Kronecker BigOperators

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D) (T : Matrix.unitaryGroup (Fin D) ℂ)
  (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U)
  (hT : ∀ i j, physicalAdjointTensor U i j =
    (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T)
  (σ : ℂ) (hσ : (T : Matrix (Fin D) (Fin D) ℂ) *
    (T : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = σ • 1)

/-- Entrywise transport of the endpoint contraction at every bulk length `N`.
Only the right source coordinate changes, by the adjoint of the square,
rank-transported comparison. Source: FBC25, lines 5432–5487 and `eq:truncsym`,
lines 2062–2099; total source length is $N+2$. -/
theorem inverseCompatibleSourceFactors_truncatedSymmetry_apply (N : ℕ)
    (l : Fin ℓ[U]) (r : Fin r[U]) (p q : Fin N → Fin d) (a b : Fin d) :
    let S₀ := sourceFactors U hU.ρ hU.ρ_posDef
    let S := inverseCompatibleSourceFactors U T hU hsimple hT σ hσ
    let C := Matrix.reindex (Equiv.refl _) (inverseCompatibleRankEquiv U T hT)
      (inverseCompatibleComparisonK U T hU.ρ hU.ρ_posDef)
    S.truncatedSymmetry N (l, p, r) (a, q, b) =
      ∑ t, Cᴴ r t * S₀.truncatedSymmetry N (l, p, t) (a, q, b) := by
  obtain ⟨_, _, hY⟩ :=
    inverseCompatibleSourceFactors_unitary_transport U T hU hsimple hT σ hσ
  have hY₂ : (inverseCompatibleSourceFactors U T hU hsimple hT σ hσ).Y₂ =
      (sourceFactors U hU.ρ hU.ρ_posDef).Y₂ := rfl
  dsimp only
  simp only [SourceFactors.truncatedSymmetry, truncatedSymmetryOfEndpoints, hY,
    hY₂, Matrix.mul_apply, Finset.mul_sum]
  rw [Fintype.sum_reverse_three]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr₂ fun α _ β _ ↦ by ac_rfl

/-- Matrix transport on the right-associated row coordinates
$\operatorname{Fin}\ell\times((\operatorname{Fin}N\to\operatorname{Fin}d)
\times\operatorname{Fin}r)$. Source: FBC25, pleasant-property transport at
lines 5486–5487 applied to `eq:truncsym` (lines 2062–2099). -/
theorem inverseCompatibleSourceFactors_truncatedSymmetry_eq (N : ℕ) :
    let S₀ := sourceFactors U hU.ρ hU.ρ_posDef
    let S := inverseCompatibleSourceFactors U T hU hsimple hT σ hσ
    let C := Matrix.reindex (Equiv.refl _) (inverseCompatibleRankEquiv U T hT)
      (inverseCompatibleComparisonK U T hU.ρ hU.ρ_posDef)
    S.truncatedSymmetry N =
      ((1 : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ) ⊗ₖ
        ((1 : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) ⊗ₖ Cᴴ)) *
          S₀.truncatedSymmetry N := by
  classical
  dsimp only
  ext ⟨l, p, r⟩ ⟨a, q, b⟩
  rw [inverseCompatibleSourceFactors_truncatedSymmetry_apply U T hU hsimple hT σ hσ]
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.one_apply, ite_mul, mul_ite]

/-- The inverse-compatible endpoint contraction is unitary between its
coordinate spaces at every bulk length `N`, or total source length $N+2\geq2$.
This follows by the proved unitary coordinate transport from the chosen-source
all-length theorem, without another induction. Source: FBC25, lines 5486–5487
and the unitarity assertion following `eq:truncsym` (lines 2062–2099). -/
theorem inverseCompatibleSourceFactors_truncatedSymmetry_isUnitaryBetween (N : ℕ) :
    Matrix.IsUnitaryBetween
      ((inverseCompatibleSourceFactors U T hU hsimple hT σ hσ).truncatedSymmetry N) := by
  classical
  obtain ⟨hC, _, _⟩ :=
    inverseCompatibleSourceFactors_unitary_transport U T hU hsimple hT σ hσ
  have hI (A : Type) [Fintype A] [DecidableEq A] :
      (1 : Matrix A A ℂ).IsUnitaryBetween := by
    simp [Matrix.IsUnitaryBetween, Matrix.IsIsometry, Matrix.IsCoisometry]
  rw [inverseCompatibleSourceFactors_truncatedSymmetry_eq U T hU hsimple hT σ hσ]
  exact ((hI (Fin ℓ[U])).kronecker _ _
    ((hI (Fin N → Fin d)).kronecker _ _ (hC.conjTranspose _))).mul _ _
      (hU.truncatedSymmetry_isUnitaryBetween hsimple N)

end MPOTensor
