/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SourceUOpenTail

/-!
# Boundary algebra for the source tensor u

This file records the normalized open-tail coefficient occurring in the proof
of `lemuisometry` from arXiv:1703.09188, lines 545--557, and closes its outer
source-factor boundary once the internal tail has the rank-one kernel shown in
equation `uUnitary`.

The coefficient retains exactly one factor $d^{-K}$. In the surrounding Gram
contraction the output pair $q$ is unstarred and the conjugated output pair $p$
is starred; their source-$u$ entries are external to the coefficient defined
here.

**Scope boundary:** no result here identifies the forward open tail with a
reflected contraction, proves that `sourceU` is an isometry, or derives a rank
bound. The terminal contraction uses only $X_2^\dagger X_2=1$, never an ambient
coisometry identity.
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D)

/-- The normalized coefficient of the fully sandwiched open $K$-site tail.

The retained source-$u$ entry indexed by $q$ is unstarred and the entry indexed
by $p$ is starred in the Gram contraction; these two external entries are not
part of the coefficient. Thus the displayed expression contains exactly one
normalization factor $d^{-K}$.

Source: arXiv:1703.09188, equation `uUnitary`, lines 550--556. -/
noncomputable def sourceUOpenTailCoefficient
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) (K : ℕ)
    (l : Fin ℓ[U]) (r : Fin r[U]) (l' : Fin ℓ[U]) (r' : Fin r[U]) : ℂ :=
  ((d : ℂ)⁻¹) ^ K *
    ∑ τ : Fin K → Fin d, ∑ ζ : Fin K → Fin d,
    ∑ j₁ : Fin d, ∑ j₂ : Fin d,
    ∑ α : Fin D, ∑ α' : Fin D,
    ∑ β : Fin D, ∑ β' : Fin D,
    ∑ i : Fin d, ∑ i' : Fin d,
      sourceX₁ U ρ hρ (α, j₁) r *
        star (sourceX₁ U ρ hρ (α', j₁) r') *
        star (sourceX₂ U (β, i) l) * sourceX₂ U (β', i') l' *
        (U i j₂ * evalWord U (List.ofFn τ) (List.ofFn ζ)) β α *
        star ((U i' j₂ * evalWord U (List.ofFn τ) (List.ofFn ζ)) β' α')

/-- If the internal open tail has kernel
$\rho_{\alpha',\alpha}\delta_{\beta,\beta'}\delta_{i,i'}$, then its weighted
$X_1$ and unweighted $X_2$ boundary is
$\delta_{l,l'}\delta_{r,r'}$.

This is the terminal boundary step in arXiv:1703.09188, equation `uUnitary`,
lines 550--556. It uses the normalization identities in equation `Y1Y1X1X1`,
lines 479--494. -/
theorem sourceU_boundary_sandwich
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (l : Fin ℓ[U]) (r : Fin r[U]) (l' : Fin ℓ[U]) (r' : Fin r[U]) :
    (∑ j : Fin d, ∑ α : Fin D, ∑ α' : Fin D,
      ∑ β : Fin D, ∑ i : Fin d,
        sourceX₁ U ρ hρ (α, j) r *
          star (sourceX₁ U ρ hρ (α', j) r') *
          star (sourceX₂ U (β, i) l) * sourceX₂ U (β, i) l' * ρ α' α) =
      (if l = l' then 1 else 0) * (if r = r' then 1 else 0) := by
  classical
  have h₁ := sourceX₁_weighted_isometry_apply U ρ hρ r' r
  simp only [sourceWeight, Matrix.kronecker_apply, Matrix.one_apply, mul_ite,
    mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Fintype.sum_prod_type] at h₁
  rw [Finset.sum_comm] at h₁
  have h₁' :
      (∑ j : Fin d, ∑ α : Fin D,
        (∑ α' : Fin D, star (sourceX₁ U ρ hρ (α', j) r') * ρ α' α) *
          sourceX₁ U ρ hρ (α, j) r) = if r' = r then 1 else 0 := by
    simpa only [Finset.sum_mul] using h₁
  have h₂ := sourceX₂_isometry_apply U l l'
  have hreorder (j : Fin d) (α α' β : Fin D) (i : Fin d) :
      sourceX₁ U ρ hρ (α, j) r * star (sourceX₁ U ρ hρ (α', j) r') *
          star (sourceX₂ U (β, i) l) * sourceX₂ U (β, i) l' * ρ α' α =
        (star (sourceX₁ U ρ hρ (α', j) r') * ρ α' α *
          sourceX₁ U ρ hρ (α, j) r) *
        (star (sourceX₂ U (β, i) l) * sourceX₂ U (β, i) l') := by
    ring
  simp_rw [hreorder]
  simp_rw [← Finset.mul_sum]
  rw [h₂]
  simp_rw [← Finset.sum_mul]
  rw [h₁']
  simp only [eq_comm, mul_comm]

end MPOTensor
