/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusPhysicalMap
import TNLean.PEPS.TorusPhysicalBondRegrouping

/-!
# Product physical maps on coherent finite sums

A finite product of rectangular physical maps transforms each factor of every
product vector separately. The identity applies to arbitrary coherent sums;
it does not assume an equality of PEPS coefficients. Source: SCP10,
arXiv:1001.3807, lines 1765–1820 and Section 7, lines 2977–3019.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {Edge Q In Out : Type*} [Fintype Edge] [DecidableEq Edge]
variable [Fintype Q] [Fintype In]
/-- A product physical map acts separately on every bond factor in a coherent sum.
Source: SCP10, accessible-virtual-coordinate argument, lines 1765–1820, and
Section 7, lines 2977–3019. -/
theorem physicalProductMap_sum_prod (F : Matrix Out In ℂ) (w : Q → ℂ)
    (x : Edge → Q → In → ℂ) :
    physicalProductMap Edge F (fun σ => ∑ q, w q * ∏ e, x e q (σ e)) =
      fun τ => ∑ q, w q * ∏ e, (F *ᵥ x e q) (τ e) := by
  ext τ
  simp only [physicalProductMap_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  calc
    _ = w q * ∑ σ : Edge → In, ∏ e, F (τ e) (σ e) * x e q (σ e) := by
      simp only [Finset.mul_sum, Finset.prod_mul_distrib, mul_left_comm]
    _ = w q * ∏ e, ∑ i : In, F (τ e) i * x e q i := by
      rw [Fintype.prod_sum]
    _ = _ := rfl
end TNLean.PEPS

namespace TNLean.PEPS
variable {G V : Type*} [Group G] [Fintype G] [Fintype V] [DecidableEq V]
variable {width height : ℕ} [NeZero width] [NeZero height]
/-- The group ratio read by an oriented native physical bond.
Source: SCP10, Section 7, lines 2977–3007. -/
def torusBondRelativeElement (q : TorusVertex width height → G)
    (e : TorusVertex width height × Bool) : G :=
  if e.2 then q e.1 * (q (e.1.1, e.1.2 + 1))⁻¹
  else q (e.1.1 + 1, e.1.2) * (q e.1)⁻¹

/-- The actual dressed averaging-site state is a coherent sum of physical
bond products. Source: SCP10, Section 7, lines 2977–3007. -/
theorem torusBondRegrouping_dressedAveragingSite_coherent
    (U : G →* Matrix V V ℂ) (W : Matrix V V ℂ)
    (hc : ∀ g, Commute W (U g)) :
    torusBondRegrouping (fun σ => torusBondNetwork
      (fun v c => torusDress W W
        (fun t => averagingSite U t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v)) c) 1 1) =
      fun β => ∑ q : TorusVertex width height → G,
        (Fintype.card G : ℂ)⁻¹ ^ Fintype.card (TorusVertex width height) *
          ∏ e : TorusVertex width height × Bool,
            (W ^ 2 * U (torusBondRelativeElement q e)) (β e).1 (β e).2 := by
  ext β
  rw [torusBondRegrouping_dressedAveragingSite U W hc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  exact torusBond_product (fun e =>
    (W ^ 2 * U (torusBondRelativeElement q e)) (β e).1 (β e).2)
/-- The actual averaging-site state is a coherent sum of physical bond products.
Source: SCP10, Section 7, lines 2977–3007. -/
theorem torusBondRegrouping_averagingSite_coherent (U : G →* Matrix V V ℂ) :
    torusBondRegrouping (fun σ => torusBondNetwork
      (fun v c => averagingSite U c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v)) 1 1) =
      fun β => ∑ q : TorusVertex width height → G,
        (Fintype.card G : ℂ)⁻¹ ^ Fintype.card (TorusVertex width height) *
          ∏ e : TorusVertex width height × Bool,
            U (torusBondRelativeElement q e) (β e).1 (β e).2 := by
  ext β
  rw [torusBondRegrouping_averagingSite, Finset.mul_sum]
  simp only [Pi.one_apply, Matrix.mul_one, ← map_mul]
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  exact torusBond_product (fun e => U (torusBondRelativeElement q e) (β e).1 (β e).2)
end TNLean.PEPS
