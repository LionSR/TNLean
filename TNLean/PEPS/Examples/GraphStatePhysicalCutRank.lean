/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.BinaryCutCharacters
import TNLean.PEPS.Examples.HoneycombCluster
import Mathlib.LinearAlgebra.Matrix.Rank

/-! The physical coefficient matrix splits a full spin assignment across a vertex bipartition. Its rank counts independent binary cross-adjacency characters. The open-region map instead takes virtual boundary labels as inputs. This proof works directly with coefficient matrices and uses no Schmidt-decomposition API. -/

open scoped BigOperators
open ManyBody (Edge)
namespace TNLean.PEPS.PhysicalCut
open BinaryCutCharacters
variable {V : Type*} [LinearOrder V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (R : Finset V)
abbrev X := R → F
abbrev Y := {v : V // v ∉ R} → F

def L (v : V) : X R →ₗ[F] F := if h : v ∈ R then LinearMap.proj ⟨v,h⟩ else 0
def T (v : V) : Y R →ₗ[F] F := if h : v ∈ R then 0 else LinearMap.proj ⟨v,h⟩

/-- Each ordered edge contributes to the cut pairing in whichever orientation crosses. -/
def cross : X R →ₗ[F] Y R →ₗ[F] F :=
  ∑ e : Edge G, ((L R e.1.1).smulRight (T R e.1.2) + (L R e.1.2).smulRight (T R e.1.1))

def q (s : V → F) := ∑ e : Edge G, s e.1.1 * s e.1.2

theorem phase_split (x : X R) (y : Y R) :
    q G (fun v => L R v x + T R v y) =
      q G (fun v => L R v x) + cross G R x y + q G (fun v => T R v y) := by
  simp only [q,cross,LinearMap.sum_apply,LinearMap.add_apply,LinearMap.smulRight_apply,
    LinearMap.smul_apply,smul_eq_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros
  ring

private theorem sign_q (s : V → F) :
    graphCircuitSign (fun e : Edge G => e.1.1) (fun e => e.1.2) s = sign (q G s) := by
  classical
  have bit (a b : F) : (-1 : ℂ) ^ (a.val * b.val) = sign (a*b) := by
    have cases2 : ∀ a : F, a = 0 ∨ a = 1 := by decide
    rcases cases2 a with rfl|rfl <;> rcases cases2 b with rfl|rfl <;> norm_num [sign, show (1:F).val = 1 by decide]
  unfold graphCircuitSign q
  change (∏ e : Edge G, (-1 : ℂ) ^ ((s e.1.1).val * (s e.1.2).val)) = _
  simp_rw [bit]
  induction (Finset.univ : Finset (Edge G)) using Finset.induction_on with
  | empty => simp
  | insert e s he ih => rw [Finset.prod_insert he,Finset.sum_insert he,AddChar.map_add_eq_mul,ih]

noncomputable def physical : Matrix (X R) (Y R) ℂ :=
  fun x y => stateCoeff (graphStatePEPS G) (fun v => L R v x + T R v y)

noncomputable def C := (Complex.invSqrtTwo : ℂ) ^ Fintype.card (Edge G)

theorem entry (x : X R) (y : Y R) :
    physical G R x y = (C G * sign (q G (fun v => L R v x))) *
      sign (cross G R x y) * sign (q G (fun v => T R v y)) := by
  unfold physical C
  rw [stateCoeff_graphStatePEPS G (fun v => L R v x + T R v y),sign_q G (fun v => L R v x + T R v y),phase_split,AddChar.map_add_eq_mul,AddChar.map_add_eq_mul]
  ring

theorem physical_rank : (physical G R).rank = 2 ^ Module.finrank F (cross G R).range := by
  classical
  let A : Matrix (X R) (Y R) ℂ := fun x y => sign (cross G R x y)
  let l (x : X R) := C G * sign (q G (fun v => L R v x))
  let r (y : Y R) := sign (q G (fun v => T R v y))
  have h : physical G R = Matrix.diagonal l * A * Matrix.diagonal r := by
    ext x y
    rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
    exact entry G R x y
  have nz (a : F) : sign a ≠ 0 := by change (if a = 0 then (1:ℂ) else -1) ≠ 0; split <;> norm_num
  rw [h, Matrix.rank_mul_eq_left_of_det_ne_zero, Matrix.rank_mul_eq_right_of_det_ne_zero,
    Matrix.rank_eq_finrank_span_row]
  · exact row_span_finrank (cross G R)
  · rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => mul_ne_zero (by simp [C,Complex.invSqrtTwo]) (nz _)
  · rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => nz _

end TNLean.PEPS.PhysicalCut

namespace TNLean.PEPS.PhysicalCut
open BinaryCutCharacters
variable {V : Type*} [LinearOrder V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem empty_rank : (physical G ∅).rank = 1 := by
  rw [physical_rank]
  have hz : cross G ∅ = 0 := by ext x y; simp [cross,L]
  simp [hz]

theorem univ_rank : (physical G Finset.univ).rank = 1 := by
  rw [physical_rank]
  have hz : cross G Finset.univ = 0 := by ext x y; simp [cross,T]
  simp [hz]

end TNLean.PEPS.PhysicalCut
