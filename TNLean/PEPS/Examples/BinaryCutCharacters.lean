/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.FieldTheory.Finiteness

/-! The complex row span of a binary bilinear character matrix has dimension two to the binary rank. -/

namespace TNLean.PEPS.BinaryCutCharacters
abbrev F := ZMod 2

private theorem cases_bit : ∀ a : F, a = 0 ∨ a = 1 := by decide

def sign : AddChar F ℂ where
  toFun t := if t = 0 then 1 else -1
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    rcases cases_bit a with rfl|rfl <;> rcases cases_bit b with rfl|rfl <;>
      norm_num [show (1:F)+1=0 by decide]
    decide

variable {X Y : Type*} [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
variable [Finite X] [Finite Y] (B : X →ₗ[F] Y →ₗ[F] F)

def character (l : Y →ₗ[F] F) := sign.compAddMonoidHom l.toAddMonoidHom

theorem row_span_finrank :
    Module.finrank ℂ (Submodule.span ℂ (Set.range fun x : X => fun y : Y => sign (B x y))) =
      2 ^ Module.finrank F B.range := by
  classical
  have : Finite B.range := Finite.of_surjective B.rangeRestrict (by rintro ⟨_,x,rfl⟩; exact ⟨x,rfl⟩)
  let _ := Fintype.ofFinite B.range
  let f (l : B.range) := character l.val
  have inj : Function.Injective f := by
    intro l k eq
    apply Subtype.ext
    ext y
    have h := congrArg (fun c : AddChar Y ℂ => c y) eq
    change (if l.val y = 0 then (1 : ℂ) else -1) = (if k.val y = 0 then 1 else -1) at h
    generalize l.val y = a at *
    generalize k.val y = b at *
    rcases cases_bit a with rfl|rfl <;> rcases cases_bit b with rfl|rfl <;> norm_num at *
  have ranges : Set.range (fun x : X => fun y : Y => sign (B x y)) =
      Set.range (fun l : B.range => (f l : Y → ℂ)) := by
    ext g
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨B.rangeRestrict x,rfl⟩
    · rintro ⟨⟨l,x,rfl⟩,rfl⟩
      exact ⟨x,rfl⟩
  rw [ranges]
  trans Fintype.card B.range
  · exact finrank_span_eq_card ((AddChar.linearIndependent Y ℂ).comp f inj)
  rw [
    Module.card_eq_pow_finrank (K := F)]
  simp [F]
end TNLean.PEPS.BinaryCutCharacters
