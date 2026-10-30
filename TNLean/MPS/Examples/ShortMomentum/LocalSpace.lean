/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.ShortMomentum.WeylWords
import TNLean.MPS.ParentHamiltonian.GroundSpace

/-!
# The actual local Weyl boundary space

Every local boundary vector is exactly a character phase times an
arbitrary function of the total Weyl charge. The converse is obtained
from explicit trace-dual matrices, so no supplied local-space
classification is used. This is a local statement; global periodic
intersection and all-volume uniqueness remain separate obligations.

Source context: SPWC10, arXiv:0909.5347, Theorem 5, main.tex lines 850--880;
see `docs/audits/2026-10-29_weyl_short_volume_candidate.md`.
-/

open Matrix
open scoped BigOperators

namespace MPSTensor.ShortMomentum

/-- The exact trace, including the central charged matrix. -/
theorem trace_chargedWeyl {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (u v : ZMod 5) :
    (chargedWeyl ζ u v).trace = if (u, v) = 0 then 5 else 0 := by
  by_cases h : (u, v) = 0
  · have hu : u = 0 := congrArg Prod.fst h
    have hv : v = 0 := congrArg Prod.snd h
    rw [ite_eq_left h, hu, hv, chargedWeyl_zero, Matrix.trace_one, ZMod.card, Nat.cast_ofNat]
  · rw [ite_eq_right h]
    exact trace_chargedWeyl_eq_zero hζ u v h

/-- The explicit matrix trace-dual to one charged Weyl matrix. -/
noncomputable def chargedWeylDual (ζ : ℂ) (p : ZMod 5 × ZMod 5) :
    Matrix (ZMod 5) (ZMod 5) ℂ :=
  ((5 : ℂ)⁻¹ * rootCharacter ζ (-p.1 * p.2)) • chargedWeyl ζ (-p.1) (-p.2)

/-- Actual trace orthogonality of the charged matrices and their explicit duals. -/
theorem trace_chargedWeyl_mul_dual {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5)
    (p q : ZMod 5 × ZMod 5) :
    (chargedWeyl ζ p.1 p.2 * chargedWeylDual ζ q).trace = if p = q then 1 else 0 := by
  rw [chargedWeylDual, mul_smul_comm, chargedWeyl_mul hζ.pow_eq_one,
    Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul,
    trace_chargedWeyl hζ]
  by_cases h : p = q
  · subst q
    have hzero : (p.1 + -p.1, p.2 + -p.2) = (0 : ZMod 5 × ZMod 5) := by simp
    rw [ite_eq_left hzero, ite_eq_left rfl]
    simp only [neg_neg]
    calc
      ((5 : ℂ)⁻¹ * rootCharacter ζ (-p.1 * p.2)) *
          (rootCharacter ζ (p.1 * p.2) * 5) =
          (5 : ℂ)⁻¹ * (rootCharacter ζ (-p.1 * p.2) *
            rootCharacter ζ (p.1 * p.2)) * 5 := by ring
      _ = 1 := by
        rw [← rootCharacter_add hζ.pow_eq_one,
          show -p.1 * p.2 + p.1 * p.2 = 0 by ring, rootCharacter_zero]
        norm_num
  · have hzero : (p.1 + -q.1, p.2 + -q.2) ≠ (0 : ZMod 5 × ZMod 5) := by
      intro hz
      apply h
      apply Prod.ext
      · exact sub_eq_zero.mp
          (by simpa only [sub_eq_add_neg, Prod.fst_zero] using congrArg Prod.fst hz)
      · exact sub_eq_zero.mp
          (by simpa only [sub_eq_add_neg, Prod.snd_zero] using congrArg Prod.snd hz)
    rw [ite_eq_right hzero, ite_eq_right h, mul_zero, mul_zero]

/-- An actual boundary matrix representing a prescribed function of the charge. -/
noncomputable def chargeBoundary (ζ : ℂ) (g : ZMod 5 × ZMod 5 → ℂ) :
    Matrix (ZMod 5) (ZMod 5) ℂ :=
  ∑ q : ZMod 5 × ZMod 5, g q • chargedWeylDual ζ q

/-- The explicit boundary matrix evaluates to the prescribed charge function. -/
theorem trace_chargedWeyl_mul_chargeBoundary {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5)
    (g : ZMod 5 × ZMod 5 → ℂ) (p : ZMod 5 × ZMod 5) :
    (chargedWeyl ζ p.1 p.2 * chargeBoundary ζ g).trace = g p := by
  simp only [chargeBoundary, Matrix.mul_sum, mul_smul_comm, Matrix.trace_sum,
    Matrix.trace_smul, smul_eq_mul, trace_chargedWeyl_mul_dual hζ]
  rw [Finset.sum_eq_single p]
  · simp
  · intro q _ hq
    simp only [ite_eq_right (Ne.symm hq), mul_zero]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- Exact local-space characterization on actual finite configurations. -/
theorem mem_groundSpace_threeLetterTensor_iff {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5)
    (n : ℕ) (f : NSiteSpace 3 n) :
    f ∈ groundSpace (threeLetterTensor ζ) n ↔
      ∃ g : ZMod 5 × ZMod 5 → ℂ, ∀ σ : Cfg 3 n,
        f σ = rootCharacter ζ (wordPhase (List.ofFn σ)) *
          g (wordCharge (List.ofFn σ)) := by
  constructor
  · rintro ⟨X, rfl⟩
    let Y : Matrix (ZMod 5) (ZMod 5) ℂ := X
    refine ⟨fun p ↦ (chargedWeyl ζ p.1 p.2 * Y).trace, fun σ ↦ ?_⟩
    rw [groundSpaceMap_apply, evalWord_threeLetterTensor hζ.pow_eq_one]
    change ((_ : Matrix (ZMod 5) (ZMod 5) ℂ) * Y).trace = _
    rw [smul_mul_assoc, Matrix.trace_smul, smul_eq_mul]
  · rintro ⟨g, hg⟩
    refine ⟨chargeBoundary ζ g, ?_⟩
    funext σ
    rw [groundSpaceMap_apply (X := chargeBoundary ζ g), evalWord_threeLetterTensor hζ.pow_eq_one]
    change ((_ : Matrix (ZMod 5) (ZMod 5) ℂ) * chargeBoundary ζ g).trace = _
    rw [smul_mul_assoc, Matrix.trace_smul, smul_eq_mul,
      trace_chargedWeyl_mul_chargeBoundary hζ]
    exact (hg σ).symm

/-- Equal-charge configurations have exactly the corresponding phase relation
in every actual local boundary vector. -/
theorem groundSpace_threeLetterTensor_same_charge {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5)
    {n : ℕ} {f : NSiteSpace 3 n} (hf : f ∈ groundSpace (threeLetterTensor ζ) n)
    (σ τ : Cfg 3 n) (hcharge : wordCharge (List.ofFn σ) = wordCharge (List.ofFn τ)) :
    rootCharacter ζ (wordPhase (List.ofFn τ)) * f σ =
      rootCharacter ζ (wordPhase (List.ofFn σ)) * f τ := by
  obtain ⟨g, hg⟩ := (mem_groundSpace_threeLetterTensor_iff hζ n f).mp hf
  rw [hg σ, hg τ, hcharge]
  ring

end MPSTensor.ShortMomentum
