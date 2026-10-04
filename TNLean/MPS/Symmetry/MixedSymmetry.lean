/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.SymmetryParity
import TNLean.Algebra.ListProduct
import TNLean.MPS.Core.CyclicTrace

/-!
# Mixed on-site, time-reversal and reflection actions

The scalar parity is time reversal. Reflection additionally transposes each
letter, hence reverses the order of sites in an ordered matrix contraction.
The physical matrices compose with conjugation according to time reversal,
whereas the virtual matrices compose at the sum of the two parities.

Source: arXiv:2011.12127, Section III.A, `Papers/2011.12127/TN-Review-main.tex`
lines 1120–1130 and 1147–1157.
-/

open scoped Matrix
open TNLean.Algebra

namespace MPSTensor

variable {d D : ℕ}

/-- Apply an on-site physical matrix together with time reversal and reflection.
The associated ordered contraction reverses sites when the reflection parity
is odd, by `TNLean.Algebra.symmetryLetter_list_prod`. -/
noncomputable def mixedTensorAction (A : MPSTensor d D)
    (U : Matrix (Fin d) (Fin d) ℂ) (t r : SymmetryParity) : MPSTensor d D :=
  fun i => ∑ j, U i j • symmetryLetter t r (A j)

/-- Physical coefficients compose with the time-reversal conjugation, while
both parities compose on the tensor letters. -/
theorem mixedTensorAction_comp (A : MPSTensor d D)
    (U V : Matrix (Fin d) (Fin d) ℂ) (t r u s : SymmetryParity) :
    mixedTensorAction (mixedTensorAction A V u s) U t r =
      mixedTensorAction A (U * parityConjMatrix t V) (t * u) (r * s) := by
  funext i
  simp only [mixedTensorAction, symmetryLetter_sum, symmetryLetter_smul,
    symmetryLetter_comp, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    parityConjMatrix_apply, Finset.sum_smul]
  exact Finset.sum_comm

/-- Transporting a virtual gauge through a mixed action conjugates it according
to the combined time-reversal/reflection parity. -/
theorem mixedTensorAction_conjugation (A : MPSTensor d D)
    (U : Matrix (Fin d) (Fin d) ℂ) (t r : SymmetryParity)
    (X : Matrix (Fin D) (Fin D) ℂ) (z : ℂ) (i : Fin d) :
    mixedTensorAction (fun j => z • (Xᴴ * A j * X)) U t r i =
      parityConj t z • ((parityConjMatrix (t * r) X)ᴴ *
        mixedTensorAction A U t r i * parityConjMatrix (t * r) X) := by
  simp only [mixedTensorAction, symmetryLetter_smul, symmetryLetter_conjugation,
    Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

/-- Trace sees the time-reversal conjugation but is invariant under transpose. -/
theorem trace_symmetryLetter (t r : SymmetryParity)
    (M : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.trace (symmetryLetter t r M) = parityConj t (Matrix.trace M) := by
  simp only [symmetryLetter]
  split <;> simp [Matrix.trace, Matrix.diag, parityConjMatrix_apply, map_sum]

/-- Conjugating tensor letters conjugates the MPV, and transposing tensor letters
reverses the physical site order. This is the actual finite-chain contraction. -/
theorem mpv_symmetryLetter (A : MPSTensor d D) (t r : SymmetryParity)
    {N : ℕ} (σ : Fin N → Fin d) :
    mpv (fun i => symmetryLetter t r (A i)) σ =
      parityConj t (mpv A (if r = 1 then σ else σ ∘ Fin.rev)) := by
  let L := List.ofFn fun n => A (σ n)
  have hprod : (L.map (symmetryLetter t r)).prod =
      symmetryLetter t r (if r = 1 then L.prod else L.reverse.prod) := by
    by_cases hr : r = 1
    · simpa [hr] using (symmetryLetter_list_prod t r L).symm
    · simpa [hr] using (symmetryLetter_list_prod t r L.reverse).symm
  simp only [mpv, coeff, evalWord_ofFn_eq_prod]
  rw [show (List.ofFn fun n => symmetryLetter t r (A (σ n))).prod =
    (L.map (symmetryLetter t r)).prod by simp [L, List.map_ofFn, Function.comp_def]]
  rw [hprod, trace_symmetryLetter]
  congr 1
  split_ifs <;> simp [L, List.ofFn_reverse, Function.comp_def]

/-- The mixed tensor action is the physical on-site matrix action, together with
complex conjugation for time reversal and reversal of sites for reflection. -/
theorem mpv_mixedTensorAction (A : MPSTensor d D)
    (U : Matrix (Fin d) (Fin d) ℂ) (t r : SymmetryParity)
    {N : ℕ} (σ : Fin N → Fin d) :
    mpv (mixedTensorAction A U t r) σ =
      ∑ τ : Fin N → Fin d, (∏ n, U (σ n) (τ n)) *
        parityConj t (mpv A (if r = 1 then τ else τ ∘ Fin.rev)) := by
  rw [mpv, coeff, evalWord_ofFn_eq_prod]
  simp only [mixedTensorAction, List.prod_ofFn_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro τ _
  rw [List.prod_ofFn_smul, Matrix.trace_smul]
  simpa only [mpv, coeff, evalWord_ofFn_eq_prod, smul_eq_mul] using
    congrArg (fun z : ℂ => (∏ n, U (σ n) (τ n)) * z)
      (mpv_symmetryLetter A t r τ)

/-- Mixed symmetry of the actual letters, with prescribed phase and virtual
unitary gauge. -/
def IsMixedSymmetric {G : Type*} (A : MPSTensor d D)
    (t r : G → SymmetryParity) (U : G → Matrix (Fin d) (Fin d) ℂ)
    (φ : G → ℂ) (X : G → Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ∀ g i, mixedTensorAction A (U g) (t g) (r g) i = φ g • ((X g)ᴴ * A i * X g)

end MPSTensor
