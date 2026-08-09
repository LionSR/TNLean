/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.TracePowerCharPoly
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Eigenspace.Zero

/-!
# Trace Powers Above One Determine the Characteristic Polynomial

For a square complex matrix `A`, suppose `tr(A^k) = 1` for every `k > 1`.
Then its characteristic polynomial is `X ^ (n - 1) * (X - 1)`. In particular,
the nonzero part of the spectrum is exactly `{1}`, and the root `1` has
algebraic multiplicity one. This is the precise power-sum consequence used in
arXiv:1703.09188, Proposition `prop:normal-tensor`, lines 349--354.

The proof applies the all-positive-moment characteristic-polynomial theorem
to `A ^ 2` and `A ^ 3`. Spectral mapping then gives, for each nonzero spectral
value `μ`, both `μ ^ 2 = 1` and `μ ^ 3 = 1`, hence `μ = 1`. Applying spectral
mapping in the reverse direction to the spectral value `1` of `A ^ 2` proves
that `1` itself occurs in the spectrum of `A`. Finally, the generalized
`1`-eigenspace of `A` embeds into that of `A ^ 2`; the latter has dimension one,
so `1` has multiplicity one for `A`. Factoring the split characteristic
polynomial gives the exact formula.

No positivity, normality, diagonalizability, or first-moment hypothesis is
used.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1703.09188,
  Proposition `prop:normal-tensor`, lines 349--354
* [Cirac--Perez-Garcia--Schuch--Verstraete 2016] arXiv:1606.00608,
  Lemma A.5, lines 1155--1163
-/

open scoped Matrix
open Polynomial

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A moment hypothesis for exponents above one becomes an all-positive-moment
hypothesis after replacing `A` by `A ^ m`, provided `m > 1`. -/
theorem forall_trace_pow_pow_eq_one_of_forall_trace_pow_eq_one_of_one_lt
    (A : Matrix n n ℂ)
    (h : ∀ k : ℕ, 1 < k → trace (A ^ k) = 1)
    (m : ℕ) (hm : 1 < m) :
    ∀ k : ℕ, 0 < k → trace ((A ^ m) ^ k) = 1 := by
  intro k hk
  rw [← pow_mul]
  exact h (m * k) (hm.trans_le (Nat.le_mul_of_pos_right m hk))

/-- If all traces `tr(A^k)` with `k > 1` equal one, every nonzero spectral
value of `A` equals one.

This is the set-spectrum part of arXiv:1703.09188, Proposition
`prop:normal-tensor`, lines 349--354.

**Scope restriction (set spectrum only):** This theorem proves only that every
nonzero spectral value equals one; set equality alone does not record algebraic
multiplicity. See `docs/paper-gaps/cpsv17_transfer_trace_power.tex`. The exact
multiplicity and characteristic-polynomial conclusion is
`Matrix.charpoly_eq_X_pow_pred_mul_X_sub_one_of_forall_trace_pow_eq_one_of_one_lt`. -/
theorem eq_one_of_mem_spectrum_of_forall_trace_pow_eq_one_of_one_lt
    (A : Matrix n n ℂ)
    (h : ∀ k : ℕ, 1 < k → trace (A ^ k) = 1)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) (hμ0 : μ ≠ 0) :
    μ = 1 := by
  have hpow2 :=
    forall_trace_pow_pow_eq_one_of_forall_trace_pow_eq_one_of_one_lt A h 2 (by omega)
  have hpow3 :=
    forall_trace_pow_pow_eq_one_of_forall_trace_pow_eq_one_of_one_lt A h 3 (by omega)
  have hchar2 :=
    charpoly_eq_X_pow_pred_mul_X_sub_one_of_forall_trace_pow_eq_one (A ^ 2) hpow2
  have hchar3 :=
    charpoly_eq_X_pow_pred_mul_X_sub_one_of_forall_trace_pow_eq_one (A ^ 3) hpow3
  have hμ2root : IsRoot (A ^ 2).charpoly (μ ^ 2) :=
    mem_spectrum_iff_isRoot_charpoly.mp (spectrum.pow_mem_pow A 2 hμ)
  have hμ3root : IsRoot (A ^ 3).charpoly (μ ^ 3) :=
    mem_spectrum_iff_isRoot_charpoly.mp (spectrum.pow_mem_pow A 3 hμ)
  have hμ2sub : μ ^ 2 - 1 = 0 := by
    rw [hchar2] at hμ2root
    simpa [IsRoot, hμ0] using hμ2root
  have hμ2 : μ ^ 2 = 1 := sub_eq_zero.mp hμ2sub
  have hμ3sub : μ ^ 3 - 1 = 0 := by
    rw [hchar3] at hμ3root
    simpa [IsRoot, hμ0] using hμ3root
  have hμ3 : μ ^ 3 = 1 := sub_eq_zero.mp hμ3sub
  calc
    μ = μ ^ 3 / μ ^ 2 := by field_simp
    _ = 1 := by rw [hμ2, hμ3]; simp

/-- If all traces `tr(A^k)` with `k > 1` equal one, then one belongs to the
spectrum of `A`.

This is the existence part of the spectral conclusion in arXiv:1703.09188,
Proposition `prop:normal-tensor`, lines 349--354.

**Scope restriction (set spectrum only):** This theorem proves only that `1` is
a spectral value; it does not record algebraic multiplicity. See
`docs/paper-gaps/cpsv17_transfer_trace_power.tex`. The exact conclusion is
`Matrix.charpoly_eq_X_pow_pred_mul_X_sub_one_of_forall_trace_pow_eq_one_of_one_lt`. -/
theorem one_mem_spectrum_of_forall_trace_pow_eq_one_of_one_lt
    (A : Matrix n n ℂ)
    (h : ∀ k : ℕ, 1 < k → trace (A ^ k) = 1) :
    (1 : ℂ) ∈ spectrum ℂ A := by
  have hpow2 :=
    forall_trace_pow_pow_eq_one_of_forall_trace_pow_eq_one_of_one_lt A h 2 (by omega)
  have hchar2 :=
    charpoly_eq_X_pow_pred_mul_X_sub_one_of_forall_trace_pow_eq_one (A ^ 2) hpow2
  have hone_sq : (1 : ℂ) ∈ spectrum ℂ (A ^ 2) := by
    apply mem_spectrum_of_isRoot_charpoly
    rw [hchar2]
    simp [IsRoot]
  rw [spectrum.map_pow_of_pos (𝕜 := ℂ) (a := A) (n := 2) (by omega)] at hone_sq
  rcases hone_sq with ⟨μ, hμ, hμ2⟩
  have hμ0 : μ ≠ 0 := by
    intro hμ0
    simp [hμ0] at hμ2
  have hμ1 := eq_one_of_mem_spectrum_of_forall_trace_pow_eq_one_of_one_lt A h hμ hμ0
  simpa [hμ1] using hμ

/-- If all traces `tr(A^k)` with `k > 1` equal one, the nonzero part of the
spectrum of `A` is the singleton `{1}`.

This is the set-spectrum consequence used in arXiv:1703.09188,
Proposition `prop:normal-tensor`, lines 349--354.

**Scope restriction (set spectrum only):** This theorem proves only equality of
the nonzero spectrum as a set; set equality alone does not assert algebraic
multiplicity. See `docs/paper-gaps/cpsv17_transfer_trace_power.tex`. The exact
multiplicity and characteristic-polynomial conclusion is
`Matrix.charpoly_eq_X_pow_pred_mul_X_sub_one_of_forall_trace_pow_eq_one_of_one_lt`. -/
theorem spectrum_diff_zero_eq_singleton_of_forall_trace_pow_eq_one_of_one_lt
    (A : Matrix n n ℂ)
    (h : ∀ k : ℕ, 1 < k → trace (A ^ k) = 1) :
    spectrum ℂ A \ {0} = {1} := by
  ext μ
  constructor
  · rintro ⟨hμ, hμ0⟩
    have hμ_ne : μ ≠ 0 := by simpa only [Set.mem_singleton_iff] using hμ0
    simp [eq_one_of_mem_spectrum_of_forall_trace_pow_eq_one_of_one_lt A h hμ hμ_ne]
  · intro hμ
    have hμ1 : μ = 1 := by simpa using hμ
    subst μ
    exact ⟨one_mem_spectrum_of_forall_trace_pow_eq_one_of_one_lt A h, by simp⟩

/-- The maximal generalized eigenspace of a matrix at `1` is contained in the maximal
generalized eigenspace of its square at `1`.

Indeed, `A ^ 2 - 1 = (A + 1) * (A - 1)`, and the two factors commute. -/
theorem maxGenEigenspace_one_le_sq (A : Matrix n n ℂ) :
    Module.End.maxGenEigenspace A.toLin' 1 ≤
      Module.End.maxGenEigenspace (A ^ 2).toLin' 1 := by
  intro x hx
  rw [Module.End.mem_maxGenEigenspace] at hx ⊢
  obtain ⟨k, hk⟩ := hx
  refine ⟨k, ?_⟩
  let f : Module.End ℂ (n → ℂ) := A.toLin'
  have hbase : (A ^ 2).toLin' - (1 : ℂ) • (1 : Module.End ℂ (n → ℂ)) =
      (f + 1) * (f - 1) := by
    calc
      (A ^ 2).toLin' - (1 : ℂ) • (1 : Module.End ℂ (n → ℂ)) =
          f * f - 1 * 1 := by simp [f, pow_two, Module.End.mul_eq_comp]
      _ = (f + 1) * (f - 1) :=
        (Commute.one_right f).mul_self_sub_mul_self_eq
  have hcomm : Commute (f + 1) (f - 1) :=
    ((Commute.refl f).sub_right (Commute.one_right f)).add_left
      ((Commute.one_left f).sub_right (Commute.refl 1))
  have hid : ((A ^ 2).toLin' - (1 : ℂ) • (1 : Module.End ℂ (n → ℂ))) ^ k =
      (A.toLin' + (1 : Module.End ℂ (n → ℂ))) ^ k *
        (A.toLin' - (1 : Module.End ℂ (n → ℂ))) ^ k := by
    rw [hbase, hcomm.mul_pow]
  rw [hid, Module.End.mul_apply]
  have hk' : ((A.toLin' - (1 : Module.End ℂ (n → ℂ))) ^ k) x = 0 := by
    simpa only [one_smul] using hk
  rw [hk', map_zero]

/-- Squaring a complex matrix cannot decrease the algebraic multiplicity of the
root `1` of its characteristic polynomial. -/
theorem rootMultiplicity_one_charpoly_le_sq (A : Matrix n n ℂ) :
    A.charpoly.rootMultiplicity 1 ≤ (A ^ 2).charpoly.rootMultiplicity 1 := by
  rw [← Matrix.charpoly_toLin', ← Matrix.charpoly_toLin',
    ← LinearMap.finrank_maxGenEigenspace_eq, ← LinearMap.finrank_maxGenEigenspace_eq]
  exact Submodule.finrank_mono (maxGenEigenspace_one_le_sq A)

/-- If `tr(A ^ k) = 1` for every `k > 1`, then the root `1` of the
characteristic polynomial of `A` has algebraic multiplicity one.

No first-moment, positivity, normality, or diagonalizability hypothesis is used.
Source: arXiv:1703.09188, Proposition `prop:normal-tensor`, lines 349--354. -/
theorem charpoly_rootMultiplicity_one_eq_one_of_forall_trace_pow_eq_one_of_one_lt
    (A : Matrix n n ℂ)
    (h : ∀ k : ℕ, 1 < k → trace (A ^ k) = 1) :
    A.charpoly.rootMultiplicity 1 = 1 := by
  have hpow2 :=
    forall_trace_pow_pow_eq_one_of_forall_trace_pow_eq_one_of_one_lt A h 2 (by omega)
  have hchar2 :=
    charpoly_eq_X_pow_pred_mul_X_sub_one_of_forall_trace_pow_eq_one (A ^ 2) hpow2
  have hle : A.charpoly.rootMultiplicity 1 ≤ 1 := by
    refine (rootMultiplicity_one_charpoly_le_sq A).trans_eq ?_
    rw [hchar2, Polynomial.rootMultiplicity_mul]
    · rw [Polynomial.rootMultiplicity_eq_zero]
      · simpa using
          (Polynomial.rootMultiplicity_X_sub_C_self (R := ℂ) (x := (1 : ℂ)))
      · simp [Polynomial.IsRoot]
    · exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
        (Polynomial.X_sub_C_ne_zero 1)
  have hpos : 0 < A.charpoly.rootMultiplicity 1 := by
    rw [Polynomial.rootMultiplicity_pos (A.charpoly_monic.ne_zero)]
    exact mem_spectrum_iff_isRoot_charpoly.mp
      (one_mem_spectrum_of_forall_trace_pow_eq_one_of_one_lt A h)
  omega

/-- If `tr(A ^ k) = 1` for every `k > 1`, then
`charpoly A = X ^ (n - 1) * (X - 1)`.

Thus `1` is the sole nonzero eigenvalue and has algebraic multiplicity one;
all remaining roots are zero. No first-moment, positivity, normality, or
diagonalizability hypothesis is used.

Source: arXiv:1703.09188, Proposition `prop:normal-tensor`, lines 349--354. -/
theorem charpoly_eq_X_pow_pred_mul_X_sub_one_of_forall_trace_pow_eq_one_of_one_lt
    (A : Matrix n n ℂ)
    (h : ∀ k : ℕ, 1 < k → trace (A ^ k) = 1) :
    A.charpoly = X ^ (Fintype.card n - 1) * (X - 1) := by
  classical
  let r := A.charpoly.roots
  have hr_card : r.card = Fintype.card n := by
    rw [← Matrix.charpoly_natDegree_eq_dim A]
    exact (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots.symm
  have hone_mult : A.charpoly.rootMultiplicity 1 = 1 :=
    charpoly_rootMultiplicity_one_eq_one_of_forall_trace_pow_eq_one_of_one_lt A h
  have hone_count : r.count 1 = 1 := by
    simpa [r, Polynomial.count_roots] using hone_mult
  have hone_mem : (1 : ℂ) ∈ r := Multiset.count_pos.mp (by omega)
  have herase_card : (r.erase 1).card = Fintype.card n - 1 := by
    rw [Multiset.card_erase_of_mem hone_mem, hr_card]
    simp [Nat.pred_eq_sub_one]
  have herase_all_zero : ∀ z ∈ r.erase 1, z = 0 := by
    intro z hz
    by_contra hz0
    have hzmem : z ∈ r := Multiset.mem_of_mem_erase hz
    have hzroot : IsRoot A.charpoly z :=
      (Polynomial.mem_roots (A.charpoly_monic.ne_zero)).mp (by simpa [r] using hzmem)
    have hzspec : z ∈ spectrum ℂ A := mem_spectrum_iff_isRoot_charpoly.mpr hzroot
    have hz1 : z = 1 :=
      eq_one_of_mem_spectrum_of_forall_trace_pow_eq_one_of_one_lt A h hzspec hz0
    subst z
    have hcount_pos : 0 < (r.erase 1).count 1 := Multiset.count_pos.mpr hz
    rw [Multiset.count_erase_self, hone_count] at hcount_pos
    omega
  have herase : r.erase 1 = Multiset.replicate (Fintype.card n - 1) 0 :=
    Multiset.eq_replicate.mpr ⟨herase_card, herase_all_zero⟩
  have hroots : r = 1 ::ₘ Multiset.replicate (Fintype.card n - 1) 0 := by
    rw [← herase, Multiset.cons_erase hone_mem]
  rw [(IsAlgClosed.splits A.charpoly).eq_prod_roots_of_monic A.charpoly_monic]
  rw [show A.charpoly.roots = r from rfl, hroots]
  simp [Multiset.map_replicate, Multiset.prod_replicate]
  ring

end Matrix
