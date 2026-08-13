/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.DeterminantTraceBound
import TNLean.Channel.ChoiJamiolkowski
import TNLean.Channel.Determinant.Basic

/-!
# Determinant of a linear map and the purity of its Choi operator

Let `T : M_d(ℂ) → M_d(ℂ)` be a linear map and `τ = (T ⊗ id)(|Ω⟩⟨Ω|)` its
Choi–Jamiolkowski operator. Wolf's bound is

  `|det T| ≤ tr[τ† τ] ^ (d² / 2)`.

No positivity, trace preservation or unitality is assumed: the estimate holds
for every linear map on `M_d(ℂ)`.

The proof follows Wolf. Write `A` for the matrix representing `T` in the
matrix-unit basis (Wolf's `\widehat{T}`). The Choi operator and `A` are related
by the reshuffling `A = d τ^Γ`, `⟨m,n| τ^Γ |k,ℓ⟩ = ⟨m,k| τ |n,ℓ⟩`, so that the
two operators carry the same multiset of squared entry moduli up to the factor
`d²`:

  `tr[τ† τ] = (1/d²) tr[A† A] = (1/d²) ∑ᵢ sᵢ²`,

with `sᵢ` the singular values of `A`. Since `|det T| = ∏ᵢ sᵢ`, the
arithmetic–geometric mean inequality applied to the `d²` numbers `sᵢ²` gives the
bound, the factors `(d²)^{d²}` on the two sides cancelling exactly.

## Main definitions

* `choiPurity T` — the purity `tr[τ† τ]` of the Choi–Jamiolkowski operator of
  `T`.

## Main statements

* `channelMatrix_apply_eq_choiMatrix` — the reshuffling `A = d τ^Γ`
  (Wolf Eq. (2.22)).
* `trace_conjTranspose_mul_self_channelMatrix` — `tr[A† A] = d² tr[τ† τ]`
  (Wolf Eq. (6.28)).
* `norm_channelDet_sq_le_choiPurity_pow` — `|det T|² ≤ tr[τ† τ]^{d²}`.
* `norm_channelDet_le_choiPurity_rpow` — `|det T| ≤ tr[τ† τ]^{d²/2}`
  (Wolf Eq. (6.27)).

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 6][Wolf2012QChannels],
  `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 520–545.

## Tags

quantum channel, determinant, Choi-Jamiolkowski operator, purity
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix

variable {d : ℕ}

namespace ChannelDeterminant
namespace Internal

/-- The matrix-unit basis of `M_d(ℂ)`: `matrixSpaceBasis d (i, j, ()) = E_{ij}`. -/
theorem matrixSpaceBasis_apply_single (i j : Fin d) :
    matrixSpaceBasis d (i, j, ()) = Matrix.single i j (1 : ℂ) := by
  simp [matrixSpaceBasis, Module.Basis.matrix_apply, Module.Basis.singleton_apply]

/-- The coordinates of `M` in the matrix-unit basis are the entries of `M`. -/
theorem matrixSpaceBasis_repr_apply (M : MatrixAlg d) (i j : Fin d) :
    (matrixSpaceBasis d).repr M (i, j, ()) = M i j := by
  classical
  have hsum : M = ∑ x : Fin d, ∑ y : Fin d, M x y • matrixSpaceBasis d (x, y, ()) := by
    ext a b
    simp only [Matrix.sum_apply, Matrix.smul_apply, matrixSpaceBasis_apply_single,
      Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single a, Finset.sum_eq_single b] <;> simp +contextual
  conv_lhs => rw [hsum]
  simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply, Prod.mk.injEq, smul_eq_mul,
    mul_ite, mul_one, mul_zero, ite_and]
  simp [Finset.sum_ite_eq']

end Internal
end ChannelDeterminant

open ChannelDeterminant.Internal

section Reshuffling

/-- The entries of the matrix `A` representing `T` in the matrix-unit basis:
`A_{(i₁,i₂),(j₁,j₂)} = T(E_{j₁ j₂})_{i₁ i₂}`. -/
theorem channelMatrix_apply (T : MatrixEnd d) (i₁ i₂ j₁ j₂ : Fin d) (u v : Unit) :
    channelMatrix T (i₁, i₂, u) (j₁, j₂, v) = T (Matrix.single j₁ j₂ (1 : ℂ)) i₁ i₂ := by
  cases u
  cases v
  rw [channelMatrix, LinearMap.toMatrix_apply, matrixSpaceBasis_apply_single,
    matrixSpaceBasis_repr_apply]

/-- The entries of the Choi–Jamiolkowski operator on matrix units:
`τ_{(i₁,i₂),(j₁,j₂)} = (1/d) T(E_{i₂ j₂})_{i₁ j₁}`. -/
theorem choiMatrix_apply_single (T : MatrixEnd d) (i₁ i₂ j₁ j₂ : Fin d) :
    ChoiJamiolkowski.choiMatrix T (i₁, i₂) (j₁, j₂) =
      (1 / (d : ℂ)) * T (Matrix.single i₂ j₂ (1 : ℂ)) i₁ j₁ := by
  have hd : 0 < d := Fin.pos i₁
  have hsingle : Matrix.single i₂ j₂ ((1 : ℂ) / (d : ℂ)) =
      ((1 : ℂ) / (d : ℂ)) • Matrix.single i₂ j₂ (1 : ℂ) := by
    ext a b
    simp [Matrix.single_apply]
  rw [ChoiJamiolkowski.choiMatrix_apply, ChoiJamiolkowski.omegaSlice_eq_single,
    ChoiJamiolkowski.omegaCoeff_eq_inv hd, hsingle, map_smul]
  simp

/-- **Wolf Eq. (2.22).** The matrix representation of `T` in the matrix-unit
basis is `d` times the reshuffling of the Choi–Jamiolkowski operator:
`A_{(i₁,i₂),(j₁,j₂)} = d · τ_{(i₁,j₁),(i₂,j₂)}`. -/
theorem channelMatrix_apply_eq_choiMatrix (T : MatrixEnd d) (i₁ i₂ j₁ j₂ : Fin d) (u v : Unit) :
    channelMatrix T (i₁, i₂, u) (j₁, j₂, v) =
      (d : ℂ) * ChoiJamiolkowski.choiMatrix T (i₁, j₁) (i₂, j₂) := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fin.pos i₁).ne'
  rw [channelMatrix_apply, choiMatrix_apply_single, ← mul_assoc,
    mul_one_div, div_self hd, one_mul]

end Reshuffling

section Purity

/-- The **purity** `tr[τ† τ]` of the Choi–Jamiolkowski operator `τ` of a linear
map `T : M_d(ℂ) → M_d(ℂ)`. Wolf §6, line 531. -/
noncomputable def choiPurity (T : MatrixEnd d) : ℝ :=
  ((ChoiJamiolkowski.choiMatrix T)ᴴ * ChoiJamiolkowski.choiMatrix T).trace.re

theorem choiPurity_nonneg (T : MatrixEnd d) : 0 ≤ choiPurity T := by
  rw [choiPurity, Matrix.trace_conjTranspose_mul_self_re]
  positivity

/-- The purity is the sum of the squared moduli of the entries of `τ`. -/
theorem choiPurity_eq_sum (T : MatrixEnd d) :
    choiPurity T =
      ∑ i₁ : Fin d, ∑ j₁ : Fin d, ∑ i₂ : Fin d, ∑ j₂ : Fin d,
        ‖ChoiJamiolkowski.choiMatrix T (i₁, j₁) (i₂, j₂)‖ ^ 2 := by
  rw [choiPurity, Matrix.trace_conjTranspose_mul_self_re]
  simp [Fintype.sum_prod_type]

/-- **Wolf Eq. (6.28).** The matrix representation and the Choi–Jamiolkowski
operator have proportional Hilbert–Schmidt norms: `tr[A† A] = d² tr[τ† τ]`. -/
theorem trace_conjTranspose_mul_self_channelMatrix (T : MatrixEnd d) :
    ((channelMatrix T)ᴴ * channelMatrix T).trace.re = (d : ℝ) ^ 2 * choiPurity T := by
  rw [Matrix.trace_conjTranspose_mul_self_re, choiPurity_eq_sum]
  simp only [Fintype.sum_prod_type, Finset.univ_unique, Finset.sum_singleton,
    channelMatrix_apply_eq_choiMatrix, norm_mul, mul_pow, Complex.norm_natCast,
    ← Finset.mul_sum]
  refine congrArg (fun s : ℝ => (d : ℝ) ^ 2 * s) ?_
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

end Purity

section ChoiBound

/-- **Wolf Eq. (6.27), squared form.** For every linear map
`T : M_d(ℂ) → M_d(ℂ)` with Choi–Jamiolkowski operator `τ`,

  `|det T|² ≤ tr[τ† τ]^{d²}`.

No positivity, trace preservation or unitality is assumed. -/
theorem norm_channelDet_sq_le_choiPurity_pow (T : MatrixEnd d) :
    ‖channelDet T‖ ^ 2 ≤ choiPurity T ^ (d ^ 2) := by
  have hcard : Fintype.card (MatrixBasisIndex d) = d ^ 2 := by
    simp [MatrixBasisIndex, pow_two]
  have hbound :=
    Matrix.pow_card_mul_norm_det_sq_le_trace_conjTranspose_mul_self_pow (channelMatrix T)
  rw [hcard, trace_conjTranspose_mul_self_channelMatrix, mul_pow] at hbound
  have hcast : ((d ^ 2 : ℕ) : ℝ) = (d : ℝ) ^ 2 := by push_cast; ring
  rw [hcast] at hbound
  have hpos : (0 : ℝ) < ((d : ℝ) ^ 2) ^ (d ^ 2) := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · norm_num
    · have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
      positivity
  exact le_of_mul_le_mul_left hbound hpos

/-- **Wolf Eq. (6.27).** For every linear map `T : M_d(ℂ) → M_d(ℂ)` with
Choi–Jamiolkowski operator `τ`,

  `|det T| ≤ tr[τ† τ]^{d²/2}`.

No positivity, trace preservation or unitality is assumed. -/
theorem norm_channelDet_le_choiPurity_rpow (T : MatrixEnd d) :
    ‖channelDet T‖ ≤ choiPurity T ^ ((d : ℝ) ^ 2 / 2) := by
  have hp : 0 ≤ choiPurity T := choiPurity_nonneg T
  have hsq : (choiPurity T ^ ((d : ℝ) ^ 2 / 2)) ^ 2 = choiPurity T ^ (d ^ 2) := by
    rw [← Real.rpow_natCast (choiPurity T ^ ((d : ℝ) ^ 2 / 2)) 2, ← Real.rpow_mul hp,
      show (d : ℝ) ^ 2 / 2 * ((2 : ℕ) : ℝ) = ((d ^ 2 : ℕ) : ℝ) by push_cast; ring]
    exact Real.rpow_natCast _ _
  have hbound := norm_channelDet_sq_le_choiPurity_pow T
  rw [← hsq] at hbound
  exact le_of_pow_le_pow_left₀ two_ne_zero (Real.rpow_nonneg hp _) hbound

end ChoiBound
