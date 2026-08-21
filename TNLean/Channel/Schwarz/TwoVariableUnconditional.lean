/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Schwarz.TwoVariable
import TNLean.Channel.Schwarz.SchurComplement

/-!
# The unconditional two-variable operator Schwarz inequality

This file proves Wolf's Theorem 5.3 (Eq. (5.4)) for independent finite input
and output matrix algebras:
for a 2-positive map `E` and all `A, B`,
`E(A†B) · pinv(E(B†B)) · E(B†A) ≤ E(A†A)`, with the inverse taken on the
range via the Moore–Penrose pseudoinverse `Douglas.pinv`.

This upgrades the conditional (witness-dependent) form
`SchwarzTwoVariable.schwarz_two_variable` of `TwoVariable.lean` by
constructing the witness `w = pinv(E(B†B)) · E(B†A) · v` explicitly for
every `v`, using the kernel-inclusion clause of the Schur complement
(`ker_inclusion_of_fromBlocks_posSemidef`) and the support-projection
absorption lemma
`Matrix.IsHermitian.mul_supportProj_eq_self_of_mulVec_kernel_le`, rather
than the `EuclideanSpace`/`PiLp` range-ker duality route that caused
`whnf` timeouts (documented in
`docs/paper-gaps/wolf_ch5_two_variable_unconditional.tex`).

## Main results

* `ker_EBB_le_ker_EAB`: `ker(E(B†B)) ⊆ ker(E(A†B))`, the kernel-inclusion
  clause of the ampliated block matrix.
* `EBB_mul_pinv_mul_EBA_eq`: the pseudoinverse witness identity
  `E(B†B) · (pinv(E(B†B)) · E(B†A)) = E(B†A)`, i.e. the range inclusion
  `ran E(B†A) ⊆ ran E(B†B)` in pseudoinverse form.
* `schwarz_two_variable_unconditional`: the unconditional inequality
  `E(A†B) · pinv(E(B†B)) · E(B†A) ≤ E(A†A)`, Wolf's Eq. (5.4), with no
  witness vector assumed to exist.
* `schwarz_two_variable_unconditional_of_traceAdjointMap`: Wolf's theorem in
  its stated trace-adjoint form, with `E = T*` and the reverse map `T`
  two-positive.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 5,
  Theorem 5.3][Wolf2012QChannels]
* Local source: `Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`,
  lines 180--190.
* `docs/paper-gaps/wolf_ch5_two_variable_unconditional.tex`.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

namespace SchwarzTwoVariable

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

local notation "MatIn" => Matrix m m ℂ
local notation "MatOut" => Matrix n n ℂ

omit [DecidableEq m] [Fintype n] [DecidableEq n] in
/-- The conjugate-transpose identity `E(B†A) = E(A†B)†`, for a 2-positive
(hence positive) map `E`. -/
theorem map_EBA_eq_conjTranspose_EAB
    [Finite n] (E : MatIn →ₗ[ℂ] MatOut) (h2pos : Is2PositiveMap E) (A B : MatIn) :
    E (Bᴴ * A) = (E (Aᴴ * B))ᴴ := by
  have hPos : IsPositiveMap E := h2pos.isPositiveMap
  rw [← hPos.map_conjTranspose (Aᴴ * B)]
  congr 1
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

omit [DecidableEq m] [DecidableEq n] in
/-- The kernel of `E(B†B)` is contained in the kernel of `E(A†B)`: this is
the Schur-complement kernel-absorption clause of Theorem 5.2 applied to the
ampliated `2×2` block matrix `[[E(A†A), E(A†B)], [E(B†A), E(B†B)]]`. -/
theorem ker_EBB_le_ker_EAB
    (E : MatIn →ₗ[ℂ] MatOut) (h2pos : Is2PositiveMap E) (A B : MatIn)
    (y : n → ℂ) (hy : (E (Bᴴ * B)).mulVec y = 0) : (E (Aᴴ * B)).mulVec y = 0 := by
  have h_psd := ampliated_block_matrix_posSemidef E h2pos A B
  rw [map_EBA_eq_conjTranspose_EAB E h2pos A B] at h_psd
  exact ker_inclusion_of_fromBlocks_posSemidef h_psd y hy

omit [DecidableEq m] in
/-- The pseudoinverse `Douglas.pinv (E(B†B))` is a genuine right-inverse
witness for `E(B†A)` on the support of `E(B†B)`:
`E(B†B) · (pinv(E(B†B)) · E(B†A)) = E(B†A)`.

This is the range-inclusion step `ran E(B†A) ⊆ ran E(B†B)` of the
unconditional Schwarz inequality, obtained from `ker_EBB_le_ker_EAB` via the
support-projection absorption lemma
`Matrix.IsHermitian.mul_supportProj_eq_self_of_mulVec_kernel_le` and the
pseudoinverse identity `Douglas.pinv (E(B†B)) · E(B†B) = supportProj`. -/
theorem EBB_mul_pinv_mul_EBA_eq
    (E : MatIn →ₗ[ℂ] MatOut) (h2pos : Is2PositiveMap E) (A B : MatIn) :
    (E (Bᴴ * B)) * (Douglas.pinv (E (Bᴴ * B)) * E (Bᴴ * A)) = E (Bᴴ * A) := by
  have hPos : IsPositiveMap E := h2pos.isPositiveMap
  have hR : (E (Bᴴ * B)).PosSemidef := hPos _ (Matrix.posSemidef_conjTranspose_mul_self B)
  have hker : ∀ y : n → ℂ,
      (E (Bᴴ * B)).mulVec y = 0 → (E (Aᴴ * B)).mulVec y = 0 :=
    ker_EBB_le_ker_EAB E h2pos A B
  have habsorb : (E (Aᴴ * B)) * hR.isHermitian.supportProj = E (Aᴴ * B) :=
    hR.isHermitian.mul_supportProj_eq_self_of_mulVec_kernel_le hker
  have habsorb' : hR.isHermitian.supportProj * (E (Aᴴ * B))ᴴ = (E (Aᴴ * B))ᴴ := by
    have h := congrArg Matrix.conjTranspose habsorb
    rwa [Matrix.conjTranspose_mul, hR.isHermitian.supportProj_isHermitian.eq] at h
  have hpinv_eq : (E (Bᴴ * B)) * Douglas.pinv (E (Bᴴ * B)) = hR.isHermitian.supportProj :=
    SchurComplement.R_mul_pinv_eq_supportProj (E (Bᴴ * B)) hR
  rw [map_EBA_eq_conjTranspose_EAB E h2pos A B]
  calc
    (E (Bᴴ * B)) * (Douglas.pinv (E (Bᴴ * B)) * (E (Aᴴ * B))ᴴ)
        = ((E (Bᴴ * B)) * Douglas.pinv (E (Bᴴ * B))) * (E (Aᴴ * B))ᴴ := by
          rw [Matrix.mul_assoc]
      _ = hR.isHermitian.supportProj * (E (Aᴴ * B))ᴴ := by rw [hpinv_eq]
      _ = (E (Aᴴ * B))ᴴ := habsorb'

omit [DecidableEq m] in
/-- **The unconditional two-variable operator Schwarz inequality**
(Wolf, Theorem 5.3, Eq. (5.4)). For a 2-positive map `E` and all `A, B`:

`E(A†B) · pinv(E(B†B)) · E(B†A) ≤ E(A†A)`,

with the inverse taken on the range via the Moore–Penrose pseudoinverse
`Douglas.pinv`. Unlike `SchwarzTwoVariable.schwarz_two_variable`, no
witness vector `w` is assumed to exist: the pseudoinverse witness
`w = pinv(E(B†B)) · E(B†A) · v` is constructed explicitly for every `v`.

Wolf, *Quantum Channels & Operations*, Theorem 5.3 and Eq. (5.4), allows
independent input and output dimensions; the declaration below has the same
generality. -/
theorem schwarz_two_variable_unconditional
    (E : MatIn →ₗ[ℂ] MatOut) (h2pos : Is2PositiveMap E) (A B : MatIn) :
    E (Aᴴ * B) * Douglas.pinv (E (Bᴴ * B)) * E (Bᴴ * A) ≤ E (Aᴴ * A) := by
  rw [Matrix.le_iff]
  refine Matrix.posSemidef_of_forall_star_dotProduct_mulVec_nonneg (fun v => ?_)
  set w : n → ℂ := (Douglas.pinv (E (Bᴴ * B)) * E (Bᴴ * A)).mulVec v with hw_def
  have hw : (E (Bᴴ * B)).mulVec w = (E (Bᴴ * A)).mulVec v := by
    rw [hw_def, Matrix.mulVec_mulVec, EBB_mul_pinv_mul_EBA_eq E h2pos A B]
  have hineq := schwarz_two_variable E h2pos A B v w hw
  have heq : (E (Aᴴ * B)).mulVec w =
      (E (Aᴴ * B) * Douglas.pinv (E (Bᴴ * B)) * E (Bᴴ * A)).mulVec v := by
    rw [hw_def, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [heq] at hineq
  rw [Matrix.sub_mulVec, dotProduct_sub]
  exact sub_nonneg.mpr hineq

omit [DecidableEq m] in
/-- **Wolf's trace-adjoint form of the two-variable Schwarz inequality**
(Wolf, Theorem 5.3, Eq. (5.4)). Let
`E : M_m(ℂ) → M_n(ℂ)` be the positive trace adjoint of
`T : M_n(ℂ) → M_m(ℂ)`. If `T` is two-positive, then for all `A, B ∈ M_m(ℂ)`,

`E(A†B) · pinv(E(B†B)) · E(B†A) ≤ E(A†A)`.

This declaration records Wolf's stated hypotheses explicitly. Rectangular
two-positivity is invariant under the trace adjoint, so the result follows
from `schwarz_two_variable_unconditional` applied to `E`.

Wolf, *Quantum Channels & Operations*, Theorem 5.3 and Eq. (5.4),
`Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`, lines 180--190. -/
theorem schwarz_two_variable_unconditional_of_traceAdjointMap
    (E : MatIn →ₗ[ℂ] MatOut) (T : MatOut →ₗ[ℂ] MatIn)
    (hE : E = Matrix.traceAdjointMap T) (_hEpos : IsPositiveMap E)
    (hT2pos : Is2PositiveMap T) (A B : MatIn) :
    E (Aᴴ * B) * Douglas.pinv (E (Bᴴ * B)) * E (Bᴴ * A) ≤ E (Aᴴ * A) := by
  have hE2pos : Is2PositiveMap E := by
    change IsNPositiveMap 2 E
    rw [hE]
    change IsNPositiveMap 2 T at hT2pos
    exact hT2pos.traceAdjointMap
  exact schwarz_two_variable_unconditional E hE2pos A B

end SchwarzTwoVariable
