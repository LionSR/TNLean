/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Defs
import TNLean.MPS.Core.Transfer

/-!
# Majumdar-Ghosh state as a Matrix Product State

This module defines the Majumdar-Ghosh (MG) state as a concrete MPS tensor with
physical dimension `d = 2` (spin-1/2) and bond dimension `D = 3`, and proves its
key properties.

The Majumdar-Ghosh state is the exact dimer ground state of the spin-1/2 chain
`H = ∑ Sᵢ · Sᵢ₊₁ + ½ ∑ Sᵢ · Sᵢ₊₂`.  On an even periodic chain it is the
superposition of the two nearest-neighbour dimer (singlet) coverings,
`(1,2)(3,4)…` and `(2,3)(4,5)…(N,1)`, and is the one-dimensional analogue of a
resonating valence-bond state.

## Bond dimension and the source notation

The review of arXiv:2011.12127 (lines 2397-2405) writes the tensor in the
valence-bond shorthand
\(A = [|0⟩((02| + (20|) + |1⟩((12| + (21|)] \otimes Y\), with
\[
Y =
\begin{pmatrix}
0 & -1 \\
1 & 0
\end{pmatrix}
\]
encoding the singlet.  Read literally as \((ab|=|a⟩⟨b|\) on a separate
three-level factor tensored with the two-level singlet space, that shorthand
would describe a six-dimensional bond. Its two-site contractions do not have the
singlet-pair support pattern: same-letter traces can be nonzero while
opposite-letter traces vanish. The shorthand is therefore treated here as a
schematic of the valence-bond construction. After the singlet \(Y\) is
contracted, the resulting matrix product operator acts on a three-dimensional
bond, with the antisymmetry of \(Y\) supplying the relative sign
\(-1/\sqrt{2}\) below.

The tensor below is the bond-dimension-three contracted representative used in
this example. The file proves its left-canonical equation, transfer-map value,
non-injectivity, and non-normality. The equality between its matrix product
vectors and the even-ring Majumdar-Ghosh dimer superposition is not yet
formalized; the source-notation gap is recorded in
`docs/paper-gaps/rmp_majumdar_ghosh_tensor_gap.tex`.

The three bond levels are the two spin-1/2 values of an open singlet partner
together with the closed inter-dimer link.

## Main definitions

* `majumdarGhoshTensor` : the Majumdar-Ghosh MPS tensor with
  \(A^0\) having nonzero entries \((A^0)_{01}=1\) and
  \((A^0)_{20}=1/\sqrt{2}\), and \(A^1\) having nonzero entries
  \((A^1)_{02}=1\) and \((A^1)_{10}=-1/\sqrt{2}\)

## Main results

* `majumdarGhosh_left_canonical` : the tensor is in left-canonical (isometric)
  form, `(A⁰)ᴴ A⁰ + (A¹)ᴴ A¹ = 1`
* `majumdarGhosh_transferMap_one` : the transfer map sends the identity to
  `diag(2, 1/2, 1/2)`
* `majumdarGhosh_not_isInjective` : the tensor is not injective
* `majumdarGhosh_not_isNBlkInjective_one` / `_two` : the tensor is not 1- or
  2-block injective
* `majumdarGhosh_not_isNormal` : the tensor is not normal, as no blocking length
  makes it block injective, matching the two-periodic dimer-covering structure
  of the physical example

## References

* RMP review (arXiv:2011.12127) lines 2397-2405
* Verstraete, Cirac — Computational power of PEPS
* Majumdar, Ghosh (1969) — original dimer model
-/

open scoped Matrix BigOperators
open Matrix Finset MPSTensor

noncomputable section

namespace MPSTensor

/-! ### Definition -/

/-- The Majumdar-Ghosh MPS tensor: a spin-1/2 chain with physical dimension
2 and bond dimension 3.

\[
A^0 =
\begin{pmatrix}
0 & 1 & 0 \\
0 & 0 & 0 \\
1/\sqrt{2} & 0 & 0
\end{pmatrix},
\qquad
A^1 =
\begin{pmatrix}
0 & 0 & 1 \\
-1/\sqrt{2} & 0 & 0 \\
0 & 0 & 0
\end{pmatrix}.
\]

The relative sign in \(A^1\) is the antisymmetry of the singlet \(Y\). -/
def majumdarGhoshTensor : MPSTensor 2 3 := fun i =>
  match i with
  | 0 => !![0, 1, 0; 0, 0, 0; (↑(1 / Real.sqrt 2) : ℂ), 0, 0]
  | 1 => !![0, 0, 1; -(↑(1 / Real.sqrt 2) : ℂ), 0, 0; 0, 0, 0]

@[simp]
lemma majumdarGhoshTensor_zero :
    majumdarGhoshTensor 0 = !![0, 1, 0; 0, 0, 0; (↑(1 / Real.sqrt 2) : ℂ), 0, 0] := rfl

@[simp]
lemma majumdarGhoshTensor_one :
    majumdarGhoshTensor 1 = !![0, 0, 1; -(↑(1 / Real.sqrt 2) : ℂ), 0, 0; 0, 0, 0] := rfl

/-! ### Scalar arithmetic -/

private lemma inv_ofReal_sqrt2_mul_self :
    (↑(Real.sqrt 2) : ℂ)⁻¹ * (↑(Real.sqrt 2) : ℂ)⁻¹ = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  norm_num

/-! ### Conjugate transposes -/

@[simp]
lemma majumdarGhoshTensor_zero_conjTranspose :
    (majumdarGhoshTensor 0)ᴴ = !![0, 0, (↑(1 / Real.sqrt 2) : ℂ); 1, 0, 0; 0, 0, 0] := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [majumdarGhoshTensor, Matrix.conjTranspose_apply, Complex.conj_ofReal]

@[simp]
lemma majumdarGhoshTensor_one_conjTranspose :
    (majumdarGhoshTensor 1)ᴴ = !![0, -(↑(1 / Real.sqrt 2) : ℂ), 0; 0, 0, 0; 1, 0, 0] := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [majumdarGhoshTensor, Matrix.conjTranspose_apply, Complex.conj_ofReal]

/-! ### Canonical form and transfer map -/

/-- The Majumdar-Ghosh tensor is in left-canonical (isometric) form:
`(A⁰)ᴴ A⁰ + (A¹)ᴴ A¹ = 1`. -/
theorem majumdarGhosh_left_canonical :
    (majumdarGhoshTensor 0)ᴴ * majumdarGhoshTensor 0 +
      (majumdarGhoshTensor 1)ᴴ * majumdarGhoshTensor 1 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [majumdarGhoshTensor, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_three, Complex.conj_ofReal, inv_ofReal_sqrt2_mul_self]
  all_goals norm_num

/-- The transfer map of the Majumdar-Ghosh tensor sends the identity to
`E(1) = A⁰ (A⁰)ᴴ + A¹ (A¹)ᴴ = diag(2, 1/2, 1/2)`. -/
theorem majumdarGhosh_transferMap_one :
    transferMap majumdarGhoshTensor 1 =
      !![2, 0, 0; 0, 1 / 2, 0; 0, 0, 1 / 2] := by
  ext a b
  simp only [transferMap_apply, Fin.sum_univ_two, Matrix.mul_one, Matrix.add_apply]
  fin_cases a <;> fin_cases b <;>
    simp [majumdarGhoshTensor, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_three, Complex.conj_ofReal, inv_ofReal_sqrt2_mul_self]
  all_goals norm_num

/-! ### Non-injectivity -/

/-- The Majumdar-Ghosh tensor is **not** injective: the span of `{A⁰, A¹}` lies
in the proper subspace of matrices whose `(2,2)` entry vanishes, so it is at most
two-dimensional and cannot be all of `M₃(ℂ)`. -/
theorem majumdarGhosh_not_isInjective : ¬ IsInjective majumdarGhoshTensor := by
  intro h
  have hmem : (1 : Matrix (Fin 3) (Fin 3) ℂ) ∈
      Submodule.span ℂ (Set.range majumdarGhoshTensor) := h ▸ Submodule.mem_top
  suffices hzero : ∀ M ∈ Submodule.span ℂ (Set.range majumdarGhoshTensor), M 2 2 = 0 by
    have h1 := hzero _ hmem
    simp at h1
  intro M hM
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    fin_cases k <;> simp [majumdarGhoshTensor]
  | zero => simp
  | add x y _ _ hx hy => simp [Matrix.add_apply, hx, hy]
  | smul c x _ hx => simp [Matrix.smul_apply, hx]

/-! ### Non-normality

The Majumdar-Ghosh state is a symmetry-broken cat of the two nearest-neighbour
dimer coverings, so its tensor is non-normal: no blocking length makes the
length-`N` products span the full matrix algebra `M₃(ℂ)`.  The obstruction is a
two-periodic grading of the bond.  Write
`oddSet = {(0,1), (0,2), (1,0), (2,0)}` and
`evenSet = {(0,0), (1,1), (1,2), (2,1), (2,2)}` for the two complementary sets of
matrix positions.  Each generator `Aⁱ` is supported on `oddSet`, and the two sets
are exchanged under left multiplication by an `Aⁱ`.  Consequently every
odd-length product is supported on `oddSet` (so its `(2,2)` entry vanishes) and
every even-length product is supported on `evenSet` (so its `(1,0)` entry
vanishes).  Either way the length-`N` span misses a basic matrix unit. -/

-- Each subgoal expands the entry of `Aⁱ * evalWord w` over both physical indices
-- `i` with a single uniform `simp` carrying every vanishing entry of the tail; for
-- any one index only the subset that survives the sparse row of `Aⁱ` is used, so
-- `linter.unusedSimpArgs` is disabled rather than splitting into per-index fact lists.
set_option linter.unusedSimpArgs false in
/-- The `(2,2)` entry of any odd-length Majumdar-Ghosh product and the `(1,0)`
entry of any even-length product both vanish.  Proved by induction on the word,
using that left multiplication by a generator exchanges the two complementary
support sets. -/
private lemma majumdarGhosh_evalWord_grading :
    ∀ w : List (Fin 2),
      ((Odd w.length → (evalWord majumdarGhoshTensor w) 2 2 = 0) ∧
        (Odd w.length → (evalWord majumdarGhoshTensor w) 1 1 = 0) ∧
        (Odd w.length → (evalWord majumdarGhoshTensor w) 1 2 = 0) ∧
        (Odd w.length → (evalWord majumdarGhoshTensor w) 2 1 = 0) ∧
        (Odd w.length → (evalWord majumdarGhoshTensor w) 0 0 = 0)) ∧
      ((Even w.length → (evalWord majumdarGhoshTensor w) 0 1 = 0) ∧
        (Even w.length → (evalWord majumdarGhoshTensor w) 0 2 = 0) ∧
        (Even w.length → (evalWord majumdarGhoshTensor w) 1 0 = 0) ∧
        (Even w.length → (evalWord majumdarGhoshTensor w) 2 0 = 0)) := by
  intro w
  induction w with
  | nil =>
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
      simp only [List.length_nil] <;> intro h <;> simp at h ⊢
  | cons i w ih =>
    obtain ⟨⟨ho22, ho11, ho12, ho21, ho00⟩, he01, he02, he10, he20⟩ := ih
    -- An odd-length `i :: w` has an even-length tail `w`, and conversely.
    have hodd_tail : Odd (i :: w).length → Even w.length := fun h => by
      rw [List.length_cons, Nat.odd_add_one, Nat.not_odd_iff_even] at h; exact h
    have heven_tail : Even (i :: w).length → Odd w.length := fun h => by
      rw [List.length_cons, Nat.even_add_one, Nat.not_even_iff_odd] at h; exact h
    -- Odd-length targets use the even-support vanishing entries of the tail.
    refine ⟨⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩,
      fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have hw := hodd_tail h
      rw [evalWord_cons]; fin_cases i <;>
        simp [majumdarGhoshTensor, Matrix.mul_apply, Fin.sum_univ_three,
          he01 hw, he02 hw, he10 hw, he20 hw]
    · have hw := hodd_tail h
      rw [evalWord_cons]; fin_cases i <;>
        simp [majumdarGhoshTensor, Matrix.mul_apply, Fin.sum_univ_three,
          he01 hw, he02 hw, he10 hw, he20 hw]
    · have hw := hodd_tail h
      rw [evalWord_cons]; fin_cases i <;>
        simp [majumdarGhoshTensor, Matrix.mul_apply, Fin.sum_univ_three,
          he01 hw, he02 hw, he10 hw, he20 hw]
    · have hw := hodd_tail h
      rw [evalWord_cons]; fin_cases i <;>
        simp [majumdarGhoshTensor, Matrix.mul_apply, Fin.sum_univ_three,
          he01 hw, he02 hw, he10 hw, he20 hw]
    · have hw := hodd_tail h
      rw [evalWord_cons]; fin_cases i <;>
        simp [majumdarGhoshTensor, Matrix.mul_apply, Fin.sum_univ_three,
          he01 hw, he02 hw, he10 hw, he20 hw]
    -- Even-length targets use the odd-support vanishing entries of the tail.
    · have hw := heven_tail h
      rw [evalWord_cons]; fin_cases i <;>
        simp [majumdarGhoshTensor, Matrix.mul_apply, Fin.sum_univ_three,
          ho22 hw, ho11 hw, ho12 hw, ho21 hw, ho00 hw]
    · have hw := heven_tail h
      rw [evalWord_cons]; fin_cases i <;>
        simp [majumdarGhoshTensor, Matrix.mul_apply, Fin.sum_univ_three,
          ho22 hw, ho11 hw, ho12 hw, ho21 hw, ho00 hw]
    · have hw := heven_tail h
      rw [evalWord_cons]; fin_cases i <;>
        simp [majumdarGhoshTensor, Matrix.mul_apply, Fin.sum_univ_three,
          ho22 hw, ho11 hw, ho12 hw, ho21 hw, ho00 hw]
    · have hw := heven_tail h
      rw [evalWord_cons]; fin_cases i <;>
        simp [majumdarGhoshTensor, Matrix.mul_apply, Fin.sum_univ_three,
          ho22 hw, ho11 hw, ho12 hw, ho21 hw, ho00 hw]

/-- For odd-length words the `(2,2)` entry of the Majumdar-Ghosh product vanishes. -/
private lemma majumdarGhosh_evalWord_22_of_odd {w : List (Fin 2)} (hw : Odd w.length) :
    (evalWord majumdarGhoshTensor w) 2 2 = 0 :=
  (majumdarGhosh_evalWord_grading w).1.1 hw

/-- For even-length words the `(1,0)` entry of the Majumdar-Ghosh product vanishes. -/
private lemma majumdarGhosh_evalWord_10_of_even {w : List (Fin 2)} (hw : Even w.length) :
    (evalWord majumdarGhoshTensor w) 1 0 = 0 :=
  (majumdarGhosh_evalWord_grading w).2.2.2.1 hw

/-- The Majumdar-Ghosh tensor is not `N`-block injective for any odd `N`: the
`(2,2)` matrix unit is not in the span of the length-`N` products. -/
theorem majumdarGhosh_not_isNBlkInjective_of_odd {N : ℕ} (hN : Odd N) :
    ¬ IsNBlkInjective majumdarGhoshTensor N := by
  intro h
  have hmem : Matrix.single (2 : Fin 3) (2 : Fin 3) (1 : ℂ) ∈
      Submodule.span ℂ (Set.range fun σ : Fin N → Fin 2 =>
        evalWord majumdarGhoshTensor (List.ofFn σ)) := h ▸ Submodule.mem_top
  suffices hzero : ∀ M ∈ Submodule.span ℂ (Set.range fun σ : Fin N → Fin 2 =>
      evalWord majumdarGhoshTensor (List.ofFn σ)), M 2 2 = 0 by
    have h1 := hzero _ hmem
    simp [Matrix.single] at h1
  intro M hM
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨σ, rfl⟩ := hx
    exact majumdarGhosh_evalWord_22_of_odd (by simpa [List.length_ofFn] using hN)
  | zero => simp
  | add x y _ _ hx hy => simp [Matrix.add_apply, hx, hy]
  | smul c x _ hx => simp [Matrix.smul_apply, hx]

/-- The Majumdar-Ghosh tensor is not `N`-block injective for any even `N`: the
`(1,0)` matrix unit is not in the span of the length-`N` products. -/
theorem majumdarGhosh_not_isNBlkInjective_of_even {N : ℕ} (hN : Even N) :
    ¬ IsNBlkInjective majumdarGhoshTensor N := by
  intro h
  have hmem : Matrix.single (1 : Fin 3) (0 : Fin 3) (1 : ℂ) ∈
      Submodule.span ℂ (Set.range fun σ : Fin N → Fin 2 =>
        evalWord majumdarGhoshTensor (List.ofFn σ)) := h ▸ Submodule.mem_top
  suffices hzero : ∀ M ∈ Submodule.span ℂ (Set.range fun σ : Fin N → Fin 2 =>
      evalWord majumdarGhoshTensor (List.ofFn σ)), M 1 0 = 0 by
    have h1 := hzero _ hmem
    simp [Matrix.single] at h1
  intro M hM
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨σ, rfl⟩ := hx
    exact majumdarGhosh_evalWord_10_of_even (by simpa [List.length_ofFn] using hN)
  | zero => simp
  | add x y _ _ hx hy => simp [Matrix.add_apply, hx, hy]
  | smul c x _ hx => simp [Matrix.smul_apply, hx]

/-- The Majumdar-Ghosh tensor is not `1`-block injective. -/
theorem majumdarGhosh_not_isNBlkInjective_one :
    ¬ IsNBlkInjective majumdarGhoshTensor 1 :=
  majumdarGhosh_not_isNBlkInjective_of_odd (by decide)

/-- The Majumdar-Ghosh tensor is not `2`-block injective. -/
theorem majumdarGhosh_not_isNBlkInjective_two :
    ¬ IsNBlkInjective majumdarGhoshTensor 2 :=
  majumdarGhosh_not_isNBlkInjective_of_even (by decide)

/-- The Majumdar-Ghosh tensor is **not** normal: no blocking length `N` makes it
`N`-block injective.  This algebraic obstruction matches the expected
two-dimer-covering structure: the bond carries a two-periodic grading that no
amount of blocking removes. -/
theorem majumdarGhosh_not_isNormal : ¬ IsNormal majumdarGhoshTensor := by
  rintro ⟨N, hN⟩
  rcases Nat.even_or_odd N with he | ho
  · exact majumdarGhosh_not_isNBlkInjective_of_even he hN
  · exact majumdarGhosh_not_isNBlkInjective_of_odd ho hN

end MPSTensor

end
