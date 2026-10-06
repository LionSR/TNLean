import TNLean.MPS.MPU.RepresentativeIndex

/-!
# Unused bond directions

A matrix product operator tensor of bond dimension `D` is embedded into bond dimension `D' ≥ D`
by placing every letter in the upper left `D × D` corner and zero on the adjoined directions.
This changes no periodic operator of positive length, hence preserves the MPU property and the
index. It is the convention under which two tensors of different bond dimensions are compared in
the definitions of strict equivalence and equivalence (CPSV17, arXiv:1703.09188, Definitions IV.3
and IV.4, lines 706--724; `docs/paper-gaps/mpu_equivalence_fixed_bond.tex`). Milestone M-B of
`codex-workflow/projects/mpu-notes/programme/mpu-close/PLAN.md`.
-/

open scoped Matrix
open Matrix

namespace MPOTensor

variable {d D D' : ℕ}

/-- The inclusion of the first `D` coordinates of `ℂ^{D'}`, as a `D' × D` matrix. -/
def bondInclusion (D D' : ℕ) (_h : D ≤ D') : Matrix (Fin D') (Fin D) ℂ :=
  Matrix.of fun a b => if (a : ℕ) = (b : ℕ) then 1 else 0

theorem bondInclusion_conjTranspose_mul (h : D ≤ D') :
    (bondInclusion D D' h)ᴴ * bondInclusion D D' h = 1 := by
  ext b c
  simp only [bondInclusion, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Matrix.one_apply]
  have hb : ((Fin.castLE h b : Fin D') : ℕ) = (b : ℕ) := rfl
  rw [Finset.sum_eq_single (Fin.castLE h b)]
  · simp only [hb, ite_true, star_one, one_mul]
    by_cases hbc : b = c
    · subst hbc; simp
    · have : (b : ℕ) ≠ (c : ℕ) := fun hh => hbc (Fin.ext hh)
      simp [this, hbc]
  · intro a _ ha
    have : (a : ℕ) ≠ (b : ℕ) := fun hh => ha (Fin.ext (by simpa [hb] using hh))
    simp [this]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

theorem bondInclusion_self (h : D ≤ D) : bondInclusion D D h = 1 := by
  ext a b
  simp [bondInclusion, Matrix.one_apply, Fin.ext_iff]

/-- The tensor `U` with unused bond directions adjoined up to bond dimension `D'`: every letter
is the upper-left block, zero elsewhere. -/
noncomputable def padBond (U : MPOTensor d D) (D' : ℕ) (h : D ≤ D') : MPOTensor d D' :=
  fun i j => bondInclusion D D' h * U i j * (bondInclusion D D' h)ᴴ

/-- Adjoining no bond direction is the identity. -/
@[simp] theorem padBond_self (U : MPOTensor d D) (h : D ≤ D) : padBond U D h = U := by
  funext i j
  simp [padBond, bondInclusion_self]

/-- Word evaluation of the enlarged tensor on words of equal positive length is the enlarged
word evaluation. -/
theorem evalWord_padBond (U : MPOTensor d D) (h : D ≤ D') :
    ∀ (is js : List (Fin d)), is.length = js.length → is ≠ [] →
      evalWord (padBond U D' h) is js =
        bondInclusion D D' h * evalWord U is js * (bondInclusion D D' h)ᴴ
  | [], _, _, hne => absurd rfl hne
  | _ :: _, [], hlen, _ => by simp at hlen
  | [i], [j], _, _ => by
      simp only [evalWord_cons, evalWord_nil, Matrix.mul_one, padBond]
  | i :: i' :: is, j :: j' :: js, hlen, _ => by
      have hlen' : (i' :: is).length = (j' :: js).length := by simpa using hlen
      have hrec := evalWord_padBond U h (i' :: is) (j' :: js) hlen' (List.cons_ne_nil _ _)
      rw [evalWord_cons (padBond U D' h) i j (i' :: is) (j' :: js), hrec,
        evalWord_cons U i j (i' :: is) (j' :: js)]
      simp only [padBond, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (bondInclusion D D' h)ᴴ (bondInclusion D D' h),
        bondInclusion_conjTranspose_mul, Matrix.one_mul]

/-- Adjoining unused bond directions changes no periodic operator of positive length.

Source: CPSV17, arXiv:1703.09188, Definitions IV.3 and IV.4 (lines 706--724), whose comparison of
tensors of different bond dimensions relies on this; the chapter's Remark on unused bond
directions. -/
theorem mpo_padBond (U : MPOTensor d D) (h : D ≤ D') (N : ℕ) [NeZero N] :
    mpo (padBond U D' h) N = mpo U N := by
  ext σ τ
  simp only [mpo_apply, mpoMatrixEntry]
  have hne : List.ofFn σ ≠ [] := by
    intro hnil
    have := congrArg List.length hnil
    rw [List.length_ofFn, List.length_nil] at this
    exact NeZero.ne N this
  rw [evalWord_padBond U h (List.ofFn σ) (List.ofFn τ) (by simp) hne, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, bondInclusion_conjTranspose_mul, Matrix.one_mul]

/-- Adjoining unused bond directions preserves the MPU property. -/
theorem IsMPU.padBond {U : MPOTensor d D} (hU : IsMPU U) (D' : ℕ) (h : D ≤ D') :
    IsMPU (padBond U D' h) := by
  intro N hN
  have : NeZero N := ⟨by omega⟩
  rw [mpo_padBond U h N]
  exact hU N hN

/-- The index is unchanged by adjoining unused bond directions. -/
theorem IsMPU.index_padBond [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U) (D' : ℕ)
    (h : D ≤ D') :
    have : NeZero D' := ⟨by have := NeZero.pos D; omega⟩
    (hU.padBond D' h).index = hU.index := by
  have : NeZero D' := ⟨by have := NeZero.pos D; omega⟩
  exact IsMPU.index_eq_of_mpo_eq (hU.padBond D' h) hU fun N hN =>
    have : NeZero N := ⟨by omega⟩
    mpo_padBond U h N

end MPOTensor
