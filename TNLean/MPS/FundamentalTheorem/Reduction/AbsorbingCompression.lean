/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Kraus.Word

/-!
# Compressing words onto an absorbing corner

Let `W : ℂ^D → ℂ^k` and `V : ℂ^k → ℂ^D` be rectangular matrices with `V W` acting as the
identity on the image of every letter of a family `B` (on the left), or with every letter
annihilating the kernel of `V W` (on the right). Then compressing each letter to
`W B^i V` compresses every nonempty word, and the trace of each nonempty word is unchanged.

This is the linear-algebra step of the canonical-form construction of the review
arXiv:2011.12127, Section IV, "Canonical form and normal tensors",
`Papers/2011.12127/TN-Review-main.tex`: when the letters satisfy the invariance condition
`B^i P₁ = P₁ B^i P₁`, `Q₁ B^i = Q₁ B^i Q₁` of lines 1784–1787 for an orthogonal projection `P₁`
with `Q₁ = 1 - P₁`, the replacement `B^i → P₁ B^i P₁ + Q₁ B^i Q₁` of lines 1793–1797 does not
change any trace. The special cases proved here are those in which one of the two diagonal
blocks vanishes, so that the trace is carried by a single block: with `P = V W`, the condition
`P B^i = B^i` says that the complementary block and the off-diagonal block below it vanish.

## Main results

* `Kraus.evalWord_compress_of_left_absorb`, `Kraus.trace_evalWord_compress_of_left_absorb`:
  the compressed words and their traces when `V W B^i = B^i`.
* `Kraus.evalWord_compress_of_right_absorb`, `Kraus.trace_evalWord_compress_of_right_absorb`:
  the same when `B^i V W = B^i`.
-/

open scoped Matrix

namespace Kraus

variable {d D k : ℕ} (B : Fin d → Matrix (Fin D) (Fin D) ℂ)
  (W : Matrix (Fin k) (Fin D) ℂ) (V : Matrix (Fin D) (Fin k) ℂ)

/-- A left-absorbing corner absorbs every nonempty word. -/
theorem mul_evalWord_of_left_absorb (h : ∀ i, V * W * B i = B i) (w : List (Fin d))
    (hw : w ≠ []) : V * W * evalWord B w = evalWord B w := by
  obtain ⟨a, w, rfl⟩ := List.exists_cons_of_ne_nil hw
  rw [evalWord_cons, ← Matrix.mul_assoc, h]

/-- A right-absorbing corner absorbs every nonempty word. -/
theorem evalWord_mul_of_right_absorb (h : ∀ i, B i * (V * W) = B i) :
    ∀ (w : List (Fin d)), w ≠ [] → evalWord B w * (V * W) = evalWord B w
  | [], hw => absurd rfl hw
  | [a], _ => by rw [evalWord_cons, evalWord_nil, Matrix.mul_one, h]
  | a :: b :: w, _ => by
      rw [evalWord_cons, Matrix.mul_assoc,
        evalWord_mul_of_right_absorb h (b :: w) (List.cons_ne_nil _ _)]

/-- **Compression onto a left-absorbing corner.** If `V W B^i = B^i` for every letter, then the
compressed letters `W B^i V` multiply out to the compression of the product: every nonempty
word satisfies `W B^{i₁} V ⋯ W B^{iₙ} V = W B^{i₁} ⋯ B^{iₙ} V`.

Source: arXiv:2011.12127, Section IV, `Papers/2011.12127/TN-Review-main.tex` lines 1793–1797
(the block replacement of the canonical-form construction, in the case where one diagonal block
carries the whole word). -/
theorem evalWord_compress_of_left_absorb (h : ∀ i, V * W * B i = B i) :
    ∀ (w : List (Fin d)), w ≠ [] →
      evalWord (fun i => W * B i * V) w = W * evalWord B w * V
  | [], hw => absurd rfl hw
  | [a], _ => by simp only [evalWord_cons, evalWord_nil, Matrix.mul_one]
  | a :: b :: w, _ => by
      rw [evalWord_cons, evalWord_compress_of_left_absorb h (b :: w) (List.cons_ne_nil _ _),
        evalWord_cons B a]
      rw [show W * B a * V * (W * evalWord B (b :: w) * V) =
          W * B a * (V * W * evalWord B (b :: w)) * V by simp only [Matrix.mul_assoc],
        mul_evalWord_of_left_absorb B W V h (b :: w) (List.cons_ne_nil _ _),
        Matrix.mul_assoc W]

/-- **Traces under compression onto a left-absorbing corner.** If `V W B^i = B^i` for every
letter, then every nonempty word of the compressed letters `W B^i V` has the trace of the
corresponding word of `B`.

Source: arXiv:2011.12127, Section IV, `Papers/2011.12127/TN-Review-main.tex` lines 1793–1797. -/
theorem trace_evalWord_compress_of_left_absorb (h : ∀ i, V * W * B i = B i)
    (w : List (Fin d)) (hw : w ≠ []) :
    Matrix.trace (evalWord (fun i => W * B i * V) w) = Matrix.trace (evalWord B w) := by
  rw [evalWord_compress_of_left_absorb B W V h w hw, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    mul_evalWord_of_left_absorb B W V h w hw]

/-- **Compression onto a right-absorbing corner.** If `B^i V W = B^i` for every letter, then
every nonempty word satisfies `W B^{i₁} V ⋯ W B^{iₙ} V = W B^{i₁} ⋯ B^{iₙ} V`.

Source: arXiv:2011.12127, Section IV, `Papers/2011.12127/TN-Review-main.tex` lines 1793–1797. -/
theorem evalWord_compress_of_right_absorb (h : ∀ i, B i * (V * W) = B i) :
    ∀ (w : List (Fin d)), w ≠ [] →
      evalWord (fun i => W * B i * V) w = W * evalWord B w * V
  | [], hw => absurd rfl hw
  | [a], _ => by simp only [evalWord_cons, evalWord_nil, Matrix.mul_one]
  | a :: b :: w, _ => by
      rw [evalWord_cons, evalWord_compress_of_right_absorb h (b :: w) (List.cons_ne_nil _ _),
        evalWord_cons B a]
      rw [show W * B a * V * (W * evalWord B (b :: w) * V) =
          W * (B a * (V * W)) * evalWord B (b :: w) * V by simp only [Matrix.mul_assoc],
        h, Matrix.mul_assoc W]

/-- **Traces under compression onto a right-absorbing corner.** If `B^i V W = B^i` for every
letter, then every nonempty word of the compressed letters `W B^i V` has the trace of the
corresponding word of `B`.

Source: arXiv:2011.12127, Section IV, `Papers/2011.12127/TN-Review-main.tex` lines 1793–1797. -/
theorem trace_evalWord_compress_of_right_absorb (h : ∀ i, B i * (V * W) = B i)
    (w : List (Fin d)) (hw : w ≠ []) :
    Matrix.trace (evalWord (fun i => W * B i * V) w) = Matrix.trace (evalWord B w) := by
  rw [evalWord_compress_of_right_absorb B W V h w hw, Matrix.mul_assoc, Matrix.trace_mul_comm,
    Matrix.mul_assoc, evalWord_mul_of_right_absorb B W V h w hw]

end Kraus
