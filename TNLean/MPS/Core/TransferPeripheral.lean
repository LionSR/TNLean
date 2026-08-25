/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Peripheral.ClosureFixedPointKraus
import QICLean.Channel.Peripheral.CyclicGroupKraus
import QICLean.Channel.Peripheral.CyclicDecomposition.LetterShift
import QICLean.Kraus.TransferChannel

/-!
# Transfer-map forms of the peripheral fixed-point and cyclic-group results

For a finite matrix family, the Kraus map equals its MPS transfer map. The
QICLean owns the Kraus-level peripheral theory.  This module retains the
MPS-specific word-level cyclic shift across the cyclic projections.

## Main statement

* `evalWord_mul_cyclicProj` — a word of length $\ell$ shifts every cyclic
  projection by $\ell$ steps.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.6]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators Fin.NatCast
open Matrix Finset Complex

namespace MPSTensor

/-- **Word-level cyclic shift**: a word $A^w=K_{w_1}\cdots K_{w_\ell}$ of
length $\ell$ moves each cyclic projection back by $\ell$ steps,
$A^wP_k=P_{k-\ell}A^w$.  In particular a word of length $m$ commutes with
every cyclic projection. -/
theorem evalWord_mul_cyclicProj {r n m : ℕ} [NeZero m]
    (K : Fin r → MatrixAlg n) (P : Fin m → MatrixAlg n)
    (hproj : ∀ k, IsOrthogonalProjection (P k))
    (hsum : ∑ k : Fin m, P k = 1)
    (hcyclic : ∀ k : Fin m, Kraus.transferMap (d := r) (D := n) K (P (k + 1)) = P k) :
    ∀ (w : List (Fin r)) (k : Fin m),
      Kraus.evalWord K w * P k = P (k - (w.length : Fin m)) * Kraus.evalWord K w := by
  have hcyclicLM : ∀ k : Fin m, Kraus.mapLM K (P (k + 1)) = P k := fun k => by
        exact hcyclic k
  intro w
  induction w with
  | nil =>
    intro k
    simp
  | cons v w ih =>
    intro k
    have hstep : K v * P (k - (w.length : Fin m)) =
        P (k - (w.length : Fin m) - 1) * K v := by
      have := Kraus.kraus_mul_cyclicProj K P hproj hsum hcyclicLM v
        (k - (w.length : Fin m) - 1)
      rwa [sub_add_cancel] at this
    calc Kraus.evalWord K (v :: w) * P k
        = K v * (Kraus.evalWord K w * P k) := by rw [Kraus.evalWord_cons, Matrix.mul_assoc]
      _ = K v * (P (k - (w.length : Fin m)) * Kraus.evalWord K w) := by rw [ih k]
      _ = (K v * P (k - (w.length : Fin m))) * Kraus.evalWord K w := by
          rw [Matrix.mul_assoc]
      _ = P (k - (w.length : Fin m) - 1) * (K v * Kraus.evalWord K w) := by
          rw [hstep, Matrix.mul_assoc]
      _ = P (k - ((v :: w).length : Fin m)) * Kraus.evalWord K (v :: w) := by
          rw [Kraus.evalWord_cons]
          congr 2
          rw [List.length_cons, Nat.cast_add, Nat.cast_one, sub_sub]

end MPSTensor
