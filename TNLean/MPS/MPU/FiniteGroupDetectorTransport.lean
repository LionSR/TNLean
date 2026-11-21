/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Conditional transport through all intermediate detector states

The finite-group detector in arXiv:2405.00439, Section V, `detectG`
(`Papers/2405.00439/MPU-DW.tex`, lines 2108–2117), needs comparisons of actual
interval operators with reference excitation vectors at every forward and
undo step. Knowing the operators only on initial ground states does not give
these comparisons.

This module proves the linear-algebra implication under those comparisons,
stated individually as explicit hypotheses. It neither derives them from the
source's circuit assumptions nor assumes the value of the full detector.
The phase factors can later be instantiated by the source's domain-wall
coefficients, after a separate construction establishes the comparisons.
The source's unconditional anomaly-detection assertion remains open.
The related endpoint-dependence gap and its general-group comparison task are
recorded in https://sirui-lu.com/TNLean/paper-gaps/gs24_truncation_detector_endpoint_dependence.pdf.
-/

open Matrix
open scoped Matrix

namespace MPOTensor.FiniteGroupDetector

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A chronological product transports an initial vector through a specified
sequence of intermediate vectors, multiplying exactly their scalar factors.
This is a general matrix identity used in the endpoint audit of
arXiv:2405.00439, `detectG`, lines 2108–2117. -/
theorem reverse_prod_mulVec_eq_smul_of_steps (A : ℕ → Matrix ι ι ℂ)
    (v : ℕ → ι → ℂ) (c : ℕ → ℂ) (n : ℕ)
    (hstep : ∀ r < n, A r *ᵥ v r = c r • v (r + 1)) :
    ((List.range n).map A).reverse.prod *ᵥ v 0 =
      ((List.range n).map c).prod • v n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprod : ((List.range (n + 1)).map A).reverse.prod =
        A n * ((List.range n).map A).reverse.prod := by
      simp [List.range_succ]
    rw [hprod, ← mulVec_mulVec, ih (fun r hr ↦ hstep r (Nat.lt_succ_of_lt hr)),
      mulVec_smul, hstep n (Nat.lt_succ_self n), smul_smul, List.prod_range_succ]

/-- The chronological forward word followed by the chronological undo word.
Here `F 0` creates the first excitation and `D r` is the interval whose
adjoint is the `r`th undo operation. Source: arXiv:2405.00439, `detectG`,
lines 2108–2117, with the product convention made explicit. -/
def detectorTransportWord (F D : ℕ → Matrix ι ι ℂ) (m : ℕ) : Matrix ι ι ℂ :=
  ((List.range (m + 1)).map fun r ↦ (D r)ᴴ).reverse.prod *
    ((List.range m).map fun r ↦ F (r + 1)).reverse.prod * F 0

/-- With scalar factors on both forward and undo states, the full detector
has the product of both sets of factors. In particular an undo phase must not
be silently discarded. The hypotheses are explicit intermediate-state
comparisons, not a whole-detector identity. Project conditional statement for
the endpoint audit of arXiv:2405.00439, `detectG`, lines 2108–2117. -/
theorem detectorTransportWord_mulVec_of_phased_intermediate_states
    (F D : ℕ → Matrix ι ι ℂ) (v w : ℕ → ι → ℂ) (c e : ℕ → ℂ) (m : ℕ) (ψ : ι → ℂ)
    (hstart : F 0 *ᵥ ψ = v 0)
    (hforward : ∀ r < m, F (r + 1) *ᵥ v r = c r • v (r + 1))
    (hjoin : w 0 = v m)
    (hundo : ∀ r < m + 1, (D r)ᴴ *ᵥ w r = e r • w (r + 1))
    (hfinish : w (m + 1) = ψ) :
    detectorTransportWord F D m *ᵥ ψ =
      (((List.range m).map c).prod * ((List.range (m + 1)).map e).prod) • ψ := by
  have hforwardWord := reverse_prod_mulVec_eq_smul_of_steps
    (fun r ↦ F (r + 1)) v c m hforward
  have hundoWord := reverse_prod_mulVec_eq_smul_of_steps
    (fun r ↦ (D r)ᴴ) w e (m + 1) hundo
  rw [detectorTransportWord, ← mulVec_mulVec, ← mulVec_mulVec, hstart,
    hforwardWord, mulVec_smul, ← hjoin, hundoWord, hfinish, smul_smul]

/-- Under explicit comparisons at every forward and undo state, the full
detector has the product of the forward scalar factors on the initial vector.
These intermediate-state comparisons are additional hypotheses, not
consequences of the source established here. Project conditional statement
for the endpoint audit of arXiv:2405.00439, `detectG`, lines 2108–2117. -/
theorem detectorTransportWord_mulVec_of_intermediate_states
    (F D : ℕ → Matrix ι ι ℂ) (v w : ℕ → ι → ℂ) (c : ℕ → ℂ) (m : ℕ) (ψ : ι → ℂ)
    (hstart : F 0 *ᵥ ψ = v 0)
    (hforward : ∀ r < m, F (r + 1) *ᵥ v r = c r • v (r + 1))
    (hjoin : w 0 = v m)
    (hundo : ∀ r < m + 1, (D r)ᴴ *ᵥ w r = w (r + 1))
    (hfinish : w (m + 1) = ψ) :
    detectorTransportWord F D m *ᵥ ψ = ((List.range m).map c).prod • ψ := by
  simpa using detectorTransportWord_mulVec_of_phased_intermediate_states
    F D v w c (fun _ ↦ 1) m ψ hstart hforward hjoin
      (fun r hr ↦ by simpa using hundo r hr) hfinish

/-- The conditional detector expectation is the product of the forward
coefficients in a normalized initial state. The action on every intermediate
state remains explicit; no whole-detector phase is an assumption. Project
conditional statement for arXiv:2405.00439, `detectG`, lines 2108–2117. -/
theorem star_dotProduct_detectorTransportWord_of_intermediate_states
    (F D : ℕ → Matrix ι ι ℂ) (v w : ℕ → ι → ℂ) (c : ℕ → ℂ) (m : ℕ) (ψ : ι → ℂ)
    (hstart : F 0 *ᵥ ψ = v 0)
    (hforward : ∀ r < m, F (r + 1) *ᵥ v r = c r • v (r + 1))
    (hjoin : w 0 = v m)
    (hundo : ∀ r < m + 1, (D r)ᴴ *ᵥ w r = w (r + 1))
    (hfinish : w (m + 1) = ψ) (hψ : star ψ ⬝ᵥ ψ = 1) :
    star ψ ⬝ᵥ (detectorTransportWord F D m *ᵥ ψ) = ((List.range m).map c).prod := by
  rw [detectorTransportWord_mulVec_of_intermediate_states F D v w c m ψ
    hstart hforward hjoin hundo hfinish, dotProduct_smul, hψ, smul_eq_mul, mul_one]

end MPOTensor.FiniteGroupDetector
