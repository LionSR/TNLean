/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.FibonacciAnomaly
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.Z3AnomalousFusion
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.Z3AnomalousInverseFusion
import TNLean.MPS.Symmetry.MPOSymmetry.Character

/-!
# Matrix product operator symmetries: the Fibonacci and anomalous `ℤ/3` instances

**Source.** Garre-Rubio, Lootens, Molnár 2023 (arXiv:2203.12563), Section 6,
`Papers/2203.12563/REsubmission.tex` lines 1991–1993: for the matrix product operator
representation of the Fibonacci fusion category `τ × τ = 1 + τ`, the only invariant family of
normal states has two blocks with `τ · x_1 = x_τ` and `τ · x_τ = x_1 + x_τ`.
The Fibonacci operators follow Bultinck et al. (arXiv:1511.08090), Appendix D.1.

**Formalized here.** The Fibonacci periodic operators of
`FibonacciCompression.fibBlock` form a fusion algebra with unit `1`; the pair of normal states
of the source is a symmetric family whose action is the regular representation, a nonnegative
integer representation. The Fibonacci ring has no fusion character in `ℕ`, and the single-block
no-go `FibonacciCompression.not_exists_normal_fibonacci_symmetric` (no normal tensor with
`O_1 ψ = ψ` and `O_τ ψ = c ψ`) is derived from the general obstruction
`MPOTensor.not_isMPOSymmetric_of_forall_not_isFusionCharacter`. The anomalous `ℤ/3` operators
`1, U, U†` of `Z3AnomalousTensor.lean` form a group-like fusion algebra in which every label is
invertible.

Not instances. The undecorated CZX operator of `CZXUnitary.lean` squares to `(-1)^L` times the
identity (`CZXCompression.mpo_czxTensor_mul_self`), so the pair `1, U_CZX` obeys the `ℤ/2`
fusion rules only at even lengths and is not a fusion algebra in the sense used here, which
requires the rules at every positive length. The Kramers–Wannier operator
`D` of `KramersWannier.lean` squares to `2^L (1 + η) T`, where `T` is the one-site translation
(`KWExample.kwSquare_trace_evalWord`). The factor `2^L` is a normalization and disappears after
rescaling `D`, but the translation `T` does not: `D² = (1 + η) T` expresses the square through
an operator outside the span of `1`, `η` and `D`, so the labels `1, η, D` do not close under
multiplication and form no fusion algebra in the sense used here.

## Provenance

The anomalous `ℤ/3` tensor is not printed in any source. It is the phase-decorated shift built
in `Z3AnomalousTensor.lean` from the `ℤ/n` three-cocycle formula of arXiv:2405.00439; its exact
data were first recorded in `Notes/OpenProblemsTN/checks/asym_z3_anomalous_data.md`, a
verification record, not a source.

## Main results

* `FibonacciCompression.isMPOFusionAlgebra_fibBlock`, `FibonacciCompression.isFusionUnit_fibFusion`,
  `FibonacciCompression.isMPOSymmetricFamily_fibNimTargets`,
  `FibonacciCompression.isNIMRep_fibFusion`, `FibonacciCompression.not_isFusionCharacter_fibFusion`,
  `FibonacciCompression.not_exists_normal_fibonacci_symmetric`.
* `Z3Anomalous.isMPOFusionAlgebra_z3Block`, `Z3Anomalous.isInvertibleLabel_z3Fusion`.

## References
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- J. Garre-Rubio, L. Lootens,
  A. Molnár, *Classifying phases protected by matrix product operator symmetries using matrix
  product states*
- [arXiv:1511.08090](https://arxiv.org/abs/1511.08090) -- N. Bultinck, M. Mariën,
  D. J. Williamson, M. B. Sahinoglu, J. Haegeman, F. Verstraete, *Anyons and matrix product
  operator algebras*
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- the `ℤ/n` three-cocycle formula from
  which the anomalous `ℤ/3` tensor is built
-/

open scoped Matrix

open MPOTensor MPSTensor

namespace FibonacciCompression

/-- Bridge: the structure constants `fibNim` of the Fibonacci fusion ring as a function of three
labels. -/
abbrev fibFusion (a b c : Fin 2) : ℕ := fibNim a b c

/-- Bridge: the periodic operators of the project's Fibonacci tensors `fibBlock` satisfy the
Fibonacci fusion rules `τ × τ = 1 + τ` printed in arXiv:2203.12563, line 1993 (operators of
arXiv:1511.08090, App. D.1), so they form a matrix product operator fusion algebra; this wraps
`fibonacci_fusion_algebra`. -/
theorem isMPOFusionAlgebra_fibBlock : IsMPOFusionAlgebra fibBlock fibFusion :=
  fun a b L hL => fibonacci_fusion_algebra a b L hL

/-- Source: arXiv:2203.12563, line 1993: the trivial label `1` is the unit of the Fibonacci
fusion ring `{1, τ; τ × τ = 1 + τ}`. -/
theorem isFusionUnit_fibFusion : IsFusionUnit fibFusion 0 := by
  intro b c
  fin_cases b <;> fin_cases c <;> simp [fibFusion, fibNim, fibFusionMatrix, Matrix.one_apply]

/-- Bridge: the project's pair of normal tensors `fibNimTargets` is a symmetric family for
`fibBlock` with the regular action `τ · x_1 = x_τ`, `τ · x_τ = x_1 + x_τ` printed in
arXiv:2203.12563, lines 1991–1993; this wraps `fibonacci_nim_rep`. -/
theorem isMPOSymmetricFamily_fibNimTargets :
    IsMPOSymmetricFamily fibBlock fibNimTargets fun a s t => (fibNim a s t : ℂ) :=
  fun a s L hL => fibonacci_nim_rep a s L hL

/-- Source: arXiv:2203.12563, line 1993: the action `τ · x_1 = x_τ`, `τ · x_τ = x_1 + x_τ`, the
regular representation of the Fibonacci fusion ring, is a nonnegative integer representation. -/
theorem isNIMRep_fibFusion : IsNIMRep fibFusion fibFusion := by
  intro a b x y
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;>
    simp [fibFusion, fibNim, fibFusionMatrix, Matrix.one_apply, Fin.sum_univ_two]

/-- Project result: the Fibonacci fusion ring has no fusion character in `ℕ`, since
`m_τ² = 1 + m_τ` has no natural solution. -/
theorem not_isFusionCharacter_fibFusion (m : Fin 2 → ℕ) : ¬ IsFusionCharacter fibFusion 0 m := by
  rintro ⟨h0, hmul⟩
  have h := hmul 1 1
  simp [fibFusion, fibNim, fibFusionMatrix, Fin.sum_univ_two, h0] at h
  exact Nat.mul_self_ne_add_one (m 1) (by omega)

/-- **No normal matrix product state is symmetric under the Fibonacci algebra.**

Project result, the single-block counterpart of arXiv:2203.12563, line 1993 (the only invariant
family has two blocks): there is no normal tensor of positive bond dimension whose periodic
vectors are fixed by the admissibility projector `O_1` and are eigenvectors of the `τ` family
with one length-independent eigenvalue. It is the instance of the general obstruction
`MPOTensor.not_isMPOSymmetric_of_forall_not_isFusionCharacter` for the Fibonacci ring, which has
no fusion character in `ℕ`. -/
theorem not_exists_normal_fibonacci_symmetric :
    ¬ ∃ (D : ℕ) (A : MPSTensor 2 D) (c : ℂ), 0 < D ∧ Kraus.IsNormal A ∧
      (∀ L : ℕ, 0 < L →
        mpo fibOne L *ᵥ (fun τ : Fin L → Fin 2 => mpv A τ) = fun σ : Fin L → Fin 2 => mpv A σ) ∧
      (∀ L : ℕ, 0 < L →
        mpo fibTau L *ᵥ (fun τ : Fin L → Fin 2 => mpv A τ) =
          c • fun σ : Fin L → Fin 2 => mpv A σ) := by
  rintro ⟨D, A, c, hD, hA, hone, hτ⟩
  have : NeZero D := ⟨hD.ne'⟩
  refine not_isMPOSymmetric_of_forall_not_isFusionCharacter (c := ![1, c])
    isMPOFusionAlgebra_fibBlock not_isFusionCharacter_fibFusion hA rfl fun a L hL => ?_
  match a with
  | 0 => exact (hone L hL).trans (one_smul ℂ _).symm
  | 1 => exact hτ L hL

end FibonacciCompression

noncomputable section

namespace Z3Anomalous

/-- Bond dimensions of the three blocks `1, U, U†`. -/
def z3Dim : Fin 3 → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 2

/-- The three blocks `1, U, U†` of the anomalous `ℤ/3` representation, labelled by `ℤ/3`. -/
def z3Block : (a : Fin 3) → MPOTensor 3 (z3Dim a)
  | 0 => identityTensor
  | 1 => uTensor
  | 2 => uDagTensor

/-- Source: arXiv:2203.12563, line 660: the fusion ring of a group, here `ℤ/3`, with
`O_g O_h = O_{gh}`, that is `N_{ab}^c = δ_{c, a + b}`. -/
def z3Fusion (a b c : Fin 3) : ℕ := if c = a + b then 1 else 0

/-- Bridge: the periodic operators `1, U, U†` of the anomalous `ℤ/3` tensor of
`Z3AnomalousTensor.lean` (built from the three-cocycle formula of arXiv:2405.00439) obey the group
fusion rule `O_g O_h = O_{gh}` of arXiv:2203.12563, line 660, at every positive length. -/
theorem isMPOFusionAlgebra_z3Block : IsMPOFusionAlgebra z3Block z3Fusion := by
  intro a b L hL
  have hI : MPOTensor.mpo identityTensor L = 1 := mpo_identityTensor L
  have hsum : ∑ c, (z3Fusion a b c : ℂ) • MPOTensor.mpo (z3Block c) L =
      MPOTensor.mpo (z3Block (a + b)) L := by
    simp [z3Fusion, ite_smul]
  rw [hsum]
  match a, b with
  | 0, 0 => exact (show MPOTensor.mpo identityTensor L * MPOTensor.mpo identityTensor L =
      MPOTensor.mpo identityTensor L by rw [hI, one_mul])
  | 0, 1 => exact (show MPOTensor.mpo identityTensor L * MPOTensor.mpo uTensor L =
      MPOTensor.mpo uTensor L by rw [hI, one_mul])
  | 0, 2 => exact (show MPOTensor.mpo identityTensor L * MPOTensor.mpo uDagTensor L =
      MPOTensor.mpo uDagTensor L by rw [hI, one_mul])
  | 1, 0 => exact (show MPOTensor.mpo uTensor L * MPOTensor.mpo identityTensor L =
      MPOTensor.mpo uTensor L by rw [hI, mul_one])
  | 2, 0 => exact (show MPOTensor.mpo uDagTensor L * MPOTensor.mpo identityTensor L =
      MPOTensor.mpo uDagTensor L by rw [hI, mul_one])
  | 1, 1 => exact mpo_uu L hL
  | 2, 2 => exact mpo_dd L hL
  | 1, 2 => exact mpo_ud L hL
  | 2, 1 => exact mpo_du L hL

/-- Source: arXiv:2203.12563, line 660: every label of the `ℤ/3` fusion ring is invertible, with
inverse `-a`. -/
theorem isInvertibleLabel_z3Fusion (a : Fin 3) : IsInvertibleLabel z3Fusion 0 a :=
  ⟨-a, fun c => by simp [z3Fusion]⟩

end Z3Anomalous

end
