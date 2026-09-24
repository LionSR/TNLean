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
integer representation; the Fibonacci ring has no fusion character in `ℕ`, so no single normal
tensor is symmetric, recovering `FibonacciCompression.not_exists_normal_fibonacci_symmetric`
(with the unit acting trivially) as an instance of the general no-go. The anomalous `ℤ/3`
operators `1, U, U†` of `Z3AnomalousTensor.lean` form a group-like fusion algebra, so every
symmetric normal tensor is invariant under `U`. The anomaly itself, a three-cocycle, is invisible
to the fusion ring and is not used here.

## Main results

* `FibonacciCompression.isMPOFusionAlgebra_fibBlock`, `FibonacciCompression.isFusionUnit_fibFusion`,
  `FibonacciCompression.isMPOSymmetricFamily_fibNimTargets`,
  `FibonacciCompression.isNIMRep_fibFusion`, `FibonacciCompression.not_isFusionCharacter_fibFusion`,
  `FibonacciCompression.not_isMPOSymmetric_fibBlock`.
* `Z3Anomalous.isMPOFusionAlgebra_z3Block`, `Z3Anomalous.isInvertibleLabel_z3Fusion`,
  `Z3Anomalous.mpo_uTensor_mulVec_eq`.

## References
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- J. Garre-Rubio, L. Lootens,
  A. Molnár, *Classifying phases protected by matrix product operator symmetries using matrix
  product states*
- [arXiv:1511.08090](https://arxiv.org/abs/1511.08090) -- N. Bultinck, M. Mariën,
  D. J. Williamson, M. B. Şahinoğlu, J. Haegeman, F. Verstraete, *Anyons and matrix product
  operator algebras*
-/

open scoped Matrix

open MPOTensor MPSTensor

namespace FibonacciCompression

/-- The structure constants of the Fibonacci fusion ring as a function of three labels. -/
abbrev fibFusion (a b c : Fin 2) : ℕ := fibNim a b c

/-- Source: arXiv:1511.08090, App. D.1; arXiv:2203.12563, line 1993. The Fibonacci periodic
operators form a matrix product operator fusion algebra. -/
theorem isMPOFusionAlgebra_fibBlock : IsMPOFusionAlgebra fibBlock fibFusion :=
  fun a b L hL => fibonacci_fusion_algebra a b L hL

/-- The trivial label is the unit of the Fibonacci fusion ring. -/
theorem isFusionUnit_fibFusion : IsFusionUnit fibFusion 0 := by
  intro b c
  fin_cases b <;> fin_cases c <;> simp [fibFusion, fibNim, fibFusionMatrix, Matrix.one_apply]

/-- Source: arXiv:2203.12563, lines 1991–1993. The pair of normal states is a symmetric family
with the regular action `τ · x_1 = x_τ`, `τ · x_τ = x_1 + x_τ`. -/
theorem isMPOSymmetricFamily_fibNimTargets :
    IsMPOSymmetricFamily fibBlock fibNimTargets fun a s t => (fibNim a s t : ℂ) :=
  fun a s L hL => fibonacci_nim_rep a s L hL

/-- The regular representation of the Fibonacci fusion ring is a nonnegative integer
representation (arXiv:2203.12563, line 1993). -/
theorem isNIMRep_fibFusion : IsNIMRep fibFusion fibFusion := by
  intro a b x y
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;>
    simp [fibFusion, fibNim, fibFusionMatrix, Matrix.one_apply, Fin.sum_univ_two]

/-- The Fibonacci fusion ring has no fusion character in `ℕ`: `m_τ² = 1 + m_τ` has no natural
solution. -/
theorem not_isFusionCharacter_fibFusion (m : Fin 2 → ℕ) : ¬ IsFusionCharacter fibFusion 0 m := by
  rintro ⟨h0, hmul⟩
  have h := hmul 1 1
  simp [fibFusion, fibNim, fibFusionMatrix, Fin.sum_univ_two, h0] at h
  exact Nat.mul_self_ne_add_one (m 1) (by omega)

/-- **No normal tensor is symmetric under the Fibonacci algebra**, as an instance of
`MPOTensor.not_isMPOSymmetric_of_forall_not_isFusionCharacter` (arXiv:2203.12563, line 1993). -/
theorem not_isMPOSymmetric_fibBlock {D : ℕ} [NeZero D] {A : MPSTensor 2 D}
    (hA : Kraus.IsNormal A) {c : Fin 2 → ℂ} (h0 : c 0 = 1) : ¬ IsMPOSymmetric fibBlock A c :=
  not_isMPOSymmetric_of_forall_not_isFusionCharacter isMPOFusionAlgebra_fibBlock
    not_isFusionCharacter_fibFusion hA h0

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

/-- The group fusion ring of `ℤ/3`: `N_{ab}^c = δ_{c, a + b}`. -/
def z3Fusion (a b c : Fin 3) : ℕ := if c = a + b then 1 else 0

/-- The anomalous `ℤ/3` periodic operators form a group-like fusion algebra. -/
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

/-- Every label of the `ℤ/3` fusion ring is invertible, with inverse `-a`. -/
theorem isInvertibleLabel_z3Fusion (a : Fin 3) : IsInvertibleLabel z3Fusion 0 a :=
  ⟨-a, fun c => by simp [z3Fusion]⟩

/-- A normal tensor whose periodic vectors are eigenvectors of the anomalous `ℤ/3` symmetry with
length-independent eigenvalue is invariant. -/
theorem mpo_uTensor_mulVec_eq {D : ℕ} [NeZero D] {A : MPSTensor 3 D} (hA : Kraus.IsNormal A)
    {c : Fin 3 → ℂ} (hsym : IsMPOSymmetric z3Block A c) (h0 : c 0 = 1) (L : ℕ) (hL : 0 < L) :
    MPOTensor.mpo uTensor L *ᵥ (fun τ : Fin L → Fin 3 => mpv A τ) =
      fun σ : Fin L → Fin 3 => mpv A σ :=
  mpo_mulVec_eq_of_isInvertibleLabel isMPOFusionAlgebra_z3Block hA hsym h0
    (isInvertibleLabel_z3Fusion 1) L hL

end Z3Anomalous

end
