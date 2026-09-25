/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.Ising.IsingFusionAlgebraOnePsi
import TNLean.MPS.Examples.Ising.IsingFusionAlgebraOneSigma
import TNLean.MPS.Examples.Ising.IsingFusionAlgebraPsiSigma
import TNLean.MPS.Examples.Ising.IsingFusionAlgebraSigma
import TNLean.MPS.Symmetry.MPOSymmetry.Character

/-!
# The Ising matrix product operators as a fusion algebra

**Source.** Bultinck et al. (arXiv:1511.08090), Appendix D.1.2, lines 1308–1312 and 1323: the
three blocks `1, ψ, σ` of the Ising matrix product operator obey the fusion rules
`ψ × ψ = 1`, `ψ × σ = σ × ψ = σ` and `σ × σ = 1 + ψ`, with `1` the unit. Garre-Rubio, Lootens
and Molnár (arXiv:2203.12563), lines 361–362, call such a family a matrix product operator
algebra with structure constants `N_{ab}^c`.

**Formalized here.** The nine products of the periodic operators of the blocks `isingOne`,
`isingPsi` and the rescaled `(√2)⁻¹ • isingSigma`, proved in
`TNLean/MPS/Examples/Ising/IsingFusionAlgebra*.lean`, assembled into one
`MPOTensor.IsMPOFusionAlgebra` statement with the Ising structure constants, together with the
consequence of `MPOTensor.not_isMPOSymmetric_of_forall_not_isFusionCharacter`: the Ising ring has
no fusion character in `ℕ` (a character would give `m_σ² = 1 + m_ψ = 2`), so no single normal
matrix product state is symmetric under the Ising algebra with the unit acting trivially.

**Local fix (normalization):** the stored tensor `isingSigma` is `√2` times the tensor `A_σ` of
the source, as recorded in the module docstring of `IsingFusionAlgebraOneSigma.lean`; the fusion
algebra uses the rescaled tensor `(√2)⁻¹ • isingSigma`.

## Main definitions

* `IsingTwist.isingDim`, `IsingTwist.isingBlock`: the three blocks indexed by the labels
  `0 = 1`, `1 = ψ`, `2 = σ`.
* `IsingTwist.isingFusion`: the structure constants of the Ising fusion ring.

## Main results

* `IsingTwist.isMPOFusionAlgebra_ising`: the Ising blocks form a fusion algebra.
* `IsingTwist.isFusionUnit_isingFusion`: `1` is the unit.
* `IsingTwist.not_isFusionCharacter_isingFusion`: the Ising ring has no fusion character in `ℕ`.
* `IsingTwist.not_isMPOSymmetric_ising`: no normal tensor is symmetric under the Ising algebra
  with the unit acting trivially.

## References

- [arXiv:1511.08090](https://arxiv.org/abs/1511.08090) -- N. Bultinck, M. Mariën,
  D. J. Williamson, M. B. Sahinoglu, J. Haegeman, F. Verstraete, *Anyons and matrix product
  operator algebras*
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- J. Garre-Rubio, L. Lootens,
  A. Molnár, *Classifying phases protected by matrix product operator symmetries using matrix
  product states*
-/

open scoped Matrix

open MPOTensor MPSTensor

noncomputable section

namespace IsingTwist

/-- Bond dimensions of the three blocks `1, ψ, σ`. -/
def isingDim : Fin 3 → ℕ
  | 0 => 3
  | 1 => 3
  | 2 => 4

/-- The three blocks `1, ψ, σ` of the Ising matrix product operator algebra, with the `σ` block
rescaled to the source's normalization (arXiv:1511.08090, lines 1308–1312). -/
def isingBlock : (a : Fin 3) → MPOTensor 10 (isingDim a)
  | 0 => isingOne
  | 1 => isingPsi
  | 2 => (Real.sqrt 2 : ℂ)⁻¹ • isingSigma

/-- The structure constants of the Ising fusion ring (arXiv:1511.08090, lines 1312 and 1323):
`1` is the unit, `ψ × ψ = 1`, `ψ × σ = σ × ψ = σ` and `σ × σ = 1 + ψ`. -/
def isingFusion : Fin 3 → Fin 3 → Fin 3 → ℕ
  | 0, b, c => if c = b then 1 else 0
  | a, 0, c => if c = a then 1 else 0
  | 1, 1, c => if c = 0 then 1 else 0
  | 1, 2, c => if c = 2 then 1 else 0
  | 2, 1, c => if c = 2 then 1 else 0
  | 2, 2, c => if c = 2 then 0 else 1

/-- **The Ising fusion algebra** (arXiv:1511.08090, lines 1308–1312 and 1323): at every positive
system size the periodic operators of the blocks `1, ψ, σ` multiply according to the Ising
fusion rules, so they form a matrix product operator fusion algebra. The nine cases are the
products proved in `TNLean/MPS/Examples/Ising/IsingFusionAlgebra*.lean`. -/
theorem isMPOFusionAlgebra_ising : IsMPOFusionAlgebra isingBlock isingFusion := by
  intro a b L hL
  simp only [Fin.sum_univ_three]
  match a, b with
  | 0, 0 => simpa [isingBlock, isingFusion] using isingOne_mul_isingOne hL
  | 0, 1 => simpa [isingBlock, isingFusion] using isingOne_mul_isingPsi hL
  | 0, 2 => simpa [isingBlock, isingFusion] using isingOne_mul_isingSigma_normalized hL
  | 1, 0 => simpa [isingBlock, isingFusion] using isingPsi_mul_isingOne hL
  | 1, 1 => simpa [isingBlock, isingFusion] using isingPsi_mul_isingPsi hL
  | 1, 2 => simpa [isingBlock, isingFusion] using isingPsi_mul_isingSigma_normalized hL
  | 2, 0 => simpa [isingBlock, isingFusion] using isingSigma_normalized_mul_isingOne hL
  | 2, 1 => simpa [isingBlock, isingFusion] using isingSigma_normalized_mul_isingPsi hL
  | 2, 2 => simpa [isingBlock, isingFusion] using isingSigma_normalized_mul_self hL

/-- The trivial label `1` is the unit of the Ising fusion ring (arXiv:1511.08090, line 1323). -/
theorem isFusionUnit_isingFusion : IsFusionUnit isingFusion 0 := by
  intro b c
  fin_cases b <;> fin_cases c <;> simp [isingFusion]

/-- Project result: the Ising fusion ring has no fusion character in `ℕ`. A character satisfies
`m_ψ² = m_1 = 1`, hence `m_ψ = 1`, and then `m_σ² = m_1 + m_ψ = 2`, which no natural number
satisfies. -/
theorem not_isFusionCharacter_isingFusion (m : Fin 3 → ℕ) :
    ¬ IsFusionCharacter isingFusion 0 m := by
  rintro ⟨h0, hmul⟩
  have hψ := hmul 1 1
  have hσ := hmul 2 2
  simp [isingFusion, Fin.sum_univ_three, h0] at hψ hσ
  have hψ1 : m 1 = 1 := Nat.eq_one_of_mul_eq_one_right hψ
  rw [hψ1] at hσ
  have hle : m 2 ≤ 1 := by nlinarith
  interval_cases (m 2) <;> omega

/-- **No normal matrix product state is symmetric under the Ising algebra.** Project result:
there is no normal tensor of positive bond dimension whose periodic vectors are eigenvectors of
the periodic operators of the Ising blocks with length-independent eigenvalues `c`, the unit
acting trivially. It is the instance of
`MPOTensor.not_isMPOSymmetric_of_forall_not_isFusionCharacter` for the Ising ring. -/
theorem not_isMPOSymmetric_ising {D : ℕ} [NeZero D] {A : MPSTensor 10 D}
    (hA : Kraus.IsNormal A) {c : Fin 3 → ℂ} (h0 : c 0 = 1) :
    ¬ IsMPOSymmetric isingBlock A c :=
  not_isMPOSymmetric_of_forall_not_isFusionCharacter isMPOFusionAlgebra_ising
    not_isFusionCharacter_isingFusion hA h0

end IsingTwist
