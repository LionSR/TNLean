/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.Ising.IsingLetterSectorOne
import TNLean.MPS.Examples.Ising.IsingLetterSectorPsi
import TNLean.MPS.Examples.Ising.IsingLetterSectorSigmaAbelian
import TNLean.MPS.Examples.Ising.IsingLetterSectorSigmaSigma

/-!
# Weighted Ising twist: the hidden bond objects

**Source.** Construction of this development. The Ising data are those of Bultinck, Mariën,
Williamson, Sahinoglu, Haegeman and Verstraete 2017 (arXiv:1511.08090), Appendix D.2.1,
`References/1511.08090/AnyonsPEPS.tex` lines 1305–1323: the labels `1, σ, ψ` with the single
nontrivial fusion `σ × σ = 1 + ψ`, the quantum dimension `d_σ = √2`, and the nontrivial
F-symbols, among them `F^{ψσψ}_{σσσ} = -1`. The topological-symmetry operators follow Feiguin,
Trebst, Ludwig, Troyer, Kitaev, Wang and Freedman 2007 (arXiv:cond-mat/0612341),
`References/cond-mat_0612341/source/fibonacci.tex` lines 510–519, who define the operator `Y` of
the Fibonacci chain by fusing an extra anyon line into the fusion tree with the F-matrix; the
tensors here are the same construction for the Ising category. The weighted bond object, its
compression and its length-dependent coefficient are not in any source: they are motivated by
the open question of Cirac, Pérez-García, Schuch and Verstraete (arXiv:1606.00608),
`Papers/1606.00608/MPDO-22-12-17-2.tex` line 995, whether there exist renormalization fixed
points whose structure constants `c^{(L)}_{αβγ}` depend on `L`.

**Formalized here.** The three topological-symmetry tensors `A_1`, `A_ψ`, `A_σ` of the Ising
anyon chain are matrix product operators on the ten fusion-tree labels `(x', ρ, x)` with
`x ∈ x' ⊗ ρ`; their letters are the F-symbols `[F^{a x' ρ}_y]_{y' x}` of the Ising category,
and a letter vanishes unless its two labels carry the same `ρ`. The weighted bond object is
`Θ = λ_1 A_1 ⊕ λ_ψ A_ψ ⊕ λ_σ A_σ`, and the block of flag `σ` is the strand `A_σ` with `Θ`
inserted before it. This file formalises the two-object part `Θ_2 = λ_1 A_1 ⊕ λ_ψ A_ψ` of that
insertion at the point `(λ_1, λ_ψ) = (1/2, 3/10)`, scaled to the integers `5, 3`, with the `σ`
strand scaled by `√2` so that every entry lies in `ℤ[√2]`.

The stacked product `Θ_2 ⋆ (√2 A_σ)`, of bond dimension `24`, compresses onto two weighted
copies of the *same* normal tensor `√2 A_σ`, with the weights `5` and `3`, and sixteen zero
slots. The two hidden bond objects `1` and `ψ` both feed the visible channel `σ` through the
fusions `1 ⊗ σ = σ` and `ψ ⊗ σ = σ`, with different weights: on a ring of length `L` the
coefficient of the `σ` strand is the power sum `λ_1^L + λ_ψ^L`, which depends on `L`. The gauge
is a signed permutation of the bond coordinates whose rows are the F-move isometries of the two
fusions; its single sign is the F-symbol `[F^{ψσψ}_σ] = -1` of the `ψ` line. The conjugated
tensor is block diagonal for every letter, so the remainder vanishes and the extension splits.

The tensors and their normality are in `IsingTensors`, the bond object, the gauge and the
sector reduction of the letters in `IsingGauge`, and the four exhaustive sector checks of the
letter identity in `IsingLetterSectorOne`, `IsingLetterSectorPsi`,
`IsingLetterSectorSigmaAbelian` and `IsingLetterSectorSigmaSigma`. This file assembles them into
the letter identity, the compression datum and its consequences.

## Main results

* `IsingTwist.isingGaugeZ_conj`: the letter identity over `ℤ√2`.
* `IsingTwist.isingCompression`: the multi-block compression datum with two weighted slots and
  sixteen zero slots.
* `IsingTwist.isingBondObject_trace_evalWord`: the word-trace identity
  `tr(B^w) = (5^{|w|} + 3^{|w|}) tr((√2 A_σ)^w)`.
* `IsingTwist.isingTwist_mpo`: the periodic-operator identity
  `O_L(Θ_2) O_L(√2 A_σ) = (5^L + 3^L) O_L(√2 A_σ)` at every positive length.
* `IsingTwist.isingBondObject_remainder`: the remainder vanishes, so the extension splits.

## References

- [arXiv:1511.08090](https://arxiv.org/abs/1511.08090) -- N. Bultinck, M. Mariën,
  D. J. Williamson, M. B. Sahinoglu, J. Haegeman, F. Verstraete, *Anyons and matrix product
  operator algebras*
- [arXiv:cond-mat/0612341](https://arxiv.org/abs/cond-mat/0612341) -- A. Feiguin, S. Trebst,
  A. W. W. Ludwig, M. Troyer, A. Kitaev, Z. Wang, M. H. Freedman, *Interacting anyons in
  topological quantum liquids: The golden chain*
- [arXiv:1606.00608](https://arxiv.org/abs/1606.00608) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product density operators: Renormalization fixed points and
  boundary theories*

## Provenance

The example instantiates the multi-block asymmetric compression theorem of
`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`
(`thm:p5-asymmetric-compression`, §7.5, Theorem 7.7), for the sitewise content of the weighted
Ising bond-object twist of
`Notes/OpenProblemsTN/problems/p6_rfp_structure_constant_l_dependence.tex`
(`thm:p6-round45-fusion`, whose items (v)–(vi) give the fusion operator
`χ_{σσ1} = diag(λ_1, λ_ψ)/ν` with two distinct eigenvalues); the point `(1/2, 3/10)` is the
generic point of the P6 numerics. The exact data, the conventions and the dictionary of labels
are recorded in `Notes/OpenProblemsTN/checks/asym_ising_action_data.md`, §1, and verified by
`checks/asym_ising_action_verify.py`. These files are verification records, not the source.
-/

open scoped Matrix Kronecker

namespace IsingTwist

open MPSTensor Zsqrtd

/-! ### The letter identity

The conjugated letter is computed sector by sector: for a letter `(h, h')` with
`ρ(h) = ρ(h') = r`, the conjugated stacked product is the sector matrix `conjSector r h h'`,
whose identity with the prescribed block diagonal matrix is decided in the four sector files;
letters with `ρ(h) ≠ ρ(h')` vanish on both sides.
-/

/-- **The letter identity over `ℤ√2`** (data file §1.3, check T2-G3): in the block coordinates,
every letter of the stacked product is block diagonal with the blocks `5 (√2 A_σ)`, `3 (√2 A_σ)`
and sixteen zeros. -/
theorem isingGaugeZ_conj (h h' : Fin 10) :
    (isingGaugeZ * mulZsqrt2Tensor thetaTwoZ isingSigmaZ h h' * isingGaugeZᵀ).submatrix
        isingTau isingTau =
      Matrix.blockDiagonal' (isingBlockZ (isingSigmaZ h h')) := by
  rw [isingGaugeZ, signedPermMatrix_mul_mul_transpose]
  rcases eq_or_ne (isingRho h) (isingRho h') with hρ | hρ
  · rw [stack_eq_sector]
    have h3 : ∀ r : Fin 3, r = 0 ∨ r = 1 ∨ r = 2 := by decide
    rcases h3 (isingRho h) with hr | hr | hr
    · rw [hr]; exact conjSector_eq_blockDiagonal_of_rho_zero h h' hr (hρ.symm.trans hr)
    · rw [hr]; exact conjSector_eq_blockDiagonal_of_rho_one h h' hr (hρ.symm.trans hr)
    · rw [hr]
      rcases lt_or_ge h.val 8 with hh | hh
      · exact conjSector_eq_blockDiagonal_of_rho_two_of_lt h h' hr (hρ.symm.trans hr) hh
      · exact conjSector_eq_blockDiagonal_of_rho_two_of_le h h' hr (hρ.symm.trans hr) hh
  · rw [stack_eq_zero_of_rho_ne hρ, isingSigmaZ_eq_zero_of_rho_ne h h' hρ, isingBlockZ_zero,
      Matrix.blockDiagonal'_zero]
    refine Matrix.ext fun x y => ?_
    simp

theorem isingBondObject_conjMatrix (a : Fin 100) :
    conjMatrix isingGauge (isingBondObject a) =
      complexOfZsqrt2 (Matrix.blockDiagonal' (isingBlockZ (isingSigmaZ
        (Fin.divNat (m := 10) (n := 10) a) (Fin.modNat (m := 10) (n := 10) a)))) := by
  rw [isingGauge, conjMatrix_gaugeOfMatrix, isingBondObject_eq, ← complexOfZsqrt2_mul,
    ← complexOfZsqrt2_mul, ← complexOfZsqrt2_submatrix, isingBondObjectZ, isingGaugeZ_conj]

/-! ### The compression datum -/

/-- **The multi-block asymmetric compression datum of the Ising bond-object twist** (P5 note,
Theorem 7.7(i)–(iii); data file §1.2–1.3): two weighted copies of the normal tensor `√2 A_σ`,
with the weights `5` and `3`, and sixteen zero slots. -/
noncomputable def isingCompression :
    MultiBlockCompression isingBondObject isingSlots isingTargets where
  z := 16
  ord := isingOrd
  gauge := isingGauge
  triangular a x y h := by
    have h' : isingOrd y.1 < isingOrd x.1 := h
    have hxy : x.1 ≠ y.1 := fun e => by rw [e] at h'; exact lt_irrefl _ h'
    rw [isingBondObject_conjMatrix, complexOfZsqrt2_apply, Matrix.blockDiagonal'_apply_ne _ _ _ hxy,
      map_zero]
  matched a s := by
    rw [isingBondObject_conjMatrix, complexOfZsqrt2, complexOfRing, Matrix.blockDiag'_map,
      Matrix.blockDiag'_blockDiagonal']
    ext p q
    simp [isingBlockZ, isingTargets, isingSigma, MPOTensor.toMPSTensor,
      zsqrt2ToComplex_isingWeightsZ]
  unmatched a t := by
    rw [isingBondObject_conjMatrix, complexOfZsqrt2, complexOfRing, Matrix.blockDiag'_map,
      Matrix.blockDiag'_blockDiagonal']
    ext p q
    simp [isingBlockZ]

/-- **The remainder of the Ising bond-object compression vanishes** (P5 note, Theorem 7.7(vi);
data file §1.3, check T2-G6): the conjugated letters are block diagonal, so the extension
splits. -/
theorem isingBondObject_remainder : isingCompression.remainder = 0 := by
  funext a
  have h : conjMatrix isingGauge (isingCompression.remainder a) =
      conjMatrix isingGauge (isingBondObject a) -
        Matrix.blockDiagonal' (conjMatrix isingGauge (isingBondObject a)).blockDiag' :=
    isingCompression.conjMatrix_remainder a
  refine conjMatrix_injective isingGauge ?_
  rw [h, Pi.zero_apply, conjMatrix_zero, sub_eq_zero, isingBondObject_conjMatrix,
    complexOfZsqrt2, complexOfRing,
    Matrix.blockDiagonal'_map _ _ (map_zero _), Matrix.blockDiag'_blockDiagonal']

/-! ### Consequences -/

/-- **The word-trace identity of the Ising bond-object twist** (data file §1.2, check T2-G5):
the periodic coefficient of the `σ` strand is the power sum `5^L + 3^L` of the two weights, the
sitewise origin of the length-dependent coefficient `λ_1^L + λ_ψ^L` of the P6 twist
(`thm:p6-round45-fusion` (v)–(vi)). -/
theorem isingBondObject_trace_evalWord (w : List (Fin 100)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord isingBondObject w) =
      ((5 : ℂ) ^ w.length + 3 ^ w.length) *
        Matrix.trace (Kraus.evalWord isingSigma.toMPSTensor w) := by
  have h := isingCompression.trace_evalWord_eq_sum w hw
  have hs : ∀ s : Fin 2,
      Matrix.trace (Kraus.evalWord (isingTargets s) w) =
        isingWeights s ^ w.length * Matrix.trace (Kraus.evalWord isingSigma.toMPSTensor w) := by
    intro s
    rw [isingTargets, show isingWeights s • isingSigma.toMPSTensor =
        fun i => isingWeights s • isingSigma.toMPSTensor i from rfl,
      Kraus.evalWord_smul, Matrix.trace_smul, smul_eq_mul]
  rw [h, show isingSlots = Finset.univ from rfl, Fin.sum_univ_two, hs 0, hs 1]
  simp only [isingWeights, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **The weighted bond object acting on the `σ` strand** (data file §1.2 and §1.5): at every
positive length, the periodic operator of `Θ_2 = 5 A_1 ⊕ 3 A_ψ` composed with the periodic
operator of `√2 A_σ` is `5^L + 3^L` times the latter. The two hidden bond objects feed the same
visible channel with different weights, and their power sum is the length-dependent coefficient
of the P6 twist (`thm:p6-round45-fusion` (v)–(vi)). -/
theorem isingTwist_mpo (L : ℕ) (hL : 0 < L) :
    MPOTensor.mpo thetaTwo L * MPOTensor.mpo isingSigma L =
      ((5 : ℂ) ^ L + 3 ^ L) • MPOTensor.mpo isingSigma L := by
  rw [← MPOTensor.mpo_mulTensor]
  ext σ τ
  have hw : (List.ofFn fun k => finProdFinEquiv (σ k, τ k)) ≠ [] := by
    simp only [ne_eq, List.ofFn_eq_nil_iff]
    omega
  have h := isingBondObject_trace_evalWord (List.ofFn fun k => finProdFinEquiv (σ k, τ k)) hw
  unfold isingBondObject at h
  rw [MPOTensor.evalWord_toMPSTensor_pairConfig, MPOTensor.evalWord_toMPSTensor_pairConfig] at h
  simpa [MPOTensor.mpoMatrixEntry] using h

/-- The Ising bond-object compression has sixteen zero slots. -/
theorem isingBondObject_z_eq : isingCompression.z = 16 := rfl

/-- **The dimension count** `24 = 4 + 4 + 16` (P5 note, Theorem 7.7(vii)). -/
theorem isingBondObject_dim_eq : (24 : ℕ) = ∑ _s ∈ isingSlots, 4 + 16 :=
  isingCompression.dim_eq

end IsingTwist
