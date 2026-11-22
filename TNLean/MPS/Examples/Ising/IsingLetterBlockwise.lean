/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.Ising.IsingGauge

/-!
# The Ising sector letters, read off block by block

**Source.** Construction of this development. The weighted bond object `Θ_2 = 5 A_1 ⊕ 3 A_ψ`
of `IsingGauge` is block diagonal, and the letter `(h, j)` of `A_1` vanishes unless `j = h`,
while the letter `(h, j)` of `A_ψ` vanishes unless `j` is the label obtained from `h` by fusing
`ψ` into both outer labels. The Ising fusion rules entering this are those of Bultinck, Mariën,
Williamson, Sahinoglu, Haegeman and Verstraete 2017 (arXiv:1511.08090), Appendix D.2.1,
`References/1511.08090/AnyonsPEPS.tex` lines 1305–1323.

**Formalized here.** In the sector `r = ρ(h)`, every entry of the stacked letter
`Θ_2 ⋆ (√2 A_σ)` at `(h, h')` is therefore a single product: on the `P_1` block it is
`5 [A_1]_{hh} [√2 A_σ]_{hh'}`, on the `P_ψ` block it is `3 [A_ψ]_{h ψh} [√2 A_σ]_{ψh, h'}`,
and it vanishes off the two blocks. The four sector checks of the letter identity
(`IsingLetterSectorOne`, `IsingLetterSectorPsi`, `IsingLetterSectorSigmaAbelian` and
`IsingLetterSectorSigmaSigma`) decide the letters in this form instead of summing over the ten
middle labels.

## Main definitions

* `IsingTwist.isingPsiPartner`: the label `(ψ ⊗ x', ρ, ψ ⊗ x)` attached to `(x', ρ, x)`.
* `IsingTwist.stackBlockwise`, `IsingTwist.conjBlockwise`: the stacked letter and its conjugate
  in the block coordinates, one product per entry.

## Main results

* `IsingTwist.stackSector_eq_stackBlockwise`, `IsingTwist.conjSector_eq_conjBlockwise`: in the
  sector of the left label, the sector matrices are the blockwise ones.

## References

- [arXiv:1511.08090](https://arxiv.org/abs/1511.08090) -- N. Bultinck, M. Mariën,
  D. J. Williamson, M. B. Sahinoglu, J. Haegeman, F. Verstraete, *Anyons and matrix product
  operator algebras*
-/

namespace IsingTwist

open MPSTensor Zsqrtd

/-- The label `(ψ ⊗ x', ρ, ψ ⊗ x)` attached to the label `(x', ρ, x)`, with `ψ ⊗ σ = σ`: the
only label `j` for which the letter `(h, j)` of `A_ψ` can be nonzero. -/
def isingPsiPartner : Fin 10 → Fin 10 := ![3, 4, 5, 0, 1, 2, 6, 7, 9, 8]

theorem isingOneZ_eq_zero_of_ne : ∀ h j : Fin 10, j ≠ h → isingOneZ h j = 0 := by
  decide +kernel

theorem isingPsiZ_eq_zero_of_ne :
    ∀ h j : Fin 10, j ≠ isingPsiPartner h → isingPsiZ h j = 0 := by
  decide +kernel

theorem isingRho_isingPsiPartner : ∀ h : Fin 10, isingRho (isingPsiPartner h) = isingRho h := by
  decide

/-- One entry of the stacked letter `(h, h')`, indexed by the block coordinates of `Θ_2` and the
coordinates of `P_σ`: a single product on each diagonal block of `Θ_2`, zero off them. -/
def blockwiseEntry (h h' : Fin 10) : Fin 3 ⊕ Fin 3 → Fin 3 ⊕ Fin 3 → Fin 4 → Fin 4 → ℤ√2
  | .inl i, .inl i', k, k' => 5 * isingOneZ h h i i' * isingSigmaZ h h' k k'
  | .inr i, .inr i', k, k' =>
      3 * isingPsiZ h (isingPsiPartner h) i i' * isingSigmaZ (isingPsiPartner h) h' k k'
  | _, _, _, _ => 0

/-- The stacked letter `(h, h')` in the bond order of `stackSector`, one product per entry. -/
def stackBlockwise (h h' : Fin 10) : Matrix (Fin 24) (Fin 24) (ℤ√2) :=
  Matrix.of fun a b =>
    let p := (finProdFinEquiv (m := 6) (n := 4)).symm a
    let q := (finProdFinEquiv (m := 6) (n := 4)).symm b
    blockwiseEntry h h' ((finSumFinEquiv (m := 3) (n := 3)).symm p.1)
      ((finSumFinEquiv (m := 3) (n := 3)).symm q.1) p.2 q.2

theorem stackSector_eq_stackBlockwise {r : Fin 3} {h : Fin 10} (hr : isingRho h = r)
    (h' : Fin 10) : stackSector r h h' = stackBlockwise h h' := by
  refine Matrix.ext fun a b => ?_
  simp only [stackSector, stackBlockwise, Matrix.submatrix_apply, Matrix.sum_apply,
    Matrix.of_apply]
  generalize (finProdFinEquiv (m := 6) (n := 4)).symm a = p
  generalize (finProdFinEquiv (m := 6) (n := 4)).symm b = q
  obtain ⟨i, k⟩ := p
  obtain ⟨i', k'⟩ := q
  obtain ⟨s, rfl⟩ := (finSumFinEquiv (m := 3) (n := 3)).surjective i
  obtain ⟨s', rfl⟩ := (finSumFinEquiv (m := 3) (n := 3)).surjective i'
  have hterm : ∀ j : Fin 10, (if isingRho j = r then
      Matrix.kronecker (thetaTwoZ h j) (isingSigmaZ j h') else 0) (finSumFinEquiv s, k)
        (finSumFinEquiv s', k') = if isingRho j = r then
      Matrix.fromBlocks ((5 : ℤ√2) • isingOneZ h j) 0 0 ((3 : ℤ√2) • isingPsiZ h j) s s' *
        isingSigmaZ j h' k k' else 0 := by
    intro j
    split_ifs <;> simp [thetaTwoZ, Matrix.kronecker]
  simp only [Matrix.kronecker] at hterm
  rw [Finset.sum_congr rfl fun j _ => hterm j, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases s with i | i <;> rcases s' with i' | i'
  · rw [Finset.sum_eq_single h]
    · simp [blockwiseEntry, hr, mul_assoc]
    · intro j _ hj
      simp [isingOneZ_eq_zero_of_ne h j hj]
    · simp
  · simp [blockwiseEntry]
  · simp [blockwiseEntry]
  · rw [Finset.sum_eq_single (isingPsiPartner h)]
    · simp [blockwiseEntry, isingRho_isingPsiPartner, hr, mul_assoc]
    · intro j _ hj
      simp [isingPsiZ_eq_zero_of_ne h j hj]
    · simp

/-- The conjugated stacked letter `(h, h')` in the block coordinates, one product per entry. -/
def conjBlockwise (h h' : Fin 10) :
    Matrix (BlockSpace isingBlockDim isingSlots 16) (BlockSpace isingBlockDim isingSlots 16)
      (ℤ√2) :=
  (Matrix.of fun x y =>
    isingSign x * stackBlockwise h h' (isingPerm x) (isingPerm y) * isingSign y).submatrix
    isingTau isingTau

theorem conjSector_eq_conjBlockwise {r : Fin 3} {h : Fin 10} (hr : isingRho h = r)
    (h' : Fin 10) : conjSector r h h' = conjBlockwise h h' := by
  rw [conjSector, conjBlockwise, stackSector_eq_stackBlockwise hr]

end IsingTwist
