/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinVecEta
import TNLean.MPS.Examples.MajumdarGhoshDimer
import TNLean.MPS.Examples.SpinHalf
import TNLean.MPS.ParentHamiltonian.ChainGroundSpace

/-!
# Majumdar-Ghosh: the Hamiltonian and the dimer coverings

**Source.** Cirac, Pérez-García, Schuch, Verstraete 2021 (arXiv:2011.12127),
Appendix A, `Papers/2011.12127/TN-Review-main.tex` lines 2397–2401: the
Majumdar-Ghosh state "appears as the ground state of the spin-\(\tfrac12\)
Hamiltonian \(H=\sum \mathbf S_i\cdot\mathbf S_{i+1}+\tfrac12\sum\mathbf
S_i\cdot\mathbf S_{i+2}\)", and it is the superposition of the singlet coverings
\((1,2),(3,4),\dots\) and \((2,3),(4,5),\dots,(N,1)\).
Review: arXiv:2011.12127, Appendix A, "The Majumdar-Ghosh model".

**Formalized here.**
* The three-site local ground space \(\mathcal G_3\) of the bond-dimension-three
  tensor `majumdarGhoshTensor` equals the lowest eigenspace, with eigenvalue
  \(-\tfrac38\), of the three-site term
  \(h=\tfrac12(\mathbf S_1\cdot\mathbf S_2+\mathbf S_2\cdot\mathbf S_3
  +\mathbf S_1\cdot\mathbf S_3)\), the three-spin states without a
  component of total spin \(\tfrac32\).
* Both nearest-neighbour singlet coverings lie in the periodic three-site
  chain ground space of the tensor on every even ring of at least four sites.
* Every vector of that chain ground space, in particular each covering and the
  periodic vector of the tensor, is an eigenvector of the review's Hamiltonian
  \(H\) with eigenvalue \(-\tfrac{3N}8\).

The lower bound \(H\ge-\tfrac{3N}8\), which makes these eigenvectors ground
states, is not formalized here.

## Main definitions
* `MPSTensor.majumdarGhoshTerm` : the three-site term \(h\)
* `MPSTensor.majumdarGhoshHamiltonian` : the review's periodic Hamiltonian

## Main results
* `MPSTensor.majumdarGhosh_groundSpace_three_eq_eigenspace`
* `MPSTensor.majumdarGhosh_pairCoveringEven_mem_chainGroundSpace`,
  `MPSTensor.majumdarGhosh_pairCoveringOdd_mem_chainGroundSpace`
* `MPSTensor.majumdarGhoshHamiltonian_apply_of_mem_chainGroundSpace`
* `MPSTensor.majumdarGhoshHamiltonian_pairCoveringEven`,
  `MPSTensor.majumdarGhoshHamiltonian_pairCoveringOdd`,
  `MPSTensor.majumdarGhoshHamiltonian_mpv`

## References
- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- Cirac, Pérez-García,
  Schuch, Verstraete, *Matrix product states and projected entangled pair
  states: Concepts, symmetries, theorems*
-/

open scoped Matrix BigOperators
open Matrix Finset

noncomputable section

namespace MPSTensor

variable {d D : ℕ}

/-! ### The two coverings lie in the chain ground space -/

/-- The bond grading \(\operatorname{diag}(1,-1,-1)\), which anticommutes with
both matrices of `majumdarGhoshTensor`. -/
private def majumdarGhoshGrading : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 0, -1, 0; 0, 0, -1]

private lemma majumdarGhoshGrading_mul (i : Fin 2) :
    majumdarGhoshGrading * majumdarGhoshTensor i =
      (-1 : ℂ) • (majumdarGhoshTensor i * majumdarGhoshGrading) := by
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [majumdarGhoshGrading, majumdarGhoshTensor, Matrix.mul_apply, Fin.sum_univ_three]

private lemma majumdarGhosh_twisted_eq {N : ℕ} (hN : Even N) (hNpos : 0 < N)
    (σ : Cfg 2 N) :
    Matrix.trace (Kraus.evalWord majumdarGhoshTensor (List.ofFn σ) * majumdarGhoshGrading) =
      pairCoveringEven majumdarGhoshSinglet σ - pairCoveringOdd majumdarGhoshSinglet σ := by
  have hmpv := majumdarGhosh_mpv_eq_pairCovering hN hNpos σ
  have h00 := evalWord_apply_hub_eq_pairProduct majumdarGhoshTensor 0
    majumdarGhoshTensor_apply_eq_zero_of_ne_zero majumdarGhoshTensor_apply_zero_zero (List.ofFn σ)
  simp only [majumdarGhoshTensor_mul_apply_zero_zero] at h00
  rw [pairProduct_ofFn_eq_pairCoveringEven _ hN] at h00
  rw [mpv_eq, coeff_eq, Matrix.trace_fin_three] at hmpv
  set M := Kraus.evalWord majumdarGhoshTensor (List.ofFn σ)
  have htr : Matrix.trace (M * majumdarGhoshGrading) = M 0 0 - M 1 1 - M 2 2 := by
    simp [Matrix.trace_fin_three, majumdarGhoshGrading, Matrix.mul_apply, Fin.sum_univ_three]
    ring
  rw [htr]
  linear_combination (2 : ℂ) * h00 - hmpv

/-- Project result: on an even ring of \(N\ge L\) sites, the covering
\((1,2)(3,4)\cdots(N-1,N)\) by normalized singlets lies in the periodic chain
ground space of `majumdarGhoshTensor` for windows of length \(L\). -/
theorem majumdarGhosh_pairCoveringEven_mem_chainGroundSpace {N L : ℕ} (hN : Even N)
    (hNpos : 0 < N) (hLN : L ≤ N) :
    (pairCoveringEven majumdarGhoshSinglet : NSiteSpace 2 N) ∈
      chainGroundSpace majumdarGhoshTensor L N := by
  have hsum := Submodule.add_mem _ (mpv_mem_chainGroundSpace majumdarGhoshTensor L N hNpos hLN)
    (twistedMPV_mem_chainGroundSpace majumdarGhoshTensor majumdarGhoshGrading (-1)
      majumdarGhoshGrading_mul L N hNpos hLN)
  have h := Submodule.smul_mem _ (1 / 2 : ℂ) hsum
  convert h using 1
  ext σ
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [majumdarGhosh_twisted_eq hN hNpos, majumdarGhosh_mpv_eq_pairCovering hN hNpos]
  ring

/-- Project result: on an even ring of \(N\ge L\) sites, the covering
\((2,3)(4,5)\cdots(N,1)\) by normalized singlets lies in the periodic chain
ground space of `majumdarGhoshTensor` for windows of length \(L\). -/
theorem majumdarGhosh_pairCoveringOdd_mem_chainGroundSpace {N L : ℕ} (hN : Even N)
    (hNpos : 0 < N) (hLN : L ≤ N) :
    (pairCoveringOdd majumdarGhoshSinglet : NSiteSpace 2 N) ∈
      chainGroundSpace majumdarGhoshTensor L N := by
  have hsub := Submodule.sub_mem _ (mpv_mem_chainGroundSpace majumdarGhoshTensor L N hNpos hLN)
    (twistedMPV_mem_chainGroundSpace majumdarGhoshTensor majumdarGhoshGrading (-1)
      majumdarGhoshGrading_mul L N hNpos hLN)
  have h := Submodule.smul_mem _ (1 / 2 : ℂ) hsub
  convert h using 1
  ext σ
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [majumdarGhosh_twisted_eq hN hNpos, majumdarGhosh_mpv_eq_pairCovering hN hNpos]
  ring

/-! ### The three-site term -/

/-- The three-site Majumdar-Ghosh term
\(h=\tfrac12(\mathbf S_1\cdot\mathbf S_2+\mathbf S_2\cdot\mathbf S_3+\mathbf S_1\cdot\mathbf S_3)\).
Summed over the translates of a periodic chain of at least three sites it gives
the review's Hamiltonian, since each nearest-neighbour bond occurs in two
translates and each next-nearest-neighbour bond in one. -/
def majumdarGhoshTerm : NSiteSpace 2 3 →ₗ[ℂ] NSiteSpace 2 3 :=
  (1 / 2 : ℂ) • (spinExchange 0 1 + spinExchange 1 2 + spinExchange 0 2)

private lemma vec3_comp_swap01 (a b c : Fin 2) :
    (![a, b, c] : Fin 3 → Fin 2) ∘ Equiv.swap 0 1 = ![b, a, c] := by
  ext x; fin_cases x <;> rfl

private lemma vec3_comp_swap12 (a b c : Fin 2) :
    (![a, b, c] : Fin 3 → Fin 2) ∘ Equiv.swap 1 2 = ![a, c, b] := by
  ext x; fin_cases x <;> rfl

private lemma vec3_comp_swap02 (a b c : Fin 2) :
    (![a, b, c] : Fin 3 → Fin 2) ∘ Equiv.swap 0 2 = ![c, b, a] := by
  ext x; fin_cases x <;> rfl

/-- A three-site vector is a \(-\tfrac38\) eigenvector of the three-site term exactly
when its three transposition images sum to zero, that is, when it has no
component of total spin \(\tfrac32\). -/
private lemma majumdarGhoshTerm_eigen_iff (v : NSiteSpace 2 3) :
    majumdarGhoshTerm v = (-3 / 8 : ℂ) • v ↔
      ∀ σ : Cfg 2 3, v (σ ∘ Equiv.swap 0 1) + v (σ ∘ Equiv.swap 1 2) +
        v (σ ∘ Equiv.swap 0 2) = 0 := by
  have happ : ∀ σ, majumdarGhoshTerm v σ = (1 / 4) * (v (σ ∘ Equiv.swap 0 1) +
      v (σ ∘ Equiv.swap 1 2) + v (σ ∘ Equiv.swap 0 2)) - (3 / 8) * v σ := by
    intro σ
    simp only [majumdarGhoshTerm, LinearMap.smul_apply, LinearMap.add_apply, Pi.smul_apply,
      Pi.add_apply, smul_eq_mul]
    rw [spinExchange_apply (by decide), spinExchange_apply (by decide),
      spinExchange_apply (by decide)]
    ring
  constructor
  · intro h σ
    have := congrFun h σ
    rw [happ, Pi.smul_apply, smul_eq_mul] at this
    linear_combination 4 * this
  · intro h
    ext σ
    rw [happ, h σ, Pi.smul_apply, smul_eq_mul]
    ring

/-- The four linear conditions cutting out the spin-\(\tfrac12\) subspace of three
spins: no weight on \(|000\rangle\) or \(|111\rangle\), and vanishing sums over the
states with one or two flipped spins. -/
private lemma majumdarGhoshTerm_eigen_iff_coords (v : NSiteSpace 2 3) :
    majumdarGhoshTerm v = (-3 / 8 : ℂ) • v ↔
      v ![0, 0, 0] = 0 ∧ v ![1, 1, 1] = 0 ∧
        v ![0, 0, 1] + v ![0, 1, 0] + v ![1, 0, 0] = 0 ∧
        v ![0, 1, 1] + v ![1, 0, 1] + v ![1, 1, 0] = 0 := by
  rw [majumdarGhoshTerm_eigen_iff]
  constructor
  · intro h
    have h000 := h ![0, 0, 0]
    have h111 := h ![1, 1, 1]
    have h001 := h ![0, 0, 1]
    have h011 := h ![0, 1, 1]
    simp only [vec3_comp_swap01, vec3_comp_swap12, vec3_comp_swap02] at h000 h111 h001 h011
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination h000 / 3
    · linear_combination h111 / 3
    · linear_combination h001
    · linear_combination h011
  · rintro ⟨h000, h111, h1, h2⟩ σ
    rw [Matrix.eq_vecCons_fin_three σ]
    simp only [vec3_comp_swap01, vec3_comp_swap12, vec3_comp_swap02]
    generalize σ 0 = a, σ 1 = b, σ 2 = c
    fin_cases a <;> fin_cases b <;> fin_cases c <;> simp only [Fin.zero_eta, Fin.mk_one]
    · rw [h000]; ring
    · linear_combination h1
    · linear_combination h1
    · linear_combination h2
    · linear_combination h1
    · linear_combination h2
    · linear_combination h2
    · rw [h111]; ring

/-- Project result: the three-site local ground space \(\mathcal G_3\) of
`majumdarGhoshTensor` is the eigenspace of the three-site term \(h\) for its
lowest eigenvalue \(-\tfrac38\), the spin-\(\tfrac12\) subspace of three spins.
The review does not state this; it motivates it by saying that the state is the
ground state of \(H\) (arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex`
lines 2397–2401), and the identification is the parent-Hamiltonian route to that
claim. -/
theorem majumdarGhosh_groundSpace_three_eq_eigenspace :
    groundSpace majumdarGhoshTensor 3 =
      Module.End.eigenspace majumdarGhoshTerm (-3 / 8 : ℂ) := by
  have hX : (↑((Real.sqrt 2)⁻¹) : ℂ) * ↑(Real.sqrt 2) = 1 := by
    push_cast
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (by positivity))
  have hX2 : (↑((Real.sqrt 2)⁻¹) : ℂ) ^ 2 = 1 / 2 := by
    push_cast
    rw [inv_pow, Complex.ofReal_sqrt_sq 2 (by norm_num)]
    norm_num
  ext v
  rw [Module.End.mem_eigenspace_iff, majumdarGhoshTerm_eigen_iff_coords]
  constructor
  · rintro ⟨X, rfl⟩
    simp only [groundSpaceMap_three_apply]
    simp only [majumdarGhoshTensor, Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      Matrix.head_fin_const, Matrix.tail_cons]
    refine ⟨by ring, by ring, by ring, by ring⟩
  · rintro ⟨h000, h111, h1, h2⟩
    set s : ℂ := (↑(Real.sqrt 2) : ℂ)
    refine ⟨!![0, -2 * v ![1, 1, 0], -2 * v ![0, 0, 1]; s * v ![1, 0, 0], 0, 0;
      -s * v ![0, 1, 1], 0, 0], ?_⟩
    ext σ
    rw [Matrix.eq_vecCons_fin_three σ]
    generalize σ 0 = a, σ 1 = b, σ 2 = e
    rw [groundSpaceMap_three_apply]
    fin_cases a <;> fin_cases b <;> fin_cases e <;>
      simp only [Fin.zero_eta, Fin.mk_one, majumdarGhoshTensor, Matrix.trace_fin_three,
        Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.tail_cons,
        one_div]
    · linear_combination -h000
    · linear_combination 2 * v ![0, 0, 1] * hX2
    · linear_combination -(v ![1, 0, 0]) * hX - 2 * v ![0, 0, 1] * hX2 - h1
    · linear_combination v ![0, 1, 1] * hX
    · linear_combination v ![1, 0, 0] * hX
    · linear_combination -(v ![0, 1, 1]) * hX - 2 * v ![1, 1, 0] * hX2 - h2
    · linear_combination 2 * v ![1, 1, 0] * hX2
    · linear_combination -h111

/-! ### The periodic Hamiltonian -/

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2398–2399.
The Majumdar-Ghosh Hamiltonian
\(H=\sum_i\mathbf S_i\cdot\mathbf S_{i+1}+\tfrac12\sum_i\mathbf S_i\cdot\mathbf S_{i+2}\)
on a periodic chain of \(N\) spin-\(\tfrac12\) sites, indices modulo \(N\). -/
def majumdarGhoshHamiltonian (N : ℕ) : NSiteSpace 2 N →ₗ[ℂ] NSiteSpace 2 N :=
  ∑ i : Fin N, spinExchange i (cyclicForwardSite i 1) +
    (1 / 2 : ℂ) • ∑ i : Fin N, spinExchange i (cyclicForwardSite i 2)

private lemma cyclicForwardSite_ne {N : ℕ} (i : Fin N) {r r' : ℕ} (hr : r < N) (hr' : r' < N)
    (hne : r ≠ r') : cyclicForwardSite i r ≠ cyclicForwardSite i r' := by
  intro h
  have h1 := offset_mod_eq i.isLt hr
  have h2 := offset_mod_eq i.isLt hr'
  have hv := congrArg Fin.val h
  simp only [cyclicForwardSite] at hv
  rw [hv] at h1
  exact hne (h1.symm.trans h2)

private lemma cyclicForwardSite_one_bijective {N : ℕ} :
    Function.Bijective (fun i : Fin N => cyclicForwardSite i 1) := by
  refine Function.Injective.bijective_of_finite fun i j h => ?_
  have key : ∀ k : Fin N, cyclicForwardSite (cyclicForwardSite k 1) (N - 1) = k := by
    intro k
    rw [cyclicForwardSite_forwardSite]
    ext
    have hk := k.isLt
    simp only [cyclicForwardSite]
    rw [show k.val + (1 + (N - 1)) = k.val + N by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hk]
  rw [← key i, ← key j]
  exact congrArg (fun k => cyclicForwardSite k (N - 1)) h

/-- Filling a window with a transposed copy of its own content transposes the two
corresponding sites of the chain configuration. -/
private lemma cyclicCfg_extractWindow_comp_swap {N : ℕ} (hN : 0 < N) (hN3 : 3 ≤ N)
    (i : Fin N) (σ : Cfg 2 N) (a b : Fin 3) :
    cyclicCfg hN 3 i (extractWindow 3 i σ ∘ Equiv.swap a b) σ =
      σ ∘ Equiv.swap (cyclicForwardSite i a.val) (cyclicForwardSite i b.val) := by
  rw [Equiv.comp_swap_eq_update, Equiv.comp_swap_eq_update, ← update_cyclicCfg hN hN3,
    ← update_cyclicCfg hN hN3, cyclicCfg_extractWindow hN hN3]
  rfl

/-- Every vector of the periodic three-site chain ground space satisfies, in every
window, the three-site condition of `majumdarGhoshTerm_eigen_iff`. -/
private lemma window_swap_sum_eq_zero {N : ℕ} (hN3 : 3 ≤ N) {ψ : NSiteSpace 2 N}
    (hψ : ψ ∈ chainGroundSpace majumdarGhoshTensor 3 N) (i : Fin N) (σ : Cfg 2 N) :
    ψ (σ ∘ Equiv.swap i (cyclicForwardSite i 1)) +
      ψ (σ ∘ Equiv.swap (cyclicForwardSite i 1) (cyclicForwardSite i 2)) +
        ψ (σ ∘ Equiv.swap i (cyclicForwardSite i 2)) = 0 := by
  have hN : 0 < N := by omega
  rw [chainGroundSpace, dite_eq_left ⟨hN, hN3⟩] at hψ
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hψ
  have hmem := hψ i σ
  rw [majumdarGhosh_groundSpace_three_eq_eigenspace, Module.End.mem_eigenspace_iff,
    majumdarGhoshTerm_eigen_iff] at hmem
  have := hmem (extractWindow 3 i σ)
  simp only [cyclicRestrictₗ_apply, cyclicCfg_extractWindow_comp_swap hN hN3] at this
  simpa using this

/-- Project result: on a periodic chain of \(N\ge3\) sites, every vector of the
periodic three-site chain ground space of `majumdarGhoshTensor` is an eigenvector
of the Majumdar-Ghosh Hamiltonian with eigenvalue \(-\tfrac{3N}8\). -/
theorem majumdarGhoshHamiltonian_apply_of_mem_chainGroundSpace {N : ℕ} (hN3 : 3 ≤ N)
    {ψ : NSiteSpace 2 N} (hψ : ψ ∈ chainGroundSpace majumdarGhoshTensor 3 N) :
    majumdarGhoshHamiltonian N ψ = (-(3 * N / 8) : ℂ) • ψ := by
  ext σ
  have h1 : ∀ i : Fin N, i ≠ cyclicForwardSite i 1 := fun i => by
    simpa using cyclicForwardSite_ne i (r := 0) (r' := 1) (by omega) (by omega) (by omega)
  have h2 : ∀ i : Fin N, i ≠ cyclicForwardSite i 2 := fun i => by
    simpa using cyclicForwardSite_ne i (r := 0) (r' := 2) (by omega) (by omega) (by omega)
  have hshift : ∑ i : Fin N,
      ψ (σ ∘ Equiv.swap (cyclicForwardSite i 1) (cyclicForwardSite i 2)) =
      ∑ i : Fin N, ψ (σ ∘ Equiv.swap i (cyclicForwardSite i 1)) := by
    have := cyclicForwardSite_one_bijective.sum_comp
      (fun k : Fin N => ψ (σ ∘ Equiv.swap k (cyclicForwardSite k 1)))
    simpa [cyclicForwardSite_forwardSite] using this
  have hsum := Finset.sum_eq_zero (s := Finset.univ) fun i (_ : i ∈ Finset.univ) =>
    window_swap_sum_eq_zero hN3 hψ i σ
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hshift] at hsum
  simp only [majumdarGhoshHamiltonian, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [spinExchange_apply (h1 _), spinExchange_apply (h2 _), Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linear_combination (1 / 4 : ℂ) * hsum

/-- Project result: on an even periodic chain of \(N\ge4\) sites, the covering
\((1,2)(3,4)\cdots(N-1,N)\) by singlets is an eigenvector of the Majumdar-Ghosh
Hamiltonian with eigenvalue \(-\tfrac{3N}8\), the energy of its local terms. -/
theorem majumdarGhoshHamiltonian_pairCoveringEven {N : ℕ} (hN : Even N) (hN4 : 4 ≤ N) :
    majumdarGhoshHamiltonian N (pairCoveringEven majumdarGhoshSinglet) =
      (-(3 * N / 8) : ℂ) • pairCoveringEven majumdarGhoshSinglet :=
  majumdarGhoshHamiltonian_apply_of_mem_chainGroundSpace (by omega)
    (majumdarGhosh_pairCoveringEven_mem_chainGroundSpace hN (by omega) (by omega))

/-- Project result: on an even periodic chain of \(N\ge4\) sites, the covering
\((2,3)(4,5)\cdots(N,1)\) by singlets is an eigenvector of the Majumdar-Ghosh
Hamiltonian with eigenvalue \(-\tfrac{3N}8\). -/
theorem majumdarGhoshHamiltonian_pairCoveringOdd {N : ℕ} (hN : Even N) (hN4 : 4 ≤ N) :
    majumdarGhoshHamiltonian N (pairCoveringOdd majumdarGhoshSinglet) =
      (-(3 * N / 8) : ℂ) • pairCoveringOdd majumdarGhoshSinglet :=
  majumdarGhoshHamiltonian_apply_of_mem_chainGroundSpace (by omega)
    (majumdarGhosh_pairCoveringOdd_mem_chainGroundSpace hN (by omega) (by omega))

/-- Project result: on a periodic chain of \(N\ge3\) sites, the periodic vector of
`majumdarGhoshTensor`, which on even chains is the sum of the two singlet
coverings, is an eigenvector of the Majumdar-Ghosh Hamiltonian with eigenvalue
\(-\tfrac{3N}8\). -/
theorem majumdarGhoshHamiltonian_mpv {N : ℕ} (hN3 : 3 ≤ N) :
    majumdarGhoshHamiltonian N (mpv majumdarGhoshTensor) =
      (-(3 * N / 8) : ℂ) • (mpv majumdarGhoshTensor : NSiteSpace 2 N) :=
  majumdarGhoshHamiltonian_apply_of_mem_chainGroundSpace hN3
    (mpv_mem_chainGroundSpace majumdarGhoshTensor 3 N (by omega) hN3)

end MPSTensor

end
