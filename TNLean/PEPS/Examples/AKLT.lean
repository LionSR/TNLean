/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Trace
import TNLean.Algebra.SingletMatrix
import TNLean.PEPS.TorusSiteTensor

/-!
# AKLT: the two-dimensional AKLT state on the square lattice as a PEPS

**Source.** Cirac, Pérez-García, Schuch, Verstraete 2021 (arXiv:2011.12127), Appendix A,
"Two dimensions: PEPS", "The AKLT model", `Papers/2011.12127/TN-Review-main.tex`
lines 2432–2437: the 2D AKLT state places singlets on the links of the lattice and projects
onto the symmetric subspace at each site; absorbing the singlets
$Y=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)$ into the projectors
$\Pi_{\mathrm{sym}}$ gives, on the square lattice, the tensor
$A=\Pi_{\mathrm{sym}}(\mathbb 1\otimes\mathbb 1\otimes Y\otimes Y)$.
Review: arXiv:2011.12127, Appendix A, "The AKLT model".

**Formalized here.** The review's tensor, with the four virtual spin-1/2 legs ordered top,
right, down, left and the physical index the four-qubit label `s : Fin 4 → Fin 2` (the
`2^4 = 16` basis states of four spin-1/2, as printed):

* $\Pi_{\mathrm{sym}}=\frac1{24}\sum_{\pi\in S_4}P_\pi$ is a Hermitian projection whose
  range, the symmetric subspace of four spin-1/2 (the spin-2 space), has dimension five;
  its entries are $1/\binom{4}{k}$ between basis states of the same weight `k`;
* the explicit entries
  $A^s_{\alpha\beta\gamma\delta}=(-1)^{\gamma+\delta}\binom{4}{k}^{-1}[\lvert s\rvert=k]$,
  $k=\alpha+\beta+(1-\gamma)+(1-\delta)$;
* the physical span of the tensor is the five-dimensional symmetric subspace;
* $SU(2)$ covariance: $U^{\otimes 4}A=A(U\otimes U\otimes\bar U\otimes\bar U)$ for every
  `U` in `SU(2)`; for a general $2\times2$ matrix the two lower legs carry
  $(\operatorname{adj}U)^T$;
* on a torus of width and height at least three, the PEPS is
  $\bigotimes_v\Pi_{\mathrm{sym}}$ applied to a singlet $\lvert01\rangle-\lvert10\rangle$ on
  every edge.

**Physical space.** The physical index is the four-qubit label, so the tensor takes values
in $(\mathbb C^2)^{\otimes 4}\cong\mathbb C^{16}$, the codomain of $\Pi_{\mathrm{sym}}$ in
the printed formula. Its physical span is the five-dimensional symmetric subspace, the
spin-2 space of the source, embedded isometrically in $\mathbb C^{16}$; a tensor with
physical dimension five, obtained by composing with an isometry from the symmetric subspace
onto $\mathbb C^5$, is not defined here.

The parent Hamiltonian, the uniqueness of the ground state, the honeycomb lattice, and the
identification of $U^{\otimes 4}$ on the symmetric subspace with the standard spin-2
representation are not formalized.

**Scope restriction (torus size):** the projected-singlet formula `stateCoeff_akltPEPS` is
stated for a torus of width and height at least three sites. Documented in
`docs/paper-gaps/rmp_peps_examples_small_torus.tex`.

## Main definitions

* `TNLean.PEPS.legKronecker`: the Kronecker product of four `2 × 2` matrices on the legs.
* `TNLean.PEPS.legPermMatrix`, `TNLean.PEPS.symProjector`: the leg permutations and the
  projector $\Pi_{\mathrm{sym}}$ onto the symmetric subspace.
* `TNLean.PEPS.akltLegs`: the matrix $\mathbb 1\otimes\mathbb 1\otimes Y\otimes Y$.
* `TNLean.PEPS.akltSiteTensorFun`, `TNLean.PEPS.akltSiteTensor`, `TNLean.PEPS.akltPEPS`:
  the AKLT tensor on four-qubit labels, on `Fin 16`, and at every site of the torus.

## Main results

* `TNLean.PEPS.symProjector_mul_self`, `TNLean.PEPS.symProjector_conjTranspose`,
  `TNLean.PEPS.symProjector_apply`, `TNLean.PEPS.finrank_range_symProjector`.
* `TNLean.PEPS.akltSiteTensorFun_apply`: the explicit entries.
* `TNLean.PEPS.span_akltSiteTensorFun`: the physical span is the symmetric subspace.
* `TNLean.PEPS.akltSiteTensor_covariant`, `TNLean.PEPS.akltSiteTensor_su2_covariant`.
* `TNLean.PEPS.stateCoeff_akltPEPS`: the PEPS is the projection of edge singlets.

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped BigOperators
open Matrix

namespace TNLean
namespace PEPS

/-! ### Operators on four spin-1/2 legs -/

/-- The Kronecker product $M_0\otimes M_1\otimes M_2\otimes M_3$ of four `2 × 2` matrices,
acting on the four-qubit labels `Fin 4 → Fin 2`. -/
def legKronecker (M : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 4 → Fin 2) (Fin 4 → Fin 2) ℂ :=
  Matrix.of fun i j => ∏ k, M k (i k) (j k)

theorem legKronecker_mul (M N : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) :
    legKronecker M * legKronecker N = legKronecker fun k => M k * N k := by
  ext i l
  simp only [legKronecker, mul_apply, of_apply]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

theorem legKronecker_one : legKronecker (fun _ => 1) = 1 := by
  ext i j
  simp only [legKronecker, of_apply, one_apply, Finset.prod_boole, Finset.mem_univ,
    forall_const, funext_iff]

theorem legKronecker_transpose (M : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) :
    (legKronecker M)ᵀ = legKronecker fun k => (M k)ᵀ := by
  ext i j
  simp [legKronecker]

/-- The permutation `π` of the four legs, as the matrix with entry `1` at `(i, j)` when
`i = j ∘ π`. -/
def legPermMatrix (π : Equiv.Perm (Fin 4)) : Matrix (Fin 4 → Fin 2) (Fin 4 → Fin 2) ℂ :=
  Matrix.of fun i j => if i = j ∘ π then 1 else 0

private theorem comp_perm_eq_iff (π : Equiv.Perm (Fin 4)) (i j : Fin 4 → Fin 2) :
    i = j ∘ π ↔ j = i ∘ π.symm := by
  constructor
  · rintro rfl
    ext k
    simp
  · rintro rfl
    ext k
    simp

theorem legPermMatrix_mul (π ρ : Equiv.Perm (Fin 4)) :
    legPermMatrix π * legPermMatrix ρ = legPermMatrix (ρ * π) := by
  ext i l
  simp only [legPermMatrix, mul_apply, of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (l ∘ ρ), ite_eq_left rfl]
  · exact if_congr (by rw [Equiv.Perm.coe_mul, Function.comp_assoc]) rfl rfl
  · intro j _ hj
    rw [ite_eq_right hj]
  · simp

theorem legPermMatrix_conjTranspose (π : Equiv.Perm (Fin 4)) :
    (legPermMatrix π)ᴴ = legPermMatrix π⁻¹ := by
  ext i j
  simp only [legPermMatrix, conjTranspose_apply, of_apply]
  have h : j = i ∘ π ↔ i = j ∘ ⇑π⁻¹ := by
    rw [Equiv.Perm.inv_def]
    exact comp_perm_eq_iff π j i
  by_cases hij : i = j ∘ ⇑π⁻¹
  · rw [ite_eq_left (h.mpr hij), ite_eq_left hij, star_one]
  · rw [ite_eq_right (fun h' => hij (h.mp h')), ite_eq_right hij, star_zero]

theorem legPermMatrix_mul_legKronecker (π : Equiv.Perm (Fin 4))
    (U : Matrix (Fin 2) (Fin 2) ℂ) :
    legPermMatrix π * legKronecker (fun _ => U) =
      legKronecker (fun _ => U) * legPermMatrix π := by
  ext i l
  simp only [legPermMatrix, legKronecker, mul_apply, of_apply, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (i ∘ π.symm), Finset.sum_eq_single (l ∘ π), ite_eq_left rfl,
    ite_eq_left (by ext k; simp)]
  · rw [← Equiv.prod_comp π]
    simp
  · intro j _ hj
    rw [ite_eq_right hj]
  · simp
  · intro j _ hj
    rw [ite_eq_right fun h => hj ((comp_perm_eq_iff π i j).mp h)]
  · simp

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2433–2435.
The projector $\Pi_{\mathrm{sym}}=\frac1{24}\sum_{\pi\in S_4}P_\pi$ onto the symmetric
subspace of four spin-1/2. -/
noncomputable def symProjector : Matrix (Fin 4 → Fin 2) (Fin 4 → Fin 2) ℂ :=
  (1 / 24 : ℂ) • ∑ π : Equiv.Perm (Fin 4), legPermMatrix π

private theorem card_perm_fin_four : Fintype.card (Equiv.Perm (Fin 4)) = 24 := by
  rw [Fintype.card_perm, Fintype.card_fin]
  rfl

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2433–2435.
$\Pi_{\mathrm{sym}}$ is idempotent. -/
theorem symProjector_mul_self : symProjector * symProjector = symProjector := by
  have hsum : (∑ π : Equiv.Perm (Fin 4), legPermMatrix π) * ∑ ρ, legPermMatrix ρ =
      (24 : ℂ) • ∑ π : Equiv.Perm (Fin 4), legPermMatrix π := by
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum, legPermMatrix_mul]
    have hinner : ∀ π : Equiv.Perm (Fin 4),
        ∑ ρ : Equiv.Perm (Fin 4), legPermMatrix (ρ * π) = ∑ σ, legPermMatrix σ := fun π =>
      Fintype.sum_equiv (Equiv.mulRight π) _ _ fun _ => rfl
    simp only [hinner, Finset.sum_const, Finset.card_univ, card_perm_fin_four]
    rw [← Nat.cast_smul_eq_nsmul ℂ]
    norm_num
  rw [symProjector, smul_mul_smul_comm, hsum, smul_smul]
  norm_num

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2433–2435.
$\Pi_{\mathrm{sym}}$ is Hermitian. -/
theorem symProjector_conjTranspose : symProjectorᴴ = symProjector := by
  rw [symProjector, conjTranspose_smul, conjTranspose_sum]
  simp_rw [legPermMatrix_conjTranspose]
  rw [Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin 4))) (fun π => legPermMatrix π⁻¹)
    legPermMatrix fun _ => rfl]
  norm_num

/-- $\Pi_{\mathrm{sym}}$ commutes with every Kronecker power $U^{\otimes 4}$. -/
theorem symProjector_mul_legKronecker (U : Matrix (Fin 2) (Fin 2) ℂ) :
    symProjector * legKronecker (fun _ => U) = legKronecker (fun _ => U) * symProjector := by
  rw [symProjector, Matrix.smul_mul, Matrix.mul_smul, Finset.sum_mul, Finset.mul_sum]
  simp_rw [legPermMatrix_mul_legKronecker]

/-! ### Entries and rank of the symmetric projector -/

/-- The number of legs of a four-qubit label carrying `1`. -/
def legWeight (i : Fin 4 → Fin 2) : ℕ :=
  (Finset.univ.filter fun k => i k = 1).card

theorem card_perm_comp_eq (i j : Fin 4 → Fin 2) :
    (Finset.univ.filter fun π : Equiv.Perm (Fin 4) => i = j ∘ π).card *
        Nat.choose 4 (legWeight j) =
      if legWeight i = legWeight j then 24 else 0 := by
  revert i j
  decide

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2433–2435.
The entries of $\Pi_{\mathrm{sym}}$: $1/\binom4k$ between basis states of the same weight
`k`, and `0` otherwise. -/
theorem symProjector_apply (i j : Fin 4 → Fin 2) :
    symProjector i j =
      if legWeight i = legWeight j then 1 / (Nat.choose 4 (legWeight j) : ℂ) else 0 := by
  have hcard := card_perm_comp_eq i j
  have hchoose : (Nat.choose 4 (legWeight j) : ℂ) ≠ 0 := by
    have : legWeight j ≤ 4 := (Finset.card_le_univ _).trans (by simp)
    exact_mod_cast (Nat.choose_pos this).ne'
  simp only [symProjector, Matrix.smul_apply, Matrix.sum_apply, legPermMatrix, of_apply,
    Finset.sum_boole, smul_eq_mul]
  split_ifs with h
  · rw [h, ite_eq_left rfl] at hcard
    field_simp
    exact_mod_cast hcard
  · rw [ite_eq_right h, mul_eq_zero] at hcard
    rcases hcard with hcard | hcard
    · simp [hcard]
    · exact absurd (by exact_mod_cast hcard) hchoose

theorem choose_legWeight_dvd (i : Fin 4 → Fin 2) :
    24 / Nat.choose 4 (legWeight i) * Nat.choose 4 (legWeight i) = 24 := by
  revert i
  decide

theorem sum_div_choose_legWeight :
    ∑ i : Fin 4 → Fin 2, 24 / Nat.choose 4 (legWeight i) = 120 := by
  decide

theorem trace_symProjector : symProjector.trace = 5 := by
  have h : ∀ i, symProjector i i = ((24 / Nat.choose 4 (legWeight i) : ℕ) : ℂ) * 24⁻¹ := by
    intro i
    rw [symProjector_apply, ite_eq_left rfl]
    have hc := choose_legWeight_dvd i
    have hne : (Nat.choose 4 (legWeight i) : ℂ) ≠ 0 := by
      intro h0
      rw [Nat.cast_eq_zero] at h0
      rw [h0] at hc
      simp at hc
    field_simp
    exact_mod_cast hc.symm.trans (mul_comm _ _)
  simp only [Matrix.trace, diag_apply, h, ← Finset.sum_mul]
  rw [← Nat.cast_sum, sum_div_choose_legWeight]
  norm_num

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2432–2435.
The symmetric subspace of four spin-1/2, the range of $\Pi_{\mathrm{sym}}$, has dimension
five (the spin-2 space). -/
theorem finrank_range_symProjector :
    Module.finrank ℂ (LinearMap.range symProjector.mulVecLin) = 5 := by
  have hidem : IsIdempotentElem symProjector.mulVecLin := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul,
      symProjector_mul_self]
  have htr := (LinearMap.IsIdempotentElem.isProj_range _ hidem).trace
  rw [← Matrix.toLin'_apply', Matrix.trace_toLin'_eq, trace_symProjector] at htr
  exact_mod_cast htr.symm

/-! ### The AKLT tensor -/

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2434–2436.
The matrix $\mathbb 1\otimes\mathbb 1\otimes Y\otimes Y$ on the four virtual legs, ordered
top, right, down, left. -/
def akltLegs : Matrix (Fin 4 → Fin 2) (Fin 4 → Fin 2) ℂ :=
  legKronecker ![1, 1, singletY, singletY]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2434–2436.
The AKLT tensor $A=\Pi_{\mathrm{sym}}(\mathbb 1\otimes\mathbb 1\otimes Y\otimes Y)$, with
virtual arguments ordered top, right, down, left and the physical index a four-qubit
label. -/
noncomputable def akltSiteTensorFun (α β γ δ : Fin 2) (s : Fin 4 → Fin 2) : ℂ :=
  (symProjector * akltLegs) s ![α, β, γ, δ]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2434–2436.
The AKLT tensor with physical dimension `16 = 2^4`, the four-qubit label of the physical
index read through `finFunctionFinEquiv`. -/
noncomputable def akltSiteTensor (α β γ δ : Fin 2) (s : Fin 16) : ℂ :=
  akltSiteTensorFun α β γ δ (finFunctionFinEquiv.symm s)

variable (width height : ℕ) [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2432–2436.
The AKLT tensor at every site of the `width × height` torus. -/
noncomputable def akltPEPS : Tensor (torusGraph width height) 16 :=
  torusSiteTensor akltSiteTensor

theorem akltLegs_apply (j v : Fin 4 → Fin 2) :
    akltLegs j v = if j = ![v 0, v 1, 1 - v 2, 1 - v 3] then
      (-1) ^ ((v 2).val + (v 3).val) else 0 := by
  have hj : j = ![v 0, v 1, 1 - v 2, 1 - v 3] ↔
      j 0 = v 0 ∧ j 1 = v 1 ∧ j 2 = 1 - v 2 ∧ j 3 = 1 - v 3 := by
    simp [funext_iff, Fin.forall_fin_succ]
  simp only [akltLegs, legKronecker, of_apply, Fin.prod_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, one_apply, singletY_apply]
  by_cases h : j 0 = v 0 ∧ j 1 = v 1 ∧ j 2 = 1 - v 2 ∧ j 3 = 1 - v 3
  · obtain ⟨h0, h1, h2, h3⟩ := h
    rw [ite_eq_left (hj.mpr ⟨h0, h1, h2, h3⟩), ite_eq_left h0, ite_eq_left h1, ite_eq_left h2,
      ite_eq_left h3, pow_add]
    ring
  · rw [ite_eq_right fun h' => h (hj.mp h')]
    split_ifs <;> simp_all

theorem legWeight_vec (α β γ δ : Fin 2) :
    legWeight ![α, β, 1 - γ, 1 - δ] = α.val + β.val + (1 - γ.val) + (1 - δ.val) := by
  revert α β γ δ
  decide

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2434–2436.
The explicit entries of the AKLT tensor:
$A^s_{\alpha\beta\gamma\delta}=(-1)^{\gamma+\delta}\binom4k^{-1}[\lvert s\rvert=k]$ with
$k=\alpha+\beta+(1-\gamma)+(1-\delta)$, since $Y\lvert0)=\lvert1)$ and
$Y\lvert1)=-\lvert0)$. -/
theorem akltSiteTensorFun_apply (α β γ δ : Fin 2) (s : Fin 4 → Fin 2) :
    akltSiteTensorFun α β γ δ s =
      if legWeight s = α.val + β.val + (1 - γ.val) + (1 - δ.val) then
        (-1) ^ (γ.val + δ.val) / (Nat.choose 4 (legWeight s) : ℂ) else 0 := by
  rw [akltSiteTensorFun, mul_apply, Finset.sum_eq_single ![α, β, 1 - γ, 1 - δ]]
  · rw [akltLegs_apply, ite_eq_left (by simp), symProjector_apply, legWeight_vec]
    simp only [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
      Matrix.head_cons]
    split_ifs with h
    · rw [h]
      ring
    · simp
  · intro j _ hj
    rw [akltLegs_apply, ite_eq_right (by simpa using hj), mul_zero]
  · simp

/-! ### Physical span -/

theorem akltLegs_mul_transpose : akltLegs * akltLegsᵀ = 1 := by
  rw [akltLegs, legKronecker_transpose, legKronecker_mul, ← legKronecker_one]
  congr 1
  funext k
  fin_cases k <;> simp [singletY_mul_transpose]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2432–2436.
The physical span of the AKLT tensor, the span of the vectors $s\mapsto
A^s_{\alpha\beta\gamma\delta}$ over all virtual labels, is the symmetric subspace, the range
of $\Pi_{\mathrm{sym}}$. -/
theorem span_akltSiteTensorFun :
    Submodule.span ℂ (Set.range fun v : Fin 4 → Fin 2 =>
        fun s => akltSiteTensorFun (v 0) (v 1) (v 2) (v 3) s) =
      LinearMap.range symProjector.mulVecLin := by
  have hcol : (fun v : Fin 4 → Fin 2 => fun s => akltSiteTensorFun (v 0) (v 1) (v 2) (v 3) s) =
      (symProjector * akltLegs).col := by
    funext v s
    simp only [akltSiteTensorFun, col_apply]
    rw [show ![v 0, v 1, v 2, v 3] = v from by ext k; fin_cases k <;> rfl]
  rw [hcol, ← Matrix.range_mulVecLin, Matrix.mulVecLin_mul, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr, Submodule.map_top]
  intro x
  refine ⟨akltLegsᵀ *ᵥ x, ?_⟩
  simp [Matrix.mulVec_mulVec, akltLegs_mul_transpose]

/-! ### `SU(2)` covariance -/

/-- Project result: for every `2 × 2` matrix `U`,
$U^{\otimes4}A=A(U\otimes U\otimes V\otimes V)$ with $V=(\operatorname{adj}U)^T$, as
matrices from the virtual to the physical labels; `Y^{-1} U Y = V` moves `U` through the
singlets on the down and left legs. -/
theorem akltSiteTensor_covariant (U : Matrix (Fin 2) (Fin 2) ℂ) :
    legKronecker (fun _ => U) * (symProjector * akltLegs) =
      symProjector * akltLegs *
        legKronecker ![U, U, (adjugate U)ᵀ, (adjugate U)ᵀ] := by
  rw [← mul_assoc, ← symProjector_mul_legKronecker, mul_assoc, mul_assoc, akltLegs,
    legKronecker_mul, legKronecker_mul]
  congr 2
  funext k
  fin_cases k <;> simp [mul_singletY]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2432–2436.
`SU(2)` covariance of the AKLT tensor: for `U ∈ SU(2)`,
$U^{\otimes4}A=A(U\otimes U\otimes\bar U\otimes\bar U)$: the physical action is
$U^{\otimes 4}$, which preserves the range of `A`, and the virtual action is `U` on the top
and right legs and its entrywise conjugate on the down and left legs, which carry the
singlets. -/
theorem akltSiteTensor_su2_covariant {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    legKronecker (fun _ => U) * (symProjector * akltLegs) =
      symProjector * akltLegs * legKronecker ![U, U, U.map star, U.map star] := by
  rw [akltSiteTensor_covariant, adjugate_eq_star_of_mem_specialUnitaryGroup hU,
    star_eq_conjTranspose, conjTranspose, transpose_map, transpose_transpose]

/-! ### The AKLT PEPS as projected singlets -/

theorem akltLegs_vec (j : Fin 4 → Fin 2) (a b c d : Fin 2) :
    akltLegs j ![a, b, c, d] =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) (j 0) a * (1 : Matrix (Fin 2) (Fin 2) ℂ) (j 1) b *
        (singletY (j 2) c * singletY (j 3) d) := by
  simp only [akltLegs, legKronecker, of_apply, Fin.prod_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons]
  rw [show ![a, b, c, d] 0 = a from rfl, show ![a, b, c, d] 1 = b from rfl]
  ring

variable {width height} [Fact (2 < width)] [Fact (2 < height)]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2432–2436.
The AKLT PEPS is obtained by placing singlets on the edges and applying
$\Pi_{\mathrm{sym}}$ at every site: its coefficient at `σ` is the sum over spin-1/2 labels
`τ v` of the four legs of every site of
$\prod_v(\Pi_{\mathrm{sym}})_{\sigma_v,\tau_v}\,Y_{\tau_{v+e_1,3},\tau_{v,1}}\,
Y_{\tau_{v+e_2,2},\tau_{v,0}}$, the factor $Y_{b,a}$ being the coefficient of
$\lvert a\rangle\lvert b\rangle$ in the singlet $\lvert01\rangle-\lvert10\rangle$ on the edge from
`v` to its right or upper neighbour. Stated for width and height at least three (the
module's scope restriction on the torus size). -/
theorem stateCoeff_akltPEPS (σ : TorusVertex width height → Fin 16) :
    stateCoeff (akltPEPS width height) σ =
      ∑ τ : TorusVertex width height → Fin 4 → Fin 2,
        (∏ v, symProjector (finFunctionFinEquiv.symm (σ v)) (τ v)) *
          ∏ v, (singletY (τ (v.1 + 1, v.2) 3) (τ v 1) *
            singletY (τ (v.1, v.2 + 1) 2) (τ v 0)) := by
  rw [akltPEPS, stateCoeff_torusSiteTensor]
  simp only [akltSiteTensor, akltSiteTensorFun, mul_apply, Fintype.prod_sum]
  calc _ = ∑ τ : TorusVertex width height → Fin 4 → Fin 2,
        ∑ hb : TorusVertex width height → Fin 2, ∑ vb : TorusVertex width height → Fin 2,
          ∏ v, symProjector (finFunctionFinEquiv.symm (σ v)) (τ v) *
            akltLegs (τ v) ![vb v, hb v, vb (v.1, v.2 - 1), hb (v.1 - 1, v.2)] := by
        exact (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun τ _ => ?_
        simp only [Finset.prod_mul_distrib, ← Finset.mul_sum]
        congr 1
        simp only [akltLegs_vec]
        rw [Fintype.sum_eq_single (fun v => τ v 1), Fintype.sum_eq_single (fun v => τ v 0)]
        · simp only [one_apply_eq, one_mul, Finset.prod_mul_distrib]
          rw [mul_comm]
          congr 1
          · exact prod_torus_sub_fst fun a b => singletY (τ a 3) (τ b 1)
          · exact prod_torus_sub_snd fun a b => singletY (τ a 2) (τ b 0)
        · intro vb hvb
          obtain ⟨v, hv⟩ := Function.ne_iff.mp hvb
          exact Finset.prod_eq_zero (Finset.mem_univ v)
            (by rw [one_apply_ne (Ne.symm hv)]; ring)
        · intro hb hhb
          obtain ⟨v, hv⟩ := Function.ne_iff.mp hhb
          exact Finset.sum_eq_zero fun vb _ => Finset.prod_eq_zero (Finset.mem_univ v)
            (by rw [one_apply_ne (Ne.symm hv)]; ring)

end PEPS
end TNLean
