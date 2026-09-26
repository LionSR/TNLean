/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Symmetry.MPOSymmetry.FusionRing
import TNLean.MPS.Symmetry.MPOSymmetry.NIMRep

/-!
# Matrix product operator symmetries: positive symmetric boundary states

**Source.** Garre-Rubio, Lootens, Molnár 2023 (arXiv:2203.12563), Section "Connection with
gapped boundaries of (2+1)d topological phases", `Papers/2203.12563/REsubmission.tex`
lines 1795–1805 (`symboundary`): for every subspace spanned by matrix product states and
invariant under the matrix product operator algebra of a fusion category, that is for every
module category, there is a periodic state `ψ = ∑_α v_α ψ_{A_α}` with positive weights `v_α`
and `O_a ψ = r_a ψ` for every label `a`, where `r_a > 0` is the spectral radius of the
multiplicity matrix `M_a`; the weights form a positive common eigenvector
`∑_α M_{a,α}^β v_α = r_a v_β`.

**Formalized here.** For a nonnegative integer representation `M` of a fusion ring
(`MPOTensor.IsFusionRing`) on which the unit acts as the identity, the vector
`v_y = ∑_{x,b} r_b M_{b,x}^y` built from the positive regular element `r` of the ring is a
positive common left eigenvector, `∑_x v_x M_{a,x}^y = d_a v_y`, with `d_a > 0` the
Perron–Frobenius dimension of `a`, and `d_a` is the spectral radius of `M_a`. For a family of
normal blocks symmetric under a matrix product operator fusion algebra with such structure
constants, the periodic state `∑_x v_x ψ_{A_x}` is a common eigenvector `O_a ψ = d_a ψ` at every
positive length. The source's fusion category enters only through its fusion ring and the unit
constraint of the module; neither indecomposability of the module nor commutativity of the
fusion ring is used.

**Scope restriction (periodic boundary):** the symmetry hypothesis is the periodic-boundary
form `MPOTensor.IsMPOSymmetricFamily` of the source's invariance of the arbitrary-boundary
subspace (lines 431–434), the form recalled at line 1801; documented in
`docs/paper-gaps/glm23_mpo_symmetric_mps_scope.tex`.

## Main results

* `MPOTensor.IsNIMRep.exists_pos_left_eigenvector`: a positive common left eigenvector of the
  multiplicity matrices with the Perron–Frobenius dimensions as eigenvalues.
* `MPOTensor.IsNIMRep.spectralRadius_eq_perronFrobeniusDim`: the spectral radius `r_a` of `M_a`
  is the Perron–Frobenius dimension `d_a`.
* `MPOTensor.IsMPOSymmetricFamily.mpo_mulVec_sum_eq_smul`: a left eigenvector of the
  multiplicities gives an eigenvector of the periodic operator.
* `MPOTensor.exists_pos_symmetric_boundary_state`: the symmetric boundary state of
  `symboundary`.

## References
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- J. Garre-Rubio, L. Lootens,
  A. Molnár, *Classifying phases protected by matrix product operator symmetries using matrix
  product states*
-/

open scoped Matrix

namespace MPOTensor

open MPSTensor

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
/-- The nonnegative integer representation identity as an identity of real matrices:
`M_b M_a = ∑_c N_{ab}^c M_c`. -/
theorem IsNIMRep.map_mul_map {N : ι → ι → ι → ℕ} {M : ι → κ → κ → ℕ} (hM : IsNIMRep N M)
    (a b : ι) :
    (Matrix.of (M b)).map ((↑) : ℕ → ℝ) * (Matrix.of (M a)).map ((↑) : ℕ → ℝ) =
      ∑ c, (N a b c : ℝ) • (Matrix.of (M c)).map ((↑) : ℕ → ℝ) := by
  ext x y
  have h := hM a b x y
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  exact_mod_cast h.symm

/-- **A positive common left eigenvector of a nonnegative integer representation.**

Source: arXiv:2203.12563, lines 1801–1803: for a module over a fusion category, "there is a
vector with positive entries such that it is the common eigenstate of all `M_a`",
`∑_α M_{a,α}^β v_α = r_a v_β`. Here the fusion category enters through its fusion ring `N`
(`MPOTensor.IsFusionRing`) and the unit constraint `M_{e,x}^y = δ_{xy}` of the module; the
eigenvalue is the Perron–Frobenius dimension `d_a`, positive by
`MPOTensor.IsFusionRing.perronFrobeniusDim_pos`, and equal to the spectral radius of `M_a` by
`MPOTensor.IsNIMRep.spectralRadius_eq_perronFrobeniusDim`. The vector is
`v_y = ∑_{x,b} r_b M_{b,x}^y` for the positive regular element `r` of the ring
(`MPOTensor.IsFusionRing.exists_pos_regular`). -/
theorem IsNIMRep.exists_pos_left_eigenvector {N : ι → ι → ι → ℕ} {e : ι} {dual : ι → ι}
    (hN : IsFusionRing N e dual) {M : ι → κ → κ → ℕ} (hM : IsNIMRep N M)
    (hunit : ∀ x y, M e x y = if x = y then 1 else 0) :
    ∃ v : κ → ℝ, (∀ x, 0 < v x) ∧
      ∀ a y, ∑ x, v x * M a x y = perronFrobeniusDim N a * v y := by
  obtain ⟨r, hr, hreg⟩ := hN.exists_pos_regular
  set Mr : ι → Matrix κ κ ℝ := fun b => (Matrix.of (M b)).map ((↑) : ℕ → ℝ) with hMr
  set S : Matrix κ κ ℝ := ∑ b, r b • Mr b with hS
  have hSM : ∀ a, S * Mr a = perronFrobeniusDim N a • S := by
    intro a
    calc S * Mr a = ∑ b, r b • ∑ c, (N a b c : ℝ) • Mr c := by
          rw [hS, Finset.sum_mul]
          exact Finset.sum_congr rfl fun b _ => by rw [Matrix.smul_mul, hM.map_mul_map a b]
      _ = ∑ c, (∑ b, r b * N a b c) • Mr c := by
          simp_rw [Finset.smul_sum, smul_smul, Finset.sum_smul]
          exact Finset.sum_comm
      _ = perronFrobeniusDim N a • S := by
          simp_rw [hreg, hS, Finset.smul_sum, smul_smul]
  refine ⟨fun y => ∑ x, S x y, fun y => ?_, fun a y => ?_⟩
  · have hSnn : ∀ x y, 0 ≤ S x y := fun x y => by
      simp only [hS, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hMr, Matrix.map_apply]
      exact Finset.sum_nonneg fun b _ => mul_nonneg (hr b).le (Nat.cast_nonneg _)
    have hyy : r e ≤ S y y := by
      have := Finset.single_le_sum (f := fun b => r b * (M b y y : ℝ))
        (fun b _ => mul_nonneg (hr b).le (Nat.cast_nonneg _)) (Finset.mem_univ e)
      simpa [hS, Matrix.sum_apply, hMr, hunit] using this
    exact (hr e).trans_le (hyy.trans (Finset.single_le_sum (fun x _ => hSnn x y)
      (Finset.mem_univ y)))
  · have h := congrFun (congrArg (fun T => (1 : κ → ℝ) ᵥ* T) (hSM a)) y
    simp only [← Matrix.vecMul_vecMul, Matrix.vecMul_smul, Pi.smul_apply, smul_eq_mul] at h
    simpa [Matrix.vecMul, dotProduct, hMr] using h

/-- **The spectral radius of `M_a` is the Perron–Frobenius dimension.**

Source: arXiv:2203.12563, line 1801: the eigenvalue `r_a` of the common positive eigenvector is
the spectral radius of the nonnegative matrix `M_a`. For a nonnegative integer representation of
a fusion ring on a nonempty set of blocks with the unit acting as the identity, it equals the
Perron–Frobenius dimension `d_a` of the fusion matrix `N_a`. -/
theorem IsNIMRep.spectralRadius_eq_perronFrobeniusDim [Nonempty κ] {N : ι → ι → ι → ℕ} {e : ι}
    {dual : ι → ι} (hN : IsFusionRing N e dual) {M : ι → κ → κ → ℕ} (hM : IsNIMRep N M)
    (hunit : ∀ x y, M e x y = if x = y then 1 else 0) (a : ι) :
    spectralRadius ℂ ((Matrix.of (M a)).map ((↑) : ℕ → ℂ)) =
      ENNReal.ofReal (perronFrobeniusDim N a) := by
  obtain ⟨v, hv, hev⟩ := hM.exists_pos_left_eigenvector hN hunit
  have hmap : (Matrix.of (M a)).map ((↑) : ℕ → ℂ) =
      ((Matrix.of (M a)).map ((↑) : ℕ → ℝ)).map ((↑) : ℝ → ℂ) := by
    ext x y; simp
  rw [hmap]
  refine Matrix.spectralRadius_map_ofReal_eq_of_pos_vecMul_eq (fun x y => by simp) hv ?_
  ext y
  simpa [Matrix.vecMul, dotProduct] using hev a y

variable {d : ℕ} {χ : ι → ℕ} {D : κ → ℕ}

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
/-- **A left eigenvector of the multiplicities gives a symmetric state.**

Source: arXiv:2203.12563, lines 1803–1805: if `∑_α M_{a,α}^β v_α = r v_β`, then
`O_a ∑_α v_α ψ_{A_α} = ∑_α v_α ∑_β M_{a,α}^β ψ_{A_β} = r ∑_β v_β ψ_{A_β}`, at every positive
length. -/
theorem IsMPOSymmetricFamily.mpo_mulVec_sum_eq_smul {O : ∀ a, MPOTensor d (χ a)}
    {A : ∀ x, MPSTensor d (D x)} {M : ι → κ → κ → ℂ} (hsym : IsMPOSymmetricFamily O A M)
    {a : ι} {v : κ → ℂ} {r : ℂ} (hv : ∀ y, ∑ x, v x * M a x y = r * v y) {L : ℕ}
    (hL : 0 < L) :
    mpo (O a) L *ᵥ (fun σ : Fin L → Fin d => ∑ x, v x * mpv (A x) σ) =
      r • fun σ : Fin L → Fin d => ∑ x, v x * mpv (A x) σ := by
  have hψ : (fun σ : Fin L → Fin d => ∑ x, v x * mpv (A x) σ) =
      ∑ x, v x • fun σ : Fin L → Fin d => mpv (A x) σ := by
    funext σ; simp [Finset.sum_apply]
  rw [hψ, Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul, hsym.mulVec_eq_sum a _ hL, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, hv]

/-- **Positive symmetric boundary state** (`symboundary`).

Source: arXiv:2203.12563, lines 1795–1805: for a family of blocks spanning a subspace invariant
under the matrix product operator algebra of a fusion category, there are positive weights
`v_x` such that `ψ = ∑_x v_x ψ_{A_x}` satisfies `O_a ψ = r_a ψ` for every label `a`, with
`r_a > 0`.

The algebra is a matrix product operator fusion algebra whose structure constants form a fusion
ring (`MPOTensor.IsFusionRing`), the fusion-ring content of the source's fusion category
(line 1236); the unit acts on the blocks as the identity, the unit constraint of the source's
module category; and the blocks are normal with linearly independent periodic vectors at one
positive length, the source's standing assumption of injective blocks (line 317). The eigenvalue
`r_a` is the Perron–Frobenius dimension `d_a`, which is also the spectral radius of the
multiplicity matrix (`MPOTensor.IsNIMRep.spectralRadius_eq_perronFrobeniusDim`). -/
theorem exists_pos_symmetric_boundary_state {O : ∀ a, MPOTensor d (χ a)} {N : ι → ι → ι → ℕ}
    (hfus : IsMPOFusionAlgebra O N) {e : ι} {dual : ι → ι} (hN : IsFusionRing N e dual)
    {A : ∀ x, MPSTensor d (D x)} {M : ι → κ → κ → ℂ} (hsym : IsMPOSymmetricFamily O A M)
    (hunit : ∀ x y, M e x y = if x = y then 1 else 0) (hA : ∀ x, Kraus.IsNormal (A x))
    (hD : ∀ x, 0 < D x) {L₀ : ℕ} (hL₀ : 0 < L₀)
    (hli : LinearIndependent ℂ fun x => fun σ : Fin L₀ → Fin d => mpv (A x) σ) :
    ∃ v : κ → ℝ, (∀ x, 0 < v x) ∧ ∀ a, 0 < perronFrobeniusDim N a ∧
      ∀ L : ℕ, 0 < L →
        mpo (O a) L *ᵥ (fun σ : Fin L → Fin d => ∑ x, (v x : ℂ) * mpv (A x) σ) =
          (perronFrobeniusDim N a : ℂ) • fun σ : Fin L → Fin d => ∑ x, (v x : ℂ) * mpv (A x) σ := by
  obtain ⟨M', hMM', hM'⟩ := exists_isNIMRep_of_isMPOSymmetricFamily hfus hsym hA hD hL₀ hli
  have hunit' : ∀ x y, M' e x y = if x = y then 1 else 0 := by
    intro x y
    have h := hunit x y
    rw [hMM'] at h
    split_ifs at h ⊢ <;> exact_mod_cast h
  obtain ⟨v, hv, hev⟩ := hM'.exists_pos_left_eigenvector hN hunit'
  refine ⟨v, hv, fun a => ⟨hN.perronFrobeniusDim_pos a, fun L hL => ?_⟩⟩
  refine hsym.mpo_mulVec_sum_eq_smul (fun y => ?_) hL
  simp_rw [hMM']
  exact_mod_cast hev a y

end MPOTensor
