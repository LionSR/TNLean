/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.PhysicalRotation
import TNLean.MPS.Core.ScaledNormality
import TNLean.MPS.Examples.AKLTParentHamiltonian
import TNLean.MPS.Examples.AKLTRotation
import TNLean.MPS.SharedInfra.Scaling
import TNLean.MPS.Symmetry.SymmetricMPS

/-!
# AKLT: the review's singlet-bond tensor and its Pauli form

**Source.** Affleck, Kennedy, Lieb, Tasaki 1987 (the AKLT construction), as presented in
Cirac, Pérez-García, Schuch, Verstraete 2021 (arXiv:2011.12127), Appendix A, "The AKLT
state", `Papers/2011.12127/TN-Review-main.tex` lines 2372–2393: the review prints the
tensor `A^{+1} = diag(1,0) Y`, `A^0 = (1/√2) σ_x Y`, `A^{-1} = diag(0,1) Y` with the
singlet `Y = [[0,-1],[1,0]]` (`eq:app:singlet-Y`), and states that in the physical basis
`|+⟩ = i(|-1⟩+|+1⟩)/√2`, `|-⟩ = (|-1⟩-|+1⟩)/√2`, `|0⟩` it becomes
`A^- = σ_x/√2`, `A^+ = σ_y/√2`, `A^0 = σ_z/√2`.
Review: arXiv:2011.12127, Appendix A, "The AKLT state".

**Formalized here.** The review's tensor in its own normalization, with the physical
labels ordered `S_z = 0, +1, -1` as the review lists them; each matrix is a spin-`1`
state of two spin-`½` particles, written as a symmetric coefficient matrix, times `Y`.
The basis in the review's display is orthonormal, and the coordinates of the state in it
are computed exactly with `rotatePhysical` by the adjoint of the basis matrix. They give
`A^- = σ_x/√2` and `A^0 = σ_z/√2` as printed, and `A^+ = -σ_y/√2`. The triple
`(σ_x, -σ_y, σ_z)` is `-σ_y (σ_x, σ_y, σ_z) σ_y`, so in the printed basis the tensor is
the virtual gauge by `σ_y` of `-1` times the printed Pauli form, and the two states differ
by the global sign `(-1)^N`. The printed `A^+ = σ_y/√2` holds exactly in the basis whose
vector `|+⟩` carries the phase `-i` in place of `i`. The review's tensor is a nonzero scalar
multiple of a virtual gauge transform of `akltTensor`, and its Pauli form is a scalar
multiple of `akltCartesian`; normality, the `Z₂ × Z₂` symmetry with its anticommuting
virtual gauges (the non-trivial SPT class), the `SO(3)` symmetry of the Pauli form, and
the unique ground state of the two-site parent Hamiltonian transfer.

**Local fix (sign of `A^+`):** in the basis printed by the review the `|+⟩` component of
the tensor is `-σ_y/√2`, not `σ_y/√2`. The printed Pauli form holds up to the virtual gauge
`σ_y` and the scalar `-1`, hence for the state up to the global sign `(-1)^N`, and exactly
for `|+⟩ = -i(|-1⟩+|+1⟩)/√2`. Documented in
`docs/paper-gaps/rmp_aklt_pauli_basis_sign.tex`.

## Main definitions
* `MPSTensor.rmpSingletY` : the singlet matrix `Y` of `eq:app:singlet-Y`
* `MPSTensor.akltRMPSpinOneState` : the three spin-`1` states as coefficient matrices
* `MPSTensor.akltTensorRMP` : the review's AKLT tensor
* `MPSTensor.akltRMPBasis` : the review's basis `|-⟩, |+⟩, |0⟩`
* `MPSTensor.akltRMPBasisFixed` : the same basis with the phase of `|+⟩` conjugated
* `MPSTensor.akltTensorRMPPauli` : the printed Pauli form `σ_i/√2`

## Main results
* `MPSTensor.rotatePhysical_akltRMPBasis` : the review's basis gives
  `(σ_x, -σ_y, σ_z)/√2`
* `MPSTensor.akltTensorRMPPauli_neg_gaugeEquiv` : this is the `σ_y` gauge of `-1` times the
  printed Pauli form
* `MPSTensor.mpv_rotatePhysical_akltRMPBasis` : so the state coefficients in the review's
  basis are `(-1)^N` times those of the printed Pauli form
* `MPSTensor.rotatePhysical_akltRMPBasisFixed` : the conjugated basis gives the
  printed Pauli form exactly
* `MPSTensor.akltTensorRMP_gaugeEquiv` : bridge to `akltTensor`
* `MPSTensor.akltTensorRMP_isNormal`, `MPSTensor.akltTensorRMP_isOnSiteSymmetric_Z2Z2`,
  `MPSTensor.akltTensorRMP_virtual_projRep`, `MPSTensor.akltTensorRMPPauli_isOnSiteSymmetric_SO3`,
  `MPSTensor.akltTensorRMP_parentHamiltonian_two_unique_gs`

## References
- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
- I. Affleck, T. Kennedy, E. H. Lieb, H. Tasaki, *Rigorous results on valence-bond ground
  states in antiferromagnets*, Phys. Rev. Lett. 59, 799 (1987)
-/

open scoped Matrix BigOperators
open Matrix Finset

noncomputable section

namespace MPSTensor

/-! ### The review's tensor -/

/-- Source: arXiv:2011.12127, `eq:app:singlet-Y`, `Papers/2011.12127/TN-Review-main.tex`
lines 2380–2385. The singlet matrix `Y = [[0,-1],[1,0]]`. -/
def rmpSingletY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2372–2378. The
three spin-`1` states `|↑↑⟩`, `(|↑↓⟩+|↓↑⟩)/√2`, `|↓↓⟩` of two spin-`½` particles, written as
coefficient matrices; the physical label `0, 1, 2` stands for `S_z = 0, +1, -1`, the order
in which the review lists the labels. -/
def akltRMPSpinOneState : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![Complex.invSqrtTwo • !![0, 1; 1, 0], !![1, 0; 0, 0], !![0, 0; 0, 1]]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2372–2385. The
review's AKLT tensor `A^{+1} = diag(1,0) Y`, `A^0 = (1/√2) σ_x Y`, `A^{-1} = diag(0,1) Y`,
with physical labels `0, 1, 2` for `S_z = 0, +1, -1`. -/
def akltTensorRMP : MPSTensor 3 2 := fun s => akltRMPSpinOneState s * rmpSingletY

private lemma sqrt2_ne_zero : (↑(Real.sqrt 2) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'

private lemma sqrt3_ne_zero : (↑(Real.sqrt 3) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)).ne'

@[simp] private lemma conj_invSqrtTwo :
    (starRingEnd ℂ) Complex.invSqrtTwo = Complex.invSqrtTwo :=
  Complex.star_invSqrtTwo

/-- Source: arXiv:2011.12127, lines 2374–2378. `A^0 = σ_z/√2`. -/
lemma akltTensorRMP_zero :
    akltTensorRMP 0 = Complex.invSqrtTwo • !![1, 0; 0, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [akltTensorRMP, akltRMPSpinOneState, rmpSingletY, Matrix.mul_apply]

/-- Source: arXiv:2011.12127, lines 2374–2378. `A^{+1} = -|0⟩⟨1|`. -/
lemma akltTensorRMP_one : akltTensorRMP 1 = !![0, -1; 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [akltTensorRMP, akltRMPSpinOneState, rmpSingletY, Matrix.mul_apply]

/-- Source: arXiv:2011.12127, lines 2374–2378. `A^{-1} = |1⟩⟨0|`. -/
lemma akltTensorRMP_two : akltTensorRMP 2 = !![0, 0; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [akltTensorRMP, akltRMPSpinOneState, rmpSingletY, Matrix.mul_apply]

/-- Project result: the three coefficient matrices are symmetric, so they are states of the
symmetric (spin-`1`) subspace of two spin-`½` particles (arXiv:2011.12127, lines 2372–2373,
"projecting the two spin-`½` at each site on the joint spin-`1` subspace"). -/
theorem akltRMPSpinOneState_transpose (s : Fin 3) :
    (akltRMPSpinOneState s)ᵀ = akltRMPSpinOneState s := by
  fin_cases s <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [akltRMPSpinOneState]

/-- Project result: the three spin-`1` states are orthonormal in the Hilbert–Schmidt inner
product, so the map to the physical site is an isometric embedding of the spin-`1`
subspace (arXiv:2011.12127, lines 2372–2373). -/
theorem akltRMPSpinOneState_orthonormal (s t : Fin 3) :
    ((akltRMPSpinOneState s)ᴴ * akltRMPSpinOneState t).trace = if s = t then 1 else 0 := by
  have h := Complex.invSqrtTwo_mul_self
  fin_cases s <;> fin_cases t <;>
    simp [akltRMPSpinOneState, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals linear_combination 2 * h

/-! ### The review's physical basis

The coordinates of a tensor in the orthonormal physical basis whose `a`-th vector is the
column `V · a` are `B^a = ∑_s conj(V_{s a}) A^s`, that is `rotatePhysical Vᴴ A`; by
`mpv_rotatePhysical` its state coefficients are the inner products of the state of `A` with
the corresponding product vectors. -/

/-- Source: arXiv:2011.12127, lines 2386–2388. The review's physical basis, as columns
over the labels `S_z = 0, +1, -1`: the column `0` is `|-⟩ = (|-1⟩-|+1⟩)/√2`, the column
`1` is `|+⟩ = i(|-1⟩+|+1⟩)/√2`, and the column `2` is `|0⟩`. -/
def akltRMPBasis : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 1;
    -Complex.invSqrtTwo, Complex.I * Complex.invSqrtTwo, 0;
    Complex.invSqrtTwo, Complex.I * Complex.invSqrtTwo, 0]

/-- Bridge: the review's basis with the phase of `|+⟩` conjugated,
`|+⟩ = -i(|-1⟩+|+1⟩)/√2`; this is the basis in which the printed Pauli form holds. -/
def akltRMPBasisFixed : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 1;
    -Complex.invSqrtTwo, -Complex.I * Complex.invSqrtTwo, 0;
    Complex.invSqrtTwo, -Complex.I * Complex.invSqrtTwo, 0]

/-- Source: arXiv:2011.12127, lines 2386–2388. The review's basis is orthonormal. -/
theorem akltRMPBasis_mem_unitaryGroup : akltRMPBasis ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [akltRMPBasis, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals grind [Complex.I_sq, Complex.invSqrtTwo_mul_self]

/-- Bridge: the conjugated basis is orthonormal. -/
theorem akltRMPBasisFixed_mem_unitaryGroup :
    akltRMPBasisFixed ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [akltRMPBasisFixed, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals grind [Complex.I_sq, Complex.invSqrtTwo_mul_self]

/-- Source: arXiv:2011.12127, lines 2389–2393, the printed Pauli form
`A^- = σ_x/√2`, `A^+ = σ_y/√2`, `A^0 = σ_z/√2`, with the labels `0, 1, 2` for `-, +, 0`.
It is `akltCartesian` scaled by `1/√2`. -/
def akltTensorRMPPauli : MPSTensor 3 2 := Complex.invSqrtTwo • akltCartesian

/-- Source: arXiv:2011.12127, lines 2386–2393, with the **Local fix (sign of `A^+`)** of the
module docstring. In the review's basis the tensor becomes `A^- = σ_x/√2`,
`A^+ = -σ_y/√2`, `A^0 = σ_z/√2`: the printed Pauli form with the sign of the `|+⟩`
component reversed, which is its `σ_y` gauge times `-1`
(`akltTensorRMPPauli_neg_gaugeEquiv`). -/
theorem rotatePhysical_akltRMPBasis :
    rotatePhysical akltRMPBasisᴴ akltTensorRMP =
      fun a => (if a = 1 then -1 else 1 : ℂ) • akltTensorRMPPauli a := by
  funext a
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [rotatePhysical, Matrix.conjTranspose_apply, akltRMPBasis, akltTensorRMPPauli,
      Fin.sum_univ_three,
      akltTensorRMP_zero, akltTensorRMP_one, akltTensorRMP_two, SpinCover.pauli] <;>
    ring_nf

/-- The virtual gauge `σ_y`, its own inverse. -/
private def gaugeSigmaY : GL (Fin 2) ℂ where
  val := !![0, -Complex.I; Complex.I, 0]
  inv := !![0, -Complex.I; Complex.I, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

/-- Source: arXiv:2011.12127, lines 2386–2393, read up to a virtual gauge and a scalar. In
the review's basis the tensor is the gauge transform by `σ_y` of `-1` times the printed
Pauli form, since `σ_y (σ_x, σ_y, σ_z) σ_y = (-σ_x, σ_y, -σ_z)`. -/
theorem akltTensorRMPPauli_neg_gaugeEquiv :
    GaugeEquiv ((-1 : ℂ) • akltTensorRMPPauli) (rotatePhysical akltRMPBasisᴴ akltTensorRMP) := by
  refine ⟨gaugeSigmaY, fun s => ?_⟩
  rw [rotatePhysical_akltRMPBasis]
  fin_cases s <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gaugeSigmaY, akltTensorRMPPauli, SpinCover.pauli, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals grind [Complex.I_sq]

/-- Source: arXiv:2011.12127, lines 2386–2393, read up to a global sign. On `N` sites the
coefficients of the review's tensor in its printed basis are `(-1)^N` times those of the
printed Pauli form. -/
theorem mpv_rotatePhysical_akltRMPBasis {N : ℕ} (σ : Fin N → Fin 3) :
    mpv (rotatePhysical akltRMPBasisᴴ akltTensorRMP) σ = (-1) ^ N * mpv akltTensorRMPPauli σ := by
  rw [← akltTensorRMPPauli_neg_gaugeEquiv.sameMPV N σ]
  exact mpv_smul (-1) akltTensorRMPPauli σ

/-- Bridge: in the basis with `|+⟩ = -i(|-1⟩+|+1⟩)/√2` the review's tensor becomes the
printed Pauli form `σ_i/√2` exactly (arXiv:2011.12127, lines 2389–2393). -/
theorem rotatePhysical_akltRMPBasisFixed :
    rotatePhysical akltRMPBasisFixedᴴ akltTensorRMP = akltTensorRMPPauli := by
  funext a
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [rotatePhysical, Matrix.conjTranspose_apply, akltRMPBasisFixed, akltTensorRMPPauli,
      Fin.sum_univ_three,
      akltTensorRMP_zero, akltTensorRMP_one, akltTensorRMP_two, SpinCover.pauli] <;>
    ring_nf

/-! ### Bridge to `akltTensor` -/

/-- The scalar `√3/√2` relating `akltTensor` to the review's normalization. -/
private def rmpScale : ℂ := ↑(Real.sqrt 3) / ↑(Real.sqrt 2)

private lemma rmpScale_ne_zero : rmpScale ≠ 0 := div_ne_zero sqrt3_ne_zero sqrt2_ne_zero

/-- The virtual gauge `σ_z`, its own inverse. -/
private def gaugeSigmaZ : GL (Fin 2) ℂ where
  val := !![1, 0; 0, -1]
  inv := !![1, 0; 0, -1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

/-- Bridge: the review's tensor is the gauge transform by `σ_z` of `√(3/2)` times
`akltTensor`, with the same physical labels `S_z = 0, +1, -1`. -/
theorem akltTensorRMP_gaugeEquiv : GaugeEquiv (rmpScale • akltTensor) akltTensorRMP := by
  refine ⟨gaugeSigmaZ, fun s => ?_⟩
  have h3 := sqrt3_ne_zero
  have h2 := sqrt2_ne_zero
  fin_cases s <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [akltTensorRMP_zero, akltTensorRMP_one, akltTensorRMP_two, akltTensor, rmpScale,
      gaugeSigmaZ, Complex.invSqrtTwo, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp

/-! ### Transferred results -/

/-- Bridge: the review's AKLT tensor is normal. -/
theorem akltTensorRMP_isNormal : Kraus.IsNormal akltTensorRMP :=
  isNormal_of_gaugeEquiv ((isNormal_smul_iff rmpScale_ne_zero _).2 aklt_isNormal)
    akltTensorRMP_gaugeEquiv

/-- Bridge: the review's AKLT tensor is on-site symmetric under the `Z₂ × Z₂` subgroup of
spin-`1` `π`-rotations. -/
theorem akltTensorRMP_isOnSiteSymmetric_Z2Z2 :
    IsOnSiteSymmetric akltTensorRMP akltZ2Z2Action :=
  (aklt_isOnSiteSymmetric_Z2Z2.smul _).of_gaugeEquiv akltTensorRMP_gaugeEquiv

/-! ### Virtual action of the `Z₂ × Z₂` symmetry -/

/-- Bridge: the `Z₂ × Z₂` twists of the review's tensor are implemented on the bond by the
projective representation with the anticommuting gauges `iσ_y` and `σ_z`, whose factor
system is the non-trivial class of `H²(Z₂ × Z₂, U(1))`: the review's AKLT tensor lies in
a non-trivial SPT phase (arXiv:2011.12127, around line 1159). -/
theorem akltTensorRMP_virtual_projRep :
    (∀ g i, twistedTensor akltTensorRMP akltZ2Z2Action g i *
        ((akltProjRep.X g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      ((akltProjRep.X g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * akltTensorRMP i) ∧
    TNLean.Algebra.ScalarCocycle.IsNontrivialClass akltOmega := by
  refine ⟨fun g i => ?_, aklt_isNontrivialSPT⟩
  change twistedTensor akltTensorRMP akltZ2Z2Action g i * (akltRepX g : Matrix _ _ ℂ) =
    (akltRepX g : Matrix _ _ ℂ) * akltTensorRMP i
  rcases zmod2sq_cases g with rfl | rfl | rfl | rfl
  · simp [akltRepX, twistedTensor, Matrix.one_apply]
  · have hU : akltZ2Z2Action (Multiplicative.ofAdd ((1, 0) : ZMod 2 × ZMod 2)) =
        !![(-1 : ℂ), 0, 0; 0, 0, 1; 0, 1, 0] := by
      simp only [akltZ2Z2Action, ofCommutingInvolutions_ofAdd_10]; rfl
    have hX : ((akltRepX (Multiplicative.ofAdd ((1, 0) : ZMod 2 × ZMod 2)) : GL (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; -1, 0] := by
      simp [akltRepX]; rfl
    rw [hX]
    simp only [twistedTensor, hU]
    fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_two, akltTensorRMP_zero,
        akltTensorRMP_one, akltTensorRMP_two]
  · have hU : akltZ2Z2Action (Multiplicative.ofAdd ((0, 1) : ZMod 2 × ZMod 2)) =
        !![(1 : ℂ), 0, 0; 0, -1, 0; 0, 0, -1] := by
      simp only [akltZ2Z2Action, ofCommutingInvolutions_ofAdd_01]; rfl
    have hX : ((akltRepX (Multiplicative.ofAdd ((0, 1) : ZMod 2 × ZMod 2)) : GL (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; 0, -1] := by
      simp [akltRepX]
    rw [hX]
    simp only [twistedTensor, hU]
    fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_two, akltTensorRMP_zero,
        akltTensorRMP_one, akltTensorRMP_two]
  · have hU : akltZ2Z2Action (Multiplicative.ofAdd ((1, 1) : ZMod 2 × ZMod 2)) =
        !![(-1 : ℂ), 0, 0; 0, 0, 1; 0, 1, 0] * !![(1 : ℂ), 0, 0; 0, -1, 0; 0, 0, -1] := by
      simp only [akltZ2Z2Action, ofCommutingInvolutions_ofAdd_11]; rfl
    have hX : ((akltRepX (Multiplicative.ofAdd ((1, 1) : ZMod 2 × ZMod 2)) : GL (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) = !![0, -1; -1, 0] := by
      simp only [akltRepX, toAdd_ofAdd, Units.val_mul]
      change (if (1 : ZMod 2) = 0 then 1 else !![(0 : ℂ), 1; -1, 0]) *
        (if (1 : ZMod 2) = 0 then 1 else !![(1 : ℂ), 0; 0, -1]) = _
      ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply]
    rw [hX]
    simp only [twistedTensor, hU]
    fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_two, akltTensorRMP_zero,
        akltTensorRMP_one, akltTensorRMP_two]

/-- Bridge: the printed Pauli form is on-site symmetric under the spin-`1` representation
of `SO(3)`. -/
theorem akltTensorRMPPauli_isOnSiteSymmetric_SO3 :
    IsOnSiteSymmetric akltTensorRMPPauli so3DefiningRep :=
  aklt_isOnSiteSymmetric_SO3.smul _

/-- Bridge: the local ground spaces of the review's tensor are those of `akltTensor`. -/
theorem akltTensorRMP_groundSpace_eq (L : ℕ) :
    groundSpace akltTensorRMP L = groundSpace akltTensor L := by
  rw [← akltTensorRMP_gaugeEquiv.groundSpace_eq L, groundSpace_smul_eq _ _ rmpScale_ne_zero]

/-- Bridge: the periodic MPS vector of the review's tensor spans the same line as that of
`akltTensor`. -/
theorem akltTensorRMP_mpvSubmodule_eq (N : ℕ) :
    mpvSubmodule akltTensorRMP N = mpvSubmodule akltTensor N := by
  have hmpv : (mpv akltTensorRMP : NSiteSpace 3 N) = rmpScale ^ N • mpv akltTensor := by
    funext σ
    rw [← akltTensorRMP_gaugeEquiv.sameMPV N σ]
    exact mpv_smul rmpScale akltTensor σ
  rw [mpvSubmodule, mpvSubmodule, hmpv]
  exact Submodule.span_singleton_smul_eq (pow_ne_zero N rmpScale_ne_zero).isUnit _

/-- Bridge: on a periodic chain of `N ≥ 3` sites the two-site parent Hamiltonian of the
review's tensor has the AKLT state as its only ground state (arXiv:2011.12127, line 2095). -/
theorem akltTensorRMP_chainGroundSpace_two_eq_mpvSubmodule {N : ℕ} (hN : 3 ≤ N) :
    chainGroundSpace akltTensorRMP 2 N = mpvSubmodule akltTensorRMP N := by
  rw [chainGroundSpace_eq_of_groundSpace_eq (akltTensorRMP_groundSpace_eq 2),
    akltTensorRMP_mpvSubmodule_eq, aklt_chainGroundSpace_two_eq_mpvSubmodule hN]

/-- Bridge: the two-site parent Hamiltonian of the review's tensor has a unique ground
state on every periodic chain of `N ≥ 3` sites. -/
theorem akltTensorRMP_parentHamiltonian_two_unique_gs {N : ℕ} (hN : 3 ≤ N) :
    HasUniqueGroundState (chainGroundSpace akltTensorRMP 2 N) := by
  rw [chainGroundSpace_eq_of_groundSpace_eq (akltTensorRMP_groundSpace_eq 2)]
  exact aklt_parentHamiltonian_two_unique_gs hN

end MPSTensor

end
