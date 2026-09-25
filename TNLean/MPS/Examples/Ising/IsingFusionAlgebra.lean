/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.Ising.IsingGauge
import TNLean.MPS.Examples.Ising.Zsqrt2OperatorFusion
import TNLean.MPS.MPDO.SimpleScaling

/-!
# Ising anyon chain: closed-path kernels and the gauges of the fusion products

**Source.** Bultinck, Mariën, Williamson, Sahinoglu, Haegeman, Verstraete 2017
(arXiv:1511.08090), Appendix D.2 "Ising string-net",
`References/1511.08090/AnyonsPEPS.tex` lines 1305–1323: the Ising labels `1, σ, ψ`, the fusion
rules `ψ × ψ = 1`, `σ × ψ = σ`, `σ × σ = 1 + ψ`, the quantum dimension `d_σ = √2`, the
F-symbols (`F^{ψσψ}_{σσσ} = F^{σψσ}_{ψσσ} = -1`, the `σσσ` block `± 1/√2`), and the statement
(line 1323) that the matrix product operator tensors are built from the `G`-symbols "similarly as
for the Fibonacci model" (lines 1257–1268). For Fibonacci the source states that the operator
blocks satisfy the fusion rules (line 1268); for Ising it prints only the fusion rules of the
category, so the operator identities below are the Ising analogue of line 1268, implied but not
printed by the source. The same abstract algebra `D_ψ² = 1`, `D_σ D_ψ = D_ψ D_σ = D_σ`,
`D_σ² = 1 + D_ψ` is printed by Aasen, Mong, Fendley 2016 (arXiv:1601.07185),
`References/1601.07185/source/Ising-Defects.tex` lines 1051–1055, for a different realization:
the defect operators of the Ising lattice model acting on spin and dual-spin configurations.

**Formalized here.** For the three topological-symmetry tensors `A_1`, `A_ψ`, `√2 A_σ` of
`IsingTensors`: the closed-path kernels of the periodic operators `O_1` and `O_ψ` (the vacuum
operator is the projector onto admissible closed fusion paths, the fermion operator moves every
label by the fusion with `ψ` and carries the sign `F^{ψσψ}_σ = -1` once per site with the label
`(σ, ψ, σ)`), and the signed-permutation gauges that prove the fusion rules with at most one
factor `σ` in `IsingFusionAlgebraOnePsi`, `IsingFusionAlgebraOneSigma` and
`IsingFusionAlgebraPsiSigma`. The rule `O_σ O_σ = O_1 + O_ψ` is in `IsingFusionAlgebraSigma`.

**Local fix (sigma scaling):** the tensors carry the physical index `(x', ρ, x)` and bond pairs of
the source, omit the factors `v_e v_f` of the `G`-symbols (lines 1257–1260), and store the `σ`
tensor multiplied by `√2`, so that every entry lies in `ℤ[√2]`. The operator statements are proved
for these `v`-free tensors. Documented in
`docs/paper-gaps/bmwshv17_ising_boundary_tensor_normalization.tex`.

Every product is proved in the same way (`MPSTensor.mpo_mul_eq_of_zsqrt2_conj`): the stacked
tensor `X ⋆ Y` of the two factors is conjugated, letter by letter, by an explicit signed
permutation of its bond coordinates into the direct sum of the target tensor and a zero tensor;
the letter identities are decided over `ℤ[√2]`, and the zero summand contributes nothing to the
periodic operator at positive length.

## Main definitions

* `IsingTwist.isingLeft`, `IsingTwist.isingRight`: the outer labels `x'` and `x` of a fusion-tree
  label `(x', ρ, x)`.
* `IsingTwist.IsAdmissiblePath`: a periodic configuration of labels is a closed fusion path.
* `IsingTwist.isingPsiFuse`: the fusion of a label with `ψ` on both outer legs.
* `IsingTwist.isingSigmaCoefZ`, `IsingTwist.isingSigmaRow`, `IsingTwist.isingSigmaCol`,
  `IsingTwist.isingSigmaNext`: the letters of `√2 A_σ` as scaled matrix units.
* `IsingTwist.isingGaugeOneOneZ`, `IsingTwist.isingGaugePsiPsiZ`,
  `IsingTwist.isingGaugeOneSigmaZ`, `IsingTwist.isingGaugeSigmaOneZ`,
  `IsingTwist.isingGaugePsiSigmaZ`, `IsingTwist.isingGaugeSigmaPsiZ`: the gauges of the
  stacked tensors.

## Main results

* `IsingTwist.mpo_isingOne_apply`, `IsingTwist.mpo_isingPsi_apply`: the closed-path kernels.
* `IsingTwist.mpo_isingOne_conjTranspose`, `IsingTwist.mpo_isingPsi_conjTranspose`: both
  operators are self-adjoint.
* `IsingTwist.isingOneZ_eq_smul_single`, `IsingTwist.isingPsiZ_eq_smul_single`,
  `IsingTwist.isingSigmaZ_eq_smul_single`: every letter is a scaled matrix unit.
* `IsingTwist.isingConj_of_rho_eq`: a letter identity of a stacked tensor reduces to the letters
  within one sector of the middle label `ρ`.

## References
- [arXiv:1511.08090](https://arxiv.org/abs/1511.08090) -- N. Bultinck, M. Mariën,
  D. J. Williamson, M. B. Sahinoglu, J. Haegeman, F. Verstraete, *Anyons and matrix product
  operator algebras*
- [arXiv:1601.07185](https://arxiv.org/abs/1601.07185) -- D. Aasen, R. S. K. Mong, P. Fendley,
  *Topological defects on the lattice I: the Ising model*

## Provenance
The tensors were first recorded in `Notes/OpenProblemsTN/checks/asym_ising_action_data.md`;
the signed permutations were found by solving the intertwiner equations numerically. These are
verification records, not the source.
-/

open scoped Matrix

namespace IsingTwist

open MPSTensor Zsqrtd

/-! ### The closed-path kernels -/

/-- The outer label `x'` of a fusion-tree label `(x', ρ, x)`, in the order `1, ψ, σ`
(Source: arXiv:1511.08090, lines 1308–1312, the labels and fusion rules of the Ising category;
the label order is that of `isingRho`). -/
def isingLeft : Fin 10 → Fin 3 := ![0, 0, 0, 1, 1, 1, 2, 2, 2, 2]

/-- The outer label `x` of a fusion-tree label `(x', ρ, x)`, in the order `1, ψ, σ`. -/
def isingRight : Fin 10 → Fin 3 := ![0, 1, 2, 1, 0, 2, 2, 2, 0, 1]

/-- A periodic configuration of fusion-tree labels is a **closed fusion path** when the outer
label `x` at each site is the outer label `x'` at the next site, cyclically. -/
def IsAdmissiblePath {N : ℕ} (σ : Fin N → Fin 10) : Prop :=
  ∀ k, isingRight (σ k) = isingLeft (σ (finRotate N k))

instance {N : ℕ} (σ : Fin N → Fin 10) : Decidable (IsAdmissiblePath σ) :=
  inferInstanceAs (Decidable (∀ _, _ = _))

/-- The fusion of an outer label with `ψ`: `1 ↦ ψ`, `ψ ↦ 1`, `σ ↦ σ`. -/
def isingPsiFlip : Fin 3 → Fin 3 := ![1, 0, 2]

/-- The fusion of a fusion-tree label `(x', ρ, x)` with `ψ` on both outer legs,
`(x', ρ, x) ↦ (ψ × x', ρ, ψ × x)`. -/
def isingPsiFuse : Fin 10 → Fin 10 := ![3, 4, 5, 0, 1, 2, 6, 7, 9, 8]

/-- Every letter of `A_1` over `ℤ√2` is the matrix unit `E_{x' x}` on the diagonal of the
physical labels. -/
theorem isingOneZ_eq_smul_single : ∀ h h' : Fin 10,
    isingOneZ h h' =
      (if h' = h then 1 else 0 : ℤ√2) • Matrix.single (isingLeft h) (isingRight h) 1 := by
  decide +kernel

/-- Every letter of `A_ψ` over `ℤ√2` is a signed matrix unit between the label and its fusion
with `ψ`. -/
theorem isingPsiZ_eq_smul_single : ∀ h h' : Fin 10,
    isingPsiZ h h' = (if h' = isingPsiFuse h then (if h = 7 then -1 else 1) else 0 : ℤ√2) •
      Matrix.single (isingPsiFlip (isingLeft h)) (isingPsiFlip (isingRight h)) 1 := by
  decide +kernel

/-! ### The letters as scaled matrix units

Each tensor has, for each left label `h`, at most two right labels `h'` with a nonzero letter;
the lists `isingOneNext`, `isingPsiNext`, `isingSigmaNext` enumerate them. With these, the
conjugated stacked letters of the fusion products are short explicit sums
(`MPSTensor.mul_mulTensorR_mul_transpose_eq_list`).
-/

/-- The coefficient of the letter `(h, h')` of `√2 A_σ` over `ℤ√2`. -/
def isingSigmaCoefZ : Fin 10 → Fin 10 → ℤ√2
  | 0, 6 => sqrtd | 1, 7 => sqrtd | 2, 8 => 1 | 2, 9 => 1 | 3, 6 => sqrtd | 4, 7 => sqrtd
  | 5, 8 => 1 | 5, 9 => -1 | 6, 0 => sqrtd | 6, 3 => sqrtd | 7, 1 => sqrtd | 7, 4 => sqrtd
  | 8, 2 => sqrtd | 8, 5 => sqrtd | 9, 2 => sqrtd | 9, 5 => -sqrtd | _, _ => 0

/-- The row of the matrix unit of the letter `(h, h')` of `√2 A_σ`. -/
def isingSigmaRow : Fin 10 → Fin 10 → Fin 4
  | 0, 6 => 2 | 1, 7 => 2 | 2, 8 => 2 | 2, 9 => 2 | 3, 6 => 3 | 4, 7 => 3
  | 5, 8 => 3 | 5, 9 => 3 | 6, 0 => 0 | 6, 3 => 1 | 7, 1 => 0 | 7, 4 => 1
  | 8, 2 => 0 | 8, 5 => 1 | 9, 2 => 0 | 9, 5 => 1 | _, _ => 0

/-- The column of the matrix unit of the letter `(h, h')` of `√2 A_σ`. -/
def isingSigmaCol : Fin 10 → Fin 10 → Fin 4
  | 0, 6 => 2 | 1, 7 => 3 | 2, 8 => 0 | 2, 9 => 1 | 3, 6 => 3 | 4, 7 => 2
  | 5, 8 => 0 | 5, 9 => 1 | 6, 0 => 0 | 6, 3 => 1 | 7, 1 => 1 | 7, 4 => 0
  | 8, 2 => 2 | 8, 5 => 2 | 9, 2 => 3 | 9, 5 => 3 | _, _ => 0

/-- Every letter of `√2 A_σ` over `ℤ√2` is a scaled matrix unit. -/
theorem isingSigmaZ_eq_smul_single : ∀ h h' : Fin 10,
    isingSigmaZ h h' =
      isingSigmaCoefZ h h' • Matrix.single (isingSigmaRow h h') (isingSigmaCol h h') 1 := by
  decide +kernel

/-- The right labels with a nonzero letter of `A_1`. -/
def isingOneNext (h : Fin 10) : List (Fin 10) := [h]

/-- The right labels with a nonzero letter of `A_ψ`. -/
def isingPsiNext (h : Fin 10) : List (Fin 10) := [isingPsiFuse h]

/-- The right labels with a nonzero letter of `√2 A_σ`. -/
def isingSigmaNext : Fin 10 → List (Fin 10) :=
  ![[6], [7], [8, 9], [6], [7], [8, 9], [0, 3], [1, 4], [2, 5], [2, 5]]

theorem isingOneNext_nodup (h : Fin 10) : (isingOneNext h).Nodup := List.nodup_singleton h

theorem isingPsiNext_nodup (h : Fin 10) : (isingPsiNext h).Nodup := List.nodup_singleton _

theorem isingSigmaNext_nodup : ∀ h : Fin 10, (isingSigmaNext h).Nodup := by decide

theorem isingOneCoef_eq_zero : ∀ h h' : Fin 10, h' ∉ isingOneNext h →
    (if h' = h then 1 else 0 : ℤ√2) = 0 := by
  decide

theorem isingPsiCoef_eq_zero : ∀ h h' : Fin 10, h' ∉ isingPsiNext h →
    (if h' = isingPsiFuse h then (if h = 7 then -1 else 1) else 0 : ℤ√2) = 0 := by
  decide

theorem isingSigmaCoef_eq_zero : ∀ h h' : Fin 10, h' ∉ isingSigmaNext h →
    isingSigmaCoefZ h h' = 0 := by
  decide +kernel

/-- **Sector reduction of a letter identity.** For tensors whose letters vanish across the
middle label `ρ`, a letter identity of the stacked tensor holds for all letters once it holds for
the letters whose two labels carry the same `ρ`. -/
theorem isingConj_of_rho_eq {D₁ D₂ k z : ℕ}
    {XZ : Fin 10 → Fin 10 → Matrix (Fin D₁) (Fin D₁) (ℤ√2)}
    {YZ : Fin 10 → Fin 10 → Matrix (Fin D₂) (Fin D₂) (ℤ√2)}
    {TZ : Fin 10 → Fin 10 → Matrix (Fin k) (Fin k) (ℤ√2)}
    (hX : ∀ h h', isingRho h ≠ isingRho h' → XZ h h' = 0)
    (hY : ∀ h h', isingRho h ≠ isingRho h' → YZ h h' = 0)
    (hT : ∀ h h', isingRho h ≠ isingRho h' → TZ h h' = 0)
    {G : Matrix (Fin (k + z)) (Fin (D₁ * D₂)) (ℤ√2)}
    {H : Matrix (Fin (D₁ * D₂)) (Fin (k + z)) (ℤ√2)}
    {c : ℤ√2}
    (hdiag : ∀ h h', isingRho h' = isingRho h →
      G * mulZsqrt2Tensor XZ YZ h h' * H = c • padZsqrt2 z (TZ h h'))
    (h h' : Fin 10) : G * mulZsqrt2Tensor XZ YZ h h' * H = c • padZsqrt2 z (TZ h h') := by
  by_cases hr : isingRho h' = isingRho h
  · exact hdiag h h' hr
  · have hne : isingRho h ≠ isingRho h' := fun e => hr e.symm
    rw [mulZsqrt2Tensor, mulTensorR_eq_zero_of_ne isingRho XZ YZ hX hY hne, hT h h' hne]
    simp [padZsqrt2]

private theorem isingPsiFlip_eq_iff : ∀ a b : Fin 3, isingPsiFlip a = isingPsiFlip b ↔ a = b := by
  decide

/-- Every letter of `A_1` is the matrix unit `E_{x' x}` on the diagonal of the physical labels. -/
theorem isingOne_eq_smul_single (h h' : Fin 10) :
    isingOne h h' = (if h' = h then 1 else 0 : ℂ) •
      Matrix.single (isingLeft h) (isingRight h) 1 := by
  ext a b
  simp only [isingOne, isingOneZ_eq_smul_single h h', complexOfZsqrt2_apply, Matrix.smul_apply,
    Matrix.single_apply, smul_eq_mul]
  split_ifs <;> simp

/-- Every letter of `A_ψ` is a signed matrix unit between the label and its fusion with `ψ`. -/
theorem isingPsi_eq_smul_single (h h' : Fin 10) :
    isingPsi h h' = (if h' = isingPsiFuse h then (if h = 7 then -1 else 1) else 0 : ℂ) •
      Matrix.single (isingPsiFlip (isingLeft h)) (isingPsiFlip (isingRight h)) 1 := by
  ext a b
  simp only [isingPsi, isingPsiZ_eq_smul_single h h', complexOfZsqrt2_apply, Matrix.smul_apply,
    Matrix.single_apply, smul_eq_mul]
  split_ifs <;> simp

/-- **The vacuum operator is the projector onto the closed fusion paths.** Project result: the
source (arXiv:1511.08090, lines 1257–1268 and 1305–1323) builds the operator but does not print
its kernel. At every positive length the periodic operator of `A_1` is diagonal, with the entry
`1` exactly on the admissible closed paths. -/
theorem mpo_isingOne_apply {N : ℕ} (hN : 0 < N) (σ τ : Fin N → Fin 10) :
    MPOTensor.mpo isingOne N σ τ = if σ = τ ∧ IsAdmissiblePath σ then 1 else 0 := by
  rw [MPOTensor.mpo_apply_of_eq_smul_single isingOne (fun h h' => if h' = h then 1 else 0)
    (fun h _ => isingLeft h) (fun h _ => isingRight h) isingOne_eq_smul_single hN,
    Finset.prod_boole]
  unfold IsAdmissiblePath
  by_cases hστ : σ = τ
  · subst hστ
    simp
  · have h : ¬ ∀ k, τ k = σ k := fun h => hστ (funext fun k => (h k).symm)
    simp [hστ, h]

/-- **The fermion operator.** Project result: the source (arXiv:1511.08090, lines 1257–1268 and
1305–1323) builds the operator but does not print its kernel. At every positive length the
periodic operator of `A_ψ` sends a closed fusion path to its fusion with `ψ`, with the sign
`F^{ψσψ}_{σσσ} = -1` (line 1320) once for every site carrying the label `(σ, ψ, σ)`. -/
theorem mpo_isingPsi_apply {N : ℕ} (hN : 0 < N) (σ τ : Fin N → Fin 10) :
    MPOTensor.mpo isingPsi N σ τ =
      if τ = isingPsiFuse ∘ σ ∧ IsAdmissiblePath σ then
        (-1) ^ (Finset.univ.filter fun k => σ k = 7).card else 0 := by
  rw [MPOTensor.mpo_apply_of_eq_smul_single isingPsi
    (fun h h' => if h' = isingPsiFuse h then (if h = 7 then -1 else 1) else 0)
    (fun h _ => isingPsiFlip (isingLeft h)) (fun h _ => isingPsiFlip (isingRight h))
    isingPsi_eq_smul_single hN, Finset.prod_ite_zero]
  simp only [isingPsiFlip_eq_iff, Finset.mem_univ, true_implies]
  have hsign : ∏ k, (if σ k = 7 then (-1 : ℂ) else 1) =
      (-1) ^ (Finset.univ.filter fun k => σ k = 7).card := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  rw [hsign]
  unfold IsAdmissiblePath
  split_ifs with h1 h2 h3 h3 <;> simp_all [funext_iff]

private theorem isingPsiFuse_involutive : ∀ h : Fin 10, isingPsiFuse (isingPsiFuse h) = h := by
  decide

private theorem isingPsiFuse_eq_seven_iff : ∀ h : Fin 10, isingPsiFuse h = 7 ↔ h = 7 := by
  decide

private theorem isingRight_isingPsiFuse :
    ∀ h : Fin 10, isingRight (isingPsiFuse h) = isingPsiFlip (isingRight h) := by
  decide

private theorem isingLeft_isingPsiFuse :
    ∀ h : Fin 10, isingLeft (isingPsiFuse h) = isingPsiFlip (isingLeft h) := by
  decide

/-- Fusing every label of a periodic configuration with `ψ` preserves closedness. -/
private theorem isAdmissiblePath_isingPsiFuse_comp {N : ℕ} (σ : Fin N → Fin 10) :
    IsAdmissiblePath (isingPsiFuse ∘ σ) ↔ IsAdmissiblePath σ := by
  simp only [IsAdmissiblePath, Function.comp_apply, isingRight_isingPsiFuse,
    isingLeft_isingPsiFuse, isingPsiFlip_eq_iff]

/-- **The vacuum operator is self-adjoint.** Project result, read off from the kernel
`mpo_isingOne_apply`: at every positive length `O_1ᴴ = O_1`. -/
theorem mpo_isingOne_conjTranspose {N : ℕ} (hN : 0 < N) :
    (MPOTensor.mpo isingOne N)ᴴ = MPOTensor.mpo isingOne N := by
  ext σ τ
  rw [Matrix.conjTranspose_apply, mpo_isingOne_apply hN, mpo_isingOne_apply hN]
  by_cases h : σ = τ
  · subst h; split_ifs <;> simp
  · simp [h, Ne.symm h]

/-- **The fermion operator is self-adjoint.** Project result, read off from the kernel
`mpo_isingPsi_apply`: the fusion with `ψ` is an involution that preserves closedness and the
number of sites with the label `(σ, ψ, σ)`, and the signs are real, so at every positive length
`O_ψᴴ = O_ψ`. -/
theorem mpo_isingPsi_conjTranspose {N : ℕ} (hN : 0 < N) :
    (MPOTensor.mpo isingPsi N)ᴴ = MPOTensor.mpo isingPsi N := by
  ext σ τ
  rw [Matrix.conjTranspose_apply, mpo_isingPsi_apply hN, mpo_isingPsi_apply hN]
  by_cases h : τ = isingPsiFuse ∘ σ
  · subst h
    have hσ : σ = isingPsiFuse ∘ isingPsiFuse ∘ σ :=
      funext fun k => (isingPsiFuse_involutive (σ k)).symm
    have hcard : (Finset.univ.filter fun k => (isingPsiFuse ∘ σ) k = 7).card =
        (Finset.univ.filter fun k => σ k = 7).card := by
      simp only [Function.comp_apply, isingPsiFuse_eq_seven_iff]
    split_ifs with h1 h2 h2
    · rw [hcard]; simp
    · exact absurd ⟨rfl, (isAdmissiblePath_isingPsiFuse_comp σ).1 h1.2⟩ h2
    · exact absurd ⟨hσ, (isAdmissiblePath_isingPsiFuse_comp σ).2 h2.2⟩ h1
    · simp
  · have h' : ¬ (σ = isingPsiFuse ∘ τ ∧ IsAdmissiblePath τ) := fun h' => h <| by
      rw [h'.1]; funext k; exact (isingPsiFuse_involutive _).symm
    have h'' : ¬ (τ = isingPsiFuse ∘ σ ∧ IsAdmissiblePath σ) := fun h'' => h h''.1
    simp only [h', h'', ↓reduceIte, star_zero]

/-! ### The fusion rules with at most one factor `σ`

Each gauge is a signed permutation of the stacked bond coordinates: its first rows pick out the
coordinates on which the stacked tensor is the target tensor, and the remaining rows the
coordinates of the zero block.
-/

/-- The gauge of `A_1 ⋆ A_1`: the diagonal bond pairs `(x, x)` first. -/
def isingGaugeOneOneZ : Matrix (Fin 9) (Fin 9) (ℤ√2) :=
  signedPermMatrix ![0, 4, 8, 1, 2, 3, 5, 6, 7] fun _ => 1

/-- The gauge of `A_ψ ⋆ A_ψ`: the bond pairs `(ψ × x, x)` first. -/
def isingGaugePsiPsiZ : Matrix (Fin 9) (Fin 9) (ℤ√2) :=
  signedPermMatrix ![3, 1, 8, 0, 2, 4, 5, 6, 7] fun _ => 1

/-- The gauge of `A_1 ⋆ (√2 A_σ)`. -/
def isingGaugeOneSigmaZ : Matrix (Fin 12) (Fin 12) (ℤ√2) :=
  signedPermMatrix ![8, 9, 2, 7, 0, 1, 3, 4, 5, 6, 10, 11] fun _ => 1

/-- The gauge of `(√2 A_σ) ⋆ A_1`. -/
def isingGaugeSigmaOneZ : Matrix (Fin 12) (Fin 12) (ℤ√2) :=
  signedPermMatrix ![0, 4, 8, 11, 1, 2, 3, 5, 6, 7, 9, 10] fun _ => 1

/-- The signs of the gauge of `A_ψ ⋆ (√2 A_σ)`: the F-symbol `-1` of the `ψ` line. -/
def isingSignPsiSigma : Fin 12 → ℤ√2 := ![1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

/-- The gauge of `A_ψ ⋆ (√2 A_σ)`. -/
def isingGaugePsiSigmaZ : Matrix (Fin 12) (Fin 12) (ℤ√2) :=
  signedPermMatrix ![8, 9, 7, 2, 0, 1, 3, 4, 5, 6, 10, 11] isingSignPsiSigma

/-- The signs of the gauge of `(√2 A_σ) ⋆ A_ψ`: the F-symbol `-1` of the `ψ` line. -/
def isingSignSigmaPsi : Fin 12 → ℤ√2 := ![1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1, 1]

/-- The gauge of `(√2 A_σ) ⋆ A_ψ`. -/
def isingGaugeSigmaPsiZ : Matrix (Fin 12) (Fin 12) (ℤ√2) :=
  signedPermMatrix ![3, 1, 8, 11, 0, 2, 4, 5, 6, 7, 9, 10] isingSignSigmaPsi

end IsingTwist
