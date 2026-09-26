/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CompleteZipperFusionDefs

/-!
# The coproduct of a complete zipper fusion family

Let $\mathcal A$ be a cosemisimple pre-bialgebra and let $\psi=\bigoplus_c\psi_c$ be the direct
sum of the irreducible representations of the dual algebra $\mathcal A^*$.  Then $\psi$
identifies $\mathcal A^*$ with the space of block boundary matrices
$\bigoplus_c M_{\chi_c}$.  The fusion tensors decompose the coproduct of $\mathcal A^*$:
\[
  (\psi_a\otimes\psi_b)\circ\Delta(f)
    =\sum_{c,\mu}V_{ab}^{c\mu}\,\psi_c(f)\,W_{ab}^{c\mu},
  \qquad W_{ab}^{c\mu}V_{ab}^{d\nu}=\delta_{cd}\delta_{\mu\nu}\,\mathrm{Id}.
\]
This is equation `eq:splitting_algebraic` of arXiv:2204.05940, `mpo.tex` line 1655.

This file reads that formula as the definition of a map $\Delta$ on the boundary space of a
complete zipper fusion family.  In the notation of `CompleteZipperFusionFamily`, the
source's $V_{ab}^{c\mu}$ is the fusion tensor $X^c_{ab,\mu}$ and the source's $W_{ab}^{c\mu}$ is
its left inverse $X^{c+}_{ab,\mu}$.

The letters $(T_c^{ik})_c$ of the family are the images under $\psi$ of the matrix coefficients
$x\mapsto\phi(x)_{ik}$ of the physical representation.  The coproduct of a matrix coefficient
is $\sum_j f_{ij}\otimes f_{jk}$.  This is the identity
$\sum_{x,y}xy\otimes\delta_x\otimes\delta_y=\sum_x x\otimes\Delta(\delta_x)$ of `mpo.tex`,
lines 2003--2006 (equation `eq:MPO_tensor_product`).  Here it is the reconstruction field
`pairLetter_eq_synthesis_mul_directSum_mul_analysis`.  The simultaneous left inverse of the
letters says that the letters span the boundary space, which is injectivity of $\phi$
(`mpo.tex`, line 1182).  Hence $\Delta$ is determined by the tensors alone.

## Main definitions

* `CompleteZipperFusionFamily.BoundarySpace`: the block boundary matrices $\bigoplus_c M_{\chi_c}$.
* `CompleteZipperFusionFamily.letter`: the boundary element $(T_c^{ik})_c$.
* `CompleteZipperFusionFamily.coproduct`: the fusion coproduct.

## Main statements

* `span_letter_eq_top`: the letters span the boundary space.
* `coproduct_letter`: $\Delta(T^{ik})_{ab}=\sum_jT_a^{ij}\otimes T_b^{jk}$.
* `coproduct_unique`: the coproduct is the only linear map with this letter formula.
* `coproduct_mul`: the coproduct is multiplicative, the pre-bialgebra axiom of `mpo.tex`,
  lines 1409--1419, read on the dual algebra.
* `coproduct_one`: the coproduct of the unit is the support projector of the fusion tensors,
  which need not be the identity (`mpo.tex`, line 1708).

## References

* arXiv:2204.05940, `mpo.tex`, lines 1409--1419, 1655, 1708, and 2003--2006.
* arXiv:1511.08090, `AnyonsPEPS.tex`, lines 161--200 and 269--277.
-/

open scoped Matrix BigOperators Kronecker
open Matrix

namespace MPOTensor

namespace CompleteZipperFusionFamily

universe u

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
variable (Fus : CompleteZipperFusionFamily Λ p)

/-- The block boundary matrices $\bigoplus_c M_{\chi_c}$.  Through the direct sum of the
irreducible representations, this is the dual algebra $\mathcal A^*$ of arXiv:2204.05940,
`mpo.tex`, lines 1070 and 1084. -/
abbrev BoundarySpace : Type u :=
  ∀ c : Λ, Matrix (Fin (Fus.bondDim c)) (Fin (Fus.bondDim c)) ℂ

/-- Pairs of blocks, $\bigoplus_{a,b}M_{\chi_a}\otimes M_{\chi_b}$, written with the Kronecker
product on each summand. -/
abbrev PairSpace : Type u :=
  ∀ a b : Λ, Matrix (Fin (Fus.bondDim a) × Fin (Fus.bondDim b))
    (Fin (Fus.bondDim a) × Fin (Fus.bondDim b)) ℂ

/-- The boundary element $(T_c^{ik})_c$ formed by one letter of every block. -/
def letter (i k : Fin p) : Fus.BoundarySpace := fun c => Fus.tensor c i k

/-- The direct sum $\bigoplus_c 1_{N_{ab}^c}\otimes X_c$ on the fusion coordinates of the pair
`(a, b)`. -/
noncomputable def directSum (a b : Λ) (X : Fus.BoundarySpace) :
    Matrix ((c : Λ) × (Fin (Fus.fusionMultiplicity a b c) × Fin (Fus.bondDim c)))
      ((c : Λ) × (Fin (Fus.fusionMultiplicity a b c) × Fin (Fus.bondDim c))) ℂ :=
  Matrix.blockDiagonal' fun c =>
    (1 : Matrix (Fin (Fus.fusionMultiplicity a b c))
      (Fin (Fus.fusionMultiplicity a b c)) ℂ) ⊗ₖ X c

theorem directSum_add (a b : Λ) (X Y : Fus.BoundarySpace) :
    Fus.directSum a b (X + Y) = Fus.directSum a b X + Fus.directSum a b Y := by
  rw [directSum, directSum, directSum, ← blockDiagonal'_add]
  congr 1
  funext c
  simp [kronecker_add]

theorem directSum_smul (a b : Λ) (r : ℂ) (X : Fus.BoundarySpace) :
    Fus.directSum a b (r • X) = r • Fus.directSum a b X := by
  rw [directSum, directSum, ← blockDiagonal'_smul]
  congr 1
  funext c
  simp [kronecker_smul]

theorem directSum_mul (a b : Λ) (X Y : Fus.BoundarySpace) :
    Fus.directSum a b (X * Y) = Fus.directSum a b X * Fus.directSum a b Y := by
  rw [directSum, directSum, directSum, ← blockDiagonal'_mul]
  congr 1
  funext c
  rw [← mul_kronecker_mul, Matrix.one_mul, Pi.mul_apply]

theorem directSum_one (a b : Λ) : Fus.directSum a b 1 = 1 := by
  rw [directSum, ← blockDiagonal'_one]
  congr 1
  funext c
  simp

/-- **The fusion coproduct.**  For boundary matrices $X=(X_c)_c$,
\[
  \Delta(X)_{ab}=\sum_{c,\mu}X^c_{ab,\mu}\,X_c\,X^{c+}_{ab,\mu},
\]
written with the synthesis and analysis matrices of the family.  In the notation of
arXiv:2204.05940, `mpo.tex`, line 1655 (equation `eq:splitting_algebraic`), this is
$(\psi_a\otimes\psi_b)\circ\Delta(f)=\sum_{c,\mu}V_{ab}^{c\mu}\psi_c(f)W_{ab}^{c\mu}$ with
$X_c=\psi_c(f)$, $V=X^c_{ab,\mu}$ and $W=X^{c+}_{ab,\mu}$. -/
noncomputable def coproduct : Fus.BoundarySpace →ₗ[ℂ] Fus.PairSpace where
  toFun X a b := Fus.fusionSynthesis a b * Fus.directSum a b X * Fus.fusionAnalysis a b
  map_add' X Y := by
    funext a b
    simp [directSum_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' r X := by
    funext a b
    simp [directSum_smul]

theorem coproduct_apply (X : Fus.BoundarySpace) (a b : Λ) :
    Fus.coproduct X a b =
      Fus.fusionSynthesis a b * Fus.directSum a b X * Fus.fusionAnalysis a b := rfl

private theorem fusionSynthesis_mul_directSum_apply (X : Fus.BoundarySpace) (a b : Λ)
    (x : Fin (Fus.bondDim a) × Fin (Fus.bondDim b)) (c : Λ)
    (ν : Fin (Fus.fusionMultiplicity a b c)) (w : Fin (Fus.bondDim c)) :
    (Fus.fusionSynthesis a b * Fus.directSum a b X) x ⟨c, ν, w⟩ =
      ∑ z, Fus.fusionSynthesis a b x ⟨c, ν, z⟩ * X c z w := by
  rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single c]
  · simp [directSum, blockDiagonal'_apply_eq, Fintype.sum_prod_type, one_apply]
  · intro c' _ hc'
    exact Finset.sum_eq_zero fun s _ => by
      rw [directSum, blockDiagonal'_apply_ne _ _ _ hc', mul_zero]
  · intro h
    exact absurd (Finset.mem_univ c) h

/-- The coproduct as a sum over fusion channels,
$\Delta(X)_{ab}=\sum_{c,\mu}X^c_{ab,\mu}X_cX^{c+}_{ab,\mu}$.

Source: arXiv:2204.05940, `mpo.tex`, line 1655 (equation `eq:splitting_algebraic`). -/
theorem coproduct_apply_eq_sum (X : Fus.BoundarySpace) (a b : Λ) :
    Fus.coproduct X a b =
      ∑ c, ∑ μ, Fus.fusionTensor a b c μ * X c * Fus.fusionTensorLeftInverse a b c μ := by
  ext x y
  rw [coproduct_apply, Matrix.mul_apply, Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type]
  simp only [fusionSynthesis_mul_directSum_apply]
  simp only [Matrix.sum_apply, Matrix.mul_apply, fusionTensor, fusionTensorLeftInverse]

/-- **Letter formula.**  The coproduct of a letter is the letter of the stacked tensor,
$\Delta(T^{ik})_{ab}=\sum_jT_a^{ij}\otimes T_b^{jk}$.

Source: arXiv:2204.05940, `mpo.tex`, lines 2003--2006: the identity
$\sum_{x,y}xy\otimes\delta_x\otimes\delta_y=\sum_x x\otimes\Delta(\delta_x)$ and equation
`eq:MPO_tensor_product`; arXiv:1511.08090, equation `inversegaugeone`, lines 184--186. -/
theorem coproduct_letter (i k : Fin p) (a b : Λ) :
    Fus.coproduct (Fus.letter i k) a b = ∑ j, Fus.tensor a i j ⊗ₖ Fus.tensor b j k :=
  (Fus.pairLetter_eq_synthesis_mul_directSum_mul_analysis a b i k).symm

private theorem sum_smul_letter_apply (c : Λ) (x y : Fin (Fus.bondDim c)) (d : Λ)
    (x' y' : Fin (Fus.bondDim d)) :
    (∑ i, ∑ k, Fus.blockLeftInverse ⟨c, x, y⟩ (i, k) • Fus.letter i k) d x' y' =
      if h : c = d then
        if _ : h ▸ x = x' then if _ : h ▸ y = y' then (1 : ℂ) else 0 else 0
      else 0 := by
  rw [← Fus.blockLeftInverse_apply c d x y x' y']
  simp [Finset.sum_apply, Matrix.sum_apply, letter]

/-- **The letters span the boundary space.**  This is the simultaneous left inverse of the
block letters, and corresponds to injectivity of the physical representation
(arXiv:2204.05940, `mpo.tex`, line 1182).

Source: arXiv:1511.08090, `AnyonsPEPS.tex`, lines 269--277. -/
theorem span_letter_eq_top :
    Submodule.span ℂ (Set.range fun ik : Fin p × Fin p => Fus.letter ik.1 ik.2) = ⊤ := by
  classical
  refine eq_top_iff.2 fun Z _ => ?_
  obtain ⟨E, hEdef⟩ : ∃ E : ∀ c : Λ, Fin (Fus.bondDim c) → Fin (Fus.bondDim c) →
      Fus.BoundarySpace,
      E = fun c x y => ∑ i, ∑ k, Fus.blockLeftInverse ⟨c, x, y⟩ (i, k) • Fus.letter i k :=
    ⟨_, rfl⟩
  have hE : ∀ c x y d x' y', E c x y d x' y' =
      if h : c = d then
        if _ : h ▸ x = x' then if _ : h ▸ y = y' then (1 : ℂ) else 0 else 0
      else 0 := by
    subst hEdef
    exact Fus.sum_smul_letter_apply
  have hZ : Z = ∑ c, ∑ x, ∑ y, Z c x y • E c x y := by
    funext d x' y'
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, hE]
    rw [Finset.sum_eq_single d]
    · simp
    · intro c _ hc
      simp [hc]
    · intro h
      exact absurd (Finset.mem_univ d) h
  rw [hZ]
  refine Submodule.sum_mem _ fun c _ => Submodule.sum_mem _ fun x _ =>
    Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ <| hEdef ▸
      Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ <| Submodule.subset_span ⟨(i, k), rfl⟩

/-- **Uniqueness of the coproduct.**  A linear map on the boundary space with the letter
formula of `coproduct_letter` is the fusion coproduct.  In particular the coproduct is
determined by the MPO blocks alone: any other choice of fusion tensors and left inverses for the
same blocks gives the same map.

Source: arXiv:2204.05940, `mpo.tex`, lines 1182 and 2003--2006. -/
theorem coproduct_unique (Δ : Fus.BoundarySpace →ₗ[ℂ] Fus.PairSpace)
    (h : ∀ i k a b, Δ (Fus.letter i k) a b = ∑ j, Fus.tensor a i j ⊗ₖ Fus.tensor b j k) :
    Δ = Fus.coproduct :=
  LinearMap.ext_on_range Fus.span_letter_eq_top fun ik => by
    funext a b
    rw [h, coproduct_letter]

/-- **Multiplicativity.**  $\Delta(XY)=\Delta(X)\Delta(Y)$.  Read on the dual algebra, this is
the pre-bialgebra axiom $\Delta(xy)=\Delta(x)\Delta(y)$.

Source: arXiv:2204.05940, `mpo.tex`, lines 1409--1419. -/
theorem coproduct_mul (X Y : Fus.BoundarySpace) :
    Fus.coproduct (X * Y) = Fus.coproduct X * Fus.coproduct Y := by
  funext a b
  rw [Pi.mul_apply, Pi.mul_apply, coproduct_apply, coproduct_apply, coproduct_apply,
    directSum_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Fus.fusionAnalysis a b), Fus.analysis_mul_synthesis, Matrix.one_mul]

/-- The coproduct of the unit is the support projector of the fusion tensors.  It need not be
the identity of the product bond space.

Source: arXiv:2204.05940, `mpo.tex`, line 1708 (equation `eq:delta_epsilon`). -/
theorem coproduct_one (a b : Λ) :
    Fus.coproduct 1 a b = Fus.fusionSynthesis a b * Fus.fusionAnalysis a b := by
  rw [coproduct_apply, directSum_one, Matrix.mul_one]

end CompleteZipperFusionFamily

end MPOTensor
