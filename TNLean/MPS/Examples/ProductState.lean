/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.CyclicTrace
import TNLean.MPS.Core.ProductVector
import TNLean.MPS.OpenBoundary

/-!
# Product states: bond-dimension-one MPS

**Source.** Cirac, Pérez-García, Schuch, Verstraete 2021 (arXiv:2011.12127), Appendix A,
"Product states", `Papers/2011.12127/TN-Review-main.tex` lines 2330–2333: a product state
$\lvert\phi^1\rangle\otimes\cdots\otimes\lvert\phi^N\rangle$ with
$\lvert\phi^s\rangle=\sum_i a^{i,[s]}\lvert i\rangle$ is a trivial MPS with `D = 1`,
$\lvert\psi\rangle=\sum_{i_1,\dots,i_N}a^{i_1,[1]}\cdots a^{i_N,[N]}\lvert i_1,\dots,i_N\rangle$.
Review: arXiv:2011.12127, Appendix A, "Product states".

**Formalized here.** The site-dependent bond-dimension-one tensor whose `s`-th matrices are
the `1 × 1` matrices $a^{i,[s]}$, and the identity: its open-boundary contraction (with the
trivial boundary vectors) is the coefficient $a^{i_1,[1]}\cdots a^{i_N,[N]}$ of the product
vector. Vectors are written in the computational basis, as functions on configurations.
For a site-independent product state the translation-invariant open-boundary and periodic
states of the one-site tensor are the same product vector.

## Main definitions

* `MPSTensor.siteOpenCoeff` : open-boundary contraction of a site-dependent tensor family
* `MPSTensor.productSiteTensor` : the site-dependent `D = 1` tensor $a^{i,[s]}$

## Main results

* `MPSTensor.siteOpenCoeff_productSiteTensor` : the product state is the MPS with `D = 1`
* `MPSTensor.siteOpenCoeff_const` : bridge to `openState` for a site-independent family
* `MPSTensor.openState_productSiteTensor_const`, `MPSTensor.mpv_productSiteTensor_const` :
  site-independent product states as translation-invariant open-boundary and periodic MPS

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- Cirac, Pérez-García, Schuch,
  Verstraete, *Matrix product states and projected entangled pair states: Concepts,
  symmetries, theorems*
-/

open scoped Matrix BigOperators
open Matrix

namespace MPSTensor

variable {d D N : ℕ}

/-- Project definition: the open-boundary contraction
$v_L^{\mathsf T}\,A^{[1]\,\sigma_1}\cdots A^{[N]\,\sigma_N}\,v_R$ of a site-dependent family of
tensors `A s`, one per site. It generalizes `openCoeff`, where every site carries the same
tensor. -/
noncomputable def siteOpenCoeff (vL vR : Fin D → ℂ) (A : Fin N → MPSTensor d D)
    (σ : Cfg d N) : ℂ :=
  vL ⬝ᵥ (List.ofFn fun s => A s (σ s)).prod *ᵥ vR

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2330–2333.
The bond-dimension-one tensor of a product state: at site `s` the matrix of physical
index `i` is the `1 × 1` matrix $a^{i,[s]}$. -/
def productSiteTensor (a : Fin N → Fin d → ℂ) : Fin N → MPSTensor d 1 :=
  fun s i => Matrix.of fun _ _ => a s i

/-- The ordered product of `1 × 1` matrices has entry the product of the entries. -/
private lemma prod_ofFn_one_apply :
    ∀ {N : ℕ} (M : Fin N → Matrix (Fin 1) (Fin 1) ℂ),
      (List.ofFn M).prod 0 0 = ∏ s, M s 0 0
  | 0, M => by simp
  | N + 1, M => by
    rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ, Matrix.mul_apply,
      Fin.sum_univ_one, prod_ofFn_one_apply (fun s => M s.succ)]

/-- Source: arXiv:2011.12127, lines 2330–2333. A product state is an MPS with `D = 1`:
the open-boundary contraction of the `1 × 1` matrices $a^{i_s,[s]}$, with trivial boundary
vectors, is the coefficient $a^{i_1,[1]}\cdots a^{i_N,[N]}$ of the product vector with
local vectors $\lvert\phi^s\rangle=\sum_i a^{i,[s]}\lvert i\rangle$. -/
theorem siteOpenCoeff_productSiteTensor (a : Fin N → Fin d → ℂ) (σ : Cfg d N) :
    siteOpenCoeff 1 1 (productSiteTensor a) σ = productVector a σ := by
  have h := prod_ofFn_one_apply (fun s => productSiteTensor a s (σ s))
  simp only [siteOpenCoeff, dotProduct, mulVec, Fin.sum_univ_one, Pi.one_apply, one_mul,
    mul_one]
  rw [h]
  rfl

/-- Bridge: a site-independent family contracts to the translation-invariant open-boundary
state `openState` of `OpenBoundary`. -/
theorem siteOpenCoeff_const (vL vR : Fin D → ℂ) (A : MPSTensor d D) (σ : Cfg d N) :
    siteOpenCoeff vL vR (fun _ => A) σ = openState vL vR A N σ := by
  rw [siteOpenCoeff, openState_apply, openCoeff_def, evalWord_ofFn_eq_prod]

/-- Source: arXiv:2011.12127, lines 2330–2333, site-independent case. When every site
carries the same local vector $\sum_i a^i\lvert i\rangle$, the translation-invariant
open-boundary state of the one-site `D = 1` tensor is the product vector. -/
theorem openState_productSiteTensor_const (a : Fin d → ℂ) (σ : Cfg d N) :
    openState 1 1 (productSiteTensor (fun (_ : Fin 1) => a) 0) N σ =
      productVector (fun _ => a) σ := by
  rw [← siteOpenCoeff_const]
  exact siteOpenCoeff_productSiteTensor (fun _ => a) σ

/-- Source: arXiv:2011.12127, lines 2330–2333, site-independent case. For `D = 1` the
trace closure is trivial, so the periodic vector of the one-site tensor is also the product
vector. -/
theorem mpv_productSiteTensor_const (a : Fin d → ℂ) (σ : Cfg d N) :
    mpv (productSiteTensor (fun (_ : Fin 1) => a) 0) σ = productVector (fun _ => a) σ := by
  rw [← openState_productSiteTensor_const, openState_apply, openCoeff_def, mpv, coeff,
    Matrix.trace_fin_one]
  simp [dotProduct, mulVec]

end MPSTensor
