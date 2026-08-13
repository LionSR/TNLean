/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Pointwise convergence of endomorphisms in finite dimension

Let $E$ be a finite-dimensional complex normed space and let $S_N$ and $P$ be
continuous linear endomorphisms of $E$. If $S_N(x)\to P(x)$ for every $x\in E$,
then $S_N\to P$ in the operator norm.

Evaluation on a finite basis identifies the endomorphisms of $E$ with a finite
product of copies of $E$, linearly and bijectively. In finite dimension both
directions of this identification are continuous, so coordinatewise convergence
of the evaluations transports back to convergence of the maps themselves.

## Main statements

* `ContinuousLinearMap.tendsto_of_tendsto_apply_of_finiteDimensional`: pointwise
  convergence of continuous linear endomorphisms of a finite-dimensional space
  implies convergence in the operator norm.
-/

open Filter
open scoped Topology

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- In finite dimension, pointwise convergence of continuous linear
endomorphisms implies convergence in the operator norm: evaluation on a finite
basis is a linear isomorphism onto a finite product, hence a homeomorphism. -/
theorem tendsto_of_tendsto_apply_of_finiteDimensional {S : ℕ → E →L[ℂ] E} {P : E →L[ℂ] E}
    (h : ∀ x : E, Tendsto (fun n : ℕ ↦ S n x) atTop (𝓝 (P x))) :
    Tendsto S atTop (𝓝 P) := by
  classical
  let ι := Fin (Module.finrank ℂ E)
  let b := Module.finBasis ℂ E
  -- Evaluation on the basis, as a continuous linear map into a finite product.
  let Φ : (E →L[ℂ] E) →L[ℂ] (ι → E) :=
    ContinuousLinearMap.pi fun i ↦ (ContinuousLinearMap.apply ℂ E) (b i)
  have hΦ : ∀ (f : E →L[ℂ] E) (i : ι), Φ f i = f (b i) := fun f i ↦
    ContinuousLinearMap.pi_apply _ f i
  -- `Φ` is bijective: maps are determined by their values on the basis.
  have hinj : Function.Injective Φ.toLinearMap := by
    intro f g hfg
    have hfg' : ∀ i : ι, f (b i) = g (b i) := fun i ↦
      calc f (b i) = Φ f i := (hΦ f i).symm
        _ = Φ g i := congrFun hfg i
        _ = g (b i) := hΦ g i
    have hlin : f.toLinearMap = g.toLinearMap := b.ext hfg'
    exact ContinuousLinearMap.ext fun x ↦ LinearMap.congr_fun hlin x
  have hsurj : Function.Surjective Φ.toLinearMap := by
    intro w
    refine ⟨LinearMap.toContinuousLinearMap (b.constr ℂ w), ?_⟩
    ext i
    change Φ (LinearMap.toContinuousLinearMap (b.constr ℂ w)) i = w i
    rw [hΦ]
    exact b.constr_basis (M' := E) ℂ w i
  let e := LinearEquiv.ofBijective Φ.toLinearMap ⟨hinj, hsurj⟩
  -- Both directions are continuous in finite dimension.
  have hfwd : Continuous e := Φ.toLinearMap.continuous_of_finiteDimensional
  have hbwd : Continuous e.symm := e.symm.toLinearMap.continuous_of_finiteDimensional
  -- Convergence of the evaluations, then transport back.
  have hEval : Tendsto (fun n : ℕ ↦ e (S n)) atTop (𝓝 (e P)) := by
    rw [tendsto_pi_nhds]
    intro i
    have hS : ∀ n : ℕ, e (S n) i = S n (b i) := fun n ↦ hΦ (S n) i
    have hP : e P i = P (b i) := hΦ P i
    simp_rw [hS, hP]
    exact h (b i)
  have hb := (hbwd.tendsto (e P)).comp hEval
  have heq : e.symm ∘ (fun n : ℕ ↦ e (S n)) = S := by
    funext n
    exact e.symm_apply_apply (S n)
  rw [heq] at hb
  simpa only [LinearEquiv.symm_apply_apply] using hb

end ContinuousLinearMap
