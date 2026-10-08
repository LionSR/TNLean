/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Perturbing a product of three bounded operators

Replacing three composable operators one at a time gives a norm estimate
for the difference of their products. This elementary estimate is used for
finite boundary Grams and supported inverses in Nachtergaele,
arXiv:cond-mat/9410110, Lemma `commutation` (i), lines 2442--2531.
The statement involves only bounded linear operators.
-/

namespace ContinuousLinearMap
variable {𝕜 E F G W : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]
/-- Telescoping three composable operators bounds their product difference
by the three individual differences. This estimate applies without finite
dimension or completeness hypotheses. -/
theorem norm_comp_three_sub_le
    (A a : G →L[𝕜] W) (B b : F →L[𝕜] G) (C c : E →L[𝕜] F) :
    ‖A.comp (B.comp C) - a.comp (b.comp c)‖ ≤
      ‖A - a‖ * ‖B‖ * ‖C‖ + ‖a‖ * ‖B - b‖ * ‖C‖ +
        ‖a‖ * ‖b‖ * ‖C - c‖ := by
  have hId : A.comp (B.comp C) - a.comp (b.comp c) =
      (A - a).comp (B.comp C) + a.comp ((B - b).comp C) +
        a.comp (b.comp (C - c)) := by
    simp only [sub_comp, comp_sub]
    abel
  have hBound (f : G →L[𝕜] W) (g : F →L[𝕜] G) (h : E →L[𝕜] F) :
      ‖f.comp (g.comp h)‖ ≤ ‖f‖ * ‖g‖ * ‖h‖ := by
    calc
      _ ≤ ‖f‖ * (‖g‖ * ‖h‖) := (opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg f))
      _ = _ := (mul_assoc _ _ _).symm
  rw [hId]
  calc
    _ ≤ ‖(A - a).comp (B.comp C)‖ + ‖a.comp ((B - b).comp C)‖ +
        ‖a.comp (b.comp (C - c))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add (hBound _ _ _) (hBound _ _ _)) (hBound _ _ _)
end ContinuousLinearMap

namespace ContinuousLinearMap
/-- Three vanishing operator differences and bounded remaining products give
a vanishing product difference. The normed spaces may vary with the index,
and the filter is arbitrary. -/
theorem tendsto_norm_comp_three_sub_zero_of_bounds
    {ι : Type*} {l : Filter ι} {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F G W : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
    [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace 𝕜 (G i)]
    [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace 𝕜 (W i)]
    (A a : (i : ι) → G i →L[𝕜] W i)
    (B b : (i : ι) → F i →L[𝕜] G i)
    (C c : (i : ι) → E i →L[𝕜] F i) {K : ℝ}
    (hBound : ∀ᶠ i in l, ‖B i‖ * ‖C i‖ ≤ K ∧
      ‖a i‖ * ‖C i‖ ≤ K ∧ ‖a i‖ * ‖b i‖ ≤ K)
    (hA : Filter.Tendsto (fun i => ‖A i - a i‖) l (nhds 0))
    (hB : Filter.Tendsto (fun i => ‖B i - b i‖) l (nhds 0))
    (hC : Filter.Tendsto (fun i => ‖C i - c i‖) l (nhds 0)) :
    Filter.Tendsto (fun i => ‖(A i).comp ((B i).comp (C i)) -
      (a i).comp ((b i).comp (c i))‖) l (nhds 0) := by
  have hUpper : Filter.Tendsto
      (fun i => K * (‖A i - a i‖ + ‖B i - b i‖ + ‖C i - c i‖)) l (nhds 0) := by
    simpa only [add_zero, mul_zero] using (hA.add hB |>.add hC).const_mul K
  refine squeeze_zero' (Filter.Eventually.of_forall fun i => norm_nonneg _) ?_ hUpper
  filter_upwards [hBound] with i hi
  refine (norm_comp_three_sub_le (A i) (a i) (B i) (b i) (C i) (c i)).trans ?_
  nlinarith [mul_le_mul_of_nonneg_left hi.1 (norm_nonneg (A i - a i)),
    mul_le_mul_of_nonneg_left hi.2.1 (norm_nonneg (B i - b i)),
    mul_le_mul_of_nonneg_right hi.2.2 (norm_nonneg (C i - c i))]
end ContinuousLinearMap
