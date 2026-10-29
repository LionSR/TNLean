/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.FrustrationFree

/-!
# Gap comparison for parity-layer regional replacements

The comparison uses squared norms throughout. QICLean's converse applies to every unit
vector. This module proves the analytic comparison for supplied commuting parity families;
it does not assert the full chain theorem or its operator Schmidt rank conclusion.

**Local fix (squared norms):** The proof of ALVV, arXiv:1602.08828v2, Theorem 5.14
prints norms where the two detectability inequalities require squared norms. See
`docs/paper-gaps/alvv16_ff_rank.tex`, which also records an independent counterexample
to the printed rank bound for interior regions.
-/

open scoped InnerProductSpace
open ContinuousLinearMap

namespace TNLean.MPS.AreaLaw.ALVV

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- A commuting parity family after regional collapse: the exterior terms followed by
one regional layer projector. ALVV, Definition 5.10 and Theorem 5.14. -/
noncomputable def collapsedLayer (h : ℕ → E →L[𝕜] E) (s : Finset ℕ) (m i : ℕ) :
    E →L[𝕜] E :=
  if i < m then restrictedTerm h (Finset.range m \ s) i
  else if i = m then 1 - regionalProjection h s m else 0

/-- Every term in a collapsed parity layer is a projection. -/
theorem isStarProjection_collapsedLayer {h : ℕ → E →L[𝕜] E}
    (hh : ∀ i, IsStarProjection (h i)) (hc : ∀ i j, Commute (h i) (h j))
    (s : Finset ℕ) (m i : ℕ) : IsStarProjection (collapsedLayer h s m i) := by
  classical
  unfold collapsedLayer
  split
  · exact isStarProjection_restrictedTerm hh _ i
  split
  · exact (isStarProjection_regionalProjection hh s (fun i _ j _ ↦ hc i j) m).one_sub
  · exact IsStarProjection.zero _

omit [CompleteSpace E] in
private theorem commute_term_regionalProjection {h : ℕ → E →L[𝕜] E}
    (hc : ∀ i j, Commute (h i) (h j)) (s : Finset ℕ) (m i : ℕ) :
    Commute (h i) (regionalProjection h s m) := by
  classical
  apply commute_complementProd
  intro j _
  unfold restrictedTerm
  split
  · exact hc i j
  · exact Commute.zero_right _

omit [CompleteSpace E] in
/-- Collapsed terms of the same parity commute, including the regional projector. -/
theorem commute_collapsedLayer {h : ℕ → E →L[𝕜] E}
    (hc : ∀ i j, Commute (h i) (h j)) (s : Finset ℕ) (m i j : ℕ) :
    Commute (collapsedLayer h s m i) (collapsedLayer h s m j) := by
  classical
  have hterm (k : ℕ) : Commute (restrictedTerm h (Finset.range m \ s) k)
      (1 - regionalProjection h s m) := by
    unfold restrictedTerm
    split
    · exact (Commute.one_right _).sub_right (commute_term_regionalProjection hc s m k)
    · exact Commute.zero_left _
  unfold collapsedLayer
  split_ifs <;> first
    | exact commute_restrictedTerm _ (fun i _ j _ ↦ hc i j) i j
    | exact hterm i
    | exact (hterm j).symm
    | exact Commute.refl _
    | exact Commute.zero_right _
    | exact Commute.zero_left _

omit [CompleteSpace E] in
/-- The actual complementary product is unchanged by collapsing one parity layer.
ALVV, Theorem 5.14, detectability-operator identity. -/
theorem complementProd_collapsedLayer {h : ℕ → E →L[𝕜] E}
    (hc : ∀ i j, Commute (h i) (h j)) (s : Finset ℕ) (m : ℕ) :
    complementProd (collapsedLayer h s m) (m + 1) = complementProd h m := by
  classical
  have hprefix (k : ℕ) (hk : k ≤ m) :
      complementProd (collapsedLayer h s m) k =
        complementProd (restrictedTerm h (Finset.range m \ s)) k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [complementProd_succ, complementProd_succ, ih (by omega)]
      simp only [collapsedLayer, show k < m by omega, ↓reduceIte]
  rw [complementProd_succ, hprefix m le_rfl]
  simp only [collapsedLayer, lt_self_iff_false, ↓reduceIte, sub_sub_cancel]
  exact regionalProjection_mul_complement hc s m

omit [CompleteSpace E] in
/-- The collapsed parity sum retains each exterior term and adds exactly one layer term. -/
theorem sum_collapsedLayer (h : ℕ → E →L[𝕜] E) (s : Finset ℕ) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), collapsedLayer h s m i =
      (∑ i ∈ Finset.range m, restrictedTerm h (Finset.range m \ s) i) +
        (1 - regionalProjection h s m) := by
  classical
  rw [Finset.sum_range_succ]
  congr 1
  · exact Finset.sum_congr rfl fun i hi ↦ by
      simp only [collapsedLayer, Finset.mem_range.mp hi, ↓reduceIte]
  · simp [collapsedLayer]

/-- The converse inequality for the actual regional replacement of two commuting parity
families, including all exterior terms. ALVV, Theorem 5.14, corrected squared-norm form. -/
theorem collapsedLayer_converse {e o : ℕ → E →L[𝕜] E}
    (he : ∀ i, IsStarProjection (e i)) (hce : ∀ i j, Commute (e i) (e j))
    (ho : ∀ i, IsStarProjection (o i)) (hco : ∀ i j, Commute (o i) (o j))
    (s t : Finset ℕ) (m : ℕ) {x : E} (hx : ‖x‖ = 1) :
    1 - 3 * RCLike.re ⟪x,
      ((∑ i ∈ Finset.range m, restrictedTerm e (Finset.range m \ s) i) +
        (1 - regionalProjection e s m) +
        ((∑ i ∈ Finset.range m, restrictedTerm o (Finset.range m \ t) i) +
          (1 - regionalProjection o t m))) x⟫_𝕜 ≤
      ‖complementProd e m (complementProd o m x)‖ ^ 2 := by
  have h := one_sub_three_mul_le_norm_sq_complementProd_comp
    (isStarProjection_collapsedLayer he hce s m) (commute_collapsedLayer hce s m)
    (isStarProjection_collapsedLayer ho hco t m) (commute_collapsedLayer hco t m)
    (m + 1) (m + 1) hx
  rwa [sum_collapsedLayer, sum_collapsedLayer,
    complementProd_collapsedLayer hce, complementProd_collapsedLayer hco] at h

/-- Concatenate the odd family and then the even family, so the latter acts last.
ALVV, Definition 5.11. -/
noncomputable def parityOrderedTerm (e o : ℕ → E →L[𝕜] E) (m i : ℕ) :
    E →L[𝕜] E := if i < m then o i else e (i - m)

/-- The concatenated family consists of projections. -/
theorem isStarProjection_parityOrderedTerm {e o : ℕ → E →L[𝕜] E}
    (he : ∀ i, IsStarProjection (e i)) (ho : ∀ i, IsStarProjection (o i)) (m i : ℕ) :
    IsStarProjection (parityOrderedTerm e o m i) := by
  unfold parityOrderedTerm
  split
  · exact ho i
  · exact he _

omit [CompleteSpace E] in
/-- The ordered complementary product is the literal two-layer detectability operator.
ALVV, Definition 5.11. -/
theorem complementProd_parityOrderedTerm (e o : ℕ → E →L[𝕜] E) (m : ℕ) :
    complementProd (parityOrderedTerm e o m) (m + m) =
      complementProd e m * complementProd o m := by
  have hprefix (k : ℕ) (hk : k ≤ m) :
      complementProd (parityOrderedTerm e o m) k = complementProd o k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [complementProd_succ, complementProd_succ, ih (by omega)]
      simp [parityOrderedTerm, show k < m by omega]
  have hsuffix (k : ℕ) : complementProd (parityOrderedTerm e o m) (m + k) =
      complementProd e k * complementProd o m := by
    induction k with
    | zero => simp [hprefix m le_rfl]
    | succ k ih =>
      rw [Nat.add_succ, complementProd_succ, ih, complementProd_succ, mul_assoc]
      simp [parityOrderedTerm]
  exact hsuffix m

omit [CompleteSpace E] in
/-- The ordered family has the original two parity sums as its Hamiltonian. -/
theorem sum_parityOrderedTerm (e o : ℕ → E →L[𝕜] E) (m : ℕ) :
    ∑ i ∈ Finset.range (m + m), parityOrderedTerm e o m i =
      (∑ i ∈ Finset.range m, e i) + ∑ i ∈ Finset.range m, o i := by
  classical
  rw [Finset.sum_range_add, add_comm]
  congr 1
  · exact Finset.sum_congr rfl fun i _ ↦ by simp [parityOrderedTerm]
  · exact Finset.sum_congr rfl fun i hi ↦ by
      simp [parityOrderedTerm, Finset.mem_range.mp hi]

/-- A complementary product preserves the orthogonal complement of the common kernel.
This justifies applying the original gap to the detectability output in ALVV, Theorem 5.14. -/
theorem complementProd_mem_orthogonal {h : ℕ → E →L[𝕜] E}
    (hh : ∀ i, IsStarProjection (h i)) (m : ℕ) {x : E}
    (hx : x ∈ (⨅ i : Fin m, LinearMap.ker (h i).toLinearMap)ᗮ) :
    complementProd h m x ∈ (⨅ i : Fin m, LinearMap.ker (h i).toLinearMap)ᗮ := by
  have hprod (k : ℕ) (hk : k ≤ m) :
      complementProd h k x ∈ (⨅ i : Fin m, LinearMap.ker (h i).toLinearMap)ᗮ := by
    induction k with
    | zero => exact hx
    | succ k ih =>
      intro z hz
      have hz' : h k z = 0 := by
        simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hz
        exact hz ⟨k, by omega⟩
      rw [complementProd_succ_apply, inner_sub_right,
        ← IsStarProjection.inner_apply_left (hh k), hz', inner_zero_left,
        (ih (by omega)) z hz, sub_zero]
  exact hprod m le_rfl

open Classical in
/-- Explicit squared-norm gap comparison for a regional collapse of two parity families.
The bounded-commutation and gap premises refer only to the original ordered family.
ALVV, Theorem 5.14(3). The conclusion holds for every unit vector orthogonal to the full
original kernel, without an eigenvector premise. -/
theorem collapsedLayer_gap {e o : ℕ → E →L[𝕜] E}
    (he : ∀ i, IsStarProjection (e i)) (hce : ∀ i j, Commute (e i) (e j))
    (ho : ∀ i, IsStarProjection (o i)) (hco : ∀ i j, Commute (o i) (o j))
    (s t : Finset ℕ) (m : ℕ) {g : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (hg : ∀ i < m + m,
      ((Finset.range (m + m)).filter (fun j ↦ j ≠ i ∧
        ¬Commute (parityOrderedTerm e o m i) (parityOrderedTerm e o m j))).card ≤ g)
    (hgap : ∀ y ∈ (⨅ i : Fin (m + m),
        LinearMap.ker (parityOrderedTerm e o m i).toLinearMap)ᗮ,
      γ * ‖y‖ ^ 2 ≤ RCLike.re ⟪y,
        ((∑ i ∈ Finset.range m, e i) + ∑ i ∈ Finset.range m, o i) y⟫_𝕜)
    {x : E} (hx : ‖x‖ = 1)
    (hxperp : x ∈ (⨅ i : Fin (m + m),
      LinearMap.ker (parityOrderedTerm e o m i).toLinearMap)ᗮ) :
    γ / (3 * (γ + (g : ℝ) ^ 2)) ≤
      RCLike.re ⟪x,
        ((∑ i ∈ Finset.range m, restrictedTerm e (Finset.range m \ s) i) +
          (1 - regionalProjection e s m) +
          ((∑ i ∈ Finset.range m, restrictedTerm o (Finset.range m \ t) i) +
            (1 - regionalProjection o t m))) x⟫_𝕜 := by
  have hh := isStarProjection_parityOrderedTerm he ho m
  have hDL := re_inner_sum_complementProd_le hh hg x
  have hy := hgap _ (complementProd_mem_orthogonal hh (m + m) hxperp)
  rw [sum_parityOrderedTerm, complementProd_parityOrderedTerm] at hDL
  rw [complementProd_parityOrderedTerm] at hy
  have hconv := collapsedLayer_converse he hce ho hco s t m hx
  change 1 - 3 * _ ≤ ‖(complementProd e m * complementProd o m) x‖ ^ 2 at hconv
  rw [hx, one_pow] at hDL
  have hden : 0 < γ + (g : ℝ) ^ 2 := by positivity
  apply (div_le_iff₀ (mul_pos (by norm_num) hden)).mpr
  nlinarith [sq_nonneg (g : ℝ)]

/-- The explicit comparison is linear in the original gap in the normalized chain
regime. ALVV, Theorem 5.14(3), with commutation degree two and constant three in the
converse. A gap parameter may always be decreased to at most one. -/
theorem gap_ratio_le {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    γ / 15 ≤ γ / (3 * (γ + (2 : ℝ) ^ 2)) := by
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 15)
    (by positivity : 0 < 3 * (γ + (2 : ℝ) ^ 2))).mpr
  nlinarith

end TNLean.MPS.AreaLaw.ALVV
