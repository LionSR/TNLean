/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.FrustrationFree.FrustrationFreeGap
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.FrustrationFree.FrustrationFreeRank
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.FrustrationFree.PhysicalFrustrationFreeTruncation
import QICLean.ManyBody.Hamiltonian.FrustrationFreeSweep

/-!
# The regional replacement on a nearest-neighbor chain

The parity commutations and commutation degree two are derived from the local
supports. The gap comparison concerns the regional replacement of any even and any odd
bond set (`parityReplacement_gap`).

The regional truncation `physicalFrustrationFreeTruncation` of a bond interaction is the
regional replacement of the bonds inside its site interval
(`physicalFrustrationFreeTruncation_eq_regionalReplacementMatrix`); this gives its
quadratic-form gap and its prefix and suffix rank bound.

**Local fix:** The all-cut rank bound in ALVV, arXiv:1602.08828v2, Theorem 5.14(2)
is `d²+3` for interior regions and `d²+2` for prefix/suffix regions. Squared norms
are used in the gap comparison. See `docs/paper-gaps/alvv16_ff_rank.tex`.
-/

open ManyBody (interval mem_interval)

open Matrix ContinuousLinearMap
open scoped InnerProductSpace

namespace TNLean.MPS.AreaLaw.ALVV

section Parity

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A single global parity of the original bond family. -/
noncomputable def colorTerm (h : ℕ → E →L[𝕜] E) (c i : ℕ) : E →L[𝕜] E :=
  if i % 2 = c then h i else 0

private theorem colorTerm_projection [CompleteSpace E] {h : ℕ → E →L[𝕜] E}
    (hh : ∀ i, IsStarProjection (h i)) (c i : ℕ) : IsStarProjection (colorTerm h c i) := by
  classical
  unfold colorTerm
  split
  · exact hh i
  · exact IsStarProjection.zero _

private theorem colorTerm_commute {h : ℕ → E →L[𝕜] E}
    (hc : ∀ i j, i + 1 ≠ j → j + 1 ≠ i → Commute (h i) (h j)) (c i j : ℕ) :
    Commute (colorTerm h c i) (colorTerm h c j) := by
  classical
  unfold colorTerm
  split <;> split
  · apply hc <;> omega
  · exact Commute.zero_right _
  · exact Commute.zero_left _
  · exact Commute.zero_left _

private theorem sum_colorTerm (h : ℕ → E →L[𝕜] E) (m : ℕ) :
    (∑ i ∈ Finset.range m, colorTerm h 0 i) + ∑ i ∈ Finset.range m, colorTerm h 1 i =
      ∑ i ∈ Finset.range m, h i := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi := Nat.mod_lt i (by norm_num : 0 < 2)
  by_cases h0 : i % 2 = 0
  · simp [colorTerm, h0]
  · simp [colorTerm, show i % 2 = 1 by omega]

private theorem ordered_colorTerm_active {h : ℕ → E →L[𝕜] E} {m j : ℕ}
    (hj : j < m + m)
    (hn : parityOrderedTerm (colorTerm h 0) (colorTerm h 1) m j ≠ 0) :
    ∃ p < m, j = (if p % 2 = 0 then m + p else p) ∧
      parityOrderedTerm (colorTerm h 0) (colorTerm h 1) m j = h p := by
  classical
  by_cases hjm : j < m
  · have hpar : j % 2 = 1 := by
      by_contra hp
      exact hn (by simp [parityOrderedTerm, colorTerm, hjm, hp])
    refine ⟨j, hjm, ?_, ?_⟩
    · simp [show j % 2 ≠ 0 by omega]
    · simp [parityOrderedTerm, colorTerm, hjm, hpar]
  · have hpar : (j - m) % 2 = 0 := by
      by_contra hp
      exact hn (by simp [parityOrderedTerm, colorTerm, hjm, hp])
    refine ⟨j - m, by omega, ?_, ?_⟩
    · simp only [hpar, ↓reduceIte]
      omega
    · simp [parityOrderedTerm, colorTerm, hjm, hpar]

open Classical in
/-- Even-then-odd ordering does not increase the nearest-neighbor commutation degree:
every active factor has at most the two adjacent original bonds as noncommuting factors.
ALVV, Theorem 5.14(3), degree-two input to the detectability lemma. -/
theorem commutationDegree_parityOrderedTerm_le_two {h : ℕ → E →L[𝕜] E}
    (hc : ∀ i j, i + 1 ≠ j → j + 1 ≠ i → Commute (h i) (h j)) (m : ℕ) :
    ∀ i < m + m,
      ((Finset.range (m + m)).filter (fun j ↦ j ≠ i ∧
        ¬Commute (parityOrderedTerm (colorTerm h 0) (colorTerm h 1) m i)
          (parityOrderedTerm (colorTerm h 0) (colorTerm h 1) m j))).card ≤ 2 := by
  intro i hi
  let T := parityOrderedTerm (colorTerm h 0) (colorTerm h 1) m
  let f : ℕ → ℕ := fun p ↦ if p % 2 = 0 then m + p else p
  change ((Finset.range (m + m)).filter (fun j ↦ j ≠ i ∧ ¬Commute (T i) (T j))).card ≤ 2
  by_cases hzero : T i = 0
  · have hempty : ((Finset.range (m + m)).filter (fun j ↦ j ≠ i ∧
        ¬Commute (T i) (T j))) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro j _ hj
      exact hj.2 (hzero ▸ Commute.zero_left _)
    simpa only [hempty, Finset.card_empty] using (show 0 ≤ 2 by omega)
  · obtain ⟨p, _, _, hTi⟩ := ordered_colorTerm_active hi hzero
    change T i = h p at hTi
    have hsub : ((Finset.range (m + m)).filter (fun j ↦ j ≠ i ∧ ¬Commute (T i) (T j))) ⊆
        {f (p - 1), f (p + 1)} := by
      intro j hj
      obtain ⟨hj, -, hnc⟩ := Finset.mem_filter.mp hj
      have hTj : T j ≠ 0 := by
        intro hz
        exact hnc (hz ▸ Commute.zero_right _)
      obtain ⟨r, _, hjr, hTr⟩ := ordered_colorTerm_active (Finset.mem_range.mp hj) hTj
      change T j = h r at hTr
      have hnear : p + 1 = r ∨ r + 1 = p := by
        by_contra hn
        exact hnc (by rw [hTi, hTr]; exact hc p r (by omega) (by omega))
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hnear with h | h
      · right
        simpa only [f, ← h] using hjr
      · left
        have : r = p - 1 := by omega
        simpa only [f, ← this] using hjr
    exact (Finset.card_le_card hsub).trans Finset.card_le_two

private theorem regionalProjection_congr_on {h h' : ℕ → E →L[𝕜] E}
    (s : Finset ℕ) (m : ℕ) (heq : ∀ i < m, i ∈ s → h i = h' i) :
    regionalProjection h s m = regionalProjection h' s m := by
  classical
  induction m with
  | zero => rfl
  | succ m ih =>
    change (1 - restrictedTerm h s m) * regionalProjection h s m =
      (1 - restrictedTerm h' s m) * regionalProjection h' s m
    rw [ih (fun i hi hs ↦ heq i (by omega) hs)]
    by_cases hm : m ∈ s <;> simp [restrictedTerm, hm, heq m (by omega)]

private theorem regionalProjection_colorTerm (h : ℕ → E →L[𝕜] E) {s t : Finset ℕ}
    (hs : ∀ i ∈ s, i % 2 = 0) (ht : ∀ i ∈ t, i % 2 = 1) (m : ℕ) :
    regionalProjection (colorTerm h 0) s m = regionalProjection h s m ∧
    regionalProjection (colorTerm h 1) t m = regionalProjection h t m := by
  classical
  constructor
  · apply regionalProjection_congr_on
    intro i _ hi
    simp [colorTerm, hs i hi]
  · apply regionalProjection_congr_on
    intro i _ hi
    simp [colorTerm, ht i hi]

private theorem collapsed_colorTerm_sum (h : ℕ → E →L[𝕜] E) {s t : Finset ℕ}
    (hs : ∀ i ∈ s, i % 2 = 0) (ht : ∀ i ∈ t, i % 2 = 1) (m : ℕ) :
    (∑ i ∈ Finset.range m,
      restrictedTerm (colorTerm h 0) (Finset.range m \ s) i) +
      (1 - regionalProjection (colorTerm h 0) s m) +
      ((∑ i ∈ Finset.range m,
        restrictedTerm (colorTerm h 1) (Finset.range m \ t) i) +
        (1 - regionalProjection (colorTerm h 1) t m)) =
      regionalReplacement h s t m := by
  classical
  obtain ⟨he, ho⟩ := regionalProjection_colorTerm h hs ht m
  rw [he, ho]
  have hsum : (∑ i ∈ Finset.range m,
      restrictedTerm (colorTerm h 0) (Finset.range m \ s) i) +
      (∑ i ∈ Finset.range m,
        restrictedTerm (colorTerm h 1) (Finset.range m \ t) i) =
      ∑ i ∈ Finset.range m, restrictedTerm h (Finset.range m \ (s ∪ t)) i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have him := Finset.mem_range.mp hi
    by_cases hpar : i % 2 = 0
    · have hit : i ∉ t := fun hit ↦ by have := ht i hit; omega
      by_cases his : i ∈ s <;> simp [restrictedTerm, colorTerm, him, hpar, his, hit]
    · have hpar' : i % 2 = 1 := by omega
      have his : i ∉ s := fun his ↦ by have := hs i his; omega
      by_cases hit : i ∈ t <;> simp [restrictedTerm, colorTerm, him, hpar', his, hit]
  unfold regionalReplacement
  rw [← hsum]
  abel

end Parity

section Chain

variable {L q m : ℕ}

/-- The finite bond family, extended by zero and acting on the Euclidean chain space. -/
noncomputable def chainTerm
    (h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (i : ℕ) :
    EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ] EuclideanSpace ℂ (Fin L → Fin q) :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)) (bondTermExtension h i)

/-- Each extended chain term is an orthogonal projection when the supplied terms are. -/
theorem isStarProjection_chainTerm
    {h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hh : ∀ i, IsStarProjection (h i)) (i : ℕ) : IsStarProjection (chainTerm h i) := by
  classical
  unfold chainTerm bondTermExtension
  split
  · exact (hh _).map (Matrix.toEuclideanCLM (𝕜 := ℂ)
      (n := Fin L → Fin q)).toStarAlgHom
  · rw [map_zero]
    exact IsStarProjection.zero _

/-- The extended chain terms below `m` add up to the operator of the supplied bond sum. -/
theorem sum_range_chainTerm
    (h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    ∑ i ∈ Finset.range m, chainTerm h i =
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)) (∑ i, h i) := by
  classical
  rw [map_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp [chainTerm, bondTermExtension, i.isLt]

/-- Disjoint nearest-neighbor bond supports give the commutations needed by detectability.
The commutations are derived from support and are not additional premises. -/
theorem chainTerm_commute_of_not_adjacent
    {h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hsupp : ∀ i, ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) (h i)
      (interval L i (i + 2))) (i j : ℕ) (hij : i + 1 ≠ j) (hji : j + 1 ≠ i) :
    Commute (chainTerm h i) (chainTerm h j) := by
  classical
  by_cases heq : i = j
  · subst j
    exact Commute.refl _
  have hd : Disjoint (interval L j (j + 2)) (interval L i (i + 2)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [mem_interval] at hx hy
    omega
  have hc : Commute (bondTermExtension h i) (bondTermExtension h j) :=
    ManyBody.commute_of_mem_supportedOperators_of_disjoint (bondTermExtension_supported hsupp i)
        (bondTermExtension_supported hsupp j) hd.symm
  exact hc.map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)).toMonoidHom

private theorem ker_ordered_chainTerm
    {h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hh : ∀ i, IsStarProjection (h i)) :
    LinearMap.ker ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q))
        (∑ i, h i)).toLinearMap =
      ⨅ i : Fin (m + m), LinearMap.ker
        (parityOrderedTerm (colorTerm (chainTerm h) 0)
          (colorTerm (chainTerm h) 1) m i).toLinearMap := by
  let T := parityOrderedTerm (colorTerm (chainTerm h) 0) (colorTerm (chainTerm h) 1) m
  have hproj := isStarProjection_parityOrderedTerm
    (colorTerm_projection (isStarProjection_chainTerm hh) 0)
    (colorTerm_projection (isStarProjection_chainTerm hh) 1) m
  have hp (i : Fin (m + m)) : (T i).toLinearMap.IsPositive :=
    (ContinuousLinearMap.IsPositive.of_isStarProjection (hproj i)).toLinearMap
  have hk := WeightedPositiveKernel.ker_sum_eq_iInf hp
  have hsum : (∑ i : Fin (m + m), (T i).toLinearMap) =
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)) (∑ i, h i)).toLinearMap := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.sum_apply, ContinuousLinearMap.coe_coe]
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ T i x) (m + m)]
    rw [← _root_.sum_apply]
    dsimp only [T]
    rw [sum_parityOrderedTerm, sum_colorTerm, sum_range_chainTerm]
  rwa [hsum] at hk

/-- Explicit gap for a parity-layer replacement collapsing any set `s` of even bonds and any
set `t` of odd bonds. The only gap premise concerns the original chain; locality supplies
degree two and every collapsed-family identity. ALVV, arXiv:1602.08828v2, Theorem 5.14(3),
lines 1541–1570, with squared norms and the constant-three converse. The source collapses one
region; collapsing a union of disjoint regions of each parity, as in the proof of
Theorem `t:aisff`, lines 1597–1599, is the same argument. -/
theorem parityReplacement_gap
    {h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hh : ∀ i, IsStarProjection (h i))
    (hsupp : ∀ i, ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) (h i)
      (interval L i (i + 2))) {γ : ℝ} (hγ : 0 < γ)
    (hgap : ∀ y ∈ (LinearMap.ker ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q))
        (∑ i, h i)).toLinearMap)ᗮ,
      γ * ‖y‖ ^ 2 ≤ Complex.re ⟪y,
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)) (∑ i, h i) y⟫_ℂ) {s t : Finset ℕ}
    (hs : ∀ i ∈ s, i % 2 = 0) (ht : ∀ i ∈ t, i % 2 = 1)
    {x : EuclideanSpace ℂ (Fin L → Fin q)} (hx : ‖x‖ = 1)
    (hxperp : x ∈ (LinearMap.ker ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q))
        (∑ i, h i)).toLinearMap)ᗮ) :
    γ / (3 * (γ + 4)) ≤ Complex.re ⟪x, regionalReplacement (chainTerm h) s t m x⟫_ℂ := by
  have hc := chainTerm_commute_of_not_adjacent hsupp
  have hproj := isStarProjection_chainTerm hh
  have hk := ker_ordered_chainTerm hh
  have hgap' : ∀ y ∈ (⨅ i : Fin (m + m), LinearMap.ker
      (parityOrderedTerm (colorTerm (chainTerm h) 0)
        (colorTerm (chainTerm h) 1) m i).toLinearMap)ᗮ,
      γ * ‖y‖ ^ 2 ≤ Complex.re ⟪y,
        ((∑ i ∈ Finset.range m, colorTerm (chainTerm h) 0 i) +
          ∑ i ∈ Finset.range m, colorTerm (chainTerm h) 1 i) y⟫_ℂ := by
    rw [← hk, sum_colorTerm, sum_range_chainTerm]
    exact hgap
  have hxperp' : x ∈ (⨅ i : Fin (m + m), LinearMap.ker
      (parityOrderedTerm (colorTerm (chainTerm h) 0)
        (colorTerm (chainTerm h) 1) m i).toLinearMap)ᗮ := by rwa [← hk]
  have hg := collapsedLayer_gap (colorTerm_projection hproj 0) (colorTerm_commute hc 0)
    (colorTerm_projection hproj 1) (colorTerm_commute hc 1)
    s t m hγ (commutationDegree_parityOrderedTerm_le_two hc m) hgap' hx hxperp'
  rw [collapsed_colorTerm_sum _ hs ht] at hg
  norm_num only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num] at hg
  exact hg

end Chain

end TNLean.MPS.AreaLaw.ALVV

/-! ### The regional truncation as a regional replacement

The regional truncation of the site interval `[a, b)` replaces the bonds `[a, b - 1)`: it is the
regional replacement of Definition 5.10 for the even and odd bonds of `[a, b - 1)`. This gives
the quadratic-form gap comparison and the prefix and suffix rank bound of ALVV,
arXiv:1602.08828v2, Theorem 5.14 (`thm:FF-tH`, lines 1541–1570), for the truncation. -/

namespace TNLean.MPS.AreaLaw

open ALVV
open scoped MatrixOrder

variable {L q : ℕ}

private theorem physicalParityProduct_restrict_eq_regionalProjection
    (Φ : ManyBody.BondInteraction L q) (a b p : ℕ) (s : Finset ℕ)
    (hs : ∀ k < L - 1, k ∈ s ↔ a ≤ k ∧ k + 1 < b ∧ k % 2 = p) :
    physicalParityProduct (Φ.restrict fun i ↦ a ≤ i.val ∧ i.val + 1 < b) p =
      regionalProjection (chainTerm Φ.term) s (L - 1) := by
  classical
  unfold physicalParityProduct regionalProjection
  refine ContinuousLinearMap.complementProd_congr fun k hk ↦ ?_
  change (if hk' : k < L - 1 then if k % 2 = p then
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q))
        ((Φ.restrict fun i ↦ a ≤ i.val ∧ i.val + 1 < b).term ⟨k, hk'⟩) else 0 else 0) =
    if k ∈ s then (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q))
      (bondTermExtension Φ.term k) else 0
  simp only [hk, ↓reduceDIte, bondTermExtension, ManyBody.Interaction.restrict_term, hs k hk]
  split_ifs <;> first | rfl | (exfalso; omega) | simp

/-- **The regional truncation is a regional replacement.** The truncation of the site interval
`[a, b)` is the regional replacement, with all exterior bonds retained, of the even and odd
bonds of `[a, b - 1)`. ALVV, arXiv:1602.08828v2, `def:FF-tH`, lines 1467–1487, and
Definition 5.10. -/
theorem physicalFrustrationFreeTruncation_eq_regionalReplacementMatrix
    (Φ : ManyBody.BondInteraction L q) (a b : ℕ) :
    physicalFrustrationFreeTruncation Φ a b =
      regionalReplacementMatrix (bondTermExtension Φ.term) (evenBonds a (b - 1))
        (oddBonds a (b - 1)) (L - 1) := by
  classical
  refine (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)).injective ?_
  change Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) _ =
    Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) _
  rw [toEuclideanCLM_regionalReplacementMatrix]
  change _ = regionalReplacement (chainTerm Φ.term) _ _ _
  simp only [physicalFrustrationFreeTruncation, regionalReplacement, map_add, map_sum,
    StarAlgEquiv.apply_symm_apply]
  rw [physicalParityProduct_restrict_eq_regionalProjection Φ a b 0 (evenBonds a (b - 1))
      (fun k _ ↦ by simp only [evenBonds, Finset.mem_filter, Finset.mem_Ico]; omega),
    physicalParityProduct_restrict_eq_regionalProjection Φ a b 1 (oddBonds a (b - 1))
      (fun k _ ↦ by simp only [oddBonds, Finset.mem_filter, Finset.mem_Ico]; omega),
    Finset.sum_range]
  congr 2
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [restrictedTerm, chainTerm, bondTermExtension, Finset.mem_sdiff,
    Finset.mem_range, i.isLt, Finset.mem_union, evenBonds, oddBonds, Finset.mem_filter,
    Finset.mem_Ico, true_and, Fin.eta]
  split_ifs <;> first | rfl | (exfalso; omega) | simp

/-- **Gap of the regional truncation, in quadratic form.** If the original chain of projection
bond terms has gap `γ > 0` above its zero space in quadratic form, then every unit vector
orthogonal to that zero space has truncated energy at least `γ / (3 (γ + 4))`, for every site
interval. ALVV, arXiv:1602.08828v2, `thm:FF-tH`(3), lines 1562–1570, with squared norms and the
constant-three converse; the zero space of the truncation is the original one by
`zeroSpace_regionalTruncationInteraction`. -/
theorem physicalFrustrationFreeTruncation_gap
    (Φ : ManyBody.BondInteraction L q) (hp : ∀ i, IsStarProjection (Φ.term i))
    {γ : ℝ} (hγ : 0 < γ)
    (hgap : ∀ y ∈ Φ.zeroSpaceᗮ, γ * ‖y‖ ^ 2 ≤
      (⟪y, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) Φ.hamiltonian y⟫_ℂ).re)
    (a b : ℕ) {x : EuclideanSpace ℂ (Fin L → Fin q)} (hx : ‖x‖ = 1)
    (hxperp : x ∈ Φ.zeroSpaceᗮ) :
    γ / (3 * (γ + 4)) ≤ (⟪x, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
      (physicalFrustrationFreeTruncation Φ a b) x⟫_ℂ).re := by
  have hker : Φ.zeroSpace = LinearMap.ker ((Matrix.toEuclideanCLM (𝕜 := ℂ)
      (n := Fin L → Fin q)) (∑ i, Φ.term i)).toLinearMap := by
    rw [ManyBody.Interaction.zeroSpace_eq_groundSpace
      fun i ↦ Matrix.nonneg_iff_posSemidef.mp (hp i).nonneg, ManyBody.groundSpace_zero]
    rfl
  rw [hker] at hgap hxperp
  have hg := parityReplacement_gap hp Φ.mem hγ hgap (s := evenBonds a (b - 1))
    (t := oddBonds a (b - 1)) (fun _ hi ↦ (Finset.mem_filter.mp hi).2)
    (fun _ hi ↦ by have := (Finset.mem_filter.mp hi).2; omega) hx hxperp
  rwa [physicalFrustrationFreeTruncation_eq_regionalReplacementMatrix,
    toEuclideanCLM_regionalReplacementMatrix]

/-- **Rank of a prefix or suffix truncation.** When the site interval starts at the left end of
the chain or reaches its right end, the regional truncation has operator Schmidt rank at most
`q² + 2` at every cut. ALVV, arXiv:1602.08828v2, `thm:FF-tH`(2), lines 1555–1562; for interior
intervals the bound is `q² + 3` (`operatorSchmidtRank_physicalFrustrationFreeTruncation_le`). -/
theorem operatorSchmidtRank_physicalFrustrationFreeTruncation_le_of_boundary (hq : 1 ≤ q)
    (Φ : ManyBody.BondInteraction L q) (a b k : ℕ) (hboundary : a = 0 ∨ L ≤ b) :
    operatorSchmidtRank (ManyBody.cutOperator (interval L 0 k)
      (physicalFrustrationFreeTruncation Φ a b)) ≤ q ^ 2 + 2 := by
  rw [physicalFrustrationFreeTruncation_eq_regionalReplacementMatrix]
  exact rank_regionalReplacementMatrix_le_sq_add_two_of_boundary Φ.term hq Φ.mem a (b - 1) k
    (by omega)

end TNLean.MPS.AreaLaw
