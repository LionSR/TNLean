/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.FrustrationFreeGap
import TNLean.MPS.AreaLaw.ALVV.FrustrationFreeRank

/-!
# The regional replacement on an actual nearest-neighbor chain

The parity commutations and commutation degree two are derived from the actual local
supports. The gap and kernel conclusions concern the literal regional replacement.

**Local fix:** The all-cut rank bound in ALVV, arXiv:1602.08828v2, Theorem 5.14(2)
is `d²+3` for interior regions and `d²+2` for prefix/suffix regions. Squared norms
are used in the gap comparison. See `docs/paper-gaps/alvv16_ff_rank.tex`.
-/

open Matrix ContinuousLinearMap
open scoped InnerProductSpace

namespace TNLean.MPS.AreaLaw.ALVV

section Parity

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A single global parity of the original bond family. -/
noncomputable def colourTerm (h : ℕ → E →L[𝕜] E) (c i : ℕ) : E →L[𝕜] E :=
  if i % 2 = c then h i else 0

private theorem colourTerm_projection [CompleteSpace E] {h : ℕ → E →L[𝕜] E}
    (hh : ∀ i, IsStarProjection (h i)) (c i : ℕ) : IsStarProjection (colourTerm h c i) := by
  classical
  unfold colourTerm
  split
  · exact hh i
  · exact IsStarProjection.zero _

private theorem colourTerm_commute {h : ℕ → E →L[𝕜] E}
    (hc : ∀ i j, i + 1 ≠ j → j + 1 ≠ i → Commute (h i) (h j)) (c i j : ℕ) :
    Commute (colourTerm h c i) (colourTerm h c j) := by
  classical
  unfold colourTerm
  split <;> split
  · apply hc <;> omega
  · exact Commute.zero_right _
  · exact Commute.zero_left _
  · exact Commute.zero_left _

private theorem sum_colourTerm (h : ℕ → E →L[𝕜] E) (m : ℕ) :
    (∑ i ∈ Finset.range m, colourTerm h 0 i) + ∑ i ∈ Finset.range m, colourTerm h 1 i =
      ∑ i ∈ Finset.range m, h i := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi := Nat.mod_lt i (by norm_num : 0 < 2)
  by_cases h0 : i % 2 = 0
  · simp [colourTerm, h0]
  · simp [colourTerm, show i % 2 = 1 by omega]

private theorem ordered_colourTerm_active {h : ℕ → E →L[𝕜] E} {m j : ℕ}
    (hj : j < m + m)
    (hn : parityOrderedTerm (colourTerm h 0) (colourTerm h 1) m j ≠ 0) :
    ∃ p < m, j = (if p % 2 = 0 then m + p else p) ∧
      parityOrderedTerm (colourTerm h 0) (colourTerm h 1) m j = h p := by
  classical
  by_cases hjm : j < m
  · have hpar : j % 2 = 1 := by
      by_contra hp
      exact hn (by simp [parityOrderedTerm, colourTerm, hjm, hp])
    refine ⟨j, hjm, ?_, ?_⟩
    · simp [show j % 2 ≠ 0 by omega]
    · simp [parityOrderedTerm, colourTerm, hjm, hpar]
  · have hpar : (j - m) % 2 = 0 := by
      by_contra hp
      exact hn (by simp [parityOrderedTerm, colourTerm, hjm, hp])
    refine ⟨j - m, by omega, ?_, ?_⟩
    · simp only [hpar, ↓reduceIte]
      omega
    · simp [parityOrderedTerm, colourTerm, hjm, hpar]

open Classical in
/-- Even-then-odd ordering does not increase the nearest-neighbor commutation degree:
every active factor has at most the two adjacent original bonds as noncommuting factors.
ALVV, Theorem 5.14(3), degree-two input to the detectability lemma. -/
theorem commutationDegree_parityOrderedTerm_le_two {h : ℕ → E →L[𝕜] E}
    (hc : ∀ i j, i + 1 ≠ j → j + 1 ≠ i → Commute (h i) (h j)) (m : ℕ) :
    ∀ i < m + m,
      ((Finset.range (m + m)).filter (fun j ↦ j ≠ i ∧
        ¬Commute (parityOrderedTerm (colourTerm h 0) (colourTerm h 1) m i)
          (parityOrderedTerm (colourTerm h 0) (colourTerm h 1) m j))).card ≤ 2 := by
  intro i hi
  let T := parityOrderedTerm (colourTerm h 0) (colourTerm h 1) m
  let f : ℕ → ℕ := fun p ↦ if p % 2 = 0 then m + p else p
  change ((Finset.range (m + m)).filter (fun j ↦ j ≠ i ∧ ¬Commute (T i) (T j))).card ≤ 2
  by_cases hzero : T i = 0
  · have hempty : ((Finset.range (m + m)).filter (fun j ↦ j ≠ i ∧
        ¬Commute (T i) (T j))) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro j _ hj
      exact hj.2 (hzero ▸ Commute.zero_left _)
    simpa only [hempty, Finset.card_empty] using (show 0 ≤ 2 by omega)
  · obtain ⟨p, _, _, hTi⟩ := ordered_colourTerm_active hi hzero
    change T i = h p at hTi
    have hsub : ((Finset.range (m + m)).filter (fun j ↦ j ≠ i ∧ ¬Commute (T i) (T j))) ⊆
        {f (p - 1), f (p + 1)} := by
      intro j hj
      obtain ⟨hj, -, hnc⟩ := Finset.mem_filter.mp hj
      have hTj : T j ≠ 0 := by
        intro hz
        exact hnc (hz ▸ Commute.zero_right _)
      obtain ⟨r, _, hjr, hTr⟩ := ordered_colourTerm_active (Finset.mem_range.mp hj) hTj
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

private theorem regionalProjection_colourTerm (h : ℕ → E →L[𝕜] E) (a b m : ℕ) :
    regionalProjection (colourTerm h 0) (evenBonds a b) m =
        regionalProjection h (evenBonds a b) m ∧
    regionalProjection (colourTerm h 1) (oddBonds a b) m =
        regionalProjection h (oddBonds a b) m := by
  classical
  constructor
  · apply regionalProjection_congr_on
    intro i _ hi
    simp [colourTerm, (Finset.mem_filter.mp hi).2]
  · apply regionalProjection_congr_on
    intro i _ hi
    have hpar := (Finset.mem_filter.mp hi).2
    have : i % 2 = 1 := by omega
    simp [colourTerm, this]

private theorem collapsed_colourTerm_sum (h : ℕ → E →L[𝕜] E) (a b m : ℕ) :
    (∑ i ∈ Finset.range m,
      restrictedTerm (colourTerm h 0) (Finset.range m \ evenBonds a b) i) +
      (1 - regionalProjection (colourTerm h 0) (evenBonds a b) m) +
      ((∑ i ∈ Finset.range m,
        restrictedTerm (colourTerm h 1) (Finset.range m \ oddBonds a b) i) +
        (1 - regionalProjection (colourTerm h 1) (oddBonds a b) m)) =
      regionalReplacement h (evenBonds a b) (oddBonds a b) m := by
  classical
  obtain ⟨he, ho⟩ := regionalProjection_colourTerm h a b m
  rw [he, ho]
  have hsum : (∑ i ∈ Finset.range m,
      restrictedTerm (colourTerm h 0) (Finset.range m \ evenBonds a b) i) +
      (∑ i ∈ Finset.range m,
        restrictedTerm (colourTerm h 1) (Finset.range m \ oddBonds a b) i) =
      ∑ i ∈ Finset.range m,
        restrictedTerm h (Finset.range m \ (evenBonds a b ∪ oddBonds a b)) i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have him := Finset.mem_range.mp hi
    by_cases hpar : i % 2 = 0
    · simp [restrictedTerm, colourTerm, evenBonds, oddBonds, him, hpar]
    · have hpar' : i % 2 = 1 := by omega
      simp [restrictedTerm, colourTerm, evenBonds, oddBonds, him, hpar']
  unfold regionalReplacement
  rw [← hsum]
  abel

end Parity

section Chain

variable {L q m : ℕ}

/-- The actual finite bond family, extended by zero and acting on the Euclidean chain space. -/
noncomputable def chainTerm
    (h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (i : ℕ) :
    EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ] EuclideanSpace ℂ (Fin L → Fin q) :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)) (bondTermExtension h i)

/-- The original nearest-neighbor chain Hamiltonian. -/
noncomputable def chainOperator
    (h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ] EuclideanSpace ℂ (Fin L → Fin q) :=
  ∑ i ∈ Finset.range m, chainTerm h i

/-- The actual regional parity-layer replacement with all exterior bonds retained. -/
noncomputable def chainReplacement
    (h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (a b : ℕ) :
    EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ] EuclideanSpace ℂ (Fin L → Fin q) :=
  regionalReplacement (chainTerm h) (evenBonds a b) (oddBonds a b) m

/-- The regional matrix used for the rank theorem is exactly the chain replacement. -/
theorem toEuclideanCLM_chainReplacementMatrix
    (h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (a b : ℕ) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q))
      (regionalReplacementMatrix (bondTermExtension h) (evenBonds a b) (oddBonds a b) m) =
      chainReplacement h a b :=
  toEuclideanCLM_regionalReplacementMatrix _ _ _ _

private theorem chainTerm_projection
    {h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hh : ∀ i, IsStarProjection (h i)) (i : ℕ) : IsStarProjection (chainTerm h i) := by
  classical
  unfold chainTerm bondTermExtension
  split
  · exact (hh _).map (Matrix.toEuclideanCLM (𝕜 := ℂ)
      (n := Fin L → Fin q)).toStarAlgHom
  · rw [map_zero]
    exact IsStarProjection.zero _

/-- The original operator is exactly the finite sum of the supplied bond matrices. -/
theorem chainOperator_eq_toEuclideanCLM_sum
    (h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    chainOperator h = (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)) (∑ i, h i) := by
  classical
  rw [map_sum]
  change (∑ i ∈ Finset.range m, chainTerm h i) = _
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp [chainTerm, bondTermExtension, i.isLt]

/-- Disjoint nearest-neighbor bond supports give the commutations needed by detectability.
The commutations are derived from support and are not additional premises. -/
theorem chainTerm_commute_of_not_adjacent
    {h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hq : 1 ≤ q)
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
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
    Entropy.commute_of_isSupportedOn_disjoint (bondTermExtension_supported hsupp i)
      (bondTermExtension_supported hsupp j) hd
      (fun _ : Fin L ↦ (⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hq⟩ : Fin q))
  exact hc.map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)).toMonoidHom

private theorem chain_parity_commute
    {h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hq : 1 ≤ q)
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) (a b : ℕ) :
    (∀ i ∈ evenBonds a b, ∀ j ∈ evenBonds a b, Commute (chainTerm h i) (chainTerm h j)) ∧
    (∀ i ∈ oddBonds a b, ∀ j ∈ oddBonds a b, Commute (chainTerm h i) (chainTerm h j)) := by
  constructor
  · intro i hi j hj
    have hi := (Finset.mem_filter.mp hi).2
    have hj := (Finset.mem_filter.mp hj).2
    apply chainTerm_commute_of_not_adjacent hq hsupp <;> omega
  · intro i hi j hj
    have hi := (Finset.mem_filter.mp hi).2
    have hj := (Finset.mem_filter.mp hj).2
    apply chainTerm_commute_of_not_adjacent hq hsupp <;> omega

private theorem chainOperator_apply_eq_zero_iff
    {h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hh : ∀ i, IsStarProjection (h i)) (x : EuclideanSpace ℂ (Fin L → Fin q)) :
    chainOperator h x = 0 ↔ ∀ i < m, chainTerm h i x = 0 := by
  have hp (i : Fin m) : (chainTerm h i).toLinearMap.IsPositive :=
    (ContinuousLinearMap.IsPositive.of_isStarProjection (chainTerm_projection hh i)).toLinearMap
  have ht := WeightedPositiveKernel.apply_sum_eq_zero_iff hp x
  simp only [LinearMap.sum_apply, ContinuousLinearMap.coe_coe, Fin.forall_iff] at ht
  rw [show (∑ i : Fin m, chainTerm h i x) = ∑ i ∈ Finset.range m, chainTerm h i x from
    Fin.sum_univ_eq_sum_range (fun i ↦ chainTerm h i x) m] at ht
  simpa only [chainOperator, _root_.sum_apply] using ht

/-- Full kernel equality for the actual finite chain, with parity commutations derived
from locality. ALVV, Theorem 5.14(1), including degenerate ground spaces. -/
theorem ker_chainReplacement
    {h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hq : 1 ≤ q)
    (hh : ∀ i, IsStarProjection (h i))
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) (a b : ℕ) :
    LinearMap.ker (chainReplacement h a b).toLinearMap =
      LinearMap.ker (chainOperator h).toLinearMap := by
  obtain ⟨he, ho⟩ := chain_parity_commute hq hsupp a b
  exact ker_regionalReplacement (chainTerm_projection hh) _ _ he ho m

private theorem ker_ordered_chainTerm
    {h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hh : ∀ i, IsStarProjection (h i)) :
    LinearMap.ker (chainOperator h).toLinearMap =
      ⨅ i : Fin (m + m), LinearMap.ker
        (parityOrderedTerm (colourTerm (chainTerm h) 0)
          (colourTerm (chainTerm h) 1) m i).toLinearMap := by
  let T := parityOrderedTerm (colourTerm (chainTerm h) 0) (colourTerm (chainTerm h) 1) m
  have hproj := isStarProjection_parityOrderedTerm
    (colourTerm_projection (chainTerm_projection hh) 0)
    (colourTerm_projection (chainTerm_projection hh) 1) m
  have hp (i : Fin (m + m)) : (T i).toLinearMap.IsPositive :=
    (ContinuousLinearMap.IsPositive.of_isStarProjection (hproj i)).toLinearMap
  have hk := WeightedPositiveKernel.ker_sum_eq_iInf hp
  have hsum : (∑ i : Fin (m + m), (T i).toLinearMap) = (chainOperator h).toLinearMap := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.sum_apply, ContinuousLinearMap.coe_coe]
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ T i x) (m + m)]
    rw [← _root_.sum_apply]
    dsimp only [T]
    rw [sum_parityOrderedTerm, sum_colourTerm]
    rfl
  rwa [hsum] at hk

/-- Explicit gap for the actual regional chain replacement. The only gap premise concerns
the original chain; locality supplies degree two and every collapsed-family identity.
ALVV, Theorem 5.14(3), with squared norms and the constant-three converse. -/
theorem chainReplacement_gap
    {h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hq : 1 ≤ q)
    (hh : ∀ i, IsStarProjection (h i))
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) {γ : ℝ} (hγ : 0 < γ)
    (hgap : ∀ y ∈ (LinearMap.ker (chainOperator h).toLinearMap)ᗮ,
      γ * ‖y‖ ^ 2 ≤ Complex.re ⟪y, chainOperator h y⟫_ℂ) (a b : ℕ)
    {x : EuclideanSpace ℂ (Fin L → Fin q)} (hx : ‖x‖ = 1)
    (hxperp : x ∈ (LinearMap.ker (chainOperator h).toLinearMap)ᗮ) :
    γ / (3 * (γ + 4)) ≤ Complex.re ⟪x, chainReplacement h a b x⟫_ℂ := by
  have hc := chainTerm_commute_of_not_adjacent hq hsupp
  have hproj := chainTerm_projection hh
  have hk := ker_ordered_chainTerm hh
  have hgap' : ∀ y ∈ (⨅ i : Fin (m + m), LinearMap.ker
      (parityOrderedTerm (colourTerm (chainTerm h) 0)
        (colourTerm (chainTerm h) 1) m i).toLinearMap)ᗮ,
      γ * ‖y‖ ^ 2 ≤ Complex.re ⟪y,
        ((∑ i ∈ Finset.range m, colourTerm (chainTerm h) 0 i) +
          ∑ i ∈ Finset.range m, colourTerm (chainTerm h) 1 i) y⟫_ℂ := by
    rw [← hk, sum_colourTerm]
    exact hgap
  have hxperp' : x ∈ (⨅ i : Fin (m + m), LinearMap.ker
      (parityOrderedTerm (colourTerm (chainTerm h) 0)
        (colourTerm (chainTerm h) 1) m i).toLinearMap)ᗮ := by rwa [← hk]
  have hg := collapsedLayer_gap (colourTerm_projection hproj 0) (colourTerm_commute hc 0)
    (colourTerm_projection hproj 1) (colourTerm_commute hc 1)
    (evenBonds a b) (oddBonds a b) m hγ
    (commutationDegree_parityOrderedTerm_le_two hc m) hgap' hx hxperp'
  rw [collapsed_colourTerm_sum] at hg
  norm_num only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num] at hg
  exact hg

/-- Every original zero-energy vector satisfies all replacement constraints separately.
The global zero-energy premise is equivalent to termwise frustration freeness because
all original terms are projections. ALVV, Theorem 5.14(1). -/
theorem chainReplacement_frustrationFree
    {h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hq : 1 ≤ q)
    (hh : ∀ i, IsStarProjection (h i))
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) (a b : ℕ) {Ω : EuclideanSpace ℂ (Fin L → Fin q)}
    (hΩ : chainOperator h Ω = 0) :
    (1 - regionalProjection (chainTerm h) (evenBonds a b) m) Ω = 0 ∧
    (1 - regionalProjection (chainTerm h) (oddBonds a b) m) Ω = 0 ∧
    ∀ i < m, i ∉ evenBonds a b ∪ oddBonds a b → chainTerm h i Ω = 0 := by
  obtain ⟨he, ho⟩ := chain_parity_commute hq hsupp a b
  exact regionalReplacement_frustrationFree (chainTerm_projection hh) _ _ he ho m
    ((chainOperator_apply_eq_zero_iff hh Ω).mp hΩ)

/-- A concrete chain gap parameter at most one yields the uniform lower bound `γ/15`
for every unit vector orthogonal to the full ground space. ALVV, Theorem 5.14(3). -/
theorem chainReplacement_gap_linear
    {h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hq : 1 ≤ q)
    (hh : ∀ i, IsStarProjection (h i))
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hgap : ∀ y ∈ (LinearMap.ker (chainOperator h).toLinearMap)ᗮ,
      γ * ‖y‖ ^ 2 ≤ Complex.re ⟪y, chainOperator h y⟫_ℂ) (a b : ℕ)
    {x : EuclideanSpace ℂ (Fin L → Fin q)} (hx : ‖x‖ = 1)
    (hxperp : x ∈ (LinearMap.ker (chainOperator h).toLinearMap)ᗮ) :
    γ / 15 ≤ Complex.re ⟪x, chainReplacement h a b x⟫_ℂ := by
  have hr := gap_ratio_le hγ hγ1
  norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at hr
  exact hr.trans (chainReplacement_gap hq hh hsupp hγ hgap a b hx hxperp)

/-- The corrected ALVV regional-replacement theorem on a finite nearest-neighbor chain.
It assembles actual layer projections, positivity, termwise frustration freeness, full
kernel equality, the corrected all-cut rank bounds, and the explicit gap comparison.
All parity commutations, degree bounds and detectability-product identities are proved
from the supplied local terms. No uniqueness assumption is needed; when the original
ground state is unique, the full kernel equality preserves that uniqueness.

The unrestricted printed rank bound in ALVV, arXiv:1602.08828v2,
Theorem 5.14(2), is replaced by `q²+3`; prefixes and suffixes retain `q²+2`.
The source's false unrestricted bound is not asserted. -/
theorem frustrationFree_regionalReplacement_chain
    (h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (hq : 1 ≤ q)
    (hh : ∀ i, IsStarProjection (h i))
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) {γ : ℝ} (hγ : 0 < γ)
    (hgap : ∀ y ∈ (LinearMap.ker (chainOperator h).toLinearMap)ᗮ,
      γ * ‖y‖ ^ 2 ≤ Complex.re ⟪y, chainOperator h y⟫_ℂ)
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩnorm : ‖Ω‖ = 1)
    (hΩ : chainOperator h Ω = 0) (a b : ℕ) :
    IsStarProjection (1 - regionalProjection (chainTerm h) (evenBonds a b) m) ∧
    IsStarProjection (1 - regionalProjection (chainTerm h) (oddBonds a b) m) ∧
    (chainReplacement h a b).IsPositive ∧
    LinearMap.ker (chainReplacement h a b).toLinearMap =
      LinearMap.ker (chainOperator h).toLinearMap ∧
    (‖Ω‖ = 1 ∧ chainReplacement h a b Ω = 0) ∧
    ((1 - regionalProjection (chainTerm h) (evenBonds a b) m) Ω = 0 ∧
      (1 - regionalProjection (chainTerm h) (oddBonds a b) m) Ω = 0 ∧
      ∀ i < m, i ∉ evenBonds a b ∪ oddBonds a b → chainTerm h i Ω = 0) ∧
    (∀ k, operatorSchmidtRank (Entropy.cutOperator (interval L 0 k)
      (regionalReplacementMatrix (bondTermExtension h) (evenBonds a b) (oddBonds a b) m)) ≤
        q ^ 2 + 3) ∧
    ((a = 0 ∨ m ≤ b) → ∀ k, operatorSchmidtRank (Entropy.cutOperator (interval L 0 k)
      (regionalReplacementMatrix (bondTermExtension h) (evenBonds a b) (oddBonds a b) m)) ≤
        q ^ 2 + 2) ∧
    (∀ x ∈ (LinearMap.ker (chainReplacement h a b).toLinearMap)ᗮ, ‖x‖ = 1 →
      γ / (3 * (γ + 4)) ≤ Complex.re ⟪x, chainReplacement h a b x⟫_ℂ) := by
  obtain ⟨he, ho⟩ := chain_parity_commute hq hsupp a b
  have hproj := chainTerm_projection hh
  have hk := ker_chainReplacement hq hh hsupp a b
  have hΩ' : chainReplacement h a b Ω = 0 := by
    change Ω ∈ LinearMap.ker (chainReplacement h a b).toLinearMap
    rw [hk]
    exact hΩ
  refine ⟨(isStarProjection_regionalProjection hproj _ he m).one_sub,
    (isStarProjection_regionalProjection hproj _ ho m).one_sub,
    isPositive_regionalReplacement hproj _ _ he ho m, hk, ⟨hΩnorm, hΩ'⟩,
    chainReplacement_frustrationFree hq hh hsupp a b hΩ,
    (fun k ↦ rank_regionalReplacementMatrix_le_sq_add_three h hq hsupp a b k),
    (fun hb k ↦ rank_regionalReplacementMatrix_le_sq_add_two_of_boundary h hq hsupp a b k hb),
    ?_⟩
  intro x hx hxnorm
  rw [hk] at hx
  exact chainReplacement_gap hq hh hsupp hγ hgap a b hxnorm hx

end Chain

end TNLean.MPS.AreaLaw.ALVV
