/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.EntropySupport
import TNLean.MPS.AreaLaw.ALVV.FrustrationFreeChain
import TNLean.MPS.AreaLaw.ALVV.RegionalSlices

/-!
# The frustration-free replacement on three regions at once

The proof of ALVV, arXiv:1602.08828v2, Theorem `t:aisff`, lines 1597–1599, applies the regional
replacement of Definition 5.10 to three disjoint regions, the bulk regions to the left of, between
and to the right of two windows of `2 ℓ` retained bonds. In zero-based bond coordinates the
regions are `[0, a)`, `[a + 2ℓ, b)` and `[b + 2ℓ, m)`, and the windows are `[a, a + 2ℓ)` and
`[b, b + 2ℓ)`.

The replacement keeps the full ground space and the gap comparison of Theorem 5.14. The gap does
not follow by iterating the one-region chain theorem, whose nearest-neighbour hypotheses fail
after one replacement. Instead, collapsing the union of the three regions of one parity into a
single projector is covered by the parity-layer comparison `parityReplacement_gap`, and the three
regional projectors dominate the collapsed one by the union bound for commuting projections.

The replacement is written as the two-window family of `eq:H-mid-cut`, lines 813–821, so that the
polynomial rank bounds for that family apply. Each regional term has operator Schmidt rank at most
`q² + 2` at a cut inside its region.
-/

open scoped InnerProductSpace Matrix.Norms.L2Operator
open ContinuousLinearMap Matrix

namespace TNLean.MPS.AreaLaw.ALVV

section Abstract

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The regional product over a disjoint union of commuting bond sets is the product of the two
regional products. ALVV, arXiv:1602.08828v2, Definition 5.10, for several regions of one
parity. -/
theorem regionalProjection_union {h : ℕ → E →L[𝕜] E} {s t : Finset ℕ}
    (hc : ∀ i ∈ s ∪ t, ∀ j ∈ s ∪ t, Commute (h i) (h j)) (hst : Disjoint s t) (m : ℕ) :
    regionalProjection h (s ∪ t) m = regionalProjection h s m * regionalProjection h t m := by
  classical
  induction m with
  | zero => simp [regionalProjection]
  | succ m ih =>
    simp only [regionalProjection, complementProd_succ] at ih ⊢
    rw [ih]
    by_cases hms : m ∈ s
    · have hmt : m ∉ t := Finset.disjoint_left.mp hst hms
      simp [restrictedTerm, hms, hmt, mul_assoc]
    · by_cases hmt : m ∈ t
      · have hcomm : Commute (1 - h m) (complementProd (restrictedTerm h s) m) := by
          apply commute_complementProd
          intro j _
          unfold restrictedTerm
          split
          · exact (Commute.one_left _).sub_left
              (hc m (Finset.mem_union_right s hmt) j (Finset.mem_union_left t ‹_›))
          · exact Commute.zero_right _
        simp only [restrictedTerm, Finset.mem_union, hms, hmt, or_true, ↓reduceIte,
          sub_zero, one_mul]
        rw [← mul_assoc, ← mul_assoc, hcomm.eq]
      · simp [restrictedTerm, hms, hmt]

variable [CompleteSpace E]

/-- The union bound for two commuting projections: `1 - PQ ≤ (1 - P) + (1 - Q)`. -/
theorem re_inner_one_sub_mul_le {P Q : E →L[𝕜] E} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) (hPQ : Commute P Q) (x : E) :
    RCLike.re ⟪x, (1 - P * Q) x⟫_𝕜 ≤
      RCLike.re ⟪x, (1 - P) x⟫_𝕜 + RCLike.re ⟪x, (1 - Q) x⟫_𝕜 := by
  have hsplit : (1 - P * Q) = (1 - P) + P * (1 - Q) := by noncomm_ring
  have hR : IsStarProjection (P * (1 - Q)) :=
    hP.mul hQ.one_sub ((Commute.one_right P).sub_right hPQ)
  have key : RCLike.re ⟪x, (P * (1 - Q)) x⟫_𝕜 ≤ RCLike.re ⟪x, (1 - Q) x⟫_𝕜 := by
    rw [hR.re_inner_apply_self, hQ.one_sub.re_inner_apply_self]
    change ‖P ((1 - Q) x)‖ ^ 2 ≤ _
    exact pow_le_pow_left₀ (norm_nonneg _) (hP.norm_apply_le _) 2
  rw [hsplit, _root_.add_apply, inner_add_right, map_add]
  linarith

/-- The union bound for three pairwise commuting projections. -/
theorem re_inner_one_sub_mul_mul_le {P Q R : E →L[𝕜] E} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) (hR : IsStarProjection R) (hPQ : Commute P Q)
    (hPR : Commute P R) (hQR : Commute Q R) (x : E) :
    RCLike.re ⟪x, (1 - P * Q * R) x⟫_𝕜 ≤
      RCLike.re ⟪x, (1 - P) x⟫_𝕜 + RCLike.re ⟪x, (1 - Q) x⟫_𝕜 +
        RCLike.re ⟪x, (1 - R) x⟫_𝕜 := by
  rw [mul_assoc]
  have h1 := re_inner_one_sub_mul_le hP (hQ.mul hR hQR) (hPQ.mul_right hPR) x
  have h2 := re_inner_one_sub_mul_le hQ hR hQR x
  linarith

end Abstract

section Chain

variable {L q m : ℕ}

/-- The two parity layers of the regional replacement on the bonds `[x, y)`, as one regional
term. ALVV, arXiv:1602.08828v2, Definition 5.10, lines 1465–1486. -/
noncomputable def regionTermMatrix (h : ℕ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (x y m : ℕ) : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  (1 - regionalProjectionMatrix h (evenBonds x y) m) +
    (1 - regionalProjectionMatrix h (oddBonds x y) m)

/-- The three-region replacement of ALVV, arXiv:1602.08828v2, proof of Theorem `t:aisff`,
lines 1597–1599, written as the two-window family of `eq:H-mid-cut`, lines 813–821: the bonds
of the windows `[a, a + 2ℓ)` and `[b, b + 2ℓ)`, followed by the regional terms of
`[0, a)`, `[a + 2ℓ, b)` and `[b + 2ℓ, m)`. -/
noncomputable def threeRegionFamily (h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (a b ℓ : ℕ) :
    ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  Sum.elim (Sum.elim (fun r ↦ bondTermExtension h (a + r)) (fun r ↦ bondTermExtension h (b + r)))
    ![regionTermMatrix (bondTermExtension h) 0 a m,
      regionTermMatrix (bondTermExtension h) (a + 2 * ℓ) b m,
      regionTermMatrix (bondTermExtension h) (b + 2 * ℓ) m m]

/-- A regional term is supported on any set containing the supports of its bonds. -/
theorem regionTermMatrix_supported {h : ℕ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hq : 1 ≤ q)
    (hh : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i) (interval L i (i + 2)))
    (x y m : ℕ) (D : Finset (Fin L))
    (hD : ∀ i, x ≤ i → i < y → interval L i (i + 2) ⊆ D) :
    Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (regionTermMatrix h x y m) D := by
  have hE := regionalProjectionMatrix_supported hq hh (evenBonds x y) m D fun i _ hi ↦ by
    obtain ⟨hi, -⟩ := Finset.mem_filter.mp hi
    exact hD i (Finset.mem_Ico.mp hi).1 (Finset.mem_Ico.mp hi).2
  have hO := regionalProjectionMatrix_supported hq hh (oddBonds x y) m D fun i _ hi ↦ by
    obtain ⟨hi, -⟩ := Finset.mem_filter.mp hi
    exact hD i (Finset.mem_Ico.mp hi).1 (Finset.mem_Ico.mp hi).2
  exact ((Entropy.isSupportedOn_one D).sub hE).add ((Entropy.isSupportedOn_one D).sub hO)

private theorem interval_edge_subset {x y i : ℕ} (hx : x ≤ i) (hy : i + 2 ≤ y ∨ L ≤ y) :
    interval L i (i + 2) ⊆ interval L x y := by
  intro v hv
  simp only [mem_interval] at hv ⊢
  have := v.isLt
  omega

/-- The supports of the three-region family, in the form required by the two-window rank
bounds. ALVV, arXiv:1602.08828v2, `eq:H-mid-cut`, lines 813–821. -/
theorem threeRegionFamily_supported {h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hq : 1 ≤ q)
    (hh : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i) (interval L i (i + 2)))
    (a b ℓ : ℕ) :
    (∀ r, threeRegionFamily h a b ℓ (Sum.inl (Sum.inl r)) ∈ QuantumCircuit.supportedOperators q
      (interval L (a + r.val) (a + r.val + 2) : Set (Fin L))) ∧
    (∀ r, threeRegionFamily h a b ℓ (Sum.inl (Sum.inr r)) ∈ QuantumCircuit.supportedOperators q
      (interval L (b + r.val) (b + r.val + 2) : Set (Fin L))) ∧
    threeRegionFamily h a b ℓ (Sum.inr 0) ∈ QuantumCircuit.supportedOperators q
      (interval L 0 (a + 1) : Set (Fin L)) ∧
    threeRegionFamily h a b ℓ (Sum.inr 1) ∈ QuantumCircuit.supportedOperators q
      (interval L (a + 2 * ℓ) (b + 1) : Set (Fin L)) ∧
    threeRegionFamily h a b ℓ (Sum.inr 2) ∈ QuantumCircuit.supportedOperators q
      (interval L (b + 2 * ℓ) L : Set (Fin L)) := by
  have hext := bondTermExtension_supported hh
  refine ⟨fun r ↦ QuantumCircuit.mem_supportedOperators_of_isSupportedOn (hext _),
    fun r ↦ QuantumCircuit.mem_supportedOperators_of_isSupportedOn (hext _), ?_, ?_, ?_⟩ <;>
  refine QuantumCircuit.mem_supportedOperators_of_isSupportedOn
    (regionTermMatrix_supported hq hext _ _ m _ fun i hx hy ↦ interval_edge_subset hx ?_) <;>
  omega

/-- The matrix regional term is the operator regional term. -/
theorem toEuclideanCLM_regionTermMatrix
    (h : ℕ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (x y m : ℕ) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)) (regionTermMatrix h x y m) =
      (1 - regionalProjection
          (fun i ↦ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)) (h i))
          (evenBonds x y) m) +
        (1 - regionalProjection
          (fun i ↦ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)) (h i))
          (oddBonds x y) m) := by
  simp only [regionTermMatrix, map_add, map_sub, map_one,
    toEuclideanCLM_regionalProjectionMatrix]

/-- The operator form of the three-region replacement. -/
theorem toEuclideanCLM_threeRegion (h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (a b ℓ : ℕ) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)) (∑ α, threeRegionFamily h a b ℓ α) =
      (∑ r : Fin (2 * ℓ), chainTerm h (a + r)) + (∑ r : Fin (2 * ℓ), chainTerm h (b + r)) +
        (((1 - regionalProjection (chainTerm h) (evenBonds 0 a) m) +
            (1 - regionalProjection (chainTerm h) (oddBonds 0 a) m)) +
          ((1 - regionalProjection (chainTerm h) (evenBonds (a + 2 * ℓ) b) m) +
            (1 - regionalProjection (chainTerm h) (oddBonds (a + 2 * ℓ) b) m)) +
          ((1 - regionalProjection (chainTerm h) (evenBonds (b + 2 * ℓ) m) m) +
            (1 - regionalProjection (chainTerm h) (oddBonds (b + 2 * ℓ) m) m))) := by
  rw [map_sum, Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_three]
  simp only [threeRegionFamily, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    toEuclideanCLM_regionTermMatrix]
  rfl

/-- Two bonds of the same parity commute. -/
theorem commute_chainTerm_of_mod_two_eq
    {h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hq : 1 ≤ q)
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) {i j : ℕ} (hij : i % 2 = j % 2) :
    Commute (chainTerm h i) (chainTerm h j) :=
  chainTerm_commute_of_not_adjacent hq hsupp i j (by omega) (by omega)

/-- The even bonds of a region have even index. -/
theorem mod_two_eq_zero_of_mem_evenBonds {x y i : ℕ} (hi : i ∈ evenBonds x y) : i % 2 = 0 :=
  (Finset.mem_filter.mp hi).2

/-- The odd bonds of a region have odd index. -/
theorem mod_two_eq_one_of_mem_oddBonds {x y i : ℕ} (hi : i ∈ oddBonds x y) : i % 2 = 1 := by
  have := (Finset.mem_filter.mp hi).2
  omega

/-- A regional product over bonds of one parity is an orthogonal projection. -/
theorem isStarProjection_regionalProjection_chainTerm
    {h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hq : 1 ≤ q)
    (hh : ∀ i, IsStarProjection (h i))
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) {s : Finset ℕ} {c : ℕ} (hs : ∀ i ∈ s, i % 2 = c) :
    IsStarProjection (regionalProjection (chainTerm h) s m) :=
  isStarProjection_regionalProjection (isStarProjection_chainTerm hh) s
    (fun i hi j hj ↦ commute_chainTerm_of_mod_two_eq hq hsupp ((hs i hi).trans (hs j hj).symm)) m

/-- The even bonds of the three regions. -/
def evenRegionBonds (a b ℓ m : ℕ) : Finset ℕ :=
  evenBonds 0 a ∪ evenBonds (a + 2 * ℓ) b ∪ evenBonds (b + 2 * ℓ) m

/-- The odd bonds of the three regions. -/
def oddRegionBonds (a b ℓ m : ℕ) : Finset ℕ :=
  oddBonds 0 a ∪ oddBonds (a + 2 * ℓ) b ∪ oddBonds (b + 2 * ℓ) m

private theorem mem_regionBonds_iff (a b ℓ m i : ℕ) :
    i ∈ evenRegionBonds a b ℓ m ∪ oddRegionBonds a b ℓ m ↔
      i < a ∨ (a + 2 * ℓ ≤ i ∧ i < b) ∨ (b + 2 * ℓ ≤ i ∧ i < m) := by
  simp only [evenRegionBonds, oddRegionBonds, evenBonds, oddBonds, Finset.mem_union,
    Finset.mem_filter, Finset.mem_Ico]
  omega

/-- The bonds outside the three regions are exactly the two windows. -/
private theorem sum_restrictedTerm_windows {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (f : ℕ → E →L[ℂ] E) {a b ℓ : ℕ}
    (hab : a + 2 * ℓ ≤ b) (hbm : b + 2 * ℓ ≤ m) :
    ∑ i ∈ Finset.range m, restrictedTerm f
        (Finset.range m \ (evenRegionBonds a b ℓ m ∪ oddRegionBonds a b ℓ m)) i =
      (∑ r : Fin (2 * ℓ), f (a + r)) + ∑ r : Fin (2 * ℓ), f (b + r) := by
  classical
  have hset : Finset.range m ∩
      (Finset.range m \ (evenRegionBonds a b ℓ m ∪ oddRegionBonds a b ℓ m)) =
      Finset.Ico a (a + 2 * ℓ) ∪ Finset.Ico b (b + 2 * ℓ) := by
    ext i
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_range]
    rw [mem_regionBonds_iff]
    simp only [Finset.mem_union, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (Finset.Ico a (a + 2 * ℓ)) (Finset.Ico b (b + 2 * ℓ)) := by
    rw [Finset.disjoint_left]
    intro i hi hj
    simp only [Finset.mem_Ico] at hi hj
    omega
  simp only [restrictedTerm]
  rw [Finset.sum_ite_mem, hset, Finset.sum_union hdisj, Finset.sum_Ico_eq_sum_range,
    Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left,
    ← Fin.sum_univ_eq_sum_range (fun r ↦ f (a + r)),
    ← Fin.sum_univ_eq_sum_range (fun r ↦ f (b + r))]

/-- The three regional projectors of one parity dominate the collapsed projector of their
union. -/
private theorem re_inner_collapsed_le
    {h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hq : 1 ≤ q)
    (hh : ∀ i, IsStarProjection (h i))
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) (c : ℕ) {s₁ s₂ s₃ : Finset ℕ}
    (h₁ : ∀ i ∈ s₁, i % 2 = c) (h₂ : ∀ i ∈ s₂, i % 2 = c) (h₃ : ∀ i ∈ s₃, i % 2 = c)
    (d₁₂ : Disjoint s₁ s₂) (d₁₃ : Disjoint s₁ s₃) (d₂₃ : Disjoint s₂ s₃)
    (x : EuclideanSpace ℂ (Fin L → Fin q)) :
    RCLike.re ⟪x, (1 - regionalProjection (chainTerm h) (s₁ ∪ s₂ ∪ s₃) m) x⟫_ℂ ≤
      RCLike.re ⟪x, (1 - regionalProjection (chainTerm h) s₁ m) x⟫_ℂ +
        RCLike.re ⟪x, (1 - regionalProjection (chainTerm h) s₂ m) x⟫_ℂ +
          RCLike.re ⟪x, (1 - regionalProjection (chainTerm h) s₃ m) x⟫_ℂ := by
  have hc (t : Finset ℕ) (ht : ∀ i ∈ t, i % 2 = c) :
      ∀ i ∈ t, ∀ j ∈ t, Commute (chainTerm h i) (chainTerm h j) := fun i hi j hj ↦
    commute_chainTerm_of_mod_two_eq hq hsupp ((ht i hi).trans (ht j hj).symm)
  have hpar {t u : Finset ℕ} (ht : ∀ i ∈ t, i % 2 = c) (hu : ∀ i ∈ u, i % 2 = c) :
      ∀ i ∈ t ∪ u, i % 2 = c := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    exacts [ht i hi, hu i hi]
  have hproj (t : Finset ℕ) (ht : ∀ i ∈ t, i % 2 = c) :
      IsStarProjection (regionalProjection (chainTerm h) t m) :=
    isStarProjection_regionalProjection (isStarProjection_chainTerm hh) t (hc t ht) m
  have hcomm {t u : Finset ℕ} (ht : ∀ i ∈ t, i % 2 = c) (hu : ∀ i ∈ u, i % 2 = c)
      (htu : Disjoint t u) :
      Commute (regionalProjection (chainTerm h) t m) (regionalProjection (chainTerm h) u m) := by
    have h1 := regionalProjection_union (hc _ (hpar ht hu)) htu m
    have h2 := regionalProjection_union (hc _ (hpar hu ht)) htu.symm m
    rw [Finset.union_comm] at h2
    exact h1.symm.trans h2
  rw [regionalProjection_union (hc _ (hpar (hpar h₁ h₂) h₃))
      (Finset.disjoint_union_left.mpr ⟨d₁₃, d₂₃⟩) m,
    regionalProjection_union (hc _ (hpar h₁ h₂)) d₁₂ m]
  exact re_inner_one_sub_mul_mul_le (hproj s₁ h₁) (hproj s₂ h₂) (hproj s₃ h₃)
    (hcomm h₁ h₂ d₁₂) (hcomm h₁ h₃ d₁₃) (hcomm h₂ h₃ d₂₃) x

private theorem disjoint_bonds {x y x' y' : ℕ} (hxy : y ≤ x') (s t : Finset ℕ)
    (hs : s ⊆ Finset.Ico x y) (ht : t ⊆ Finset.Ico x' y') : Disjoint s t := by
  rw [Finset.disjoint_left]
  intro i his hit
  have h1 := Finset.mem_Ico.mp (hs his)
  have h2 := Finset.mem_Ico.mp (ht hit)
  omega

private theorem evenBonds_subset (x y : ℕ) : evenBonds x y ⊆ Finset.Ico x y :=
  Finset.filter_subset _ _

private theorem oddBonds_subset (x y : ℕ) : oddBonds x y ⊆ Finset.Ico x y :=
  Finset.filter_subset _ _

/-- **Gap of the three-region replacement.** For every unit vector orthogonal to the full ground
space of the original chain, the quadratic form of the replacement is at least
`γ / (3 (γ + 4))`, the constant of the one-region theorem. ALVV, arXiv:1602.08828v2, proof of
Theorem `t:aisff`, lines 1597–1599, from Theorem 5.14(3), lines 1541–1570. -/
theorem threeRegion_gap
    {h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hq : 1 ≤ q)
    (hh : ∀ i, IsStarProjection (h i))
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) {γ : ℝ} (hγ : 0 < γ)
    (hgap : ∀ y ∈ (LinearMap.ker (chainOperator h).toLinearMap)ᗮ,
      γ * ‖y‖ ^ 2 ≤ Complex.re ⟪y, chainOperator h y⟫_ℂ)
    {a b ℓ : ℕ} (hab : a + 2 * ℓ ≤ b) (hbm : b + 2 * ℓ ≤ m)
    {x : EuclideanSpace ℂ (Fin L → Fin q)} (hx : ‖x‖ = 1)
    (hxperp : x ∈ (LinearMap.ker (chainOperator h).toLinearMap)ᗮ) :
    γ / (3 * (γ + 4)) ≤ Complex.re ⟪x,
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q))
        (∑ α, threeRegionFamily h a b ℓ α) x⟫_ℂ := by
  have heven : ∀ i ∈ evenRegionBonds a b ℓ m, i % 2 = 0 := by
    intro i hi
    simp only [evenRegionBonds, evenBonds, Finset.mem_union, Finset.mem_filter] at hi
    omega
  have hodd : ∀ i ∈ oddRegionBonds a b ℓ m, i % 2 = 1 := by
    intro i hi
    simp only [oddRegionBonds, oddBonds, Finset.mem_union, Finset.mem_filter] at hi
    omega
  have hunion := parityReplacement_gap hq hh hsupp hγ hgap heven hodd hx hxperp
  refine hunion.trans ?_
  have hE := re_inner_collapsed_le hq hh hsupp 0
    (s₁ := evenBonds 0 a) (s₂ := evenBonds (a + 2 * ℓ) b) (s₃ := evenBonds (b + 2 * ℓ) m)
    (fun _ ↦ mod_two_eq_zero_of_mem_evenBonds) (fun _ ↦ mod_two_eq_zero_of_mem_evenBonds)
    (fun _ ↦ mod_two_eq_zero_of_mem_evenBonds)
    (disjoint_bonds (by omega) _ _ (evenBonds_subset _ _) (evenBonds_subset _ _))
    (disjoint_bonds (by omega) _ _ (evenBonds_subset _ _) (evenBonds_subset _ _))
    (disjoint_bonds (by omega) _ _ (evenBonds_subset _ _) (evenBonds_subset _ _)) x
  have hO := re_inner_collapsed_le hq hh hsupp 1
    (s₁ := oddBonds 0 a) (s₂ := oddBonds (a + 2 * ℓ) b) (s₃ := oddBonds (b + 2 * ℓ) m)
    (fun _ ↦ mod_two_eq_one_of_mem_oddBonds) (fun _ ↦ mod_two_eq_one_of_mem_oddBonds)
    (fun _ ↦ mod_two_eq_one_of_mem_oddBonds)
    (disjoint_bonds (by omega) _ _ (oddBonds_subset _ _) (oddBonds_subset _ _))
    (disjoint_bonds (by omega) _ _ (oddBonds_subset _ _) (oddBonds_subset _ _))
    (disjoint_bonds (by omega) _ _ (oddBonds_subset _ _) (oddBonds_subset _ _)) x
  rw [toEuclideanCLM_threeRegion]
  unfold regionalReplacement
  rw [sum_restrictedTerm_windows _ hab hbm]
  simp only [evenRegionBonds, oddRegionBonds] at hE hO ⊢
  simp only [_root_.add_apply, inner_add_right, Complex.add_re,
    RCLike.re_to_complex] at hE hO ⊢
  linarith

/-- Every member of the three-region family is a positive operator. -/
theorem isPositive_toEuclideanCLM_threeRegionFamily
    {h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hq : 1 ≤ q)
    (hh : ∀ i, IsStarProjection (h i))
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) (a b ℓ : ℕ) (α : (Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) :
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q))
      (threeRegionFamily h a b ℓ α)).IsPositive := by
  have hproj := isStarProjection_chainTerm hh
  have hlayer (s : Finset ℕ) (c : ℕ) (hs : ∀ i ∈ s, i % 2 = c) :
      (1 - regionalProjection (chainTerm h) s m).IsPositive :=
    IsPositive.of_isStarProjection
      (isStarProjection_regionalProjection_chainTerm hq hh hsupp hs).one_sub
  have hreg (x y : ℕ) : ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q))
      (regionTermMatrix (bondTermExtension h) x y m)).IsPositive := by
    rw [toEuclideanCLM_regionTermMatrix]
    exact (hlayer _ 0 fun _ hi ↦ mod_two_eq_zero_of_mem_evenBonds hi).add
      (hlayer _ 1 fun _ hi ↦ mod_two_eq_one_of_mem_oddBonds hi)
  rcases α with ((r | r) | j)
  · exact IsPositive.of_isStarProjection (hproj _)
  · exact IsPositive.of_isStarProjection (hproj _)
  · fin_cases j <;> simpa [threeRegionFamily] using hreg _ _

/-- The three-region replacement is a positive operator. -/
theorem isPositive_toEuclideanCLM_threeRegion
    {h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hq : 1 ≤ q)
    (hh : ∀ i, IsStarProjection (h i))
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) (a b ℓ : ℕ) :
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q))
      (∑ α, threeRegionFamily h a b ℓ α)).IsPositive := by
  rw [map_sum]
  exact isPositive_sum _ fun α _ ↦
    isPositive_toEuclideanCLM_threeRegionFamily hq hh hsupp a b ℓ α

/-- **Kernel of the three-region replacement.** A vector is annihilated by the replacement
exactly when it is annihilated by every original term. ALVV, arXiv:1602.08828v2, proof of
Theorem `t:aisff`, line 1599, from Theorem 5.14(1). No uniqueness is used. -/
theorem threeRegion_apply_eq_zero_iff
    {h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hq : 1 ≤ q)
    (hh : ∀ i, IsStarProjection (h i))
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) (a b ℓ : ℕ) (x : EuclideanSpace ℂ (Fin L → Fin q)) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q))
        (∑ α, threeRegionFamily h a b ℓ α) x = 0 ↔ ∀ i < m, chainTerm h i x = 0 := by
  classical
  set C := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
  have hproj := isStarProjection_chainTerm hh
  have hlayer (s : Finset ℕ) (hs : ∀ i ∈ s, ∀ j ∈ s, i % 2 = j % 2) :
      IsStarProjection (1 - regionalProjection (chainTerm h) s m) :=
    (isStarProjection_regionalProjection hproj s
      (fun i hi j hj ↦ commute_chainTerm_of_mod_two_eq hq hsupp (hs i hi j hj)) m).one_sub
  have heven (x y : ℕ) : ∀ i ∈ evenBonds x y, ∀ j ∈ evenBonds x y, i % 2 = j % 2 := by
    intro i hi j hj
    rw [(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2]
  have hodd (x y : ℕ) : ∀ i ∈ oddBonds x y, ∀ j ∈ oddBonds x y, i % 2 = j % 2 := by
    intro i hi j hj
    have := (Finset.mem_filter.mp hi).2
    have := (Finset.mem_filter.mp hj).2
    omega
  have hregion (x y : ℕ) :
      C (regionTermMatrix (bondTermExtension h) x y m) =
        (1 - regionalProjection (chainTerm h) (evenBonds x y) m) +
          (1 - regionalProjection (chainTerm h) (oddBonds x y) m) :=
    toEuclideanCLM_regionTermMatrix _ x y m
  have hpos : ∀ α, (C (threeRegionFamily h a b ℓ α)).toLinearMap.IsPositive := fun α ↦
    (isPositive_toEuclideanCLM_threeRegionFamily hq hh hsupp a b ℓ α).toLinearMap
  have hsum := WeightedPositiveKernel.apply_sum_eq_zero_iff hpos x
  simp only [LinearMap.sum_apply, ContinuousLinearMap.coe_coe] at hsum
  have hsumx : C (∑ α, threeRegionFamily h a b ℓ α) x =
      ∑ α, C (threeRegionFamily h a b ℓ α) x := by
    rw [map_sum, _root_.sum_apply]
  rw [hsumx, hsum]
  have hpair (x' y' : ℕ) (v : EuclideanSpace ℂ (Fin L → Fin q)) :
      C (regionTermMatrix (bondTermExtension h) x' y' m) v = 0 ↔
        ∀ i < m, i ∈ Finset.Ico x' y' → chainTerm h i v = 0 := by
    rw [hregion]
    have hA := hlayer _ (heven x' y')
    have hB := hlayer _ (hodd x' y')
    have hsplit : ((1 - regionalProjection (chainTerm h) (evenBonds x' y') m) +
        (1 - regionalProjection (chainTerm h) (oddBonds x' y') m)) v = 0 ↔
        (1 - regionalProjection (chainTerm h) (evenBonds x' y') m) v = 0 ∧
          (1 - regionalProjection (chainTerm h) (oddBonds x' y') m) v = 0 := by
      constructor
      · intro hv
        have hre := congrArg (fun w ↦ RCLike.re ⟪v, w⟫_ℂ) hv
        simp only [_root_.add_apply, inner_add_right, map_add, inner_zero_right, map_zero,
          hA.re_inner_apply_self, hB.re_inner_apply_self] at hre
        obtain ⟨h1, h2⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp hre
        exact ⟨norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h1),
          norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)⟩
      · rintro ⟨h1, h2⟩
        rw [_root_.add_apply, h1, h2, add_zero]
    rw [hsplit, sub_regionalProjection_apply_eq_zero_iff hproj _
        (fun i hi j hj ↦ commute_chainTerm_of_mod_two_eq hq hsupp (heven _ _ i hi j hj)),
      sub_regionalProjection_apply_eq_zero_iff hproj _
        (fun i hi j hj ↦ commute_chainTerm_of_mod_two_eq hq hsupp (hodd _ _ i hi j hj))]
    constructor
    · rintro ⟨he, ho⟩ i hi hI
      by_cases hpar : i % 2 = 0
      · exact he i hi (Finset.mem_filter.mpr ⟨hI, hpar⟩)
      · exact ho i hi (Finset.mem_filter.mpr ⟨hI, hpar⟩)
    · intro hv
      exact ⟨fun i hi hs ↦ hv i hi (Finset.mem_filter.mp hs).1,
        fun i hi hs ↦ hv i hi (Finset.mem_filter.mp hs).1⟩
  have hwin (i : ℕ) : C (bondTermExtension h i) = chainTerm h i := rfl
  have hbeyond (i : ℕ) (hi : ¬ i < m) : chainTerm h i = 0 := by
    change C (bondTermExtension h i) = 0
    simp [bondTermExtension, hi]
  constructor
  · intro hall i hi
    by_cases h1 : i < a
    · exact (hpair 0 a x).mp (hall (Sum.inr 0)) i hi (Finset.mem_Ico.mpr ⟨by omega, h1⟩)
    by_cases h2 : i < a + 2 * ℓ
    · have := hall (Sum.inl (Sum.inl ⟨i - a, by omega⟩))
      simpa [threeRegionFamily, hwin, show a + (i - a) = i by omega] using this
    by_cases h3 : i < b
    · exact (hpair (a + 2 * ℓ) b x).mp (hall (Sum.inr 1)) i hi
        (Finset.mem_Ico.mpr ⟨by omega, h3⟩)
    by_cases h4 : i < b + 2 * ℓ
    · have := hall (Sum.inl (Sum.inr ⟨i - b, by omega⟩))
      simpa [threeRegionFamily, hwin, show b + (i - b) = i by omega] using this
    · exact (hpair (b + 2 * ℓ) m x).mp (hall (Sum.inr 2)) i hi
        (Finset.mem_Ico.mpr ⟨by omega, hi⟩)
  · intro hall
    have hterm (i : ℕ) : chainTerm h i x = 0 := by
      by_cases hi : i < m
      · exact hall i hi
      · rw [hbeyond i hi, _root_.zero_apply]
    rintro ((r | r) | j)
    · exact hterm _
    · exact hterm _
    · fin_cases j
      · exact (hpair 0 a x).mpr fun i hi _ ↦ hall i hi
      · exact (hpair (a + 2 * ℓ) b x).mpr fun i hi _ ↦ hall i hi
      · exact (hpair (b + 2 * ℓ) m x).mpr fun i hi _ ↦ hall i hi

/-- The three-region replacement has the same kernel as the original chain. -/
theorem ker_threeRegion
    {h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hq : 1 ≤ q)
    (hh : ∀ i, IsStarProjection (h i))
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) (a b ℓ : ℕ) :
    LinearMap.ker ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q))
        (∑ α, threeRegionFamily h a b ℓ α)).toLinearMap =
      LinearMap.ker (chainOperator h).toLinearMap := by
  ext x
  exact (threeRegion_apply_eq_zero_iff hq hh hsupp a b ℓ x).trans
    (chainOperator_apply_eq_zero_iff hh x).symm

/-- **Norm of the three-region replacement.** It is a sum of `4 ℓ + 6` projections. The proof of
ALVV, arXiv:1602.08828v2, Theorem `t:aisff`, line 1599, asserts norm `O(1)`; the windows are not
truncated, and the norm can equal `4 ℓ + 6`. -/
theorem norm_threeRegion_le
    {h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hq : 1 ≤ q)
    (hh : ∀ i, IsStarProjection (h i))
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) (a b ℓ : ℕ) :
    ‖∑ α, threeRegionFamily h a b ℓ α‖ ≤ 4 * ℓ + 6 := by
  have hproj := isStarProjection_chainTerm hh
  have hE (x y : ℕ) := (isStarProjection_regionalProjection_chainTerm hq hh hsupp
    (s := evenBonds x y) fun _ hi ↦ mod_two_eq_zero_of_mem_evenBonds hi).one_sub.norm_le
  have hO (x y : ℕ) := (isStarProjection_regionalProjection_chainTerm hq hh hsupp
    (s := oddBonds x y) fun _ hi ↦ mod_two_eq_one_of_mem_oddBonds hi).one_sub.norm_le
  have hreg (x y : ℕ) : ‖(1 - regionalProjection (chainTerm h) (evenBonds x y) m) +
      (1 - regionalProjection (chainTerm h) (oddBonds x y) m)‖ ≤ 2 :=
    (norm_add_le _ _).trans (by linarith [hE x y, hO x y])
  have hwin (c : ℕ) : ‖∑ r : Fin (2 * ℓ), chainTerm h (c + r)‖ ≤ 2 * ℓ := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ r : Fin (2 * ℓ), ‖chainTerm h (c + r)‖ ≤ ∑ _r : Fin (2 * ℓ), (1 : ℝ) :=
          Finset.sum_le_sum fun r _ ↦ (hproj (c + r)).norm_le
      _ = 2 * ℓ := by simp
  rw [Matrix.cstar_norm_def, toEuclideanCLM_threeRegion]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add ((norm_add_le _ _).trans (add_le_add (hwin a) (hwin b)))
    ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add (hreg _ _) (hreg _ _))) (hreg _ _)))).trans ?_
  linarith

private theorem operatorSchmidtRank_cutOperator_sub_le (B : Finset (Fin L))
    (X Y : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    operatorSchmidtRank (Entropy.cutOperator B (X - Y)) ≤
      operatorSchmidtRank (Entropy.cutOperator B X) +
        operatorSchmidtRank (Entropy.cutOperator B Y) := by
  have hneg : operatorSchmidtRank (Entropy.cutOperator B (-Y)) ≤
      operatorSchmidtRank (Entropy.cutOperator B Y) := by
    simpa only [Entropy.cutOperator, reindex_apply, Matrix.submatrix_neg, Pi.neg_apply,
      neg_one_smul] using operatorSchmidtRank_smul_le (-1 : ℂ) (Entropy.cutOperator B Y)
  rw [sub_eq_add_neg]
  exact (operatorSchmidtRank_add_le _ _).trans (Nat.add_le_add_left hneg _)

/-- **Rank of a regional term at a cut.** At every cut of the chain, a regional term has operator
Schmidt rank at most `q² + 2`: the parity layer containing the crossing bond contributes `q²`,
the other layer `1`, and the identity `1`. Supporting ALVV, arXiv:1602.08828v2, Theorem
`thm:FF-tH`(2), lines 1555–1562, and the proof of Theorem `t:aisff`, line 1606. -/
theorem rank_regionTermMatrix_le {h : ℕ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hq : 1 ≤ q)
    (hh : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i) (interval L i (i + 2)))
    (x y m c : ℕ) :
    operatorSchmidtRank ((regionTermMatrix h x y m).reindex
      (TNLean.Lattice.sheetSplit q (interval L 0 c))
      (TNLean.Lattice.sheetSplit q (interval L 0 c))) ≤ q ^ 2 + 2 := by
  rw [← TNLean.MPS.AreaLaw.operatorSchmidtRank_cutOperator_eq]
  have hdecomp : regionTermMatrix h x y m = (1 + 1) - regionalProjectionMatrix h (evenBonds x y) m -
      regionalProjectionMatrix h (oddBonds x y) m := by
    unfold regionTermMatrix
    abel
  rw [hdecomp]
  have hone : operatorSchmidtRank (Entropy.cutOperator (interval L 0 c)
      ((1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) + 1)) ≤ 1 :=
    ((Entropy.isSupportedOn_one (∅ : Finset (Fin L))).add
      (Entropy.isSupportedOn_one ∅)).operatorSchmidtRank_cutOperator_le_one
        (Or.inl (Finset.empty_subset _))
  have hsq (s : Finset ℕ) := rank_regionalProjectionMatrix_le_sq hq hh s m c
  refine (operatorSchmidtRank_cutOperator_sub_le _ _ _).trans ?_
  refine (Nat.add_le_add_right (operatorSchmidtRank_cutOperator_sub_le _ _ _) _).trans ?_
  by_cases hc : c % 2 = 0
  · have hE := rank_regionalProjectionMatrix_le_one hh (evenBonds x y) m c fun i _ hi ↦ by
      have := (Finset.mem_filter.mp hi).2
      omega
    have := hsq (oddBonds x y)
    omega
  · have hO := rank_regionalProjectionMatrix_le_one hh (oddBonds x y) m c fun i _ hi ↦ by
      have := (Finset.mem_filter.mp hi).2
      omega
    have := hsq (evenBonds x y)
    omega

end Chain

end TNLean.MPS.AreaLaw.ALVV
