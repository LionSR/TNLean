/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.GroupTruncation
import TNLean.PEPS.Approximation.SiteChainNetwork

/-!
# Dimension-free truncation of chains of rank-one site operators

The network of a chain of rank-one steps (`TNLean.PEPS.Approximation.SiteChainNetwork`) has no
wire from a vertex to itself, and its vertex tensors are the normalized bras and kets of the
steps. The whole-group truncation of Lemma 6.2 therefore applies to it, with one group for the
open legs of each vertex. This file transfers the resulting Hilbert-space estimate to an
operator-norm estimate for the chain operator: an operator read off from a tensor on the
open-leg groups acts as that tensor, reshaped as a matrix, tensored with the identity on the
untouched sites, so its operator norm is at most the Hilbert--Schmidt norm of the tensor, with
no factor depending on the dimensions of the sites.

## Main definitions

* `SiteChain.approxOp`: the operator read off from a tensor on the open-leg groups.
* `SiteChain.termOp`: the product term of a choice of one vector on each open-leg group.

## Main results

* `SiteChain.l2_opNorm_le_of_blocks`: the operator norm of a block-diagonal matrix is at most
  the largest Hilbert--Schmidt norm of its blocks.
* `SiteChain.vertexNormSq_tensor_le_one`: the vertex tensors have norm at most one.
* `SiteChain.norm_approxOp_le`: the operator norm is at most the Hilbert-space norm.
* `SiteChain.exists_chainOp_truncation`: Lemma 6.2 applied to the network of a chain.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 6.2 `lem:group-tensor`,
  `05-frames.tex`, lines 125–179, and the proof of Lemma 6.3 `lem:small-rewrite`, lines 306–329.

Source text: `openai/math` at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, file
`preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/`
`build/sections/05-frames.tex`. The statements and proofs here are formalized independently from
the manuscript; no upstream Lean proof text was reused.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.PEPS.SiteChain

open EncodedFrame WholeGroup

/-! ### Sums along injective maps -/

theorem sum_comp_le_of_injective {α β : Type*} [Fintype α] [Fintype β] {g : α → β}
    (hg : Function.Injective g) {F : β → ℝ} (hF : ∀ b, 0 ≤ F b) :
    ∑ a, F (g a) ≤ ∑ b, F b := by
  classical
  rw [← Finset.sum_image fun a _ b _ h => hg h]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun b _ _ => hF b

theorem sum_sum_comp_le_of_injective {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    {g : α → β → γ} (hg : Function.Injective fun p : α × β => g p.1 p.2)
    {F : γ → ℝ} (hF : ∀ c, 0 ≤ F c) : ∑ a, ∑ b, F (g a b) ≤ ∑ c, F c := by
  rw [← Fintype.sum_prod_type']
  exact sum_comp_le_of_injective hg hF

/-! ### Operator norm of a block-diagonal matrix -/

/-- **Block-diagonal operator norm.** If `Y a b` vanishes unless the labels `u a` and `u' b`
agree, then the operator norm of `Y` is at most the largest Hilbert--Schmidt norm of its diagonal
blocks. -/
theorem l2_opNorm_le_of_blocks {α β U : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [Finite U] [DecidableEq U] (Y : Matrix α β ℂ) (u : α → U) (u' : β → U)
    (hY : ∀ a b, u a ≠ u' b → Y a b = 0) {c : ℝ} (hc : 0 ≤ c)
    (hblock : ∀ z, ∑ a ∈ Finset.univ.filter (u · = z),
      ∑ b ∈ Finset.univ.filter (u' · = z), ‖Y a b‖ ^ 2 ≤ c ^ 2) :
    ‖Y‖ ≤ c := by
  have := Fintype.ofFinite U
  refine l2_opNorm_le_of_forall hc fun v => ?_
  set F : U → ℝ := fun z => ∑ b ∈ Finset.univ.filter (u' · = z), ‖v b‖ ^ 2
  have hrow : ∀ a, ‖(Y *ᵥ v) a‖ ^ 2 ≤
      (∑ b ∈ Finset.univ.filter (u' · = u a), ‖Y a b‖ ^ 2) * F (u a) := by
    intro a
    have hsum : (Y *ᵥ v) a = ∑ b ∈ Finset.univ.filter (u' · = u a), Y a b * v b := by
      rw [mulVec, dotProduct, Finset.sum_filter]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs with h
      · rfl
      · rw [hY a b (Ne.symm h), zero_mul]
    rw [hsum]
    calc ‖∑ b ∈ Finset.univ.filter (u' · = u a), Y a b * v b‖ ^ 2
        ≤ (∑ b ∈ Finset.univ.filter (u' · = u a), ‖Y a b‖ * ‖v b‖) ^ 2 := by
          gcongr
          exact (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun b _ => norm_mul _ _)
      _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hv : ‖(EuclideanSpace.equiv β ℂ).symm v‖ ^ 2 = ∑ z, F z := by
    rw [EuclideanSpace.norm_sq_eq, Finset.sum_fiberwise]
    rfl
  have hYv : ‖(EuclideanSpace.equiv α ℂ).symm (Y *ᵥ v)‖ ^ 2 ≤
      (c * ‖(EuclideanSpace.equiv β ℂ).symm v‖) ^ 2 := by
    rw [mul_pow, hv, Finset.mul_sum, EuclideanSpace.norm_sq_eq]
    calc ∑ a, ‖(EuclideanSpace.equiv α ℂ).symm (Y *ᵥ v) a‖ ^ 2
        ≤ ∑ a, (∑ b ∈ Finset.univ.filter (u' · = u a), ‖Y a b‖ ^ 2) * F (u a) :=
          Finset.sum_le_sum fun a _ => hrow a
      _ = ∑ z, ∑ a ∈ Finset.univ.filter (u · = z),
            (∑ b ∈ Finset.univ.filter (u' · = z), ‖Y a b‖ ^ 2) * F z := by
          rw [← Finset.sum_fiberwise Finset.univ u]
          refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun a ha => ?_
          rw [(Finset.mem_filter.mp ha).2]
      _ ≤ ∑ z, c ^ 2 * F z := by
          refine Finset.sum_le_sum fun z _ => ?_
          rw [← Finset.sum_mul]
          exact mul_le_mul_of_nonneg_right (hblock z)
            (Finset.sum_nonneg fun b _ => sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hYv

variable {ι : Type*} {q : ℕ} [NeZero q] {n : ℕ} (st : Fin n → Step ι q)

/-- On the configurations where the chain operator can be nonzero, the open-leg configurations
together with the values at the untouched sites determine the output and input
configurations. -/
theorem eq_of_groupsOf_eq {σ τ σ' τ' : ι → Fin q} (hG : Good st σ τ) (hG' : Good st σ' τ')
    (hσ : ∀ x, Untouched st x → σ x = σ' x) (hτ : ∀ x, Untouched st x → τ x = τ' x)
    (h : groupsOf st σ τ = groupsOf st σ' τ') : σ = σ' ∧ τ = τ' := by
  refine ⟨funext fun x => ?_, funext fun x => ?_⟩
  · by_cases hx : Untouched st x
    · exact hσ x hx
    · simp only [Untouched, not_forall, not_not] at hx
      obtain ⟨i, hxi, hL⟩ := exists_outEnd hx
      by_cases hk : (st i).ket.isSome
      · exact congrFun (congrFun h (.inr i)) ⟨x, hxi, hL, hk⟩
      · rw [hG.2.2 x ⟨i, hxi, hL, by simpa using hk⟩, hG'.2.2 x ⟨i, hxi, hL, by simpa using hk⟩]
  · by_cases hx : Untouched st x
    · exact hτ x hx
    · simp only [Untouched, not_forall, not_not] at hx
      obtain ⟨j, hxj, hE⟩ := exists_inEnd hx
      by_cases hb : (st j).bra.isSome
      · exact congrFun (congrFun h (.inl j)) ⟨x, hxj, hE, hb⟩
      · rw [hG.2.1 x ⟨j, hxj, hE, by simpa using hb⟩, hG'.2.1 x ⟨j, hxj, hE, by simpa using hb⟩]

variable [DecidableEq ι]

/-! ### Vertex norms -/

theorem ketCfg_injective (i : Fin n) :
    Function.Injective fun p : ({e // IsIncident (tail st) (head st) (.inr i) e} → Fin q) ×
      Group st (.inr i) => ketCfg st i p.1 p.2 := by
  rintro ⟨lab, o⟩ ⟨lab', o'⟩ h
  refine Prod.ext (funext fun e => ?_) (funext fun x => ?_)
  · obtain ⟨⟨⟨y, j⟩, hy, hL⟩, he⟩ := e
    obtain rfl : j = i := by
      rcases he with he | he
      · exact Sum.inr_injective he
      · exact absurd he Sum.inl_ne_inr
    have hx := congrFun h ⟨y, hy⟩
    simp only [ketCfg] at hx
    rwa [dite_eq_left hL, dite_eq_left hL] at hx
  · obtain ⟨y, hy, hL, hk⟩ := x
    have hx := congrFun h ⟨y, hy⟩
    simp only [ketCfg] at hx
    rwa [dite_eq_right hL, dite_eq_right hL, dite_eq_left hk, dite_eq_left hk] at hx

theorem braCfg_injective (j : Fin n) :
    Function.Injective fun p : ({e // IsIncident (tail st) (head st) (.inl j) e} → Fin q) ×
      Group st (.inl j) => braCfg st j p.1 p.2 := by
  rintro ⟨lab, o⟩ ⟨lab', o'⟩ h
  refine Prod.ext (funext fun e => ?_) (funext fun x => ?_)
  · obtain ⟨e, he⟩ := e
    have hj : prevIdx st e = j := by
      rcases he with he | he
      · exact absurd he Sum.inr_ne_inl
      · exact Sum.inl_injective he
    have hspec := prevIdx_spec st e
    have hy : e.1.1 ∈ (st j).sites := hj ▸ hspec.2
    have hE : EarlierTouch st j e.1.1 := ⟨e.1.2, hj ▸ hspec.1, e.2.1⟩
    have hx := congrFun h ⟨e.1.1, hy⟩
    simp only [braCfg] at hx
    rw [dite_eq_left hE, dite_eq_left hE] at hx
    have hee : edgeInto st j e.1.1 hy hE = e := by
      subst hj
      exact edgeInto_prevIdx st e
    convert hx using 3 <;> exact Subtype.ext hee.symm
  · obtain ⟨y, hy, hE, hb⟩ := x
    have hx := congrFun h ⟨y, hy⟩
    simp only [braCfg] at hx
    rwa [dite_eq_right hE, dite_eq_right hE, dite_eq_left hb, dite_eq_left hb] at hx

variable [Fintype ι]

/-- Every vertex tensor of the network of a chain of steps with vectors of norm at most one has
norm at most one. -/
theorem vertexNormSq_tensor_le_one (hket : ∀ i, ‖(st i).ketVec‖ ≤ 1)
    (hbra : ∀ i, ‖(st i).braVec‖ ≤ 1) (v : Fin n ⊕ Fin n) : vertexNormSq (tensor st) v ≤ 1 := by
  rcases v with j | i
  · have key := sum_sum_comp_le_of_injective (g := braCfg st j) (braCfg_injective st j)
      (F := fun c => ‖(st j).braVec c‖ ^ 2) fun _ => sq_nonneg _
    calc vertexNormSq (tensor st) (.inl j)
        = ∑ a, ∑ b, (fun c => ‖(st j).braVec c‖ ^ 2) (braCfg st j a b) := by
          rw [vertexNormSq]
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun p _ => ?_
          change ‖star ((st j).braVec (braCfg st j x p))‖ ^ 2 = _
          rw [norm_star]
      _ ≤ ∑ c, (fun c => ‖(st j).braVec c‖ ^ 2) c := key
      _ ≤ 1 := by
          rw [← EuclideanSpace.norm_sq_eq]
          exact pow_le_one₀ (norm_nonneg _) (hbra j)
  · have key := sum_sum_comp_le_of_injective (g := ketCfg st i) (ketCfg_injective st i)
      (F := fun c => ‖(st i).ketVec c‖ ^ 2) fun _ => sq_nonneg _
    calc vertexNormSq (tensor st) (.inr i)
        = ∑ a, ∑ b, (fun c => ‖(st i).ketVec c‖ ^ 2) (ketCfg st i a b) := by
          rw [vertexNormSq]
          rfl
      _ ≤ ∑ c, (fun c => ‖(st i).ketVec c‖ ^ 2) c := key
      _ ≤ 1 := by
          rw [← EuclideanSpace.norm_sq_eq]
          exact pow_le_one₀ (norm_nonneg _) (hket i)

/-! ### Operators read off from tensors on the open legs -/

/-- The operator with entry `W(groups(σ, τ))` at the configurations `σ, τ` on which the chain
operator can be nonzero, and `0` elsewhere. -/
def approxOp (W : ((v : Fin n ⊕ Fin n) → Group st v) → ℂ) : Matrix (ι → Fin q) (ι → Fin q) ℂ :=
  Matrix.of fun σ τ => if Good st σ τ then W (groupsOf st σ τ) else 0

theorem chainOp_eq_approxOp : chainOp st = approxOp st (contraction (tensor st)) := by
  ext σ τ
  rw [chainOp_apply]
  rfl

theorem approxOp_sub (W W' : ((v : Fin n ⊕ Fin n) → Group st v) → ℂ) :
    approxOp st (W - W') = approxOp st W - approxOp st W' := by
  ext σ τ
  simp only [approxOp, of_apply, Matrix.sub_apply, Pi.sub_apply]
  split_ifs <;> simp

theorem approxOp_sum_smul {κ : Type*} [Fintype κ] (c : κ → ℂ)
    (T : κ → ((v : Fin n ⊕ Fin n) → Group st v) → ℂ) :
    approxOp st (fun ω => ∑ i, c i * T i ω) = ∑ i, c i • approxOp st (T i) := by
  ext σ τ
  simp only [approxOp, of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- **The operator norm is at most the Hilbert-space norm on the open legs.** The operator read
off from a tensor `W` on the open-leg groups acts as `W`, reshaped as a matrix, tensored with the
identity on the untouched sites; its operator norm is at most the Hilbert--Schmidt norm of `W`,
whatever the dimensions of the untouched sites.

Polynomial-PEPS manuscript (September 24, 2026), proof of Lemma 6.3 `lem:small-rewrite`,
`05-frames.tex`, lines 321–329. -/
theorem norm_approxOp_le (W : ((v : Fin n ⊕ Fin n) → Group st v) → ℂ) :
    ‖approxOp st W‖ ≤
      ‖(WithLp.toLp 2 W : EuclideanSpace ℂ ((v : Fin n ⊕ Fin n) → Group st v))‖ := by
  refine l2_opNorm_le_of_blocks _ (fun σ : ι → Fin q => fun x : {x // Untouched st x} => σ x)
    (fun τ x => τ x) (fun σ τ hne => ?_) (norm_nonneg _) fun z => ?_
  · simp only [approxOp, of_apply]
    exact ite_eq_right fun hG => hne (funext fun x => hG.1 x x.2)
  · rw [EuclideanSpace.norm_sq_eq, ← Finset.sum_product']
    set A := Finset.univ.filter fun σ : ι → Fin q => (fun x : {x // Untouched st x} => σ x) = z
    have hinj : ∀ p ∈ (A ×ˢ A).filter (fun p => Good st p.1 p.2),
        ∀ p' ∈ (A ×ˢ A).filter (fun p => Good st p.1 p.2),
          groupsOf st p.1 p.2 = groupsOf st p'.1 p'.2 → p = p' := by
      intro p hp p' hp' h
      simp only [Finset.mem_filter, Finset.mem_product, A, Finset.mem_univ, true_and] at hp hp'
      obtain ⟨h1, h2⟩ := eq_of_groupsOf_eq st hp.2 hp'.2
        (fun x hx => congrFun (hp.1.1.trans hp'.1.1.symm) ⟨x, hx⟩)
        (fun x hx => congrFun (hp.1.2.trans hp'.1.2.symm) ⟨x, hx⟩) h
      exact Prod.ext h1 h2
    calc ∑ p ∈ A ×ˢ A, ‖approxOp st W p.1 p.2‖ ^ 2
        = ∑ p ∈ (A ×ˢ A).filter (fun p => Good st p.1 p.2), ‖W (groupsOf st p.1 p.2)‖ ^ 2 := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun p _ => ?_
          simp only [approxOp, of_apply]
          split_ifs <;> simp
      _ = ∑ ω ∈ ((A ×ˢ A).filter (fun p => Good st p.1 p.2)).image
            (fun p => groupsOf st p.1 p.2), ‖W ω‖ ^ 2 :=
          (Finset.sum_image (f := fun ω => ‖W ω‖ ^ 2) hinj).symm
      _ ≤ ∑ ω, ‖W ω‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
      _ = ∑ ω, ‖(WithLp.toLp 2 W : EuclideanSpace ℂ ((v : Fin n ⊕ Fin n) → Group st v)) ω‖ ^ 2 :=
          rfl

/-- A product term: the operator read off from the product tensor `∏_v e_{v, i_v}` of one vector
on the open-leg group of each vertex. Its entry at `σ, τ` is
`∏_v e_{v, i_v}(groups_v(σ, τ))` on the configurations where the chain operator can be nonzero,
so it is the tensor product of the normalized output vectors `e_{v, i_v}` at the ket vertices,
the normalized input covectors at the bra vertices, the product zero vectors of the steps that
have them, and the identity on the untouched sites. -/
def termOp {r : Fin n ⊕ Fin n → ℕ}
    (e : (v : Fin n ⊕ Fin n) → Fin (r v) → EuclideanSpace ℂ (Group st v))
    (i : (v : Fin n ⊕ Fin n) → Fin (r v)) : Matrix (ι → Fin q) (ι → Fin q) ℂ :=
  approxOp st fun ω => ∏ v, e v (i v) (ω v)

theorem termOp_apply {r : Fin n ⊕ Fin n → ℕ}
    (e : (v : Fin n ⊕ Fin n) → Fin (r v) → EuclideanSpace ℂ (Group st v))
    (i : (v : Fin n ⊕ Fin n) → Fin (r v)) (σ τ : ι → Fin q) :
    termOp st e i σ τ = if Good st σ τ then ∏ v, e v (i v) (groupsOf st σ τ v) else 0 :=
  rfl

/-- **Whole-group truncation of a chain of rank-one steps (Lemma 6.2 applied to the network of a
chain).** Let every step have output and input vectors of norm at most one, and let `G` be a
set of vertices containing every vertex with an open leg. For every `k ≥ 1` there are
orthonormal families of at most `k` vectors on the open-leg groups and coefficients of modulus
at most one such that the chain operator differs in operator norm by at most `|G| / √k` from
the sum of the corresponding product terms, of which there are at most `k ^ |G|`. No constant
depends on the dimensions of the sites.

Polynomial-PEPS manuscript (September 24, 2026), proof of Lemma 6.3 `lem:small-rewrite`,
`05-frames.tex`, lines 274–329, with Lemma 6.2 `lem:group-tensor`, lines 125–141. -/
theorem exists_chainOp_truncation (hket : ∀ i, ‖(st i).ketVec‖ ≤ 1)
    (hbra : ∀ i, ‖(st i).braVec‖ ≤ 1) (G : Finset (Fin n ⊕ Fin n))
    (hG : ∀ v ∉ G, ∀ x, ¬IsOpen st v x) (k : ℕ) (hk : 1 ≤ k) :
    ∃ (r : Fin n ⊕ Fin n → ℕ)
      (e : (v : Fin n ⊕ Fin n) → Fin (r v) → EuclideanSpace ℂ (Group st v))
      (c : ((v : Fin n ⊕ Fin n) → Fin (r v)) → ℂ),
      (∀ v, r v ≤ k) ∧ (∀ v, Orthonormal ℂ (e v)) ∧ (∀ i, ‖c i‖ ≤ 1) ∧
      Fintype.card ((v : Fin n ⊕ Fin n) → Fin (r v)) ≤ k ^ G.card ∧
      ‖chainOp st - ∑ i, c i • termOp st e i‖ ≤ G.card / √k := by
  have hG' : ∀ v ∉ G, Fintype.card (Group st v) ≤ 1 := fun v hv => by
    have : IsEmpty {x // IsOpen st v x} := ⟨fun x => hG v hv x.1 x.2⟩
    exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance
  obtain ⟨r, e, hr, he, herr, hcard, c, hc, hZk⟩ := exists_simultaneous_group_truncation
    (tensor st) (tail_ne_head st) (vertexNormSq_tensor_le_one st hket hbra) G hG' k hk
  refine ⟨r, e, c, hr, he, hc, hcard, ?_⟩
  set Z : EuclideanSpace ℂ ((v : Fin n ⊕ Fin n) → Group st v) :=
    WithLp.toLp 2 (contraction (tensor st))
  set Zk := toEuclideanLin (factorMatrix fun v => orthonormalProjector (e v)) Z
  have hterm : ∑ i, c i • termOp st e i = approxOp st Zk.ofLp := by
    rw [hZk]
    unfold termOp
    rw [← approxOp_sum_smul]
    congr 1
    funext ω
    simp [productVector]
  have hdiff : chainOp st - ∑ i, c i • termOp st e i = approxOp st (Z - Zk).ofLp := by
    rw [hterm, chainOp_eq_approxOp, WithLp.ofLp_sub, approxOp_sub]
  rw [hdiff]
  exact (norm_approxOp_le st _).trans herr

end TNLean.PEPS.SiteChain
