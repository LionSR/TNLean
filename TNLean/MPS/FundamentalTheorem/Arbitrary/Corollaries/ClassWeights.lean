/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Arbitrary.Corollaries.WeightedStates

/-!
# Class weights

Let `(R_j)_j` be periodic tensors of periods `m_j`, pairwise not related by a phase and a gauge.
A tensor `A` has *class weights* `(a_j)_j` over this family if `V_N(A) = ∑_j p_N(a_j) V_N(R_j)` at
every positive length, where `p_N(s) = ∑_{α ∈ s} α ^ N`. Any two tensors have class weights over a
common family. This file compares tensors through their class weights:

* the weighted identity `tr V^N V_N(A) = tr U^N V_N(B)` says
  `(σ(V) a_j)^{m_j} = (σ(U) b_j)^{m_j}` for every `j`;
* linear dependence of the states at all large lengths says `a_i^L b_j^L = a_j^L b_i^L`, where
  `L = lcm(m_i, m_j)`;
* if every class occurs once on each side, dependence gives a single `λ` with
  `V_N(A) = λ ^ N V_N(B)`.

## Main results

* `MPSTensor.exists_hasClassWeights`.
* `MPSTensor.forall_trace_pow_mul_mpv_eq_iff_classWeights`.
* `MPSTensor.eventually_mpv_eq_pow_mul_iff_classWeights`.
* `MPSTensor.eventually_statesDependentAt_iff_classWeights`.
* `MPSTensor.exists_pow_of_card_classWeights_eq_one`.

## Implementation notes

For the last result the congruences `x ≡ x_j` modulo `M / m_j` are pairwise compatible but the
moduli need not be coprime, so the Chinese remainder theorem is used in its general form, by
induction on the index set (`exists_modEq_of_pairwise`).

## References

* De las Cuevas, Cirac, Schuch, Pérez-García, arXiv:1708.00029, Eq. `eq:bdnr`, whose diagonal
  matrices `R_j` are the class weights.
-/

open Filter

namespace MPSTensor

variable {d : ℕ}

/-! ### Multisets of weights -/

/-- The multiset of products of an element of `s` and an element of `t`. -/
noncomputable def weightProduct (s t : Multiset ℂ) : Multiset ℂ :=
  (s ×ˢ t).map fun p => p.1 * p.2

theorem sum_map_pow_weightProduct (s t : Multiset ℂ) (N : ℕ) :
    ((weightProduct s t).map (· ^ N)).sum = (s.map (· ^ N)).sum * (t.map (· ^ N)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [weightProduct]
  | cons a s ih =>
      simp only [weightProduct] at ih ⊢
      rw [Multiset.cons_product, Multiset.map_add, Multiset.map_add, Multiset.sum_add, ih,
        Multiset.map_cons, Multiset.sum_cons, add_mul, Multiset.map_map, Multiset.map_map]
      simp only [Function.comp_def, mul_pow, Multiset.sum_map_mul_left]

theorem weightProduct_singleton_left (c : ℂ) (t : Multiset ℂ) :
    weightProduct {c} t = t.map (c * ·) := by
  change ((c ::ₘ 0) ×ˢ t).map _ = _
  rw [Multiset.cons_product, Multiset.zero_product, add_zero, Multiset.map_map]
  rfl

private theorem notMem_zero_weightProduct {s t : Multiset ℂ} (hs : (0 : ℂ) ∉ s)
    (ht : (0 : ℂ) ∉ t) : (0 : ℂ) ∉ weightProduct s t := by
  intro h
  obtain ⟨⟨x, y⟩, hp, hxy⟩ := Multiset.mem_map.mp h
  obtain ⟨hx, hy⟩ := Multiset.mem_product.mp hp
  rcases mul_eq_zero.mp hxy with h0 | h0
  · exact hs (h0 ▸ hx)
  · exact ht (h0 ▸ hy)

private theorem notMem_zero_map_pow {s : Multiset ℂ} (hs : (0 : ℂ) ∉ s) (L : ℕ) :
    (0 : ℂ) ∉ s.map (· ^ L) := by
  intro h
  obtain ⟨x, hx, hxL⟩ := Multiset.mem_map.mp h
  have hne : x ≠ 0 := fun h0 => hs (h0 ▸ hx)
  exact pow_ne_zero L hne hxL

private theorem sum_map_pow_map_pow (s : Multiset ℂ) (m k : ℕ) :
    ((s.map (· ^ m)).map (· ^ k)).sum = (s.map (· ^ (m * k))).sum := by
  rw [Multiset.map_map]
  simp only [Function.comp_def, pow_mul]

/-! ### Class weights -/

/-- `V_N(A) = ∑_j (∑_{α ∈ a_j} α ^ N) V_N(R_j)` at every positive length, with nonzero weights. -/
def HasClassWeights {g : ℕ} {dim : Fin g → ℕ} (R : ∀ j, MPSTensor d (dim j)) {D : ℕ}
    (A : MPSTensor d D) (a : Fin g → Multiset ℂ) : Prop :=
  (∀ j, (0 : ℂ) ∉ a j) ∧ ∀ N, 0 < N → ∀ σ : Fin N → Fin d,
    mpv A σ = ∑ j, ((a j).map (· ^ N)).sum * mpv (R j) σ

section

variable {DA DB : ℕ}

/-- The weights of one tensor, read from a class decomposition of its blocks. -/
private theorem hasClassWeights_of_blocks {r g : ℕ} {dimB : Fin r → ℕ} {dim : Fin g → ℕ}
    (blocks : ∀ k, MPSTensor d (dimB k)) (R : ∀ j, MPSTensor d (dim j)) {A : MPSTensor d DA}
    (hsame : SameMPV₂Pos A (toTensorFromBlocks (d := d) (μ := fun _ : Fin r => (1 : ℂ)) blocks))
    (cls : Fin r → Fin g) (lam : Fin r → ℂ) (hlam : ∀ k, lam k ≠ 0)
    (hmpv : ∀ k N (σ : Fin N → Fin d), mpv (blocks k) σ = lam k ^ N * mpv (R (cls k)) σ) :
    HasClassWeights R A fun j => (Finset.univ.filter fun k => cls k = j).val.map lam := by
  refine ⟨fun j h => ?_, fun N hN σ => ?_⟩
  · obtain ⟨k, -, hk⟩ := Multiset.mem_map.mp h
    exact hlam k hk
  · rw [hsame N hN σ, mpv_toTensorFromBlocks_eq_sum]
    simp only [one_pow, smul_eq_mul, one_mul]
    rw [← sum_fiber_pow_mul_mpv_eq_sum R blocks cls lam hmpv σ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Multiset.map_map]
    rfl

/-- **Existence of class weights.** Any two tensors have class weights over a common family of
periodic tensors, pairwise not related by a phase and a gauge. -/
theorem exists_hasClassWeights (A : MPSTensor d DA) (B : MPSTensor d DB) :
    ∃ (g : ℕ) (dim : Fin g → ℕ) (R : ∀ j, MPSTensor d (dim j)) (per : Fin g → ℕ)
      (a b : Fin g → Multiset ℂ),
      (∀ j, IsPeriodic (per j) (R j)) ∧
      (∀ i j, i ≠ j → ∀ hdim : dim i = dim j,
        ¬ RepeatedBlocks (cast (congr_arg (MPSTensor d) hdim) (R i)) (R j)) ∧
      HasClassWeights R A a ∧ HasClassWeights R B b := by
  classical
  obtain ⟨r, dimA, blocksA, hIrrA, hletA, -, hsameA, -⟩ :=
    exists_irreducible_blockDecomp_nonzeroBlocks A
  obtain ⟨r', dimB, blocksB, hIrrB, hletB, -, hsameB, -⟩ :=
    exists_irreducible_blockDecomp_nonzeroBlocks B
  let U := Fin r ⊕ Fin r'
  let DU : U → ℕ := Sum.elim dimA dimB
  let CU : ∀ u, MPSTensor d (DU u) := fun u =>
    match u with
    | Sum.inl s => blocksA s
    | Sum.inr t => blocksB t
  have hirrU : ∀ u, Matrix.IsIrreducibleAction (CU u) := by
    rintro (s | t)
    · exact (Kraus.isIrreducibleAction_iff_isIrreducibleFamily _).2 (hIrrA s)
    · exact (Kraus.isIrreducibleAction_iff_isIrreducibleFamily _).2 (hIrrB t)
  have hletU : ∀ u, ∃ i, CU u i ≠ 0 := by
    rintro (s | t)
    exacts [hletA s, hletB t]
  obtain ⟨g, dim, R, per, cls, lam, hper, hnonrep, hlam, hmpv, -⟩ :=
    exists_periodic_class_decomposition CU hirrU hletU
  exact ⟨g, dim, R, per, _, _, hper, hnonrep,
    hasClassWeights_of_blocks blocksA R hsameA (fun s => cls (Sum.inl s))
      (fun s => lam (Sum.inl s)) (fun s => hlam _) (fun s => hmpv (Sum.inl s)),
    hasClassWeights_of_blocks blocksB R hsameB (fun t => cls (Sum.inr t))
      (fun t => lam (Sum.inr t)) (fun t => hlam _) (fun t => hmpv (Sum.inr t))⟩

variable {g : ℕ} {dim : Fin g → ℕ} {R : ∀ j, MPSTensor d (dim j)} {per : Fin g → ℕ}
  {a b : Fin g → Multiset ℂ} {A : MPSTensor d DA} {B : MPSTensor d DB}

/-- The identity with arbitrary weight multisets in place of the eigenvalues. -/
private theorem forall_sum_mul_mpv_eq_iff_classWeights {s t : Multiset ℂ}
    (hs : (0 : ℂ) ∉ s) (ht : (0 : ℂ) ∉ t)
    (hR : ∀ j, IsPeriodic (per j) (R j))
    (hnr : ∀ i j, i ≠ j → ∀ hdim : dim i = dim j,
      ¬ RepeatedBlocks (cast (congr_arg (MPSTensor d) hdim) (R i)) (R j))
    (ha : HasClassWeights R A a) (hb : HasClassWeights R B b) :
    (∀ N, 0 < N → ∀ σ : Fin N → Fin d,
        (s.map (· ^ N)).sum * mpv A σ = (t.map (· ^ N)).sum * mpv B σ) ↔
      ∀ j, (weightProduct s (a j)).map (· ^ per j) =
        (weightProduct t (b j)).map (· ^ per j) := by
  constructor
  · intro h j
    obtain ⟨N₁, hN₁⟩ := periodicBasis_nonzero_subfamily_eventuallyLinearlyIndependent R per hR hnr
    refine Multiset.eq_of_notMem_zero_of_forall_sum_map_pow_eq
      (notMem_zero_map_pow (notMem_zero_weightProduct hs (ha.1 j)) _)
      (notMem_zero_map_pow (notMem_zero_weightProduct ht (hb.1 j)) _)
      ⟨N₁ + 1, fun L hL => ?_⟩
    rw [sum_map_pow_map_pow, sum_map_pow_map_pow, sum_map_pow_weightProduct,
      sum_map_pow_weightProduct]
    have hper := (hR j).period_pos
    have hNpos : 0 < per j * L := Nat.mul_pos hper (by omega)
    have hNge : N₁ ≤ per j * L := by nlinarith
    have hc : ∀ σ : Fin (per j * L) → Fin d,
        ∑ i, ((s.map (· ^ (per j * L))).sum * ((a i).map (· ^ (per j * L))).sum -
          (t.map (· ^ (per j * L))).sum * ((b i).map (· ^ (per j * L))).sum) * mpv (R i) σ = 0 := by
      intro σ
      have h1 := h _ hNpos σ
      rw [ha.2 _ hNpos σ, hb.2 _ hNpos σ, Finset.mul_sum, Finset.mul_sum, ← sub_eq_zero,
        ← Finset.sum_sub_distrib] at h1
      exact (Finset.sum_congr rfl fun i _ => by ring).trans h1
    exact sub_eq_zero.1 (coeff_eq_zero_of_forall_sum_mul_mpv_eq_zero R per hR (hN₁ _ hNge) _ hc j
      (dvd_mul_right _ _))
  · intro h N hN σ
    rw [ha.2 N hN σ, hb.2 N hN σ, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hd : per j ∣ N
    · obtain ⟨k, rfl⟩ := hd
      have h1 := congrArg (fun x => (x.map (· ^ k)).sum) (h j)
      simp only [sum_map_pow_map_pow, sum_map_pow_weightProduct] at h1
      linear_combination mpv (R j) σ * h1
    · rw [pgvwc07_stateVector_eq_zero_of_not_dvd (R j) (hR j) hd σ]
      simp

/-- **The weighted identity by classes.** Through class weights, the weighted identity says
`(σ(V) a_j)^{m_j} = (σ(U) b_j)^{m_j}` for every `j`. -/
theorem forall_trace_pow_mul_mpv_eq_iff_classWeights {m n : ℕ}
    {V : Matrix (Fin m) (Fin m) ℂ} {U : Matrix (Fin n) (Fin n) ℂ}
    (hR : ∀ j, IsPeriodic (per j) (R j))
    (hnr : ∀ i j, i ≠ j → ∀ hdim : dim i = dim j,
      ¬ RepeatedBlocks (cast (congr_arg (MPSTensor d) hdim) (R i)) (R j))
    (ha : HasClassWeights R A a) (hb : HasClassWeights R B b) :
    (∀ N, 0 < N → ∀ σ : Fin N → Fin d,
        Matrix.trace (V ^ N) * mpv A σ = Matrix.trace (U ^ N) * mpv B σ) ↔
      ∀ j, (weightProduct (nonzeroSpectrum V) (a j)).map (· ^ per j) =
        (weightProduct (nonzeroSpectrum U) (b j)).map (· ^ per j) := by
  have hnz : ∀ {k : ℕ} (M : Matrix (Fin k) (Fin k) ℂ), (0 : ℂ) ∉ nonzeroSpectrum M := fun M h =>
    (Multiset.mem_filter.mp h).2 rfl
  rw [← forall_sum_mul_mpv_eq_iff_classWeights (hnz V) (hnz U) hR hnr ha hb]
  refine forall₂_congr fun N hN => forall_congr' fun σ => ?_
  rw [trace_pow_eq_sum_nonzeroSpectrum V hN, trace_pow_eq_sum_nonzeroSpectrum U hN]

/-- **Proportional states by classes.** `V_N(A) = λ ^ N V_N(B)` for all large `N` exactly when
`a_j^{m_j} = (λ b_j)^{m_j}` for every `j`. -/
theorem eventually_mpv_eq_pow_mul_iff_classWeights {lam : ℂ} (hlam : lam ≠ 0)
    (hR : ∀ j, IsPeriodic (per j) (R j))
    (hnr : ∀ i j, i ≠ j → ∀ hdim : dim i = dim j,
      ¬ RepeatedBlocks (cast (congr_arg (MPSTensor d) hdim) (R i)) (R j))
    (ha : HasClassWeights R A a) (hb : HasClassWeights R B b) :
    (∀ᶠ N in atTop, ∀ σ : Fin N → Fin d, mpv A σ = lam ^ N * mpv B σ) ↔
      ∀ j, (a j).map (· ^ per j) = (b j).map (fun β => (lam * β) ^ per j) := by
  have hV : ∀ N : ℕ, Matrix.trace ((1 : Matrix (Fin 1) (Fin 1) ℂ) ^ N) = 1 := fun N => by simp
  have hU : ∀ N : ℕ, Matrix.trace ((lam • (1 : Matrix (Fin 1) (Fin 1) ℂ)) ^ N) = lam ^ N :=
    fun N => by simp [smul_pow, Matrix.trace_smul]
  have htfae := (tfae_weightedStates A B (1 : Matrix (Fin 1) (Fin 1) ℂ)
    (lam • (1 : Matrix (Fin 1) (Fin 1) ℂ))).out 1 2
  simp only [hV, hU, one_mul] at htfae
  rw [htfae]
  have h1 : (0 : ℂ) ∉ ({1} : Multiset ℂ) := by simp
  have h2 : (0 : ℂ) ∉ ({lam} : Multiset ℂ) := by simpa using hlam.symm
  have key := forall_sum_mul_mpv_eq_iff_classWeights h1 h2 hR hnr ha hb
  simp only [Multiset.map_singleton, Multiset.sum_singleton, one_pow, one_mul,
    weightProduct_singleton_left, Multiset.map_map, Function.comp_def, Multiset.map_id'] at key
  exact key

/-- **Dependent states by classes.** Through class weights, linear dependence of the states at all
large lengths says `a_i^L b_j^L = a_j^L b_i^L` for all `i`, `j`, with `L = lcm(m_i, m_j)`. -/
theorem eventually_statesDependentAt_iff_classWeights
    (hR : ∀ j, IsPeriodic (per j) (R j))
    (hnr : ∀ i j, i ≠ j → ∀ hdim : dim i = dim j,
      ¬ RepeatedBlocks (cast (congr_arg (MPSTensor d) hdim) (R i)) (R j))
    (ha : HasClassWeights R A a) (hb : HasClassWeights R B b) :
    (∀ᶠ N in atTop, StatesDependentAt A B N) ↔
      ∀ i j, weightProduct ((a i).map (· ^ Nat.lcm (per i) (per j)))
          ((b j).map (· ^ Nat.lcm (per i) (per j))) =
        weightProduct ((a j).map (· ^ Nat.lcm (per i) (per j)))
          ((b i).map (· ^ Nat.lcm (per i) (per j))) := by
  constructor
  · intro h i j
    have hL : 0 < Nat.lcm (per i) (per j) :=
      Nat.lcm_pos (hR i).period_pos (hR j).period_pos
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp h
    obtain ⟨N₁, hN₁⟩ := periodicBasis_nonzero_subfamily_eventuallyLinearlyIndependent R per hR hnr
    refine Multiset.eq_of_notMem_zero_of_forall_sum_map_pow_eq
      (notMem_zero_weightProduct (notMem_zero_map_pow (ha.1 i) _) (notMem_zero_map_pow (hb.1 j) _))
      (notMem_zero_weightProduct (notMem_zero_map_pow (ha.1 j) _) (notMem_zero_map_pow (hb.1 i) _))
      ⟨N₀ + N₁ + 1, fun k hk => ?_⟩
    rw [sum_map_pow_weightProduct, sum_map_pow_weightProduct, sum_map_pow_map_pow,
      sum_map_pow_map_pow, sum_map_pow_map_pow, sum_map_pow_map_pow]
    set N := Nat.lcm (per i) (per j) * k with hNdef
    have hNge : N₀ + N₁ + 1 ≤ N := by nlinarith
    have hNpos : 0 < N := by omega
    have hdi : per i ∣ N := (Nat.dvd_lcm_left _ _).trans (dvd_mul_right _ _)
    have hdj : per j ∣ N := (Nat.dvd_lcm_right _ _).trans (dvd_mul_right _ _)
    obtain ⟨α, β, hαβ, hdep⟩ := hN₀ N (by omega)
    have hc : ∀ σ : Fin N → Fin d,
        ∑ r, (α * ((a r).map (· ^ N)).sum - β * ((b r).map (· ^ N)).sum) * mpv (R r) σ = 0 := by
      intro σ
      have h1 := hdep σ
      rw [ha.2 N hNpos σ, hb.2 N hNpos σ, Finset.mul_sum, Finset.mul_sum, ← sub_eq_zero,
        ← Finset.sum_sub_distrib] at h1
      exact (Finset.sum_congr rfl fun r _ => by ring).trans h1
    have hci := coeff_eq_zero_of_forall_sum_mul_mpv_eq_zero R per hR (hN₁ N (by omega)) _ hc i hdi
    have hcj := coeff_eq_zero_of_forall_sum_mul_mpv_eq_zero R per hR (hN₁ N (by omega)) _ hc j hdj
    rcases hαβ with hα | hβ
    · apply mul_left_cancel₀ hα
      linear_combination ((b j).map (· ^ N)).sum * hci - ((b i).map (· ^ N)).sum * hcj
    · apply mul_left_cancel₀ hβ
      linear_combination ((a j).map (· ^ N)).sum * hci - ((a i).map (· ^ N)).sum * hcj
  · intro h
    refine eventually_atTop.2 ⟨1, fun N hN => ?_⟩
    have hN' : 0 < N := hN
    have rel : ∀ i j, per i ∣ N → per j ∣ N →
        ((a i).map (· ^ N)).sum * ((b j).map (· ^ N)).sum =
          ((a j).map (· ^ N)).sum * ((b i).map (· ^ N)).sum := by
      intro i j hi hj
      obtain ⟨k, hk⟩ := Nat.lcm_dvd hi hj
      have h1 := congrArg (fun x => (x.map (· ^ k)).sum) (h i j)
      simp only [sum_map_pow_map_pow, sum_map_pow_weightProduct] at h1
      rwa [← hk] at h1
    by_cases hz : ∃ j, per j ∣ N ∧ ((b j).map (· ^ N)).sum ≠ 0
    · obtain ⟨j₀, hj₀, hne⟩ := hz
      refine ⟨_, ((a j₀).map (· ^ N)).sum, Or.inl hne, fun σ => ?_⟩
      rw [ha.2 N hN' σ, hb.2 N hN' σ, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hd : per r ∣ N
      · linear_combination mpv (R r) σ * rel r j₀ hd hj₀
      · rw [pgvwc07_stateVector_eq_zero_of_not_dvd (R r) (hR r) hd σ]
        simp
    · push Not at hz
      refine ⟨0, 1, Or.inr one_ne_zero, fun σ => ?_⟩
      rw [zero_mul, one_mul, hb.2 N hN' σ]
      symm
      refine Finset.sum_eq_zero fun r _ => ?_
      by_cases hd : per r ∣ N
      · rw [hz r hd, zero_mul]
      · rw [pgvwc07_stateVector_eq_zero_of_not_dvd (R r) (hR r) hd σ, mul_zero]

/-! ### One factor per class -/

private theorem gcd_lcm_dvd (x y z : ℕ) :
    Nat.gcd (Nat.lcm x y) z ∣ Nat.lcm (Nat.gcd x z) (Nat.gcd y z) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simpa using Nat.dvd_lcm_left z (Nat.gcd y z)
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simpa using Nat.dvd_lcm_right (Nat.gcd x z) z
  rcases Nat.eq_zero_or_pos z with rfl | hz
  · simp
  have hl : Nat.lcm x y ≠ 0 := (Nat.lcm_pos hx hy).ne'
  have hg1 : Nat.gcd (Nat.lcm x y) z ≠ 0 := (Nat.gcd_pos_of_pos_right _ hz).ne'
  have hg2 : Nat.gcd x z ≠ 0 := (Nat.gcd_pos_of_pos_left _ hx).ne'
  have hg3 : Nat.gcd y z ≠ 0 := (Nat.gcd_pos_of_pos_left _ hy).ne'
  refine (Nat.factorization_prime_le_iff_dvd hg1 (Nat.lcm_ne_zero hg2 hg3)).1 fun p _ => ?_
  rw [Nat.factorization_gcd hl hz.ne', Nat.factorization_lcm hg2 hg3,
    Nat.factorization_lcm hx.ne' hy.ne', Nat.factorization_gcd hx.ne' hz.ne',
    Nat.factorization_gcd hy.ne' hz.ne']
  simp only [Finsupp.inf_apply, Finsupp.sup_apply]
  omega

private theorem modEq_lcm_of_modEq {x y u v : ℕ} (h₁ : x ≡ y [MOD u]) (h₂ : x ≡ y [MOD v]) :
    x ≡ y [MOD Nat.lcm u v] := by
  rw [Nat.modEq_iff_dvd] at *
  rw [Int.natCast_dvd] at *
  exact Nat.lcm_dvd h₁ h₂

private theorem modEq_gcd_finset_lcm {ι : Type*} (n : ι → ℕ) (m y z : ℕ)
    (T : Finset ι) (h : ∀ i ∈ T, y ≡ z [MOD Nat.gcd (n i) m]) :
    y ≡ z [MOD Nat.gcd (T.lcm n) m] := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [Nat.modEq_one]
  | insert i T _ ih =>
      rw [Finset.lcm_insert]
      have h1 := h i (Finset.mem_insert_self _ _)
      have h2 := ih fun k hk => h k (Finset.mem_insert_of_mem hk)
      exact (modEq_lcm_of_modEq h1 h2).of_dvd (gcd_lcm_dvd _ _ _)

/-- The general Chinese remainder theorem: pairwise compatible congruences have a common
solution. -/
theorem exists_modEq_of_pairwise {ι : Type*} (S : Finset ι) (n x : ι → ℕ)
    (h : ∀ i ∈ S, ∀ j ∈ S, x i ≡ x j [MOD Nat.gcd (n i) (n j)]) :
    ∃ y, ∀ i ∈ S, y ≡ x i [MOD n i] := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert j₀ S _ ih =>
      obtain ⟨y, hy⟩ := ih fun i hi j hj =>
        h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
      have key : y ≡ x j₀ [MOD Nat.gcd (S.lcm n) (n j₀)] := by
        refine modEq_gcd_finset_lcm n (n j₀) y (x j₀) S fun i hi => ?_
        exact ((hy i hi).of_dvd (Nat.gcd_dvd_left _ _)).trans
          (h i (Finset.mem_insert_of_mem hi) j₀ (Finset.mem_insert_self _ _))
      obtain ⟨z, hz₁, hz₂⟩ := Nat.chineseRemainder' key
      refine ⟨z, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · exact hz₂
      · exact (hz₁.of_dvd (Finset.dvd_lcm hi')).trans (hy i hi')

private theorem pow_eq_pow_iff_modEq_of_isPrimitiveRoot {ζ : ℂ} {M : ℕ}
    (h : IsPrimitiveRoot ζ M) (hM : 0 < M) {x y : ℕ} : ζ ^ x = ζ ^ y ↔ x ≡ y [MOD M] := by
  have hmod : ∀ u : ℕ, ζ ^ (u % M) = ζ ^ u := fun u => by
    conv_rhs => rw [← Nat.div_add_mod u M, pow_add, pow_mul, h.pow_eq_one, one_pow, one_mul]
  constructor
  · intro hxy
    exact h.pow_inj (Nat.mod_lt _ hM) (Nat.mod_lt _ hM) (by rw [hmod, hmod, hxy])
  · intro hxy
    rw [← hmod x, ← hmod y, hxy]

/-- Numbers `ρ_j` whose powers agree pairwise at the least common multiples of the exponents `m_j`
have one `λ ≠ 0` with `λ ^ m_j = ρ_j ^ m_j` for every `j`. -/
theorem exists_pow_eq_pow_of_pairwise {g : ℕ} (per : Fin g → ℕ) (hper : ∀ j, 0 < per j)
    (ρ : Fin g → ℂ) (hρ : ∀ j, ρ j ≠ 0)
    (h : ∀ i j, ρ i ^ Nat.lcm (per i) (per j) = ρ j ^ Nat.lcm (per i) (per j)) :
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ j, lam ^ per j = ρ j ^ per j := by
  classical
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · exact ⟨1, one_ne_zero, fun j => j.elim0⟩
  let j₀ : Fin g := ⟨0, hg⟩
  set M : ℕ := ∏ j, per j with hMdef
  have hM : 0 < M := Finset.prod_pos fun j _ => hper j
  have hdM : ∀ j, per j ∣ M := fun j => Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  have : NeZero M := ⟨hM.ne'⟩
  have hζ := Complex.isPrimitiveRoot_exp M hM.ne'
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / M) with hζdef
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hM.ne'
  have hroot : ∀ i j, (ρ i / ρ j) ^ Nat.lcm (per i) (per j) = 1 := fun i j => by
    rw [div_pow, h i j, div_self (pow_ne_zero _ (hρ j))]
  have hex : ∀ j, ∃ x, ζ ^ x = ρ j / ρ j₀ := fun j => by
    have hL : Nat.lcm (per j) (per j₀) ∣ M := Nat.lcm_dvd (hdM j) (hdM j₀)
    obtain ⟨c, hc⟩ := hL
    have h1 : (ρ j / ρ j₀) ^ M = 1 := by rw [hc, pow_mul, hroot, one_pow]
    obtain ⟨x, -, hx⟩ := hζ.eq_pow_of_pow_eq_one h1
    exact ⟨x, hx⟩
  choose x hx using hex
  have hcompat : ∀ i ∈ (Finset.univ : Finset (Fin g)), ∀ j ∈ (Finset.univ : Finset (Fin g)),
      x i ≡ x j [MOD Nat.gcd (M / per i) (M / per j)] := by
    intro i _ j _
    set L := Nat.lcm (per i) (per j) with hLdef
    have hLpos : 0 < L := Nat.lcm_pos (hper i) (hper j)
    set c := Nat.gcd (M / per i) (M / per j) with hcdef
    have h1 : per i * c ∣ M := Nat.mul_dvd_of_dvd_div (hdM i) (Nat.gcd_dvd_left _ _)
    have h2 : per j * c ∣ M := Nat.mul_dvd_of_dvd_div (hdM j) (Nat.gcd_dvd_right _ _)
    have h3 : c * L ∣ M := by
      rw [mul_comm c L, hLdef, ← Nat.lcm_mul_right]
      exact Nat.lcm_dvd h1 h2
    have hquot : ζ ^ (x i * L) = ζ ^ (x j * L) := by
      rw [pow_mul, pow_mul, hx, hx, div_pow, div_pow, h i j]
    have hmod := (pow_eq_pow_iff_modEq_of_isPrimitiveRoot hζ hM).1 hquot
    exact Nat.ModEq.mul_right_cancel' hLpos.ne' (hmod.of_dvd h3)
  obtain ⟨y, hy⟩ := exists_modEq_of_pairwise Finset.univ (fun j => M / per j) x hcompat
  refine ⟨ρ j₀ * ζ ^ y, mul_ne_zero (hρ j₀) (pow_ne_zero _ hζ0), fun j => ?_⟩
  have h1 : ρ j = ρ j₀ * ζ ^ x j := by
    rw [hx, mul_div_cancel₀ _ (hρ j₀)]
  have h2 : y * per j ≡ x j * per j [MOD M] := by
    have := (hy j (Finset.mem_univ j)).mul_right' (per j)
    rwa [Nat.div_mul_cancel (hdM j)] at this
  have h3 := (pow_eq_pow_iff_modEq_of_isPrimitiveRoot hζ hM).2 h2
  rw [mul_pow, h1, mul_pow, ← pow_mul, ← pow_mul, h3]

/-- **A single constant for dependent states.** If every class occurs once in each tensor and the
states are dependent at all large lengths, there is one `λ ≠ 0` with `V_N(A) = λ ^ N V_N(B)` for
every `N ≥ 1`. -/
theorem exists_pow_of_card_classWeights_eq_one
    (hR : ∀ j, IsPeriodic (per j) (R j))
    (hnr : ∀ i j, i ≠ j → ∀ hdim : dim i = dim j,
      ¬ RepeatedBlocks (cast (congr_arg (MPSTensor d) hdim) (R i)) (R j))
    (ha : HasClassWeights R A a) (hb : HasClassWeights R B b)
    (ha1 : ∀ j, Multiset.card (a j) = 1) (hb1 : ∀ j, Multiset.card (b j) = 1)
    (h : ∀ᶠ N in atTop, StatesDependentAt A B N) :
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ N, 0 < N → ∀ σ : Fin N → Fin d, mpv A σ = lam ^ N * mpv B σ := by
  choose α hα using fun j => Multiset.card_eq_one.mp (ha1 j)
  choose β hβ using fun j => Multiset.card_eq_one.mp (hb1 j)
  have hα0 : ∀ j, α j ≠ 0 := fun j h0 => ha.1 j (by rw [hα, h0]; simp)
  have hβ0 : ∀ j, β j ≠ 0 := fun j h0 => hb.1 j (by rw [hβ, h0]; simp)
  have hrel := (eventually_statesDependentAt_iff_classWeights hR hnr ha hb).1 h
  have hpair : ∀ i j, (α i / β i) ^ Nat.lcm (per i) (per j) =
      (α j / β j) ^ Nat.lcm (per i) (per j) := by
    intro i j
    have h1 := hrel i j
    simp only [hα, hβ, Multiset.map_singleton, weightProduct_singleton_left,
      Multiset.singleton_inj] at h1
    rw [div_pow, div_pow, div_eq_div_iff (pow_ne_zero _ (hβ0 i)) (pow_ne_zero _ (hβ0 j))]
    linear_combination h1
  obtain ⟨lam, hlam, hpow⟩ := exists_pow_eq_pow_of_pairwise per (fun j => (hR j).period_pos)
    (fun j => α j / β j) (fun j => div_ne_zero (hα0 j) (hβ0 j)) hpair
  refine ⟨lam, hlam, fun N hN σ => ?_⟩
  rw [ha.2 N hN σ, hb.2 N hN σ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [hα, hβ, Multiset.map_singleton, Multiset.sum_singleton]
  by_cases hd : per j ∣ N
  · obtain ⟨k, rfl⟩ := hd
    have h1 : lam ^ (per j * k) = (α j / β j) ^ (per j * k) := by
      rw [pow_mul, hpow, ← pow_mul]
    rw [h1, div_pow, ← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero _ (hβ0 j))]
  · rw [pgvwc07_stateVector_eq_zero_of_not_dvd (R j) (hR j) hd σ]
    simp

end

end MPSTensor
