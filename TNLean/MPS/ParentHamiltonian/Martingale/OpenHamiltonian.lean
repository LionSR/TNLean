/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.Transport
import TNLean.MPS.ParentHamiltonian.UniqueGroundState

/-!
# The nonwrapping open-chain parent Hamiltonian

For a chain of length `N`, this file sums the canonical local parent interactions
only over starts whose length-`L` windows stay inside the linear interval.  Thus
no local term crosses the cut between the last and first sites.

When the tensor has virtual dimension \(D \ge 1\) and is block-injective at
length \(L₀\), with \(0 < L₀\) and \(L₀ + 1 \le N\), the kernel of the
length-\(L₀ + 1\) open Hamiltonian is the open MPS boundary-condition space
`groundSpaceES A N`. This is the finite-volume ground-space input for
Nachtergaele's C1--C3 martingale theorem.

## References

* Nachtergaele, arXiv:cond-mat/9410110, equations (3.12)--(3.16).
* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:2011.12127, Section IV.C.

**Transitional (#10948).** The declarations of the last section compare the open-chain parent
Hamiltonian with the Euclidean-space local terms `localTermES` and `parentInteractionES`; they
are kept for the files that still use those operators and are deleted with their last users.
-/

open scoped BigOperators ComplexOrder

/-- Two sums over initial segments of the natural numbers agree when the summands agree at the
common positions and vanish at the positions beyond the other segment. -/
theorem Fin.sum_eq_sum_of_val_eq {M : Type*} [AddCommMonoid M] {a b : ℕ} (f : Fin a → M)
    (g : Fin b → M) (hfg : ∀ (k : ℕ) (ha : k < a) (hb : k < b), f ⟨k, ha⟩ = g ⟨k, hb⟩)
    (hf : ∀ i : Fin a, b ≤ i.val → f i = 0) (hg : ∀ i : Fin b, a ≤ i.val → g i = 0) :
    ∑ i, f i = ∑ i, g i := by
  have key (c : ℕ) (u : Fin c → M) :
      ∑ i, u i = ∑ k ∈ Finset.range c, if h : k < c then u ⟨k, h⟩ else 0 := by
    rw [Finset.sum_range]
    exact Fintype.sum_congr _ _ fun i ↦ by rw [dite_eq_left i.isLt]
  have hsub (c e : ℕ) (u : Fin c → M) (hu : ∀ i : Fin c, e ≤ i.val → u i = 0) :
      ∑ k ∈ Finset.range c, (if h : k < c then u ⟨k, h⟩ else 0) =
        ∑ k ∈ Finset.range (min c e), if h : k < c then u ⟨k, h⟩ else 0 := by
    refine (Finset.sum_subset (fun k hk ↦ ?_) fun k hk hk' ↦ ?_).symm
    · rw [Finset.mem_range] at hk ⊢
      omega
    · rw [Finset.mem_range] at hk hk'
      rw [dite_eq_left hk]
      exact hu _ (by simp only; omega)
  rw [key, key, hsub a b f hf, hsub b a g hg, min_comm b a]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Finset.mem_range] at hk
  rw [dite_eq_left (by omega), dite_eq_left (by omega)]
  exact hfg k _ _

namespace ManyBody.Interaction

open scoped MatrixOrder Matrix

section Restrict

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {ι : Type*} [Fintype ι] {S : ι → Finset V} {Φ : Interaction X S}

/-- For positive semidefinite terms, the Hamiltonian of the restriction of an interaction to the
indices with a property annihilates a vector exactly when every term with the property does. -/
theorem mem_ker_toEuclideanLin_hamiltonian_restrict_iff (hΦ : ∀ i, (Φ.term i).PosSemidef)
    (p : ι → Prop) [DecidablePred p] {v : EuclideanSpace ℂ (Config X)} :
    v ∈ LinearMap.ker (Matrix.toEuclideanLin (Φ.restrict p).hamiltonian) ↔
      ∀ i, p i → Matrix.toEuclideanLin (Φ.term i) v = 0 := by
  rw [LinearMap.mem_ker, Matrix.toLpLin_apply, WithLp.toLp_eq_zero,
    hamiltonian_mulVec_eq_zero_iff fun i ↦ forall_restrict_term Matrix.PosSemidef.zero (hΦ i)]
  refine forall_congr' fun i ↦ ?_
  by_cases hi : p i
  · simp [hi, Matrix.toLpLin_apply]
  · simp [hi]

/-- For positive semidefinite terms, the Hamiltonian of an interaction annihilates a vector
exactly when the operator of every term does. -/
theorem mem_ker_toEuclideanLin_hamiltonian_iff (hΦ : ∀ i, (Φ.term i).PosSemidef)
    {v : EuclideanSpace ℂ (Config X)} :
    v ∈ LinearMap.ker (Matrix.toEuclideanLin Φ.hamiltonian) ↔
      ∀ i, Matrix.toEuclideanLin (Φ.term i) v = 0 := by
  simp only [LinearMap.mem_ker, Matrix.toLpLin_apply, WithLp.toLp_eq_zero,
    hamiltonian_mulVec_eq_zero_iff hΦ]

/-- The Hamiltonians of two restrictions of an interaction commute when every term of the first
commutes with every term of the second. -/
theorem commute_hamiltonian_restrict (p q : ι → Prop) [DecidablePred p] [DecidablePred q]
    (h : ∀ i j, p i → q j → Commute (Φ.term i) (Φ.term j)) :
    Commute (Φ.restrict p).hamiltonian (Φ.restrict q).hamiltonian :=
  Commute.sum_left _ _ _ fun i _ ↦ Commute.sum_right _ _ _ fun j _ ↦ by
    by_cases hi : p i
    · by_cases hj : q j
      · simpa [hi, hj] using h i j hi hj
      · simp [hj]
    · simp [hi]

/-- For nonnegative terms, the Hamiltonian of a restriction of an interaction is below the
Hamiltonian. -/
theorem hamiltonian_restrict_le (hΦ : ∀ i, 0 ≤ Φ.term i) (p : ι → Prop) [DecidablePred p] :
    (Φ.restrict p).hamiltonian ≤ Φ.hamiltonian :=
  Finset.sum_le_sum fun i _ ↦ by
    rw [restrict_term]
    split_ifs
    exacts [le_rfl, hΦ i]

/-- Summing the Hamiltonians of a family of restrictions of an interaction gives the Hamiltonian
of one restriction when every index of the latter lies in exactly one member of the family and
no other index lies in any. -/
theorem sum_hamiltonian_restrict_eq_hamiltonian_restrict {κ : Type*} (s : Finset κ)
    (P : κ → ι → Prop) [∀ n, DecidablePred (P n)] (Q : ι → Prop) [DecidablePred Q] (g : ι → κ)
    (hg : ∀ i, Q i → g i ∈ s) (h : ∀ i, ∀ n ∈ s, P n i ↔ Q i ∧ n = g i) :
    ∑ n ∈ s, (Φ.restrict (P n)).hamiltonian = (Φ.restrict Q).hamiltonian := by
  simp only [hamiltonian, restrict_term]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases hQ : Q i
  · rw [ite_eq_left hQ, Finset.sum_eq_single_of_mem (g i) (hg i hQ) fun n hn hne ↦
      ite_eq_right fun hP ↦ hne ((h i n hn).mp hP).2]
    exact ite_eq_left ((h i _ (hg i hQ)).mpr ⟨hQ, rfl⟩)
  · rw [ite_eq_right hQ]
    exact Finset.sum_eq_zero fun n hn ↦ ite_eq_right fun hP ↦ hQ ((h i n hn).mp hP).1

/-- For nonnegative terms, the Hamiltonians of two restrictions of an interaction to disjoint
sets of indices add up to at most the Hamiltonian. -/
theorem hamiltonian_restrict_add_hamiltonian_restrict_le (hΦ : ∀ i, 0 ≤ Φ.term i)
    (p q : ι → Prop) [DecidablePred p] [DecidablePred q] (hpq : ∀ i, p i → ¬q i) :
    (Φ.restrict p).hamiltonian + (Φ.restrict q).hamiltonian ≤ Φ.hamiltonian := by
  simp only [hamiltonian, restrict_term]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  by_cases hp : p i
  · rw [ite_eq_left hp, ite_eq_right (hpq i hp), add_zero]
  · rw [ite_eq_right hp, zero_add]
    split_ifs
    exacts [le_rfl, hΦ i]

end Restrict

/-- **The counting bound of condition C1.** On the open chain, each window of `R` sites lies in
at most `W - R + 1` of the intervals `[n - W, n)`, `W ≤ n ≤ N`; summing the Hamiltonians of the
restrictions of the translates of a positive semidefinite matrix to the windows inside these
intervals gives at most `W - R + 1` times the Hamiltonian. Nachtergaele, arXiv:cond-mat/9410110,
condition C1, lines 1030--1041. -/
theorem sum_hamiltonian_restrict_chainTranslates_le {α : Type*} [Fintype α] [DecidableEq α]
    {R W : ℕ} (hRW : R ≤ W) {h : Matrix (Fin R → α) (Fin R → α) ℂ} (hh : 0 ≤ h) (N : ℕ) :
    ∑ n ∈ Finset.Icc W N, ((chainTranslates R N h).restrict
        fun i ↦ n - W ≤ i.val ∧ i.val + R ≤ n).hamiltonian ≤
      ((W - R + 1 : ℕ) : ℂ) • (chainTranslates R N h).hamiltonian := by
  simp only [hamiltonian, restrict_term]
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [← Finset.sum_filter, Finset.sum_const, Nat.cast_smul_eq_nsmul]
  refine nsmul_le_nsmul_left (ofPlaceAlong_term_nonneg _ (fun _ ↦ hh) i) ?_
  calc _ ≤ (Finset.Icc (i.val + R) (i.val + W)).card :=
        Finset.card_le_card fun n hn ↦ by
          simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
          omega
    _ = W - R + 1 := by
        rw [Nat.card_Icc]
        omega

end ManyBody.Interaction

namespace MPSTensor

variable {d D : ℕ}

/-- A start site whose length-`L` window does not cross the right endpoint of an
`N`-site open chain.

This is the index set in Nachtergaele, arXiv:cond-mat/9410110, equation (3.12). -/
abbrev NonwrappingStart (L N : ℕ) :=
  {i : Fin N // i.val + L ≤ N}

/-! ### Dimension of the open-boundary ground space -/

/-- The canonical \(\ell^2\) realization of the local ground space has dimension
\(D^2\) under block injectivity at length \(L\). -/
theorem groundSpaceES_finrank_eq_of_isNBlkInjective {A : MPSTensor d D} {L : ℕ}
    (hInj : Kraus.IsNBlkInjective A L) :
    Module.finrank ℂ (groundSpaceES A L) = D ^ 2 := by
  rw [groundSpaceES, LinearEquiv.finrank_map_eq]
  exact groundSpace_finrank_eq_of_isNBlkInjective hInj

/-! ### The open-chain parent Hamiltonian as the Hamiltonian of `parentChainInteraction`

The same facts for the Hamiltonian of the parent interaction on the open chain
(`parentChainInteraction`), the matrix of the open-chain parent Hamiltonian; statements about
vectors take its operator `Matrix.toEuclideanLin`. -/

section ChainInteraction

open scoped Matrix MatrixOrder

private theorem contiguousCfg_chainWindow {L N a : ℕ} (h : a + L ≤ N) (ω : Cfg d L)
    (σ : Cfg d N) (u : Fin L) : contiguousCfg a L ω σ (ManyBody.chainWindow a h u) = ω u := by
  unfold contiguousCfg
  rw [dite_eq_left (show a ≤ (ManyBody.chainWindow a h u).val ∧
    (ManyBody.chainWindow a h u).val < a + L by simp)]
  exact congrArg ω (Fin.ext (by simp))

private theorem contiguousCfg_of_forall_chainWindow_ne {L N a : ℕ} (h : a + L ≤ N)
    (ω : Cfg d L) (σ : Cfg d N) {v : Fin N} (hv : ∀ u, ManyBody.chainWindow a h u ≠ v) :
    contiguousCfg a L ω σ v = σ v := by
  unfold contiguousCfg
  rw [dite_eq_right]
  rintro ⟨h₁, h₂⟩
  exact hv ⟨v.val - a, by omega⟩ (Fin.ext (by simp only [ManyBody.val_chainWindow]; omega))

private theorem contiguousCfg_contiguousCfg {L N a : ℕ} (ω ω' : Cfg d L) (τ : Cfg d N) :
    contiguousCfg a L ω' (contiguousCfg a L ω τ) = contiguousCfg a L ω' τ := by
  funext k
  unfold contiguousCfg
  split_ifs <;> rfl

/-- A matrix placed on the window of `L` sites starting at `a` acts at a configuration `σ` as
the matrix on the restriction of the vector to that window, the other sites fixed by `σ`, read
at the window of `σ`. -/
theorem placeAlong_chainWindow_mulVec_apply {L N a : ℕ} (h : a + L ≤ N)
    (K : Matrix (Cfg d L) (Cfg d L) ℂ) (ψ : Cfg d N → ℂ) (σ : Cfg d N) :
    (ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.chainWindow a h) K *ᵥ ψ) σ =
      (K *ᵥ contiguousRestrictₗ a L h σ ψ) (fun u ↦ σ (ManyBody.chainWindow a h u)) := by
  rw [ManyBody.placeAlong_mulVec_apply_of _ _ ψ σ (fun ω ↦ contiguousCfg a L ω σ)
    (contiguousCfg_chainWindow h · σ)
    (fun ω _ hv ↦ contiguousCfg_of_forall_chainWindow_ne h ω σ hv)]
  rfl

private theorem toMatrix'_parentInteraction_mulVec_eq_zero_iff (A : MPSTensor d D) {L : ℕ}
    (f : Cfg d L → ℂ) :
    LinearMap.toMatrix' (parentInteraction A L) *ᵥ f = 0 ↔ f ∈ groundSpace A L := by
  have hf : f ∈ groundSpace A L ↔ WithLp.toLp 2 f ∈ groundSpaceES A L :=
    (mem_groundSpaceES_iff A L _).symm
  rw [hf, ← toEuclideanLin_toMatrix'_parentInteraction_apply_eq_zero_iff, Matrix.toLpLin_apply,
    WithLp.ofLp_toLp, WithLp.toLp_eq_zero]

/-- **Kernel of a term.** The term of the parent interaction on the open chain at the start `i`
annihilates a vector exactly when every restriction of the vector to the window of the term,
the other sites fixed, lies in the local ground space \(G_L(A)\). Nachtergaele,
arXiv:cond-mat/9410110, equation (3.12). -/
theorem parentChainInteraction_term_mulVec_eq_zero_iff (A : MPSTensor d D) {L N : ℕ}
    (i : Fin (N + 1 - L)) (ψ : Cfg d N → ℂ) :
    (parentChainInteraction A L N).term i *ᵥ ψ = 0 ↔
      ∀ τ : Cfg d N, contiguousRestrictₗ i.val L (by omega) τ ψ ∈ groundSpace A L := by
  have hi : i.val + L ≤ N := by omega
  rw [ManyBody.Interaction.ofPlaceAlong_term]
  constructor
  · intro hψ τ
    rw [← toMatrix'_parentInteraction_mulVec_eq_zero_iff]
    funext ω
    have h := congrFun hψ (contiguousCfg i.val L ω τ)
    rw [placeAlong_chainWindow_mulVec_apply hi] at h
    have hr : contiguousRestrictₗ i.val L hi (contiguousCfg i.val L ω τ) ψ =
        contiguousRestrictₗ i.val L hi τ ψ := by
      funext ω'
      exact congrArg ψ (contiguousCfg_contiguousCfg ω ω' τ)
    have hw : (fun u ↦ contiguousCfg i.val L ω τ (ManyBody.chainWindow i.val hi u)) = ω :=
      funext (contiguousCfg_chainWindow hi ω τ)
    rw [hr, hw] at h
    exact h
  · intro hψ
    funext σ
    rw [placeAlong_chainWindow_mulVec_apply hi,
      (toMatrix'_parentInteraction_mulVec_eq_zero_iff A _).mpr (hψ σ)]
    rfl

/-- Every term of the parent interaction on the open chain is positive semidefinite. -/
theorem posSemidef_parentChainInteraction_term (A : MPSTensor d D) (L N : ℕ)
    (i : Fin (N + 1 - L)) : ((parentChainInteraction A L N).term i).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (ManyBody.Interaction.ofPlaceAlong_term_nonneg _
    (fun _ ↦ Matrix.nonneg_iff_posSemidef.mpr (posSemidef_toMatrix'_parentInteraction A L)) i)

/-- Every term of the parent interaction on the open chain is an orthogonal projection. -/
theorem isStarProjection_parentChainInteraction_term (A : MPSTensor d D) (L N : ℕ)
    (i : Fin (N + 1 - L)) : IsStarProjection ((parentChainInteraction A L N).term i) := by
  have hP := isStarProjection_toMatrix'_parentInteraction A L
  rw [ManyBody.Interaction.ofPlaceAlong_term]
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, ← ManyBody.placeAlong_mul, hP.isIdempotentElem.eq]
  · rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, ← ManyBody.placeAlong_conjTranspose,
      ← Matrix.star_eq_conjTranspose, hP.isSelfAdjoint.star_eq]

/-- Two terms of the parent interaction on the open chain whose windows are ordered and do not
meet commute. -/
theorem commute_parentChainInteraction_term_of_add_le (A : MPSTensor d D) {L N : ℕ}
    {i j : Fin (N + 1 - L)} (hij : i.val + L ≤ j.val) :
    Commute ((parentChainInteraction A L N).term i) ((parentChainInteraction A L N).term j) := by
  refine ManyBody.commute_placeAlong_of_disjoint (X := fun _ ↦ Fin d) _
    (Finset.disjoint_left.mpr fun k hki hkj ↦ ?_) _ _
  rw [ManyBody.map_chainWindow, ManyBody.mem_interval] at hki hkj
  omega

/-- The Hamiltonian of a restriction of the parent interaction on the open chain to a set of
windows is positive semidefinite. -/
theorem posSemidef_hamiltonian_restrict_parentChainInteraction (A : MPSTensor d D) (L N : ℕ)
    (p : Fin (N + 1 - L) → Prop) [DecidablePred p] :
    ((parentChainInteraction A L N).restrict p).hamiltonian.PosSemidef :=
  ManyBody.Interaction.posSemidef_hamiltonian fun i ↦
    ManyBody.Interaction.forall_restrict_term Matrix.PosSemidef.zero
      (posSemidef_parentChainInteraction_term A L N i)

/-- The Hamiltonian of the parent interaction on the open chain is positive semidefinite. -/
theorem posSemidef_hamiltonian_parentChainInteraction (A : MPSTensor d D) (L N : ℕ) :
    (parentChainInteraction A L N).hamiltonian.PosSemidef :=
  ManyBody.Interaction.posSemidef_hamiltonian (posSemidef_parentChainInteraction_term A L N)

/-- **Frustration-free extraction.** A vector annihilated by the Hamiltonian of the parent
interaction on the open chain has every restriction to a window of `L` sites in the local
ground space. Nachtergaele, arXiv:cond-mat/9410110, equation (3.12). -/
theorem contiguousRestrictₗ_mem_groundSpace_of_mem_ker_hamiltonian_parentChainInteraction
    (A : MPSTensor d D) {L N : ℕ} {v : EuclideanSpace ℂ (Cfg d N)}
    (hv : v ∈ LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A L N).hamiltonian))
    (s : ℕ) (hs : s + L ≤ N) (τ : Cfg d N) :
    contiguousRestrictₗ s L hs τ (WithLp.ofLp v) ∈ groundSpace A L := by
  have hH : (parentChainInteraction A L N).hamiltonian *ᵥ WithLp.ofLp v = 0 := by
    rw [LinearMap.mem_ker, Matrix.toLpLin_apply, WithLp.toLp_eq_zero] at hv
    exact hv
  have hterm := (ManyBody.Interaction.hamiltonian_mulVec_eq_zero_iff
    (posSemidef_parentChainInteraction_term A L N)).mp hH ⟨s, by omega⟩
  exact (parentChainInteraction_term_mulVec_eq_zero_iff A ⟨s, by omega⟩ _).mp hterm τ

/-- The cyclic form of the frustration-free extraction: for a window that does not cross the
right endpoint, the cyclic restriction is the contiguous one. -/
theorem cyclicRestrictₗ_mem_groundSpace_of_mem_ker_hamiltonian_parentChainInteraction
    (A : MPSTensor d D) {L N : ℕ} (hLN : L ≤ N) {v : EuclideanSpace ℂ (Cfg d N)}
    (hv : v ∈ LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A L N).hamiltonian))
    (i : Fin N) (hi : i.val + L ≤ N) (τ : Fin N → Fin d) :
    cyclicRestrictₗ (Fin.pos i) L i τ (WithLp.linearEquiv 2 ℂ (NSiteSpace d N) v) ∈
      groundSpace A L := by
  rw [cyclicRestrictₗ_eq_contiguousRestrictₗ (Fin.pos i) hLN hi]
  exact contiguousRestrictₗ_mem_groundSpace_of_mem_ker_hamiltonian_parentChainInteraction A hv
    i.val hi τ

/-- The open MPS boundary-condition space lies in the kernel of the Hamiltonian of the parent
interaction on the open chain: every window restriction of an open-boundary MPS vector is an
open-boundary MPS vector. Nachtergaele, arXiv:cond-mat/9410110, equation (3.12). -/
theorem groundSpaceES_le_ker_hamiltonian_parentChainInteraction (A : MPSTensor d D)
    (L N : ℕ) :
    groundSpaceES A N ≤
      LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A L N).hamiltonian) := by
  intro v hv
  rw [mem_groundSpaceES_iff, groundSpace, LinearMap.mem_range] at hv
  obtain ⟨X, hX⟩ := hv
  rw [LinearMap.mem_ker, Matrix.toLpLin_apply, WithLp.toLp_eq_zero,
    ManyBody.Interaction.hamiltonian, Matrix.sum_mulVec]
  refine Finset.sum_eq_zero fun i _ ↦ (parentChainInteraction_term_mulVec_eq_zero_iff A i _).mpr
    fun τ ↦ ?_
  have := contiguousRestrictₗ_groundSpaceMap_mem_groundSpace (A := A)
    (show i.val + L ≤ N by omega) τ X
  rwa [hX] at this

/-- Under block injectivity at length \(L_0 > 0\), the kernel of the Hamiltonian of the
length-\((L_0+1)\) parent interaction on the open chain lies in the open MPS boundary-condition
space. Nachtergaele, arXiv:cond-mat/9410110, equations (3.12)--(3.16). -/
theorem ker_hamiltonian_parentChainInteraction_le_groundSpaceES_of_isNBlkInjective
    {A : MPSTensor d D} [NeZero D] {L₀ N : ℕ}
    (hInj : Kraus.IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hL₀N : L₀ + 1 ≤ N) :
    LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A (L₀ + 1) N).hamiltonian) ≤
      groundSpaceES A N := by
  intro v hv
  rw [mem_groundSpaceES_iff]
  exact contiguous_mem_groundSpace_of_isNBlkInjective hInj hL₀ hL₀N fun s hs τ ↦
    contiguousRestrictₗ_mem_groundSpace_of_mem_ker_hamiltonian_parentChainInteraction A hv s hs τ

/-- For a block-injective tensor, the kernel of the Hamiltonian of the parent interaction on the
open chain is exactly the open MPS boundary-condition space. Nachtergaele,
arXiv:cond-mat/9410110, equations (3.12)--(3.16). -/
theorem ker_hamiltonian_parentChainInteraction_eq_groundSpaceES_of_isNBlkInjective
    {A : MPSTensor d D} [NeZero D] {L₀ N : ℕ}
    (hInj : Kraus.IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hL₀N : L₀ + 1 ≤ N) :
    LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A (L₀ + 1) N).hamiltonian) =
      groundSpaceES A N :=
  le_antisymm (ker_hamiltonian_parentChainInteraction_le_groundSpaceES_of_isNBlkInjective
    hInj hL₀ hL₀N) (groundSpaceES_le_ker_hamiltonian_parentChainInteraction A (L₀ + 1) N)

/-- Project result: **boundary degeneracy of the open-chain parent Hamiltonian.** For a tensor
block-injective at length \(L_0 > 0\), the kernel of the Hamiltonian of the length-\((L_0+1)\)
parent interaction on \(N \ge L_0 + 1\) sites has dimension exactly \(D^2\). Sources: Nachtergaele,
arXiv:cond-mat/9410110, lines 1484--1486, 1505--1510, 1545--1558; Pérez-García--Verstraete--
Wolf--Cirac, arXiv:quant-ph/0608197, lines 1211--1233; arXiv:2011.12127, line 1174 (a lower
bound; the theorem is sharper than the review's statement). -/
theorem finrank_ker_hamiltonian_parentChainInteraction_of_isNBlkInjective
    {A : MPSTensor d D} [NeZero D] {L₀ N : ℕ}
    (hInj : Kraus.IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hL₀N : L₀ + 1 ≤ N) :
    Module.finrank ℂ (LinearMap.ker
      (Matrix.toEuclideanLin (parentChainInteraction A (L₀ + 1) N).hamiltonian)) = D ^ 2 := by
  rw [ker_hamiltonian_parentChainInteraction_eq_groundSpaceES_of_isNBlkInjective hInj hL₀ hL₀N]
  exact groundSpaceES_finrank_eq_of_isNBlkInjective (isNBlkInjective_of_le hL₀ hInj (by omega))

/-- At volume \(N = L\) the Hamiltonian of the parent interaction on the open chain is the local
parent interaction itself: the only window is the whole chain. -/
theorem hamiltonian_parentChainInteraction_self (A : MPSTensor d D) (L : ℕ) :
    (parentChainInteraction A L L).hamiltonian = LinearMap.toMatrix' (parentInteraction A L) := by
  rw [ManyBody.Interaction.hamiltonian_chainTranslates_eq_sum_range, Nat.add_sub_cancel_left,
    Finset.sum_range_one, dite_eq_left (by omega)]
  have hw : ManyBody.chainWindow (N := L) (k := L) 0 (by omega) = Function.Embedding.refl _ :=
    Function.Embedding.ext fun j ↦ Fin.ext (by simp)
  rw [hw, ManyBody.placeAlong_refl]

/-- At the first full-window volume the operator of the open-chain parent Hamiltonian preserves
the norm on the orthogonal complement of its kernel. -/
theorem norm_toEuclideanLin_hamiltonian_parentChainInteraction_self_of_mem_orthogonal_ker
    (A : MPSTensor d D) (L : ℕ) (v : EuclideanSpace ℂ (Cfg d L))
    (hv : v ∈ (LinearMap.ker
      (Matrix.toEuclideanLin (parentChainInteraction A L L).hamiltonian))ᗮ) :
    ‖Matrix.toEuclideanLin (parentChainInteraction A L L).hamiltonian v‖ = ‖v‖ := by
  rw [hamiltonian_parentChainInteraction_self, toEuclideanLin_toMatrix'_parentInteraction] at hv ⊢
  change ‖(groundSpaceES A L)ᗮ.starProjection v‖ = ‖v‖
  apply Submodule.norm_starProjection_apply
  have hker : LinearMap.ker ((groundSpaceES A L)ᗮ.starProjection.toLinearMap) =
      groundSpaceES A L := by
    ext w
    rw [LinearMap.mem_ker, ← toEuclideanLin_toMatrix'_parentInteraction,
      toEuclideanLin_toMatrix'_parentInteraction_apply_eq_zero_iff]
  rwa [hker] at hv

/-- The open-chain parent Hamiltonian has unit gap at the first full-window volume: every
eigenvalue is `0` or at least `1`. This is \(γ_{l+1} = 1\) in Nachtergaele,
arXiv:cond-mat/9410110, Theorem 2.1(i), for \(L = l + 1\).

**Scope restriction (single-window volume):** This proves only the volume \(N=L\). It does not
establish the general-volume C1--C3 martingale gap; see
`docs/paper-gaps/cpgsv21_martingale_overlap.tex`. -/
theorem unit_gap_hamiltonian_parentChainInteraction_self (A : MPSTensor d D) (L : ℕ) :
    ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction A L L).hamiltonian) μ →
        μ = 0 ∨ (1 : ℂ) ≤ μ := by
  have h := (ManyBody.forall_hasEigenvalue_iff_norm (Δ := 1)
    (posSemidef_hamiltonian_parentChainInteraction A L L)).mpr fun v hv ↦ by
      rw [one_mul,
        norm_toEuclideanLin_hamiltonian_parentChainInteraction_self_of_mem_orthogonal_ker A L v hv]
  simpa only [Complex.ofReal_one] using h

/-- **Condition C1.** For the prefixes \(\Lambda_n=[0,n)\) of the open chain, each term of the
range-\(L\) parent interaction lies in at most \(l-L+1\) of the intervals
\(\Lambda_n\setminus\Lambda_{n-l}\), \(l\le n\le N\); the Hamiltonian of such an interval is the
Hamiltonian of the interaction restricted to the windows inside it. Therefore
\[
0\leq\sum_{n=l}^N H_{\Lambda_n\setminus\Lambda_{n-l}}\leq (l-L+1)H_{\Lambda_N}.
\]
The source gives \(d_l=pl-r+1\) for \(\Lambda_n=[1,pn]\); here \(p=1\) and \(r=L\). Nachtergaele,
arXiv:cond-mat/9410110, condition C1, lines 1030--1041. -/
theorem parentChainInteraction_C1 (A : MPSTensor d D) {L l : ℕ} (hLl : L ≤ l) (N : ℕ) :
    0 ≤ ∑ n ∈ Finset.Icc l N, ((parentChainInteraction A L N).restrict
        fun i ↦ n - l ≤ i.val ∧ i.val + L ≤ n).hamiltonian ∧
      ∑ n ∈ Finset.Icc l N, ((parentChainInteraction A L N).restrict
        fun i ↦ n - l ≤ i.val ∧ i.val + L ≤ n).hamiltonian ≤
        ((l - L + 1 : ℕ) : ℂ) • (parentChainInteraction A L N).hamiltonian :=
  ⟨Finset.sum_nonneg fun _ _ ↦ Matrix.nonneg_iff_posSemidef.mpr
      (ManyBody.Interaction.posSemidef_hamiltonian fun i ↦
        ManyBody.Interaction.forall_restrict_term Matrix.PosSemidef.zero
          (posSemidef_parentChainInteraction_term A L N i)),
    ManyBody.Interaction.sum_hamiltonian_restrict_chainTranslates_le hLl
      (Matrix.nonneg_iff_posSemidef.mpr (posSemidef_toMatrix'_parentInteraction A L)) N⟩

/-! ### Transitional forms (#10948)

Comparison with the Euclidean-space local terms, for the files not yet restated. -/

/-- Each nonwrapping range-\(R\) term lies in at most \(W-R+1\) complete
length-\(W\) windows. Summing positive terms therefore gives the corresponding
operator bound. This is the counting argument for Nachtergaele,
arXiv:cond-mat/9410110, condition C1. -/
theorem sum_nonwrappingWindowTerms_le {R W N : ℕ} (hRW : R ≤ W)
    {ι : Type*} [Fintype ι]
    (f : NonwrappingStart R N → EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (hf : ∀ i, 0 ≤ f i) :
    (∑ n ∈ Finset.Icc W N,
      ∑ i ∈ Finset.univ.filter (fun i : NonwrappingStart R N =>
        n - W ≤ i.1.val ∧ i.1.val + R ≤ n), f i) ≤
      ((W - R + 1 : ℕ) : ℂ) • ∑ i, f i := by
  classical
  let windows := fun i : NonwrappingStart R N =>
    (Finset.Icc W N).filter fun n => n - W ≤ i.1.val ∧ i.1.val + R ≤ n
  have hwindows_card (i : NonwrappingStart R N) :
      (windows i).card ≤ W - R + 1 := by
    calc
      (windows i).card ≤ (Finset.Icc (i.1.val + R) (i.1.val + W)).card := by
        apply Finset.card_le_card
        intro n hn
        simp only [windows, Finset.mem_filter, Finset.mem_Icc] at hn
        simp only [Finset.mem_Icc]
        omega
      _ = W - R + 1 := by
        rw [Nat.card_Icc]
        omega
  rw [Finset.sum_comm'
    (s := Finset.Icc W N)
    (t := fun n => Finset.univ.filter fun i : NonwrappingStart R N =>
      n - W ≤ i.1.val ∧ i.1.val + R ≤ n)
    (t' := Finset.univ) (s' := windows) (fun n i => by simp [windows]),
    Finset.smul_sum]
  apply Finset.sum_le_sum
  intro i _
  simp only [Finset.sum_const, Nat.cast_smul_eq_nsmul]
  exact nsmul_le_nsmul_left (hf i) (hwindows_card i)

/-- At a start whose window does not cross the right endpoint, the Euclidean-space local term
is the operator of the term of the parent interaction on the open chain. -/
theorem localTermES_eq_toEuclideanLin_parentChainInteraction_term (A : MPSTensor d D)
    {L N : ℕ} (i : Fin N) (hi : i.val + L ≤ N) :
    localTermES A L i =
      Matrix.toEuclideanLin ((parentChainInteraction A L N).term ⟨i.val, by omega⟩) := by
  have hLN : L ≤ N := by omega
  have h₁ := localTermES_isSymmetricProjection A L i
  have h₂ := Matrix.isSymmetricProjection_toEuclideanLin_iff.mpr
    (isStarProjection_parentChainInteraction_term A L N ⟨i.val, by omega⟩)
  refine h₁.ext h₂ ?_
  rw [← Submodule.orthogonal_orthogonal (LinearMap.range (localTermES A L i)),
    h₁.isSymmetric.orthogonal_range, ← Submodule.orthogonal_orthogonal (LinearMap.range
      (Matrix.toEuclideanLin ((parentChainInteraction A L N).term ⟨i.val, by omega⟩))),
    h₂.isSymmetric.orthogonal_range]
  congr 1
  ext v
  rw [LinearMap.mem_ker, LinearMap.mem_ker,
    localTermES_eq_zero_iff_forall_cyclicRestrictES_mem_groundSpaceES A hLN i v,
    Matrix.toLpLin_apply, WithLp.toLp_eq_zero, parentChainInteraction_term_mulVec_eq_zero_iff]
  refine forall_congr' fun τ ↦ ?_
  rw [mem_groundSpaceES_iff, ← cyclicRestrictₗ_eq_contiguousRestrictₗ (Fin.pos i) hLN hi]
  rfl

/-- For a positive range, the operator of the open-chain parent Hamiltonian is the sum of the
Euclidean-space local terms over the starts whose windows do not cross the right endpoint. -/
theorem hamiltonian_parentChainInteraction_eq_sum_localTermES (A : MPSTensor d D) {L : ℕ}
    (hL : 0 < L)
    (N : ℕ) :
    Matrix.toEuclideanLin (parentChainInteraction A L N).hamiltonian = ∑ i : NonwrappingStart L N,
        localTermES A L i.1 := by
  classical
  rw [ManyBody.Interaction.hamiltonian, map_sum]
  trans ∑ i : Fin N, if i.val + L ≤ N then localTermES A L i else 0
  · refine Fin.sum_eq_sum_of_val_eq _ _ (fun k ha hb ↦ ?_)
      (fun i hi ↦ absurd i.isLt (by omega)) (fun i hi ↦ ite_eq_right (by omega))
    have hk : (⟨k, hb⟩ : Fin N).val + L ≤ N := by
      change k + L ≤ N
      omega
    simp only [hk, ↓reduceIte]
    exact (localTermES_eq_toEuclideanLin_parentChainInteraction_term A ⟨k, hb⟩ hk).symm
  · rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (fun i => by simp) _

/-- For a positive range, the operator of an interval Hamiltonian is the sum of the
Euclidean-space local terms over the starts whose windows lie in the interval. -/
theorem hamiltonian_restrict_parentChainInteraction_eq_sum_localTermES (A : MPSTensor d D) {L : ℕ}
    (hL : 0 < L) (l N n : ℕ) :
    Matrix.toEuclideanLin
        ((parentChainInteraction A L N).restrict fun i ↦ n - l ≤ i.val ∧ i.val + L ≤
            n).hamiltonian =
      ∑ i ∈ Finset.univ.filter fun i : NonwrappingStart L N =>
        n - l ≤ i.1.val ∧ i.1.val + L ≤ n, localTermES A L i.1 := by
  classical
  rw [ManyBody.Interaction.hamiltonian, map_sum]
  trans ∑ i : Fin N, if i.val + L ≤ N ∧ n - l ≤ i.val ∧ i.val + L ≤ n then localTermES A L i
    else 0
  · refine Fin.sum_eq_sum_of_val_eq _ _ (fun k ha hb ↦ ?_)
      (fun i hi ↦ absurd i.isLt (by omega)) (fun i hi ↦ ite_eq_right (by omega))
    have hk : (⟨k, hb⟩ : Fin N).val + L ≤ N := by
      change k + L ≤ N
      omega
    rw [ManyBody.Interaction.restrict_term]
    by_cases hq : n - l ≤ k ∧ k + L ≤ n
    · rw [ite_eq_left hq, ite_eq_left ⟨hk, hq⟩]
      exact (localTermES_eq_toEuclideanLin_parentChainInteraction_term A ⟨k, hb⟩ hk).symm
    · rw [ite_eq_right hq, ite_eq_right fun h ↦ hq h.2, map_zero]
  · rw [Finset.sum_filter, ← Finset.sum_subtype (Finset.univ.filter fun i : Fin N ↦ i.val + L ≤ N)
      (fun i ↦ by simp) (fun i ↦ if n - l ≤ i.val ∧ i.val + L ≤ n then localTermES A L i else 0),
      Finset.sum_filter]
    exact Finset.sum_congr rfl fun i _ ↦ by
      by_cases h1 : i.val + L ≤ N <;> by_cases h2 : n - l ≤ i.val ∧ i.val + L ≤ n <;> simp [h1, h2]

theorem hamiltonian_parentChainInteraction_self_eq_parentInteractionES (A : MPSTensor d D)
    {L : ℕ} (_hL : 0 < L) :
    Matrix.toEuclideanLin (parentChainInteraction A L L).hamiltonian = parentInteractionES A L := by
  rw [hamiltonian_parentChainInteraction_self,
    toEuclideanLin_toMatrix'_parentInteraction]
  rfl

theorem localTermES_eq_zero_of_hamiltonian_parentChainInteraction_eq_zero
    (A : MPSTensor d D) (L N : ℕ) {v : EuclideanSpace ℂ (Cfg d N)}
    (hv : Matrix.toEuclideanLin (parentChainInteraction A L N).hamiltonian v = 0)
        (i : NonwrappingStart L N) :
    localTermES A L i.1 v = 0 := by
  have hLN : L ≤ N := by have := i.2; omega
  rw [localTermES_eq_zero_iff_forall_cyclicRestrictES_mem_groundSpaceES A hLN i.1 v]
  intro τ
  rw [mem_groundSpaceES_iff]
  simpa [cyclicRestrictES] using
    cyclicRestrictₗ_mem_groundSpace_of_mem_ker_hamiltonian_parentChainInteraction A hLN
      (LinearMap.mem_ker.mpr hv) i.1 i.2 τ

end ChainInteraction

end MPSTensor
