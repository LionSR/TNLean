/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CharacterProjectorTwirl
import TNLean.MPS.ParentHamiltonian.UniqueGroundState
import TNLean.PEPS.GInjectiveMPSIntersection

/-!
# Parent Hamiltonians of G-injective matrix product states

**Source.** Schuch, Cirac, Pérez-García 2010 (arXiv:1001.3807), Section 4, "Parent
Hamiltonians", `Papers/1001.3807/paper_v3.tex`:

* Theorem 4.11 (`thm:noninj:parentham`), lines 1177–1195. For a `G`-injective tensor `A`, the
  parent Hamiltonian `H = ∑_i h_i` on a ring of `L` sites, with `h_i = 1 - Π_{𝒮_2}` acting on the
  sites `i` and `i + 1`, has a subspace of frustration-free ground states spanned by the MPS
  `|𝓜(A|U_g)⟩` with closure `U_g`. The proof is that of Theorem 3.5 (lines 758–817), run on
  Theorems 4.8 and 4.9 in place of Theorems 3.3 and 3.4.
* Theorem 4.12, lines 1197–1260. This ground space is spanned by the linearly independent states
  `|𝓜(A|Π_i)⟩`, where `Π_i` runs over the isotypic projectors of the irreducible representations
  occurring in `U_g`, so it is `I`-fold degenerate. If `U_g` is semi-regular, then `I` is the
  number of conjugacy classes, and the states `|𝓜(A|U_g)⟩`, one representative `g` per conjugacy
  class, are linearly independent and span the ground space.

**Formalized here.** The chain ground space `MPSTensor.chainGroundSpace A L N` of the injective
development is the common kernel of the parent interactions on the `N` cyclic windows of
length `L` of a ring of `N` sites, and the MPS with closure `K` is `MPSTensor.groundSpaceMap A N K`
(Definition 4.10, lines 1165–1176). `G`-injectivity is the predicate of
`TNLean.PEPS.GInjectiveMPS` for a representation `ρ` of `G` on the bond space, with `U_g` the
matrix of `ρ(g)`. The source's two-site interaction is the window length `L = 2`; the results
hold for every window length `2 ≤ L ≤ N`, and every ring of `N ≥ 2` sites carries the two-site
interaction. Unitarity of `U_g` is not used.

The proof of Theorem 4.11 follows the source. The open-chain step
`chainGroundSpace_le_groundSpace_of_isGInjective` iterates Theorem 4.8
(`IsGInjective.intersection_property`) along the chain, exactly as the proof of Theorem 3.5
iterates Theorem 3.3 (equation `eq:inj:S-L-as-intersect`, lines 776–797). The closing step
compares the open-boundary operators at two cuts of the ring and applies Theorem 4.9
(`IsGInjective.eq_sum_of_closure`) to the one-site tensor `A` and the blocked tensor of the
remaining `N - 1` sites (lines 800–817).

For Theorem 4.12 the source uses the completeness of the irreducible characters in the class
functions to pass from the `U_g` to the `Π_i`. Here the twirl formula
`σ(U_g) = ∑_χ (χ(g)/χ(1)) P_χ` (`Representation.averageMap_linHom_rep`) replaces it, and the
`I = #conjugacy classes` statement is obtained by computing the dimension of the ground space in
both ways, without the completeness of characters.

## Main results

* `MPSTensor.chainGroundSpace_le_groundSpace_of_isGInjective`: the chain ground space lies in
  the open-chain space `𝒮_N`.
* `MPSTensor.chainGroundSpace_eq_span_closure_of_isGInjective`: Theorem 4.11.
* `MPSTensor.chainGroundSpace_eq_span_charProjector_of_isGInjective`,
  `MPSTensor.linearIndependent_groundSpaceMap_charProjector_of_isGInjective`,
  `MPSTensor.finrank_chainGroundSpace_of_isGInjective`: Theorem 4.12, first part.
* `MPSTensor.chainGroundSpace_eq_span_conjClasses_of_isGInjective`,
  `MPSTensor.linearIndependent_groundSpaceMap_conjClasses_of_isSemiRegular`,
  `MPSTensor.finrank_chainGroundSpace_of_isSemiRegular`,
  `MPSTensor.card_irreducibleCharacterFinset_of_isSemiRegular`: Theorem 4.12, second part.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

universe u

open Module LinearMap Representation

namespace TNLean
namespace PEPS

variable {V ι : Type*} [AddCommGroup V] [Module ℂ V]

/-- Blocking `n + 1` sites with a first letter `i` multiplies the blocked tensor of the
remaining `n` sites on the left by `A^i`. -/
theorem wordTensor_cons (A : ι → Module.End ℂ V) {n : ℕ} (i : ι) (w : Fin n → ι) :
    wordTensor A (n + 1) (Fin.cons i w) = A i * wordTensor A n w := by
  simp [wordTensor, List.ofFn_succ]

/-- Blocking `n + 1` sites with a last letter `k` multiplies the blocked tensor of the first
`n` sites on the right by `A^k`. -/
theorem wordTensor_snoc (A : ι → Module.End ℂ V) {n : ℕ} (w : Fin n → ι) (k : ι) :
    wordTensor A (n + 1) (Fin.snoc w k) = wordTensor A n w * A k := by
  change (List.ofFn (A ∘ Fin.snoc w k)).prod = _
  rw [Fin.comp_snoc, List.ofFn_snoc, List.prod_append, List.prod_singleton]
  rfl

end PEPS
end TNLean

namespace MPSTensor

open TNLean.PEPS

variable {G : Type u} [Group G] {d D : ℕ}

/-- Two functions of configurations on `n + 2` sites agree once they agree on every
configuration `(i, w, k)` with first letter `i` and last letter `k`. -/
theorem funext_cons_snoc {β : Type*} {n : ℕ} {f g : (Fin (n + 2) → Fin d) → β}
    (h : ∀ (i : Fin d) (w : Fin n → Fin d) (k : Fin d),
      f (Fin.cons i (Fin.snoc w k)) = g (Fin.cons i (Fin.snoc w k))) :
    f = g := by
  funext τ
  have := h (τ 0) (Fin.init (Fin.tail τ)) (Fin.tail τ (Fin.last n))
  rwa [Fin.snoc_init_self, Fin.cons_self_tail] at this

/-- The blocked operator tensor of the matrices `A^i` is the operator of the word product. -/
theorem wordTensor_toLin' (A : MPSTensor d D) (n : ℕ) (σ : Fin n → Fin d) :
    wordTensor (fun i => Matrix.toLin' (A i)) n σ =
      Matrix.toLin' (Kraus.evalWord A (List.ofFn σ)) := by
  rw [toLin'_evalWord, List.map_ofFn]
  rfl

/-- Bridge: the MPS with closure `X` on `n` open sites, `σ ↦ tr[A^σ X]`, is the map `𝒫` of the
tensor obtained by blocking `n` sites, applied to the operator of `X`. -/
theorem groundSpaceMap_eq_mpsSiteMap_wordTensor (A : MPSTensor d D) (n : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    groundSpaceMap A n X =
      mpsSiteMap (wordTensor (fun i => Matrix.toLin' (A i)) n) (Matrix.toLin' X) := by
  funext σ
  rw [groundSpaceMap_apply, mpsSiteMap_apply, wordTensor_toLin', Module.End.mul_eq_comp,
    ← Matrix.toLin'_mul, Matrix.trace_toLin'_eq]

/-- The MPS with the closure of an operator `M` is the map `𝒫` of the blocked tensor at `M`. -/
theorem groundSpaceMap_toMatrix' (A : MPSTensor d D) (n : ℕ)
    (M : Module.End ℂ (Fin D → ℂ)) :
    groundSpaceMap A n (LinearMap.toMatrix' M) =
      mpsSiteMap (wordTensor (fun i => Matrix.toLin' (A i)) n) M := by
  rw [groundSpaceMap_eq_mpsSiteMap_wordTensor, Matrix.toLin'_toMatrix']

/-- The open-chain space `𝒮_n` is the range of the map `𝒫` of the blocked tensor. -/
theorem mem_groundSpace_iff_exists_mpsSiteMap {A : MPSTensor d D} {n : ℕ}
    {ψ : NSiteSpace d n} :
    ψ ∈ groundSpace A n ↔
      ∃ M : Module.End ℂ (Fin D → ℂ),
        mpsSiteMap (wordTensor (fun i => Matrix.toLin' (A i)) n) M = ψ := by
  constructor
  · rintro ⟨X, rfl⟩
    exact ⟨Matrix.toLin' X, (groundSpaceMap_eq_mpsSiteMap_wordTensor A n X).symm⟩
  · rintro ⟨M, rfl⟩
    exact ⟨LinearMap.toMatrix' M, groundSpaceMap_toMatrix' A n M⟩

/-- The MPS with closure `X` on `n + 1` sites, read with its first letter split off, is the map
`𝒫` of the concatenation of `A` with the blocked tensor of the remaining `n` sites. -/
theorem groundSpaceMap_cons (A : MPSTensor d D) (n : ℕ) (X : Matrix (Fin D) (Fin D) ℂ)
    (a : Fin d) (w : Fin n → Fin d) :
    groundSpaceMap A (n + 1) X (Fin.cons a w) =
      mpsSiteMap (concatTensor (fun i => Matrix.toLin' (A i))
        (wordTensor (fun i => Matrix.toLin' (A i)) n)) (Matrix.toLin' X) (a, w) := by
  rw [groundSpaceMap_eq_mpsSiteMap_wordTensor, mpsSiteMap_apply, mpsSiteMap_apply,
    wordTensor_cons, concatTensor_apply]

section GInjective

variable [Finite G] {ρ : Representation ℂ G (Fin D → ℂ)} {A : MPSTensor d D}

/-- The blocked tensor of `n ≥ 1` sites of a `G`-injective tensor is `G`-injective. -/
theorem isGInjective_mpsSiteMap_wordTensor
    (hA : IsGInjective (linHom ρ ρ) (mpsSiteMap fun i => Matrix.toLin' (A i))) {n : ℕ}
    (hn : 0 < n) :
    IsGInjective (linHom ρ ρ) (mpsSiteMap (wordTensor (fun i => Matrix.toLin' (A i)) n)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact hA.mpsSiteMap_wordTensor m

/-- Source: arXiv:1001.3807, proof of Theorem 3.5 (lines 766–797, the step
`𝒮_{k-1} ⊗ ℂ^d ∩ ℂ^d ⊗ 𝒮_{k-1} = 𝒮_k`), run on Theorem 4.8 as in the proof of Theorem 4.11
(lines 1191–1195). For a `G`-injective tensor and `K ≥ 1`, a vector on `K + 2` sites whose
restrictions to the first and to the last `K + 1` sites lie in `𝒮_{K+1}` lies in `𝒮_{K+2}`. -/
theorem mem_groundSpace_add_two_of_isGInjective
    (hA : IsGInjective (linHom ρ ρ) (mpsSiteMap fun i => Matrix.toLin' (A i))) {K : ℕ}
    (hK : 0 < K) {ψ : NSiteSpace d (K + 2)} (hLeft : InLeftGround A (K + 1) ψ)
    (hRight : InRightGround A (K + 1) ψ) :
    ψ ∈ groundSpace A (K + 2) := by
  set A' : Fin d → Module.End ℂ (Fin D → ℂ) := fun i => Matrix.toLin' (A i) with hA'
  set W := wordTensor A' K with hWdef
  have hW : IsGInjective (linHom ρ ρ) (mpsSiteMap W) := isGInjective_mpsSiteMap_wordTensor hA hK
  choose Y hY using fun i => mem_groundSpace_iff_exists_mpsSiteMap.1 (hRight i)
  choose Z hZ using fun k => mem_groundSpace_iff_exists_mpsSiteMap.1 (hLeft k)
  let φ : (Fin d × (Fin K → Fin d)) × Fin d → ℂ :=
    fun p => ψ (Fin.cons p.1.1 (Fin.snoc p.1.2 p.2))
  have h1 : ∀ i w k, φ ((i, w), k) = LinearMap.trace ℂ _ (A' i * W w * Z k) := by
    intro i w k
    have h := congr_fun (hZ k) (Fin.cons i w)
    rw [mpsSiteMap_apply, wordTensor_cons, restrictLast_apply] at h
    change ψ (Fin.cons i (Fin.snoc w k)) = _
    rw [Fin.cons_snoc_eq_snoc_cons, ← h]
  have h2 : ∀ i w k, φ ((i, w), k) = LinearMap.trace ℂ _ (Y i * W w * A' k) := by
    intro i w k
    have h := congr_fun (hY i) (Fin.snoc w k)
    rw [mpsSiteMap_apply, wordTensor_snoc, restrictFirst_apply] at h
    change ψ (Fin.cons i (Fin.snoc w k)) = _
    rw [← h, LinearMap.trace_mul_comm, mul_assoc]
  have hmem : φ ∈ Set.range (mpsSiteMap (concatTensor (concatTensor A' W) A')) := by
    rw [← hA.intersection_property hW]
    exact ⟨⟨Z, h1⟩, ⟨Y, h2⟩⟩
  obtain ⟨X, hX⟩ := hmem
  rw [mem_groundSpace_iff_exists_mpsSiteMap]
  refine ⟨X, funext_cons_snoc fun i w k => ?_⟩
  rw [mpsSiteMap_apply, wordTensor_cons, wordTensor_snoc]
  have h := congr_fun hX ((i, w), k)
  simp only [mpsSiteMap_apply, concatTensor_apply] at h
  rw [← mul_assoc, h]

/-- Source: arXiv:1001.3807, proof of Theorem 3.5 (lines 766–797, equation
`eq:inj:S-L-as-intersect`), run on Theorem 4.8 as in the proof of Theorem 4.11
(lines 1191–1195). For a `G`-injective tensor, a vector in the chain ground space of a ring of
`N` sites with window length `2 ≤ L ≤ N` lies in the open-chain space `𝒮_N`: it is
`σ ↦ tr[A^σ X]` for some operator `X`. -/
theorem chainGroundSpace_le_groundSpace_of_isGInjective
    (hA : IsGInjective (linHom ρ ρ) (mpsSiteMap fun i => Matrix.toLin' (A i))) {L N : ℕ}
    (hL : 2 ≤ L) (hLN : L ≤ N) :
    chainGroundSpace A L N ≤ groundSpace A N := by
  intro ψ hψ
  have hN0 : 0 < N := by omega
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have : ψ = 0 := funext fun σ => (σ ⟨0, hN0⟩).elim0
    rw [this]
    exact zero_mem _
  have : NeZero d := ⟨hd.ne'⟩
  rw [chainGroundSpace, dite_eq_left ⟨hN0, hLN⟩] at hψ
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hψ
  refine contiguous_mem_of_restriction_intersection_submodules (groundSpace A) (L := L)
    (by omega) hLN (fun M hM => le_antisymm ?_ ?_) fun s hs τ => ?_
  · intro φ hφ
    simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at hφ
    obtain ⟨K, rfl⟩ : ∃ K, M = K + 1 := ⟨M - 1, by omega⟩
    exact mem_groundSpace_add_two_of_isGInjective hA (by omega) hφ.1 hφ.2
  · intro φ hφ
    simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
    exact ⟨groundSpace_inLeftGround A M hφ, groundSpace_inRightGround A M hφ⟩
  · rw [← cyclicRestrictₗ_eq_contiguousRestrictₗ hN0 hLN
      (show (⟨s, by omega⟩ : Fin N).val + L ≤ N from hs)]
    exact hψ ⟨s, by omega⟩ τ

variable [Fintype G]

omit [Fintype G] in
/-- Source: arXiv:1001.3807, proof of Theorem 3.5 (lines 800–817), run on Theorem 4.9 as in
the proof of Theorem 4.11 (lines 1191–1195). For a `G`-injective tensor and `K ≥ 1`, let the
open-chain vector `tr[A^σ X]` on `K + 1` sites, cut at a second position, be `tr[A^σ Y]`, so
that `tr[A^w X A^a] = tr[A^w A^a Y]` for every word `w` of length `K` and letter `a`. Then it
is a combination of the MPS `|𝓜(A|U_g)⟩` with closure `U_g`. -/
theorem groundSpaceMap_mem_span_closure_of_isGInjective
    (hA : IsGInjective (linHom ρ ρ) (mpsSiteMap fun i => Matrix.toLin' (A i))) {K : ℕ}
    (hK : 0 < K) {X Y : Matrix (Fin D) (Fin D) ℂ}
    (h : ∀ a, groundSpaceMap A K (X * A a) = groundSpaceMap A K (A a * Y)) :
    groundSpaceMap A (K + 1) X ∈
      Submodule.span ℂ
        (Set.range fun g => groundSpaceMap A (K + 1) (LinearMap.toMatrix' (ρ g))) := by
  have := Fintype.ofFinite G
  set A' : Fin d → Module.End ℂ (Fin D → ℂ) := fun i => Matrix.toLin' (A i) with hA'
  set W := wordTensor A' K with hWdef
  have hW : IsGInjective (linHom ρ ρ) (mpsSiteMap W) := isGInjective_mpsSiteMap_wordTensor hA hK
  let φ : Fin d × (Fin K → Fin d) → ℂ := fun p => groundSpaceMap A (K + 1) X (Fin.cons p.1 p.2)
  have hM : φ = mpsSiteMap (concatTensor A' W) (Matrix.toLin' X) :=
    funext fun p => groundSpaceMap_cons A K X p.1 p.2
  have hN : ∀ j w, φ (j, w) = LinearMap.trace ℂ _ (A' j * Matrix.toLin' Y * W w) := by
    intro j w
    have hj := congr_fun (h j) w
    rw [groundSpaceMap_eq_mpsSiteMap_wordTensor, groundSpaceMap_eq_mpsSiteMap_wordTensor,
      mpsSiteMap_apply, mpsSiteMap_apply, Matrix.toLin'_mul, Matrix.toLin'_mul,
      ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp] at hj
    rw [hM, mpsSiteMap_apply, concatTensor_apply, mul_assoc, LinearMap.trace_mul_comm,
      mul_assoc, hj, LinearMap.trace_mul_comm, mul_assoc]
  have hsum := hW.eq_sum_of_closure hA hM hN
  have hX : groundSpaceMap A (K + 1) X = ∑ g,
      LinearMap.trace ℂ _ (ρ g⁻¹ * (linHom ρ ρ).averageMap (Matrix.toLin' Y) *
        deltaOperator ρ) • groundSpaceMap A (K + 1) (LinearMap.toMatrix' (ρ g)) := by
    funext τ
    rw [← Fin.cons_self_tail τ]
    have hτ := congr_fun hsum (τ 0, Fin.tail τ)
    simp only [Finset.sum_apply, Pi.smul_apply] at hτ ⊢
    change φ (τ 0, Fin.tail τ) = _
    rw [hτ]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [groundSpaceMap_cons, Matrix.toLin'_toMatrix']
  rw [hX]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

omit [Finite G] [Fintype G] in
/-- The closure `U_g` commutes with every matrix of a `G`-injective tensor. -/
theorem toMatrix'_rep_mul_of_isGInjective
    (hA : IsGInjective (linHom ρ ρ) (mpsSiteMap fun i => Matrix.toLin' (A i))) (g : G)
    (i : Fin d) :
    LinearMap.toMatrix' (ρ g) * A i = A i * LinearMap.toMatrix' (ρ g) := by
  have hconj := (mpsSiteMap_comp_linHom_eq_iff ρ _).1 hA.invariant
  have hcomm := mul_comm_of_conj_eq (fun h => hconj h i) g
  have := congrArg LinearMap.toMatrix' hcomm
  rwa [LinearMap.toMatrix'_mul, LinearMap.toMatrix'_mul, LinearMap.toMatrix'_toLin'] at this

omit [Finite G] [Fintype G] in
/-- The MPS `|𝓜(A|U_g)⟩` with closure `U_g` lies in the chain ground space. -/
theorem groundSpaceMap_rep_mem_chainGroundSpace
    (hA : IsGInjective (linHom ρ ρ) (mpsSiteMap fun i => Matrix.toLin' (A i))) (g : G)
    {L N : ℕ} (hN : 0 < N) (hLN : L ≤ N) :
    groundSpaceMap A N (LinearMap.toMatrix' (ρ g)) ∈ chainGroundSpace A L N := by
  have h := twistedMPV_mem_chainGroundSpace A (LinearMap.toMatrix' (ρ g)) 1
    (fun i => by rw [one_smul, toMatrix'_rep_mul_of_isGInjective hA g i]) L N hN hLN
  convert h using 1
  funext σ
  rw [groundSpaceMap_apply]

omit [Fintype G] in
/-- Source: arXiv:1001.3807, Theorem 4.11 (`thm:noninj:parentham`),
`Papers/1001.3807/paper_v3.tex` lines 1177–1195. For a `G`-injective tensor `A`, the
frustration-free ground space of the parent Hamiltonian on a ring of `N` sites is spanned by the
MPS `|𝓜(A|U_g)⟩ = ∑_σ tr[A^σ U_g] |σ⟩` with closure `U_g`. The source's two-site interaction is
the window length `L = 2`; the statement holds for every window length `2 ≤ L ≤ N`. The proof is
that of Theorem 3.5 (lines 758–817) with Theorems 4.8 and 4.9 in place of Theorems 3.3
and 3.4, as the source states. -/
theorem chainGroundSpace_eq_span_closure_of_isGInjective
    (hA : IsGInjective (linHom ρ ρ) (mpsSiteMap fun i => Matrix.toLin' (A i))) {L N : ℕ}
    (hL : 2 ≤ L) (hLN : L ≤ N) :
    chainGroundSpace A L N =
      Submodule.span ℂ (Set.range fun g => groundSpaceMap A N (LinearMap.toMatrix' (ρ g))) := by
  have := Fintype.ofFinite G
  have hN0 : 0 < N := by omega
  apply le_antisymm
  · intro ψ hψ
    obtain ⟨X, hX⟩ := chainGroundSpace_le_groundSpace_of_isGInjective hA hL hLN hψ
    obtain ⟨K, rfl⟩ : ∃ K, N = K + 1 := ⟨N - 1, by omega⟩
    have hψ' := cyclicTranslateState_mem_chainGroundSpace A hN0 hLN ⟨K, by omega⟩ hψ
    obtain ⟨Y, hY⟩ := chainGroundSpace_le_groundSpace_of_isGInjective hA hL hLN hψ'
    rw [← hX]
    refine groundSpaceMap_mem_span_closure_of_isGInjective hA (Y := Y) (by omega) fun a => ?_
    exact groundSpaceMap_mul_eq_of_cyclicTranslate_groundSpaceMap_eq X Y (by rw [hX, hY]) a
  · rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact groundSpaceMap_rep_mem_chainGroundSpace hA g hN0 hLN

attribute [local instance] Representation.invertibleFintypeCardComplex

/-- Replacing the closure by its twirl does not change the MPS of a `G`-injective tensor. -/
theorem groundSpaceMap_toMatrix'_averageMap
    (hA : IsGInjective (linHom ρ ρ) (mpsSiteMap fun i => Matrix.toLin' (A i))) {N : ℕ}
    (hN : 0 < N) (M : Module.End ℂ (Fin D → ℂ)) :
    groundSpaceMap A N (LinearMap.toMatrix' ((linHom ρ ρ).averageMap M)) =
      groundSpaceMap A N (LinearMap.toMatrix' M) := by
  rw [groundSpaceMap_toMatrix', groundSpaceMap_toMatrix']
  exact apply_averageMap_of_forall_comp_eq (isGInjective_mpsSiteMap_wordTensor hA hN).invariant M

/-- Source: arXiv:1001.3807, Theorem 4.12, `Papers/1001.3807/paper_v3.tex` lines 1197–1238.
For a `G`-injective tensor `A`, the chain ground space of Theorem 4.11 is spanned by the MPS
`|𝓜(A|Π_χ)⟩` whose closures are the isotypic projectors
`Π_χ = (χ(1)/|G|) ∑_g χ(g⁻¹) U_g` of the irreducible characters `χ` occurring in `U_g`
(equation `eq:noninj:all-indep-closures`). -/
theorem chainGroundSpace_eq_span_charProjector_of_isGInjective
    (hA : IsGInjective (linHom ρ ρ) (mpsSiteMap fun i => Matrix.toLin' (A i))) {L N : ℕ}
    (hL : 2 ≤ L) (hLN : L ≤ N) :
    chainGroundSpace A L N =
      Submodule.span ℂ (Set.range fun χ : irreducibleCharacterFinset ρ =>
        groundSpaceMap A N (LinearMap.toMatrix' (charProjector ρ χ.1))) := by
  have hN0 : 0 < N := by omega
  rw [chainGroundSpace_eq_span_closure_of_isGInjective hA hL hLN]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    dsimp only
    rw [SetLike.mem_coe, ← groundSpaceMap_toMatrix'_averageMap hA hN0, averageMap_linHom_rep,
      map_sum, map_sum]
    refine Submodule.sum_mem _ fun χ hχ => ?_
    rw [map_smul, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨χ, hχ⟩, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨χ, rfl⟩
    dsimp only
    rw [SetLike.mem_coe, charProjector, map_smul, map_smul, map_sum, map_sum]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g _ => ?_)
    rw [map_smul, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

/-- Source: arXiv:1001.3807, proof of Theorem 4.12, `Papers/1001.3807/paper_v3.tex`
lines 1240–1255 (equation `eq:noninj:Ug-lin-indep-diag`). For a `G`-injective tensor and every
ring of `N ≥ 1` sites, the MPS `|𝓜(A|Π_χ)⟩` of the irreducible characters `χ` occurring in `U_g`
are linearly independent. The source applies the left inverse of the `N`-fold blocked tensor;
here this is `G`-injectivity of the blocked tensor on the operators commuting with `U_g`, which
contain the `Π_χ`. -/
theorem linearIndependent_groundSpaceMap_charProjector_of_isGInjective
    (hA : IsGInjective (linHom ρ ρ) (mpsSiteMap fun i => Matrix.toLin' (A i))) {N : ℕ}
    (hN : 0 < N) :
    LinearIndependent ℂ fun χ : irreducibleCharacterFinset ρ =>
      groundSpaceMap A N (LinearMap.toMatrix' (charProjector ρ χ.1)) := by
  have hW := isGInjective_mpsSiteMap_wordTensor hA hN
  have hfun : (fun χ : irreducibleCharacterFinset ρ =>
      groundSpaceMap A N (LinearMap.toMatrix' (charProjector ρ χ.1))) =
      mpsSiteMap (wordTensor (fun i => Matrix.toLin' (A i)) N) ∘
        fun χ : irreducibleCharacterFinset ρ => charProjector ρ χ.1 :=
    funext fun χ => groundSpaceMap_toMatrix' A N _
  rw [hfun]
  refine (linearIndependent_charProjector ρ).map ?_
  rw [Submodule.disjoint_def]
  intro x hx hker
  refine hW.injOn_invariants x ?_ hker
  refine (Submodule.span_le.2 ?_) hx
  rintro _ ⟨χ, rfl⟩
  refine (mem_invariants_linHom_iff ρ _).2 fun g => ?_
  rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp,
    rep_mul_charProjector ρ (apply_conj_of_mem_irreducibleCharacters ρ
      ((mem_irreducibleCharacterFinset ρ).1 χ.2))]

/-- Source: arXiv:1001.3807, Theorem 4.12, `Papers/1001.3807/paper_v3.tex` lines 1197–1203.
For a `G`-injective tensor, the ground space of Theorem 4.11 is `I`-fold degenerate, where `I`
is the number of irreducible representations occurring in `U_g`. -/
theorem finrank_chainGroundSpace_of_isGInjective
    (hA : IsGInjective (linHom ρ ρ) (mpsSiteMap fun i => Matrix.toLin' (A i))) {L N : ℕ}
    (hL : 2 ≤ L) (hLN : L ≤ N) :
    finrank ℂ (chainGroundSpace A L N) = (irreducibleCharacterFinset ρ).card := by
  rw [chainGroundSpace_eq_span_charProjector_of_isGInjective hA hL hLN,
    finrank_span_eq_card (linearIndependent_groundSpaceMap_charProjector_of_isGInjective hA
      (by omega)), Fintype.card_coe]

omit [Fintype G] in
/-- Source: arXiv:1001.3807, proof of Theorem 4.12, `Papers/1001.3807/paper_v3.tex`
lines 1219–1223: `|𝓜(A|U_g)⟩ = |𝓜(A|U_h U_g U_h†)⟩ = |𝓜(A|U_{hgh⁻¹})⟩`, so the chain ground
space is spanned by the MPS `|𝓜(A|U_g)⟩` of one representative `g` per conjugacy class. -/
theorem chainGroundSpace_eq_span_conjClasses_of_isGInjective
    (hA : IsGInjective (linHom ρ ρ) (mpsSiteMap fun i => Matrix.toLin' (A i)))
    (r : ConjClasses G → G) (hr : ∀ c, ConjClasses.mk (r c) = c) {L N : ℕ}
    (hL : 2 ≤ L) (hLN : L ≤ N) :
    chainGroundSpace A L N =
      Submodule.span ℂ (Set.range fun c => groundSpaceMap A N (LinearMap.toMatrix' (ρ (r c)))) := by
  have hN0 : 0 < N := by omega
  rw [chainGroundSpace_eq_span_closure_of_isGInjective hA hL hLN]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    obtain ⟨h, hh⟩ := isConj_iff.1 (ConjClasses.mk_eq_mk_iff_isConj.1 (hr (ConjClasses.mk g)))
    refine Submodule.subset_span ⟨ConjClasses.mk g, ?_⟩
    set r₀ := r (ConjClasses.mk g)
    change groundSpaceMap A N (LinearMap.toMatrix' (ρ r₀)) =
      groundSpaceMap A N (LinearMap.toMatrix' (ρ g))
    have hconj : ρ g = linHom ρ ρ h (ρ r₀) := by
      rw [← hh, linHom_apply, map_mul, map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
        LinearMap.comp_assoc]
    rw [groundSpaceMap_toMatrix', groundSpaceMap_toMatrix', hconj, ← LinearMap.comp_apply,
      (isGInjective_mpsSiteMap_wordTensor hA hN0).invariant h]
  · exact Submodule.span_mono (Set.range_subset_iff.2 fun c => ⟨r c, rfl⟩)

omit [Fintype G] in
/-- Source: arXiv:1001.3807, Theorem 4.12, second part, `Papers/1001.3807/paper_v3.tex`
lines 1204–1207 and 1257–1259, with Lemma 4.6 (lines 1015–1029). For a `G`-injective tensor
with semi-regular `U_g` and every ring of `N ≥ 1` sites, the MPS `|𝓜(A|U_g)⟩` of one
representative `g = r c` per conjugacy class `c` are linearly independent. -/
theorem linearIndependent_groundSpaceMap_conjClasses_of_isSemiRegular
    (hA : IsGInjective (linHom ρ ρ) (mpsSiteMap fun i => Matrix.toLin' (A i)))
    (hρ : IsSemiRegular ρ) (r : ConjClasses G → G) (hr : ∀ c, ConjClasses.mk (r c) = c)
    {N : ℕ} (hN : 0 < N) :
    LinearIndependent ℂ fun c => groundSpaceMap A N (LinearMap.toMatrix' (ρ (r c))) := by
  have := Fintype.ofFinite G
  have hW := isGInjective_mpsSiteMap_wordTensor hA hN
  have hfun : (fun c => groundSpaceMap A N (LinearMap.toMatrix' (ρ (r c)))) =
      mpsSiteMap (wordTensor (fun i => Matrix.toLin' (A i)) N) ∘
        fun c => (linHom ρ ρ).averageMap (ρ (r c)) := by
    funext c
    rw [Function.comp_apply, ← groundSpaceMap_toMatrix', groundSpaceMap_toMatrix'_averageMap hA hN]
  rw [hfun]
  refine (linearIndependent_averageMap_conjClasses ρ hρ r hr).map ?_
  rw [Submodule.disjoint_def]
  intro x hx hker
  refine hW.injOn_invariants x ?_ hker
  refine (Submodule.span_le.2 ?_) hx
  rintro _ ⟨c, rfl⟩
  exact (linHom ρ ρ).averageMap_invariant _

omit [Fintype G] in
/-- Source: arXiv:1001.3807, Theorem 4.12, second part, `Papers/1001.3807/paper_v3.tex`
lines 1204–1207. For a `G`-injective tensor with semi-regular `U_g`, the ground space of
Theorem 4.11 has dimension equal to the number of conjugacy classes of `G`. -/
theorem finrank_chainGroundSpace_of_isSemiRegular
    (hA : IsGInjective (linHom ρ ρ) (mpsSiteMap fun i => Matrix.toLin' (A i)))
    (hρ : IsSemiRegular ρ) {L N : ℕ} (hL : 2 ≤ L) (hLN : L ≤ N) :
    finrank ℂ (chainGroundSpace A L N) = Nat.card (ConjClasses G) := by
  have := Fintype.ofFinite G
  classical
  choose r hr using ConjClasses.exists_rep (α := G)
  rw [chainGroundSpace_eq_span_conjClasses_of_isGInjective hA r hr hL hLN,
    finrank_span_eq_card (linearIndependent_groundSpaceMap_conjClasses_of_isSemiRegular hA hρ r hr
      (by omega)), Nat.card_eq_fintype_card]

/-- Source: arXiv:1001.3807, Theorem 4.12, second part, `Papers/1001.3807/paper_v3.tex`
lines 1204–1205 and 1257–1259. If a `G`-injective tensor exists for a semi-regular `U_g`, then
the number `I` of irreducible representations occurring in `U_g` is the number of conjugacy
classes of `G`. The source quotes this from the equality of the numbers of conjugacy classes and
of irreducible representations; here both numbers are computed as the dimension of the ground
space of a ring of two sites. -/
theorem card_irreducibleCharacterFinset_of_isSemiRegular
    (hA : IsGInjective (linHom ρ ρ) (mpsSiteMap fun i => Matrix.toLin' (A i)))
    (hρ : IsSemiRegular ρ) :
    (irreducibleCharacterFinset ρ).card = Nat.card (ConjClasses G) := by
  rw [← finrank_chainGroundSpace_of_isGInjective hA (le_refl 2) (le_refl 2),
    finrank_chainGroundSpace_of_isSemiRegular hA hρ (le_refl 2) (le_refl 2)]

end GInjective

end MPSTensor
