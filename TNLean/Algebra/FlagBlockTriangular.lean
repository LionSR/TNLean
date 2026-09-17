/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Complex.Basic

/-!
# Flag-adapted coordinates give block-triangular matrices

Let `H : Fin (r + 1) → Submodule K V` be an increasing flag of subspaces of a finite-dimensional
vector space `V`, from `⊥` to `⊤`, and let `f : ι → Module.End K V` be a family of endomorphisms
each preserving every subspace of the flag. This file shows that coordinates on `V` may be chosen
so that every `f i` becomes block upper triangular with respect to the flag, with diagonal blocks
equal to the matrices induced by the `f i` on the successive subquotients `H (k+1) / H k`.

This is Lemma 7.6 ("composition-series triangular gauge") of the P5 asymmetric-compression
fundamental-theorem note.

## Main definitions

* `Submodule.flagQuot`: the subquotient `H (k+1) ⧸ H k` of two adjacent flag members.
* `LinearMap.flagQuotMap`: the endomorphism induced by a flag-preserving endomorphism on a
  subquotient of the flag.

## Main results

* `exists_linearEquiv_blockTriangular_of_flag`: a linear equivalence between `V` and a graded
  coordinate space `(Σ k, Fin (n k)) → ℂ` under which every `f i` is block upper triangular, with
  diagonal block `k` the matrix of `LinearMap.flagQuotMap H (f i) (hf i) k` in the coordinates
  `ψ k`.
* `finrank_eq_sum_of_flag`: the dimension of `V` is the sum of the block sizes `n k`.
-/

open scoped Matrix

namespace Submodule

/-- The subquotient `H (k+1) ⧸ H k` of two nested submodules. -/
abbrev flagQuot {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {r : ℕ}
    (H : Fin (r + 1) → Submodule K V) (k : Fin r) : Type _ :=
  ↥(H k.succ) ⧸ (H k.castSucc).comap (H k.succ).subtype

end Submodule

namespace LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {r : ℕ}

/-- The map induced on the subquotient `H (k+1) ⧸ H k` by an endomorphism `f` of `V` that
preserves every member of the flag `H`. -/
def flagQuotMap (H : Fin (r + 1) → Submodule K V) (f : V →ₗ[K] V)
    (hf : ∀ k, ∀ x ∈ H k, f x ∈ H k) (k : Fin r) :
    Submodule.flagQuot H k →ₗ[K] Submodule.flagQuot H k :=
  Submodule.mapQ _ _ (f.restrict (hf k.succ)) (by
    intro x hx
    simp only [Submodule.mem_comap] at hx ⊢
    exact hf k.castSucc x hx)

@[simp]
theorem flagQuotMap_mk (H : Fin (r + 1) → Submodule K V) (f : V →ₗ[K] V)
    (hf : ∀ k, ∀ x ∈ H k, f x ∈ H k) (k : Fin r) (x : H k.succ) :
    flagQuotMap H f hf k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f.restrict (hf k.succ) x) :=
  rfl

end LinearMap

/-- The dimension of `V` is the sum of the block sizes `n k` recorded by coordinates `ψ k` on the
successive subquotients of an increasing flag from `⊥` to `⊤`. Proved by telescoping
`Submodule.finrank_quotient_add_finrank` along the flag (Lemma 7.6 of the P5 asymmetric-compression
fundamental-theorem note). -/
theorem finrank_eq_sum_of_flag {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {r : ℕ} (H : Fin (r + 1) → Submodule K V) (h0 : H 0 = ⊥)
    (htop : H (Fin.last r) = ⊤) (hmono : Monotone H) (n : Fin r → ℕ)
    (ψ : ∀ k, Submodule.flagQuot H k ≃ₗ[K] (Fin (n k) → K)) :
    Module.finrank K V = ∑ k, n k := by
  classical
  have step : ∀ k : Fin r, Module.finrank K (H k.succ) =
      n k + Module.finrank K (H k.castSucc) := by
    intro k
    have hle : H k.castSucc ≤ H k.succ := hmono k.castSucc_le_succ
    have h1 := Submodule.finrank_quotient_add_finrank
      ((H k.castSucc).comap (H k.succ).subtype)
    have h2 : Module.finrank K ((H k.castSucc).comap (H k.succ).subtype) =
        Module.finrank K (H k.castSucc) := (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
    have h3 : Module.finrank K (Submodule.flagQuot H k) = n k := by
      rw [(ψ k).finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    rw [h3, h2] at h1
    omega
  have key : ∀ l : Fin (r + 1), Module.finrank K (H l) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin r => j.castSucc < l), n j := by
    intro l
    induction l using Fin.induction with
    | zero => simp [h0]
    | succ k ih =>
      have hins : Finset.univ.filter (fun j : Fin r => j.castSucc < k.succ) =
          insert k (Finset.univ.filter (fun j : Fin r => j.castSucc < k.castSucc)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Fin.lt_def, Fin.val_castSucc, Fin.val_succ, Fin.ext_iff]
        omega
      have hnotmem : k ∉ Finset.univ.filter (fun j : Fin r => j.castSucc < k.castSucc) := by
        simp
      rw [hins, Finset.sum_insert hnotmem, ← ih, step k]
  have hlast : Finset.univ.filter (fun j : Fin r => j.castSucc < Fin.last r) = Finset.univ := by
    ext j
    simp [Fin.lt_def]
  have hkey := key (Fin.last r)
  rw [htop, finrank_top, hlast] at hkey
  simpa using hkey

/-- **Composition-series triangular gauge** (Lemma 7.6 of the P5 asymmetric-compression
fundamental-theorem note). If `H` is an increasing flag of subspaces from `⊥` to `⊤` of a
finite-dimensional complex vector space `V`, and every endomorphism `f i` preserves every member
of the flag, then there are coordinates on `V`, graded by the flag, in which every `f i` is block
upper triangular with diagonal blocks the matrices induced on the successive subquotients. -/
theorem exists_linearEquiv_blockTriangular_of_flag {ι : Type*} {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] {r : ℕ} (H : Fin (r + 1) → Submodule ℂ V)
    (h0 : H 0 = ⊥) (htop : H (Fin.last r) = ⊤) (hmono : Monotone H)
    (f : ι → Module.End ℂ V) (hf : ∀ i k, ∀ x ∈ H k, f i x ∈ H k)
    (n : Fin r → ℕ) (ψ : ∀ k, Submodule.flagQuot H k ≃ₗ[ℂ] (Fin (n k) → ℂ)) :
    ∃ e : V ≃ₗ[ℂ] ((Σ k : Fin r, Fin (n k)) → ℂ),
      (∀ i, (LinearMap.toMatrix' (e.conj (f i))).BlockTriangular Sigma.fst) ∧
      (∀ i k, Matrix.blockDiag' (LinearMap.toMatrix' (e.conj (f i))) k =
        LinearMap.toMatrix' ((ψ k).conj (LinearMap.flagQuotMap H (f i) (hf i) k))) ∧
      (∀ k, ∀ v : H k.succ, ∀ j, e (v : V) ⟨k, j⟩ = ψ k (Submodule.Quotient.mk v) j) ∧
      (∀ k, ∀ v ∈ H k.castSucc, ∀ l : Fin r, k ≤ l → ∀ j, e v ⟨l, j⟩ = 0) := by
  classical
  -- Complements of `H k.castSucc` inside `H k.succ`, giving explicit sections of the flag
  -- quotient maps.
  choose W hW using
    fun k : Fin r => Submodule.exists_isCompl ((H k.castSucc).comap (H k.succ).subtype)
  set equivK : ∀ k, Submodule.flagQuot H k ≃ₗ[ℂ] (W k) :=
    fun k => Submodule.quotientEquivOfIsCompl _ (W k) (hW k) with hequivK
  set σ : ∀ k, Submodule.flagQuot H k →ₗ[ℂ] H k.succ :=
    fun k => (W k).subtype ∘ₗ (equivK k).toLinearMap with hσdef
  have hσ : ∀ k (x : Submodule.flagQuot H k), Submodule.Quotient.mk (σ k x) = x := by
    intro k x
    exact Submodule.mk_quotientEquivOfIsCompl_apply (hW k) x
  -- The block-`k` term of the coordinate map.
  set term : ∀ k : Fin r, ((Σ k : Fin r, Fin (n k)) → ℂ) →ₗ[ℂ] V :=
    fun k => (H k.succ).subtype ∘ₗ σ k ∘ₗ (ψ k).symm.toLinearMap ∘ₗ
      LinearMap.funLeft ℂ ℂ (fun j => (⟨k, j⟩ : Σ k' : Fin r, Fin (n k'))) with hterm
  set Φ : ((Σ k : Fin r, Fin (n k)) → ℂ) →ₗ[ℂ] V := ∑ k : Fin r, term k with hΦ
  have hΦ_apply : ∀ x, Φ x = ∑ k : Fin r, term k x := by
    intro x; simp [hΦ, LinearMap.sum_apply]
  have hterm_apply : ∀ k x, term k x = (σ k ((ψ k).symm (fun j => x ⟨k, j⟩)) : V) := by
    intro k x; rfl
  have hterm_mem : ∀ k x, term k x ∈ H k.succ := by
    intro k x; rw [hterm_apply]; exact (σ k _).2
  have hmono_succ : ∀ k l : Fin r, k < l → H k.succ ≤ H l.castSucc := by
    intro k l hkl
    apply hmono
    rw [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc]
    have := Fin.lt_def.mp hkl
    omega
  -- General triangularity lemma: if `Φ x` lies in a flag member `H p`, then every block of `x`
  -- past `p` vanishes. Specializing `p` recovers injectivity of `Φ` (`p = 0`), the block-support
  -- half of the flag-coordinate formula (`p = k.succ`), and the flag-visibility clause
  -- (`p = k.castSucc`).
  have general : ∀ (p : Fin (r + 1)) (x : (Σ k : Fin r, Fin (n k)) → ℂ), Φ x ∈ H p →
      ∀ m : Fin r, p ≤ m.castSucc → ∀ j, x ⟨m, j⟩ = 0 := by
    intro p x hx
    by_contra hcon
    push Not at hcon
    obtain ⟨m0, hm0, j0, hj0⟩ := hcon
    set S : Finset (Fin r) :=
      Finset.univ.filter (fun m => p ≤ m.castSucc ∧ (fun j => x ⟨m, j⟩) ≠ 0) with hSdef
    have hSne : S.Nonempty := by
      refine ⟨m0, ?_⟩
      simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hm0, fun h => hj0 (congrFun h j0)⟩
    set l0 := S.max' hSne with hl0
    have hl0S : l0 ∈ S := S.max'_mem hSne
    have hl0p : p ≤ l0.castSucc ∧ (fun j => x ⟨l0, j⟩) ≠ 0 := by
      simpa [hSdef] using hl0S
    have hmax : ∀ m ∈ S, m ≤ l0 := fun m hm => S.le_max' m hm
    have hzero_above : ∀ m : Fin r, l0 < m → (fun j => x ⟨m, j⟩) = 0 := by
      intro m hm
      by_contra hne
      have hmS : m ∈ S := by
        simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨le_trans hl0p.1 (Fin.castSucc_lt_castSucc_iff.mpr hm).le, hne⟩
      exact absurd (hmax m hmS) (not_le.mpr hm)
    have hins : Finset.univ.filter (fun m : Fin r => m ≤ l0) =
        insert l0 (Finset.univ.filter (fun m : Fin r => m < l0)) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro h; rcases lt_or_eq_of_le h with h' | h'
        · exact Or.inr h'
        · exact Or.inl h'
      · rintro (rfl | h)
        · exact le_refl _
        · exact h.le
    have hnotmem : l0 ∉ Finset.univ.filter (fun m : Fin r => m < l0) := by simp
    have hsplit : Φ x = (∑ m ∈ Finset.univ.filter (fun m : Fin r => m < l0), term m x) +
        term l0 x := by
      rw [hΦ_apply, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun m => m ≤ l0)
        (fun m => term m x), hins, Finset.sum_insert hnotmem]
      have h2 : ∑ m ∈ Finset.univ.filter (fun m : Fin r => ¬ m ≤ l0), term m x = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hm
        rw [hterm_apply, hzero_above m hm]
        simp
      rw [h2, add_zero]
      abel
    have hsum_lt_mem :
        (∑ m ∈ Finset.univ.filter (fun m : Fin r => m < l0), term m x) ∈ H l0.castSucc := by
      apply Submodule.sum_mem
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      exact hmono_succ m l0 hm (hterm_mem m x)
    have hΦx_mem : Φ x ∈ H l0.castSucc := hmono hl0p.1 hx
    have hterm_l0_mem : term l0 x ∈ H l0.castSucc := by
      have heq2 : term l0 x =
          Φ x - ∑ m ∈ Finset.univ.filter (fun m : Fin r => m < l0), term m x := by
        rw [hsplit]; abel
      rw [heq2]
      exact Submodule.sub_mem _ hΦx_mem hsum_lt_mem
    have heq : term l0 x = (σ l0 ((ψ l0).symm (fun j => x ⟨l0, j⟩)) : V) := hterm_apply l0 x
    have hmem : σ l0 ((ψ l0).symm (fun j => x ⟨l0, j⟩)) ∈
        (H l0.castSucc).comap (H l0.succ).subtype := by
      rw [Submodule.mem_comap]
      change ↑(σ l0 ((ψ l0).symm (fun j => x ⟨l0, j⟩))) ∈ H l0.castSucc
      rw [← heq]
      exact hterm_l0_mem
    have hzero : Submodule.Quotient.mk (σ l0 ((ψ l0).symm (fun j => x ⟨l0, j⟩))) =
        (0 : Submodule.flagQuot H l0) := by
      rw [Submodule.Quotient.mk_eq_zero]
      exact hmem
    rw [hσ l0 ((ψ l0).symm (fun j => x ⟨l0, j⟩))] at hzero
    have hxzero : (fun j => x ⟨l0, j⟩) = 0 := by
      have h2 := congrArg (ψ l0) hzero
      simpa using h2
    exact hl0p.2 hxzero
  have hinj : Function.Injective Φ := by
    have hker : LinearMap.ker Φ = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      rw [LinearMap.mem_ker] at hx
      funext p
      obtain ⟨m, j⟩ := p
      have h0mem : Φ x ∈ H (0 : Fin (r + 1)) := by rw [hx, h0]; exact Submodule.zero_mem _
      have := general 0 x h0mem m (Fin.zero_le _) j
      simpa using this
    exact LinearMap.ker_eq_bot.mp hker
  have hdim : Module.finrank ℂ ((Σ k : Fin r, Fin (n k)) → ℂ) = Module.finrank ℂ V := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sigma]
    simp only [Fintype.card_fin]
    exact (finrank_eq_sum_of_flag H h0 htop hmono n ψ).symm
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  set e : V ≃ₗ[ℂ] ((Σ k : Fin r, Fin (n k)) → ℂ) :=
    (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).symm with he
  have hΦe : ∀ v, Φ (e v) = v := fun v => by
    rw [he]; exact (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).apply_symm_apply v
  have heΦ : ∀ x, e (Φ x) = x := fun x => by
    rw [he]; exact (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).symm_apply_apply x
  have he_symm : ∀ x, e.symm x = Φ x := by
    intro x
    have h2 : e.symm (e (Φ x)) = e.symm x := by rw [heΦ]
    rwa [e.symm_apply_apply] at h2
  -- A basis vector supported at a single block is sent by `Φ` entirely into that block's
  -- flag member; every other block-map term of the sum vanishes on it.
  have hΦ_single : ∀ (l : Fin r) (j : Fin (n l)),
      Φ (Pi.single (⟨l, j⟩ : Σ k : Fin r, Fin (n k)) (1 : ℂ)) =
        term l (Pi.single (⟨l, j⟩ : Σ k : Fin r, Fin (n k)) (1 : ℂ)) := by
    intro l j
    set u : (Σ k : Fin r, Fin (n k)) → ℂ := Pi.single (⟨l, j⟩ : Σ k : Fin r, Fin (n k)) (1 : ℂ)
      with hu
    rw [hΦ_apply]
    refine Finset.sum_eq_single_of_mem l (Finset.mem_univ l) ?_
    intro m _ hml
    rw [hterm_apply]
    have hzero : (fun j' => u ⟨m, j'⟩) = 0 := by
      funext j'
      have hne : (⟨m, j'⟩ : Σ k : Fin r, Fin (n k)) ≠ ⟨l, j⟩ := by
        intro h; exact hml (congrArg Sigma.fst h)
      simp [hu, hne]
    rw [hzero]
    simp
  -- Clause 3: the exact value of the coordinate on the flag member `H k.succ`.
  have hclause3 : ∀ (k : Fin r) (v : H k.succ) (j : Fin (n k)),
      e (v : V) ⟨k, j⟩ = ψ k (Submodule.Quotient.mk v) j := by
    intro k v j
    have hzero_above : ∀ l : Fin r, k < l → ∀ j', e (v : V) ⟨l, j'⟩ = 0 := by
      intro l hkl j'
      have hp : Φ (e (v : V)) ∈ H k.succ := by rw [hΦe]; exact v.2
      refine general k.succ (e (v : V)) hp l ?_ j'
      rw [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc]
      have := Fin.lt_def.mp hkl
      omega
    have hins : Finset.univ.filter (fun l : Fin r => l ≤ k) =
        insert k (Finset.univ.filter (fun l : Fin r => l < k)) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro h; rcases lt_or_eq_of_le h with h' | h'
        · exact Or.inr h'
        · exact Or.inl h'
      · rintro (rfl | h)
        · exact le_refl _
        · exact h.le
    have hnotmem : k ∉ Finset.univ.filter (fun l : Fin r => l < k) := by simp
    have hsplit : Φ (e (v : V)) =
        (∑ l ∈ Finset.univ.filter (fun l : Fin r => l < k), term l (e (v : V))) +
          term k (e (v : V)) := by
      rw [hΦ_apply, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun l => l ≤ k)
        (fun l => term l (e (v : V))), hins, Finset.sum_insert hnotmem]
      have h2 : ∑ l ∈ Finset.univ.filter (fun l : Fin r => ¬ l ≤ k), term l (e (v : V)) = 0 := by
        apply Finset.sum_eq_zero
        intro l hl
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hl
        rw [hterm_apply]
        have hz : (fun j' => e (v : V) ⟨l, j'⟩) = 0 := funext (hzero_above l hl)
        rw [hz]
        simp
      rw [h2, add_zero]
      abel
    have hsum_lt_mem :
        (∑ l ∈ Finset.univ.filter (fun l : Fin r => l < k), term l (e (v : V))) ∈
          H k.castSucc := by
      apply Submodule.sum_mem
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      exact hmono_succ l k hl (hterm_mem l (e (v : V)))
    have hterm_k_eq : term k (e (v : V)) = (v : V) -
        ∑ l ∈ Finset.univ.filter (fun l : Fin r => l < k), term l (e (v : V)) := by
      rw [hΦe] at hsplit
      rw [eq_sub_iff_add_eq, add_comm]
      exact hsplit.symm
    have hmk : (Submodule.Quotient.mk (⟨term k (e (v : V)), hterm_mem k (e (v : V))⟩ : H k.succ) :
        Submodule.flagQuot H k) = Submodule.Quotient.mk v := by
      rw [Submodule.Quotient.eq]
      rw [Submodule.mem_comap]
      change ((⟨term k (e (v : V)), hterm_mem k (e (v : V))⟩ : H k.succ) : V) - (v : V) ∈
        H k.castSucc
      have hval : (term k (e (v : V)) : V) - (v : V) ∈ H k.castSucc := by
        rw [hterm_k_eq]
        have hrw : (v : V) -
            (∑ l ∈ Finset.univ.filter (fun l : Fin r => l < k), term l (e (v : V))) - (v : V) =
            -(∑ l ∈ Finset.univ.filter (fun l : Fin r => l < k), term l (e (v : V))) := by abel
        rw [hrw]
        exact Submodule.neg_mem _ hsum_lt_mem
      exact hval
    have heq2 : (⟨term k (e (v : V)), hterm_mem k (e (v : V))⟩ : H k.succ) =
        σ k ((ψ k).symm (fun j' => e (v : V) ⟨k, j'⟩)) := by
      apply Subtype.ext
      exact hterm_apply k (e (v : V))
    rw [heq2] at hmk
    rw [hσ] at hmk
    have hcg := congrArg (ψ k) hmk
    simpa using congrFun hcg j
  -- Clause 4: coordinates past a flag member vanish.
  have hclause4 : ∀ (k : Fin r) (v : V), v ∈ H k.castSucc → ∀ l : Fin r, k ≤ l →
      ∀ j, e v ⟨l, j⟩ = 0 := by
    intro k v hv l hkl j
    have hp : Φ (e v) ∈ H k.castSucc := by rw [hΦe]; exact hv
    refine general k.castSucc (e v) hp l ?_ j
    rw [Fin.le_iff_val_le_val, Fin.val_castSucc, Fin.val_castSucc]
    exact Fin.le_iff_val_le_val.mp hkl
  -- Clause 1: block upper triangularity.
  have hclause1 : ∀ i, (LinearMap.toMatrix' (e.conj (f i))).BlockTriangular Sigma.fst := by
    intro i rowidx colidx hlt
    obtain ⟨l1, j1⟩ := rowidx
    obtain ⟨l2, j2⟩ := colidx
    simp only at hlt
    rw [LinearMap.toMatrix'_apply]
    set w : (Σ k : Fin r, Fin (n k)) → ℂ := Pi.single (⟨l2, j2⟩ : Σ k : Fin r, Fin (n k)) 1 with hw
    have hΦw_mem : Φ w ∈ H l2.succ := by rw [hΦ_single]; exact hterm_mem l2 w
    have hfΦw_mem : f i (Φ w) ∈ H l2.succ := hf i l2.succ (Φ w) hΦw_mem
    have hp : Φ (e (f i (Φ w))) ∈ H l2.succ := by rw [hΦe]; exact hfΦw_mem
    have hzero := general l2.succ (e (f i (Φ w))) hp l1 (by
      rw [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc]
      have := Fin.lt_def.mp hlt
      omega) j1
    rw [LinearEquiv.conj_apply_apply, he_symm]
    exact hzero
  -- Clause 2: diagonal blocks are the induced subquotient maps.
  have hclause2 : ∀ i k, Matrix.blockDiag' (LinearMap.toMatrix' (e.conj (f i))) k =
      LinearMap.toMatrix' ((ψ k).conj (LinearMap.flagQuotMap H (f i) (hf i) k)) := by
    intro i k
    funext row col
    rw [Matrix.blockDiag'_apply, LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply]
    set w : (Σ k' : Fin r, Fin (n k')) → ℂ := Pi.single (⟨k, col⟩ : Σ k' : Fin r, Fin (n k')) 1
      with hw
    have hΦw_mem : Φ w ∈ H k.succ := by rw [hΦ_single]; exact hterm_mem k w
    have hfΦw_mem : f i (Φ w) ∈ H k.succ := hf i k.succ (Φ w) hΦw_mem
    rw [LinearEquiv.conj_apply_apply, he_symm]
    rw [hclause3 k ⟨f i (Φ w), hfΦw_mem⟩ row]
    rw [LinearEquiv.conj_apply_apply]
    have hΦw_eq : Submodule.Quotient.mk (⟨Φ w, hΦw_mem⟩ : H k.succ) =
        (ψ k).symm (Pi.single col 1) := by
      have h1 : term k w = (σ k ((ψ k).symm (fun j' => w ⟨k, j'⟩)) : V) := hterm_apply k w
      have h2 : Φ w = term k w := hΦ_single k col
      have h3 : (fun j' => w ⟨k, j'⟩) = Pi.single col (1 : ℂ) := by
        funext j'
        simp [hw, Pi.single_apply, Sigma.ext_iff]
      rw [h3] at h1
      have h4 : (⟨Φ w, hΦw_mem⟩ : H k.succ) = σ k ((ψ k).symm (Pi.single col 1)) :=
        Subtype.ext (h2.trans h1)
      rw [h4]
      exact hσ k _
    have hfeq : Submodule.Quotient.mk (⟨f i (Φ w), hfΦw_mem⟩ : H k.succ) =
        LinearMap.flagQuotMap H (f i) (hf i) k
          (Submodule.Quotient.mk (⟨Φ w, hΦw_mem⟩ : H k.succ)) := by
      rw [LinearMap.flagQuotMap_mk]
      congr 1
    rw [hfeq, hΦw_eq]
  exact ⟨e, hclause1, hclause2, hclause3, hclause4⟩
