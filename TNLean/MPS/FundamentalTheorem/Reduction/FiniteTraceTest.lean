/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.TracePairing

/-!
# Finitely many lengths decide equality of states

Two tensors of bond dimensions `D₁`, `D₂` have the same states at every positive length as soon
as the traces of their words agree for all lengths from `1` to `D₁ ^ 2 + D₂ ^ 2`.

The proof considers the block diagonal tensor `B ⊕ B'`: the spans of its words of lengths `1`
to `n` increase inside a space of dimension `D₁ ^ 2 + D₂ ^ 2`, and a single plateau is permanent.

## Main results

* `Monotone.le_of_plateau`: a monotone chain of bounded rank whose plateaus are permanent is
  constant from the rank bound on.
* `prod_map_mem_span_of_finrank_le`: in a finite dimensional algebra, every word of
  length at least `k ≤ 1` lies in the span of the words of lengths `k` to `N`, once
  `finrank ≤ N + (1 - k)`.
* `MPSTensor.sameMPV₂Pos_of_forall_trace_evalWord_eq`
-/

namespace MPSTensor

variable {d : ℕ}

/-- **Plateau lemma.** Let `S` be a monotone chain in a partial order with a strictly monotone
rank `r`, such that a single plateau `S (n + 1) = S n` forces `S (n + 2) = S (n + 1)`. If the
rank grows by at most `N` along the chain, then every `S n` lies below `S N`: the chain is
constant from `N` on. -/
theorem _root_.Monotone.le_of_plateau {α : Type*} [PartialOrder α] {S : ℕ → α} (hS : Monotone S)
    (hstep : ∀ n, S (n + 1) = S n → S (n + 2) = S (n + 1))
    {r : α → ℕ} (hr : StrictMono r) {N : ℕ} (hN : ∀ n, r (S n) ≤ r (S 0) + N) (n : ℕ) :
    S n ≤ S N := by
  have hex : ∃ m ≤ N, S (m + 1) = S m := by
    by_contra hne
    simp only [not_exists, not_and] at hne
    have hgrow : ∀ k ≤ N + 1, r (S 0) + k ≤ r (S k) := by
      intro k hk
      induction k with
      | zero => simp
      | succ k ih =>
        have hlt : S k < S (k + 1) :=
          lt_of_le_of_ne (hS (Nat.le_succ k)) (fun h => hne k (by omega) h.symm)
        have h1 := hr hlt
        have h2 := ih (by omega)
        omega
    have h1 := hgrow (N + 1) le_rfl
    have h2 := hN (N + 1)
    omega
  obtain ⟨m, hm, hplat⟩ := hex
  have hsucc : ∀ j, S (m + j + 1) = S (m + j) := by
    intro j
    induction j with
    | zero => simpa using hplat
    | succ j ih => exact hstep (m + j) ih
  have hconst : ∀ j, S (m + j) = S m := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [← Nat.add_assoc, hsucc j, ih]
  rcases le_or_gt n N with hn | hn
  · exact hS hn
  · obtain ⟨j, rfl⟩ : ∃ j, n = m + j := ⟨n - m, by omega⟩
    rw [hconst j]
    exact hS hm

/-- **Words in a finite dimensional algebra.** Let `z` be letters in a finite dimensional
algebra `A` and `k ≤ 1`. If `finrank A ≤ N + (1 - k)`, every word of length at least `k` lies in
the span of the words of lengths `k` to `N`. For `k = 1` the spans of the words of lengths
`1, …, n` start at `0`; for `k = 0` they start at the line through `1`. -/
theorem _root_.prod_map_mem_span_of_finrank_le {A : Type*} [Ring A] [Algebra ℂ A]
    [FiniteDimensional ℂ A] (z : Fin d → A) {k N : ℕ} (hk : k ≤ 1)
    (hN : Module.finrank ℂ A ≤ N + (1 - k)) (w : List (Fin d)) (hw : k ≤ w.length) :
    (w.map z).prod ∈ Submodule.span ℂ
      {x | ∃ u : List (Fin d), k ≤ u.length ∧ u.length ≤ N ∧ (u.map z).prod = x} := by
  set S : ℕ → Submodule ℂ A := fun n => Submodule.span ℂ
    {x | ∃ u : List (Fin d), k ≤ u.length ∧ u.length ≤ n ∧ (u.map z).prod = x} with hSdef
  have hmono : Monotone S := by
    intro m n hmn
    refine Submodule.span_mono ?_
    rintro x ⟨u, hu1, hu2, rfl⟩
    exact ⟨u, hu1, hu2.trans hmn, rfl⟩
  have hmem : ∀ n (u : List (Fin d)), k ≤ u.length → u.length ≤ n → (u.map z).prod ∈ S n :=
    fun n u hu1 hu2 => Submodule.subset_span ⟨u, hu1, hu2, rfl⟩
  have hmul : ∀ n (i : Fin d) {x : A}, x ∈ S n → z i * x ∈ S (n + 1) := by
    intro n i x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu1, hu2, rfl⟩ := hx
      have := hmem (n + 1) (i :: u) (by simp; omega) (by simp; omega)
      simpa using this
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx
  have hstep : ∀ n, S (n + 1) = S n → S (n + 2) = S (n + 1) := by
    intro n hn
    refine le_antisymm ?_ (hmono (Nat.le_succ _))
    refine Submodule.span_le.mpr ?_
    rintro x ⟨u, hu1, hu2, rfl⟩
    rcases Nat.lt_or_ge u.length (n + 2) with hlt | hge
    · exact hmem (n + 1) u hu1 (by omega)
    · obtain ⟨i, u', rfl⟩ : ∃ i u', u = i :: u' := by
        cases u with
        | nil => simp at hge
        | cons i u' => exact ⟨i, u', rfl⟩
      have hu' : (u'.map z).prod ∈ S n := by
        rw [← hn]
        exact hmem (n + 1) u' (by simp at hu2 hge; omega) (by simp at hu2; omega)
      simpa using hmul n i hu'
  have hr : StrictMono fun s : Submodule ℂ A => Module.finrank ℂ s :=
    fun _ _ h => Submodule.finrank_lt_finrank_of_lt h
  have hbound : ∀ n, Module.finrank ℂ (S n) ≤ Module.finrank ℂ (S 0) + N := by
    intro n
    have hle : Module.finrank ℂ (S n) ≤ Module.finrank ℂ A := Submodule.finrank_le _
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      by_cases h1 : (1 : A) = 0
      · have : Subsingleton A := subsingleton_of_zero_eq_one h1.symm
        have : Module.finrank ℂ A = 0 := Module.finrank_zero_of_subsingleton
        omega
      · have h1mem : (1 : A) ∈ S 0 := by simpa using hmem 0 [] le_rfl le_rfl
        have hspan : Submodule.span ℂ {(1 : A)} ≤ S 0 :=
          Submodule.span_le.mpr (by simpa using h1mem)
        have hone := finrank_span_singleton (K := ℂ) h1
        have := Submodule.finrank_mono hspan
        omega
    · have : 1 - k = 0 := by omega
      omega
  have hplat := hmono.le_of_plateau hstep hr hbound w.length
  exact hplat (hmem w.length w hw le_rfl)

/-- Words of the block diagonal tensor `B ⊕ B'`, realized in the product algebra, are the pairs
of words. -/
theorem prod_map_prodMk_eq_evalWord {D₁ D₂ : ℕ} (B : MPSTensor d D₁) (B' : MPSTensor d D₂)
    (w : List (Fin d)) :
    (w.map fun i => (B i, B' i)).prod = (Kraus.evalWord B w, Kraus.evalWord B' w) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [ih]

/-- **Finite trace test.** If `tr B^w = tr B'^w` for every word with
`1 ≤ |w| ≤ D₁ ^ 2 + D₂ ^ 2`, then `B` and `B'` have the same states at every positive length. -/
theorem sameMPV₂Pos_of_forall_trace_evalWord_eq {D₁ D₂ : ℕ}
    {B : MPSTensor d D₁} {B' : MPSTensor d D₂}
    (h : ∀ w : List (Fin d), 1 ≤ w.length → w.length ≤ D₁ ^ 2 + D₂ ^ 2 →
      Matrix.trace (Kraus.evalWord B w) = Matrix.trace (Kraus.evalWord B' w)) :
    SameMPV₂Pos B B' := by
  let A := Matrix (Fin D₁) (Fin D₁) ℂ × Matrix (Fin D₂) (Fin D₂) ℂ
  let φ : A →ₗ[ℂ] ℂ :=
    (Matrix.traceLinearMap (Fin D₁) ℂ ℂ).comp (LinearMap.fst ℂ _ _) -
      (Matrix.traceLinearMap (Fin D₂) ℂ ℂ).comp (LinearMap.snd ℂ _ _)
  have hφ : ∀ Y : A, φ Y = Matrix.trace Y.1 - Matrix.trace Y.2 := fun _ => rfl
  have hfin : Module.finrank ℂ A ≤ (D₁ ^ 2 + D₂ ^ 2) + (1 - 1) := by
    simp [A, Module.finrank_prod, Module.finrank_matrix, sq]
  have hspan : Submodule.span ℂ {x | ∃ u : List (Fin d), 1 ≤ u.length ∧
      u.length ≤ D₁ ^ 2 + D₂ ^ 2 ∧ (u.map fun i => (B i, B' i)).prod = x} ≤
      LinearMap.ker φ := by
    refine Submodule.span_le.mpr ?_
    rintro x ⟨u, hu1, hu2, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hφ, prod_map_prodMk_eq_evalWord]
    rw [h u hu1 hu2, sub_self]
  intro n hn σ
  have hw : 1 ≤ (List.ofFn σ).length := by simp only [List.length_ofFn]; omega
  have hmem := hspan (prod_map_mem_span_of_finrank_le (A := A) (fun i => (B i, B' i))
    le_rfl hfin (List.ofFn σ) hw)
  rw [LinearMap.mem_ker, hφ, prod_map_prodMk_eq_evalWord] at hmem
  simpa [mpv, coeff, sub_eq_zero] using hmem

end MPSTensor
