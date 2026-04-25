/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.Basic
import TNLean.MPS.ParentHamiltonian.CyclicWindow
import TNLean.MPS.ParentHamiltonian.ExtendRight
import TNLean.MPS.ParentHamiltonian.RestrictTransport
import TNLean.MPS.ParentHamiltonian.WrappingWindow
import TNLean.MPS.FundamentalTheorem.FiniteLength
import TNLean.Algebra.TracePairing
import TNLean.Wielandt.SpanGrowth.CumulativeToWordSpan

/-!
# Unique ground state for injective MPS parent Hamiltonians

For an injective MPS tensor `A` on a periodic chain, the expected parent-Hamiltonian
ground space is spanned by the MPV state
`σ ↦ tr(A^{σ₀} ⋯ A^{σ_{N-1}})`.

## Overview

The proof combines the intersection property from `IntersectionProperty.lean`
with the periodic boundary condition:

1. **Open chain**: By iterated application of the intersection property,
   any state satisfying all local ground-space conditions has the form
   `ψ(σ) = tr(A^σ · X)` for some boundary matrix `X ∈ M_D(ℂ)`.
   This yields a `D²`-dimensional space.

2. **Periodic chain**: The wrapping window condition (connecting the last and
   first sites) constrains `X`. For injective `A`, the matrices `{A^i}` span
   `M_D(ℂ)`, so the commutation condition forces `X ∝ I`, yielding a
   one-dimensional ground space spanned by the MPV.

## Main results

* `MPSTensor.mpvSubmodule` — the subspace spanned by the MPV
* `MPSTensor.mpv_mem_groundSpace` — the MPV lies in the ground space
* `MPSTensor.chainGroundSpace` — the periodic-chain ground space as intersection
  of cyclic window ground submodules
* `MPSTensor.chainGroundSpace_le_groundSpace_of_isNBlkInjective` — cyclic
  normal-range constraints imply open-chain ground-space membership
* `MPSTensor.groundSpace_unique_periodic` — uniqueness on the periodic chain
* `MPSTensor.parentHamiltonian_unique_gs_injective` — uniqueness for `2L₀` sites
* `MPSTensor.parentHamiltonian_unique_gs_normal` — optimal uniqueness for `L₀+1` sites

## References

* [CPGSV21] arXiv:2011.12127, lines 2013–2094 (full argument)
* [FNW92] Sections 3–4
* [PGVWC07] arXiv:quant-ph/0608197, Sections 5–6
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ### The MPV submodule -/

/-- The submodule spanned by the MPV state.

On the periodic chain, the MPV state is `σ ↦ tr(A^{σ₀} ⋯ A^{σ_{N-1}})`,
which corresponds to the ground-space map applied to the identity:
`mpv A = groundSpaceMap A N 1`. -/
noncomputable def mpvSubmodule (A : MPSTensor d D) (N : ℕ) :
    Submodule ℂ (NSiteSpace d N) :=
  Submodule.span ℂ {mpv A}

/-- The MPV is the ground-space map applied to the identity matrix. -/
theorem mpv_eq_groundSpaceMap_one (A : MPSTensor d D) (N : ℕ) :
    (mpv A : NSiteSpace d N) = groundSpaceMap A N 1 := by
  ext σ
  simp [mpv, coeff, groundSpaceMap_apply]

/-- The MPV state lies in the ground space `G_N(A)` for any `N`. -/
theorem mpv_mem_groundSpace (A : MPSTensor d D) (N : ℕ) :
    (mpv A : NSiteSpace d N) ∈ groundSpace A N := by
  rw [groundSpace, LinearMap.mem_range]
  exact ⟨1, by ext σ; simp [groundSpaceMap_apply, mpv, coeff]⟩

/-! ### Periodic chain ground space

On a periodic chain of `N` sites, the ground space of the parent Hamiltonian
is the set of states whose restriction to every cyclic window of `L` consecutive
sites lies in `G_L(A)`.

The definition below makes this intersection explicit using cyclic restriction
maps. It uses `⊤` for degenerate lengths (`N = 0` or `L > N`) so that downstream
theorems can state their nondegenerate hypotheses separately. -/

/-- The periodic chain ground space: the set of states `ψ` on `N` sites such
that every cyclic window of `L` consecutive sites restricts into `G_L(A)`.

When `N = 0` or `L > N`, we return `⊤` as a degenerate convention. -/
noncomputable def chainGroundSpace (A : MPSTensor d D) (L N : ℕ) :
    Submodule ℂ (NSiteSpace d N) :=
  if hN : 0 < N ∧ L ≤ N then
    ⨅ (i : Fin N) (τ : Fin N → Fin d),
      (groundSpace A L).comap (cyclicRestrictₗ hN.1 L i τ)
  else ⊤

/-- The MPV state is in the chain ground space.

The proof uses trace cyclicity: for each cyclic window at position `i`, the
restriction of the MPV to that window equals `groundSpaceMap A L X_τ` where
`X_τ` is the product of `A`-matrices at outside positions. The cyclic list
bookkeeping follows from the window-level membership calculation. -/
theorem mpv_mem_chainGroundSpace (A : MPSTensor d D) (L N : ℕ)
    (hN : 0 < N) (hLN : L ≤ N) :
    (mpv A : NSiteSpace d N) ∈ chainGroundSpace A L N := by
  rw [chainGroundSpace, dif_pos ⟨hN, hLN⟩]
  simp only [Submodule.mem_iInf, Submodule.mem_comap]
  intro i τ
  simpa [cyclicRestrictₗ_apply, cyclicCfg, replaceWindow] using
    mpv_window_mem_groundSpace A L N hLN i τ

/-- Peeling the last site of every cyclic window shows that a larger interaction
range imposes at least the constraints of the preceding range. -/
theorem chainGroundSpace_le_chainGroundSpace_succ (A : MPSTensor d D)
    {L N : ℕ} (hN : 0 < N) (hLN : L + 1 ≤ N) :
    chainGroundSpace A (L + 1) N ≤ chainGroundSpace A L N := by
  intro ψ hψ
  rw [chainGroundSpace, dif_pos ⟨hN, hLN⟩] at hψ
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hψ
  rw [chainGroundSpace, dif_pos ⟨hN, show L ≤ N from by omega⟩]
  simp only [Submodule.mem_iInf, Submodule.mem_comap]
  intro i τ
  let peeled : Fin N := ⟨(i.val + L) % N, Nat.mod_lt _ hN⟩
  let τ' : Fin N → Fin d :=
    fun k => if (k.val + N - i.val) % N = L then τ peeled else τ k
  have hτ' : cyclicRestrictₗ hN L i τ' ψ = cyclicRestrictₗ hN L i τ ψ := by
    ext σ
    simp only [cyclicRestrictₗ_apply]
    congr 1
    ext k
    simp only [cyclicCfg]
    by_cases hsmall : (k.val + N - i.val) % N < L
    · rw [dif_pos hsmall, dif_pos hsmall]
    · rw [dif_neg hsmall, dif_neg hsmall]
      by_cases hlast : (k.val + N - i.val) % N = L
      · have hk : k = peeled :=
          eq_cyclic_site_of_offset_eq hN hlast
        simp [τ', hk]
      · simp [τ', hlast]
  have hbig := hψ i τ
  have hleft := groundSpace_inLeftGround A L hbig (τ peeled)
  rw [cyclicRestrictₗ_restrictLast hN i τ ψ (τ peeled)] at hleft
  exact hτ' ▸ hleft

/-- The periodic chain ground space is antitone in the interaction range: longer
cyclic windows imply all shorter cyclic-window constraints. -/
theorem chainGroundSpace_le_chainGroundSpace_of_le (A : MPSTensor d D)
    {L' L N : ℕ} (hN : 0 < N) (hL'L : L' ≤ L) (hLN : L ≤ N) :
    chainGroundSpace A L N ≤ chainGroundSpace A L' N := by
  have claim : ∀ m : ℕ, L' + m ≤ N →
      chainGroundSpace A (L' + m) N ≤ chainGroundSpace A L' N := by
    intro m
    induction m with
    | zero =>
        intro _ ψ hψ
        simpa using hψ
    | succ m ih =>
        intro hmN
        exact le_trans
          (by
            simpa [Nat.add_assoc] using
              chainGroundSpace_le_chainGroundSpace_succ (A := A) hN
                (L := L' + m) (by omega : L' + m + 1 ≤ N))
          (ih (by omega))
  have hEq : L' + (L - L') = L := Nat.add_sub_of_le hL'L
  simpa [hEq] using claim (L - L') (by omega : L' + (L - L') ≤ N)

/-! ### Unique ground state -/

/-- A submodule has a unique ground state (up to scalar) if its dimension is exactly 1. -/
def HasUniqueGroundState {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S : Submodule ℂ V) : Prop :=
  Module.finrank ℂ S = 1

/-- Characterization: a unique ground state is generated by a single nonzero vector. -/
theorem hasUniqueGroundState_iff_proportional {V : Type*} [AddCommGroup V] [Module ℂ V]
    {S : Submodule ℂ V} [FiniteDimensional ℂ S] :
    HasUniqueGroundState S ↔
      ∃ ψ₀ : S, ψ₀ ≠ 0 ∧ ∀ ψ : S, ∃ c : ℂ, ψ = c • ψ₀ := by
  constructor
  · intro hS
    have hpos : 0 < Module.finrank ℂ S := by
      rw [hS]
      norm_num
    obtain ⟨ψ₀, hψ₀⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    refine ⟨ψ₀, hψ₀, ?_⟩
    have hgen : ∀ ψ : S, ∃ c : ℂ, c • ψ₀ = ψ :=
      (finrank_eq_one_iff_of_nonzero' ψ₀ hψ₀).mp hS
    intro ψ
    obtain ⟨c, hc⟩ := hgen ψ
    exact ⟨c, hc.symm⟩
  · rintro ⟨ψ₀, hψ₀, hgen⟩
    exact (finrank_eq_one_iff_of_nonzero' ψ₀ hψ₀).2 fun ψ => by
      obtain ⟨c, hc⟩ := hgen ψ
      exact ⟨c, hc.symm⟩

/-! ### Helper: MPV nonvanishing for block-injective tensors -/

/-- If all products of some positive length `k` are zero and `A` is `L₀`-block-injective
with `L₀ > 0`, we reach a contradiction.

**Descent argument**: if `k ≤ L₀`, factor every length-`L₀` word through a zero
length-`k` prefix; if `k > L₀`, use `wordSpan A L₀ = M_D` with `M = 1` to show
all length-(`k − L₀`) products are zero, then recurse. -/
private theorem allZero_contradiction [NeZero D]
    {A : MPSTensor d D} {L₀ : ℕ} (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    {k : ℕ} (hk : 0 < k)
    (hzero : ∀ w : List (Fin d), w.length = k → evalWord A w = 0) : False := by
  have hws : wordSpan A L₀ = ⊤ := (wordSpan_eq_top_iff_isNBlkInjective A L₀).mpr hInj
  -- Strong induction on k.
  suffices ∀ k, 0 < k → (∀ w : List (Fin d), w.length = k → evalWord A w = 0) → False from
    this k hk hzero
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk_pos hk_zero
    by_cases hkL : k ≤ L₀
    · -- Case k ≤ L₀: factor every length-L₀ word as (take k) ++ (drop k).
      have hws_bot : wordSpan A L₀ = ⊥ := by
        rw [eq_bot_iff, wordSpan]
        apply Submodule.span_le.mpr
        rintro _ ⟨σ, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_bot]
        have hsplit := List.take_append_drop k (List.ofFn σ)
        have htake_len : (List.take k (List.ofFn σ)).length = k := by
          rw [List.length_take]; simp; omega
        calc evalWord A (List.ofFn σ)
            = evalWord A (List.take k (List.ofFn σ) ++
                List.drop k (List.ofFn σ)) := by rw [hsplit]
          _ = evalWord A (List.take k (List.ofFn σ)) *
                evalWord A (List.drop k (List.ofFn σ)) := evalWord_append ..
          _ = 0 * evalWord A (List.drop k (List.ofFn σ)) := by
                rw [hk_zero _ htake_len]
          _ = 0 := zero_mul _
      exact absurd (hws ▸ hws_bot) top_ne_bot
    · -- Case k > L₀: use span = M_D and M = 1 to descend to k - L₀.
      push Not at hkL
      have hkL₀_pos : 0 < k - L₀ := by omega
      apply ih (k - L₀) (by omega) hkL₀_pos
      intro w₂ hw₂
      -- For each σ₁ of length L₀: evalWord A (ofFn σ₁) * evalWord A w₂ = 0.
      have hmul_zero : ∀ σ₁ : Fin L₀ → Fin d,
          evalWord A (List.ofFn σ₁) * evalWord A w₂ = 0 := by
        intro σ₁
        have hlen : (List.ofFn σ₁ ++ w₂).length = k := by simp [hw₂]; omega
        have := hk_zero _ hlen
        rwa [evalWord_append] at this
      -- The map M ↦ M * evalWord A w₂ vanishes on wordSpan A L₀ = ⊤.
      have hright : LinearMap.mulRight ℂ (evalWord A w₂) = 0 := by
        apply LinearMap.ext_on_range
          (v := fun σ : Fin L₀ → Fin d => evalWord A (List.ofFn σ))
          (hv := by rwa [← wordSpan])
        intro σ₁
        simp [LinearMap.mulRight_apply, hmul_zero σ₁]
      -- Taking M = 1: evalWord A w₂ = 0.
      have h1 : (1 : Matrix (Fin D) (Fin D) ℂ) * evalWord A w₂ = 0 :=
        show LinearMap.mulRight ℂ (evalWord A w₂) 1 = 0 by rw [hright]; simp
      simpa using h1

/-- For a block-injective tensor, the MPV is nonzero on chains of sufficient length.

Assuming `mpv = 0` (all trace products of length `N` vanish), factor through
`wordSpan A L₀ = M_D` to force all length-(`N − L₀`) products to zero, then
`allZero_contradiction` gives the contradiction. -/
theorem mpv_ne_zero_of_isNBlkInjective {A : MPSTensor d D} [NeZero D]
    {L₀ : ℕ} (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    {N : ℕ} (hN : L₀ + 1 ≤ N) :
    (mpv A : NSiteSpace d N) ≠ 0 := by
  have hws : wordSpan A L₀ = ⊤ := (wordSpan_eq_top_iff_isNBlkInjective A L₀).mpr hInj
  intro hzero
  -- mpv = 0 means tr(evalWord A (List.ofFn σ)) = 0 for all σ : Fin N → Fin d.
  have htr_zero : ∀ σ : Fin N → Fin d,
      Matrix.trace (evalWord A (List.ofFn σ)) = 0 := by
    intro σ; simpa [mpv, coeff] using congrFun hzero σ
  -- All products of length (N - L₀) are zero by trace nondegeneracy.
  have hprod_zero : ∀ w₂ : List (Fin d), w₂.length = N - L₀ →
      evalWord A w₂ = 0 := by
    intro w₂ hw₂
    -- Show ∀ M, tr(evalWord A w₂ * M) = 0 to get evalWord A w₂ = 0.
    apply trace_mul_right_eq_zero
    intro M
    -- The functional P ↦ tr(P * evalWord A w₂) vanishes on wordSpan A L₀ = ⊤.
    have hφ : (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
        (LinearMap.mulRight ℂ (evalWord A w₂)) = 0 := by
      apply LinearMap.ext_on_range
        (v := fun σ : Fin L₀ → Fin d => evalWord A (List.ofFn σ))
        (hv := by rwa [← wordSpan])
      intro σ₁
      simp only [LinearMap.comp_apply, LinearMap.mulRight_apply,
        Matrix.traceLinearMap_apply]
      -- tr(evalWord A (List.ofFn σ₁) * evalWord A w₂) = tr(evalWord A (σ₁ ++ w₂))
      rw [← evalWord_append]
      -- This is a trace of a length-N word product, hence 0.
      have hlen : (List.ofFn σ₁ ++ w₂).length = N := by simp [hw₂]; omega
      let σ' : Fin N → Fin d :=
        fun i => (List.ofFn σ₁ ++ w₂).get ⟨i.val, hlen.symm ▸ i.isLt⟩
      have hw_eq : List.ofFn σ' = List.ofFn σ₁ ++ w₂ := by
        apply List.ext_get
        · simp [hw₂]; omega
        · intro i h1 h2; simp [σ']
      rw [← hw_eq]
      exact htr_zero σ'
    -- From hφ: ∀ P, tr(P * evalWord A w₂) = 0. By trace commutativity:
    calc Matrix.trace (evalWord A w₂ * M)
        = Matrix.trace (M * evalWord A w₂) := Matrix.trace_mul_comm ..
      _ = 0 := by
          simpa [Matrix.traceLinearMap_apply] using congrArg (· M) hφ
  exact allZero_contradiction hInj hL₀ (by omega : 0 < N - L₀) hprod_zero

/-- A positive block-injectivity length over nonzero virtual dimension forces the
physical alphabet to be nonempty. -/
private theorem neZero_d_of_isNBlkInjective [NeZero D]
    {A : MPSTensor d D} {L₀ : ℕ} (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) :
    NeZero d := by
  by_contra h
  simp only [not_neZero] at h
  subst h
  have hempty :
      Set.range (fun σ : Fin L₀ → Fin 0 => evalWord A (List.ofFn σ)) = ∅ := by
    ext M
    constructor
    · rintro ⟨σ, _⟩
      exact (σ ⟨0, hL₀⟩).elim0
    · intro hM
      cases hM
  rw [IsNBlkInjective, hempty, Submodule.span_empty] at hInj
  exact bot_ne_top hInj

/-- Open-chain range reduction for block-injective tensors.

If all contiguous windows of size `L₀ + 1` lie in the corresponding MPS ground
space, then the full open chain lies in `groundSpace A N`.  This is the
chain-level iteration of `groundSpace_extend_right_of_isNBlkInjective`; it is the
open-boundary half of the normal parent-Hamiltonian range reduction. -/
theorem contiguous_mem_groundSpace_of_isNBlkInjective
    {A : MPSTensor d D} [NeZero D] {L₀ N : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hLN : L₀ + 1 ≤ N)
    {ψ : NSiteSpace d N}
    (hwindow : ∀ (s : ℕ) (hs : s + (L₀ + 1) ≤ N) (τ : Fin N → Fin d),
      contiguousRestrictₗ s (L₀ + 1) hs τ ψ ∈ groundSpace A (L₀ + 1)) :
    ψ ∈ groundSpace A N := by
  haveI : NeZero d := neZero_d_of_isNBlkInjective hInj hL₀
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  let τ₀ : Fin N → Fin d := fun _ => ⟨0, hd⟩
  have claim : ∀ K : ℕ, ∀ (s : ℕ) (hs : s + (K + L₀ + 1) ≤ N)
      (τ : Fin N → Fin d),
      contiguousRestrictₗ s (K + L₀ + 1) hs τ ψ ∈ groundSpace A (K + L₀ + 1) := by
    intro K
    induction K with
    | zero =>
        intro s hs τ
        have hEq0 : L₀ + 1 = 0 + L₀ + 1 := by omega
        have hs₀ : s + (L₀ + 1) ≤ N := by omega
        rw [← contiguousRestrictₗ_reindex_window (d := d) hEq0 hs₀ hs τ ψ]
        exact reindexSites_mem_groundSpace hEq0 (hwindow s hs₀ τ)
    | succ K ih =>
        intro s hs τ
        apply groundSpace_extend_right_of_isNBlkInjective (A := A) (K := K + 1) hInj hL₀
        · intro j
          rw [contiguousRestrictₗ_restrictLast]
          have hEq : K + L₀ + 1 = (K + 1) + L₀ := by omega
          let τj := Function.update τ ⟨s + ((K + 1) + L₀), by omega⟩ j
          have hs₁ : s + (K + L₀ + 1) ≤ N := by omega
          have hs₂ : s + ((K + 1) + L₀) ≤ N := by omega
          rw [← contiguousRestrictₗ_reindex_window (d := d) hEq hs₁ hs₂ τj ψ]
          exact reindexSites_mem_groundSpace hEq (ih s hs₁ τj)
        · intro u
          have hsTail : s + ((K + 1) + (L₀ + 1)) ≤ N := by omega
          change tailRestrictₗ u
              (contiguousRestrictₗ s ((K + 1) + (L₀ + 1)) hsTail τ ψ) ∈
            groundSpace A (L₀ + 1)
          rw [tailRestrictₗ_contiguousRestrictₗ (d := d) (s := s) (K := K + 1)
            (L := L₀ + 1) hsTail u τ ψ]
          exact hwindow (s + (K + 1)) (by omega) _
  have hK : N - (L₀ + 1) + L₀ + 1 = N := by omega
  have hmemK := claim (N - (L₀ + 1)) 0 (by omega) τ₀
  have hmemN := reindexSites_mem_groundSpace hK hmemK
  have hfull :
      reindexSites hK
        (contiguousRestrictₗ 0 (N - (L₀ + 1) + L₀ + 1) (by omega) τ₀ ψ) = ψ := by
    ext σ
    simp only [reindexSites_apply, contiguousRestrictₗ_apply]
    congr 1
    ext k
    simp only [contiguousCfg]
    rw [dif_pos (show 0 ≤ k.val ∧ k.val < 0 + (N - (L₀ + 1) + L₀ + 1) by omega)]
    congr 1
  rwa [hfull] at hmemN

/-- Cyclic reduced-window constraints imply open-chain ground-space membership for
block-injective tensors.

This combines cyclic window monotonicity (peeling longer cyclic windows down to
`L₀ + 1`), the non-wrapping cyclic/contiguous identification, and the
open-chain range-reduction argument for block-injective tensors. It stops at
open-chain membership; the wrapped-boundary scalarity step remains separate. -/
theorem chainGroundSpace_le_groundSpace_of_isNBlkInjective
    {A : MPSTensor d D} [NeZero D] {L₀ L N : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    (hN : 0 < N) (hL : L₀ < L) (hLN : L ≤ N) :
    chainGroundSpace A L N ≤ groundSpace A N := by
  intro ψ hψ
  have hL₀N : L₀ + 1 ≤ N := by omega
  have hψred : ψ ∈ chainGroundSpace A (L₀ + 1) N :=
    chainGroundSpace_le_chainGroundSpace_of_le (A := A) hN (by omega : L₀ + 1 ≤ L) hLN hψ
  rw [chainGroundSpace, dif_pos ⟨hN, hL₀N⟩] at hψred
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hψred
  apply contiguous_mem_groundSpace_of_isNBlkInjective hInj hL₀ hL₀N
  intro s hs τ
  rw [← cyclicRestrictₗ_eq_contiguousRestrictₗ hN hL₀N
    (show (⟨s, by omega⟩ : Fin N).val + (L₀ + 1) ≤ N from hs)]
  exact hψred ⟨s, by omega⟩ τ

/-! ### Helper: vanishing on all word products implies zero -/

/-- If `X` has the property that `tr(evalWord A w * X) = 0` for all words of
length `k` (with `k ≥ 1` and `A` injective), then `X = 0`. -/
private theorem eq_zero_of_trace_evalWord_mul_eq_zero {A : MPSTensor d D}
    (hA : IsInjective A) {k : ℕ} (hk : 0 < k)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (h : ∀ σ : Fin k → Fin d,
      Matrix.trace (evalWord A (List.ofFn σ) * X) = 0) :
    X = 0 := by
  have hwordK : wordSpan A k = ⊤ := wordSpan_eq_top_of_isInjective hA hk
  have hφ :
      (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp (LinearMap.mulRight ℂ X) = 0 := by
    apply LinearMap.ext_on_range
      (v := fun σ : Fin k → Fin d => evalWord A (List.ofFn σ))
    · simpa [wordSpan] using hwordK
    · intro σ
      simp [Matrix.traceLinearMap_apply, h σ]
  exact trace_mul_right_eq_zero fun N => by
    have hNX : Matrix.trace (N * X) = 0 := by
      simpa [Matrix.traceLinearMap_apply] using congrArg (fun f => f N) hφ
    calc Matrix.trace (X * N) = Matrix.trace (N * X) := Matrix.trace_mul_comm X N
    _ = 0 := hNX

/-! ### Uniqueness theorems -/

/-- On a periodic chain, the injective parent-Hamiltonian ground space
coincides with the span of the MPV when the window size satisfies `L ≥ 2`.

For injective tensors, the open-chain intersection argument requires only
a window of at least `2` sites. -/
theorem chainGroundSpace_eq_mpvSubmodule {A : MPSTensor d D} [NeZero D]
    (hA : IsInjective A) {L N : ℕ} (hN : 2 ≤ N) (hL : 1 < L) (hLN : L ≤ N) :
    chainGroundSpace A L N = mpvSubmodule A N := by
  have hN0 : 0 < N := by omega
  haveI : NeZero d := neZero_d_of_isInjective hA
  apply le_antisymm
  · -- ⊆ direction: chainGroundSpace ≤ mpvSubmodule
    intro ψ hψ
    rw [chainGroundSpace, dif_pos ⟨hN0, hLN⟩] at hψ
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hψ
    -- Step 1: ψ ∈ groundSpace A N (via non-wrapping windows)
    have hψGS : ψ ∈ groundSpace A N := by
      apply contiguous_mem_groundSpace hA hL hLN
      intro s hs τ
      rw [← cyclicRestrictₗ_eq_contiguousRestrictₗ hN0 hLN
        (show (⟨s, by omega⟩ : Fin N).val + L ≤ N from hs)]
      exact hψ ⟨s, by omega⟩ τ
    -- Step 2: ψ = groundSpaceMap A N X for some X
    rw [groundSpace, LinearMap.mem_range] at hψGS
    obtain ⟨X, hX⟩ := hψGS
    -- Step 3: X commutes with all A j (wrapping window constraint)
    have hComm : ∀ j : Fin d, X * A j = A j * X := by
      apply boundary_matrix_commutes hA hN hL hLN
      intro i τ
      rw [show groundSpaceMap A N X = ψ from hX]
      exact hψ i τ
    -- Step 4: X is scalar (center argument)
    have hCenter : X ∈ Set.center (Matrix (Fin D) (Fin D) ℂ) := by
      rw [Semigroup.mem_center_iff]
      intro M
      have hext : LinearMap.mulLeft ℂ X = LinearMap.mulRight ℂ X := by
        apply LinearMap.ext_on_range (v := A) (hv := hA.span_eq_top)
        intro j
        simp only [LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
        exact hComm j
      have := LinearMap.congr_fun hext M
      simp only [LinearMap.mulLeft_apply, LinearMap.mulRight_apply] at this
      exact this.symm
    rw [Matrix.center_eq_range] at hCenter
    obtain ⟨c, hc⟩ := hCenter
    have hX_eq : X = c • (1 : Matrix (Fin D) (Fin D) ℂ) := by
      rw [← hc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
    -- Step 5: ψ = c • mpv A
    rw [mpvSubmodule]
    rw [Submodule.mem_span_singleton]
    refine ⟨c, ?_⟩
    rw [← hX]
    ext σ
    simp only [groundSpaceMap_apply, Pi.smul_apply, smul_eq_mul, mpv, coeff]
    rw [hX_eq, Algebra.mul_smul_comm, mul_one, Matrix.trace_smul, smul_eq_mul]
  · -- ⊇ direction: mpvSubmodule ≤ chainGroundSpace
    intro ψ hψ
    rw [mpvSubmodule, Submodule.mem_span_singleton] at hψ
    obtain ⟨c, rfl⟩ := hψ
    exact Submodule.smul_mem _ c (mpv_mem_chainGroundSpace A L N hN0 hLN)

/-- Range-reduction bridge for normal tensors.

This is the missing hard direction of `chainGroundSpace_eq_mpvSubmodule_normal`:
for a normal tensor with an `L₀`-block-injective presentation, the reduced
periodic window constraints `L > L₀` already force a chain ground state to lie
in the MPV line. -/
theorem chainGroundSpace_le_mpvSubmodule_of_normal_range_reduction
    {A : MPSTensor d D} [NeZero D]
    (_hA : IsNormal A) {L₀ : ℕ} (_hInj : IsNBlkInjective A L₀)
    {L N : ℕ} (_hN : 2 ≤ N) (_hL : L₀ < L) (_hLN : L ≤ N) :
    chainGroundSpace A L N ≤ mpvSubmodule A N := by
  -- Missing bridge: the normal-form range-reduction theorem for periodic
  -- windows. It should turn the `L₀ + 1` cyclic-window constraints into the
  -- same boundary-matrix commutation conclusion used by
  -- `chainGroundSpace_eq_mpvSubmodule`.
  sorry

/-- On a periodic chain, the normal parent-Hamiltonian ground space coincides
with the span of the MPV with the reduced window `L > L₀` (instead of `2L₀`).

The normality hypothesis enables the range reduction from `2L₀` to `L₀ + 1`
via the structure theory of normal MPS (peripheral spectrum, canonical form).
See [CPGSV21] arXiv:2011.12127 §IV.C. -/
-- TODO(parent-hamiltonian): derive using the normal-form range reduction and
-- the cyclic-window definition of `chainGroundSpace`.
theorem chainGroundSpace_eq_mpvSubmodule_normal {A : MPSTensor d D} [NeZero D]
    (hA : IsNormal A) {L₀ : ℕ} (hInj : IsNBlkInjective A L₀)
    {L N : ℕ} (hN : 2 ≤ N) (hL : L₀ < L) (hLN : L ≤ N) :
    chainGroundSpace A L N = mpvSubmodule A N := by
  apply le_antisymm
  · exact chainGroundSpace_le_mpvSubmodule_of_normal_range_reduction
      hA hInj hN hL hLN
  · intro ψ hψ
    rw [mpvSubmodule, Submodule.mem_span_singleton] at hψ
    obtain ⟨c, rfl⟩ := hψ
    exact Submodule.smul_mem _ c (mpv_mem_chainGroundSpace A L N (by omega) hLN)

/-- **Unique ground state on the periodic chain** for injective MPS.

For an injective tensor `A` on a periodic chain of `N ≥ 2` sites, the chain ground
space is one-dimensional, spanned by the MPV.

The proof uses the intersection property iteratively:
1. From the intersection property, any state in the chain ground space has the form
   `ψ(σ) = tr(A^σ · X)` for some `X ∈ M_D(ℂ)`.
2. The wrapping window condition (window crossing the periodic boundary) constrains
   `X` to commute with all `A^i`.
3. For injective `A`, the center of `span{A^i} = M_D(ℂ)` consists only of scalars,
   so `X = c · I` and `ψ = c · mpv A`. -/
theorem groundSpace_unique_periodic {A : MPSTensor d D} [NeZero D] (hA : IsInjective A)
    {L N : ℕ} (hN : 2 ≤ N) (hL : 1 < L) (hLN : L ≤ N) :
    HasUniqueGroundState (chainGroundSpace A L N) := by
  rw [HasUniqueGroundState, chainGroundSpace_eq_mpvSubmodule hA hN hL hLN]
  have hmpv : (mpv A : NSiteSpace d N) ≠ 0 := by
    intro hzero
    have hEq :
        groundSpaceMap A N (1 : Matrix (Fin D) (Fin D) ℂ) =
          groundSpaceMap A N (0 : Matrix (Fin D) (Fin D) ℂ) := by
      simpa [mpv_eq_groundSpaceMap_one A N] using hzero
    have h10 : (1 : Matrix (Fin D) (Fin D) ℂ) = 0 :=
      (groundSpaceMap_injective hA (by omega : 0 < N)) hEq
    exact one_ne_zero h10
  simpa [mpvSubmodule] using finrank_span_singleton (K := ℂ) hmpv

/-- **Unique ground state for `L₀`-block-injective tensors on `2L₀` sites**.

If `A` is `L₀`-block-injective with `L₀ > 0`, the parent Hamiltonian with
interaction range `2L₀` on a periodic chain of `N ≥ 2L₀` sites has a unique
ground state.

**Proof sketch**: First rewrite the chain ground space as the MPV submodule
using `chainGroundSpace_eq_mpvSubmodule_normal`, applying normality obtained
from block injectivity. Then use `mpv_ne_zero_of_isNBlkInjective` to show the
MPV submodule is one-dimensional. -/
theorem parentHamiltonian_unique_gs_injective {A : MPSTensor d D} [NeZero D]
    {L₀ : ℕ} (hA : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    {N : ℕ} (hN : 2 * L₀ ≤ N) :
    HasUniqueGroundState (chainGroundSpace A (2 * L₀) N) := by
  have hNormal : IsNormal A := ⟨L₀, hA⟩
  have hN' : L₀ + 1 ≤ N := by omega
  rw [HasUniqueGroundState,
    chainGroundSpace_eq_mpvSubmodule_normal hNormal hA (by omega) (by omega) hN]
  have hmpv := mpv_ne_zero_of_isNBlkInjective hA hL₀ hN'
  simpa [mpvSubmodule] using finrank_span_singleton (K := ℂ) hmpv

/-- **Optimal unique ground state for normal tensors on `L₀ + 1` sites**.

If `A` is normal and `L₀`-block-injective with `L₀ > 0`, the interaction range
can be reduced from `2L₀` to `L₀ + 1`. The chain ground space with window
`L₀ + 1` on `N ≥ L₀ + 1` sites has a unique ground state.

The proof rewrites via `chainGroundSpace_eq_mpvSubmodule_normal`, then uses
`mpv_ne_zero_of_isNBlkInjective` to show the MPV submodule is 1D. -/
theorem parentHamiltonian_unique_gs_normal {A : MPSTensor d D} [NeZero D]
    {L₀ : ℕ} (hA : IsNormal A) (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    {N : ℕ} (hN : L₀ + 1 ≤ N) :
    HasUniqueGroundState (chainGroundSpace A (L₀ + 1) N) := by
  rw [HasUniqueGroundState,
    chainGroundSpace_eq_mpvSubmodule_normal hA hInj (by omega) (by omega) hN]
  have hmpv := mpv_ne_zero_of_isNBlkInjective hInj hL₀ hN
  simpa [mpvSubmodule] using finrank_span_singleton (K := ℂ) hmpv

end MPSTensor
