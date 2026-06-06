/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.Basic
import TNLean.MPS.ParentHamiltonian.BoundaryOverlap
import TNLean.MPS.ParentHamiltonian.CyclicWindow
import TNLean.MPS.ParentHamiltonian.ExtendRight
import TNLean.MPS.ParentHamiltonian.Nonvanishing
import TNLean.MPS.ParentHamiltonian.RestrictTransport
import TNLean.MPS.ParentHamiltonian.WrappingWindow
import TNLean.MPS.FundamentalTheorem.FiniteLength
import TNLean.Algebra.TracePairing
import TNLean.Wielandt.SpanGrowth.CumulativeToWordSpan

/-!
# Unique ground state for injective MPS parent Hamiltonians

For an injective MPS tensor `A` on a periodic chain, the expected parent-Hamiltonian
ground space is spanned by the MPS vector
`σ ↦ tr(A^{σ₀} ⋯ A^{σ_{N-1}})`.

## Overview

The proof combines the intersection property with the periodic boundary
condition:

1. **Open chain**: By iterated application of the intersection property,
   any state satisfying all local ground-space conditions has the form
   \(\psi(\sigma)=\operatorname{tr}(A^\sigma X)\) for some boundary
   matrix \(X \in M_D(\mathbb C)\). This yields a \(D^2\)-dimensional space.

2. **Periodic chain**: The boundary condition obtained when closing the
   periodic chain constrains \(X\). For injective \(A\), the one-site matrices
   span \(M_D(\mathbb C)\), so the commutation condition forces \(X\) to be
   scalar, yielding a one-dimensional ground space spanned by the MPS vector.

## Main results

The formal statements define the periodic-chain ground space, prove that the
MPS vector lies in it, reduce cyclic constraints to an open-chain boundary matrix,
and show that the boundary-closing comparison forces the boundary matrix to be
scalar. The final statements record uniqueness for injective tensors and the
range \(L_0+1\) uniqueness theorem for normal tensors.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2021] arXiv:2011.12127,
  Section IV.C, lines 1976--2094 (parent Hamiltonian definition and uniqueness
  argument)
* [FNW92] Sections 3–4
* [PGVWC07] arXiv:quant-ph/0608197, Sections 5–6

## Remaining mathematical ingredients

The remaining boundary-closing ingredient is the passage from
\[
  A^\mu A^j X=Y^+_{\tau^+_\eta(\mu)}A^j,\qquad
  X A^j A^\mu=A^jY^-_{\tau^-_\eta(\mu)}
\]
to
\[
  Y^+_{\tau^+_\eta(\mu)}=Y^-_{\tau^-_\eta(\mu)}
\]
for the same complementary-site word \(\mu\); see arXiv:2011.12127,
Section IV.C, lines 2078--2090.

The open-chain build-up follows the inverting-and-growing-back argument from
arXiv:2011.12127, Section IV.C, lines 2049--2078.  The normal case also uses the
Wielandt span-growth theorem to pass from a cumulative span conclusion to the
fixed-length word-span theorem used to make the open-chain boundary matrix
scalar.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ### The MPS submodule -/

/-- The submodule spanned by the MPS vector.

On the periodic chain, the MPS vector is `σ ↦ tr(A^{σ₀} ⋯ A^{σ_{N-1}})`,
which corresponds to the ground-space map applied to the identity:
`mpv A = groundSpaceMap A N 1`. -/
noncomputable def mpvSubmodule (A : MPSTensor d D) (N : ℕ) :
    Submodule ℂ (NSiteSpace d N) :=
  Submodule.span ℂ {mpv A}

/-- The MPS vector is the ground-space map applied to the identity matrix. -/
theorem mpv_eq_groundSpaceMap_one (A : MPSTensor d D) (N : ℕ) :
    (mpv A : NSiteSpace d N) = groundSpaceMap A N 1 := by
  ext σ
  simp [mpv, coeff, groundSpaceMap_apply]

/-- The MPS vector lies in the ground space `G_N(A)` for any `N`. -/
theorem mpv_mem_groundSpace (A : MPSTensor d D) (N : ℕ) :
    (mpv A : NSiteSpace d N) ∈ groundSpace A N := by
  rw [groundSpace, LinearMap.mem_range]
  exact ⟨1, by ext σ; simp [groundSpaceMap_apply, mpv, coeff]⟩

/-! ### Periodic chain ground space

On a periodic chain of `N` sites, the ground space of the parent Hamiltonian
is the set of states whose restriction to every cyclic window of `L` consecutive
sites lies in `G_L(A)`.

For the nondegenerate regime used below, this is the intersection of all cyclic
window constraints. The subsequent theorems state their nondegeneracy assumptions
explicitly. -/

/-- The periodic chain ground space: the set of states `ψ` on `N` sites such
that every cyclic window of `L` consecutive sites restricts into `G_L(A)`.

When `N = 0` or `L > N`, we return `⊤` as a degenerate convention. -/
noncomputable def chainGroundSpace (A : MPSTensor d D) (L N : ℕ) :
    Submodule ℂ (NSiteSpace d N) :=
  if hN : 0 < N ∧ L ≤ N then
    ⨅ (i : Fin N) (τ : Fin N → Fin d),
      (groundSpace A L).comap (cyclicRestrictₗ hN.1 L i τ)
  else ⊤

/-- The MPS vector is in the chain ground space.

The proof uses trace cyclicity: for each cyclic window at position `i`, the
restriction of the MPS vector to that window equals `groundSpaceMap A L X_τ` where
`X_τ` is the product of `A`-matrices at outside positions. The cyclic list
verification follows from the window-level membership calculation. -/
theorem mpv_mem_chainGroundSpace (A : MPSTensor d D) (L N : ℕ)
    (hN : 0 < N) (hLN : L ≤ N) :
    (mpv A : NSiteSpace d N) ∈ chainGroundSpace A L N := by
  rw [chainGroundSpace, dif_pos ⟨hN, hLN⟩]
  simp only [Submodule.mem_iInf, Submodule.mem_comap]
  intro i τ
  simpa [cyclicRestrictₗ_apply, cyclicCfg, replaceWindow] using
    mpv_window_mem_groundSpace A L N hLN i τ

/-- Every constrained cyclic window of a chain-ground-space vector has a boundary
matrix representation in the local MPS ground space. -/
theorem chainGroundSpace_window_witnesses (A : MPSTensor d D)
    {L N : ℕ} (hN : 0 < N) (hLN : L ≤ N)
    {ψ : NSiteSpace d N} (hψ : ψ ∈ chainGroundSpace A L N) :
    ∃ YAt : (i : Fin N) → (Fin N → Fin d) → Matrix (Fin D) (Fin D) ℂ,
      ∀ (i : Fin N) (τ : Fin N → Fin d),
        cyclicRestrictₗ hN L i τ ψ = groundSpaceMap A L (YAt i τ) := by
  rw [chainGroundSpace, dif_pos ⟨hN, hLN⟩] at hψ
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hψ
  have hLocal : ∀ (i : Fin N) (τ : Fin N → Fin d),
      ∃ Y : Matrix (Fin D) (Fin D) ℂ,
        cyclicRestrictₗ hN L i τ ψ = groundSpaceMap A L Y := by
    intro i τ
    have hmem := hψ i τ
    rw [groundSpace, LinearMap.mem_range] at hmem
    obtain ⟨Y, hY⟩ := hmem
    exact ⟨Y, hY.symm⟩
  choose YAt hYAt using hLocal
  exact ⟨YAt, hYAt⟩

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

/-- Open-chain intersection property for block-injective tensors.

If all contiguous windows of size `L₀ + 1` lie in the corresponding MPS ground
space, then the full open chain lies in `groundSpace A N`.  This is the
chain-level iteration of the inverting and growing-back argument in
arXiv:2011.12127, Section IV.C. -/
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
open-chain membership; the boundary-closing scalarity step remains separate. -/
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

/-! ### Vanishing on all word products implies zero -/

/-- If \(X\) has the property that \(\operatorname{tr}(A^w X)=0\) for all words
of length \(k\), with \(k \ge 1\) and \(A\) injective, then \(X=0\). -/
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
coincides with `ℂ V^{(N)}(A)` when the window size satisfies `L ≥ 2`.

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
    -- Step 3: X commutes with all A j (periodic boundary condition)
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

/-- Reduced cyclic constraints give the two cyclic-window compatibility families
at the boundary for an open-chain boundary matrix.

After the cyclic-to-open-chain step writes a periodic-chain vector as
\(\psi=\Gamma_N(X)\), the two reduced cyclic windows used when closing the
boundary expose the boundary matrix \(X\) on opposite sides of the same
length \(N-(L₀+1)\) complement word. This theorem gives the local algebraic
output needed for the remaining boundary-closing comparison
(arXiv:2011.12127, Section IV.C, lines 2078--2090). -/
theorem chainGroundSpace_wrapped_boundary_compatibilities_of_isNBlkInjective
    {A : MPSTensor d D} [NeZero D] {L₀ L N : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    (hN : 2 ≤ N) (hL : L₀ < L) (hLN : L ≤ N)
    {ψ : NSiteSpace d N} {X : Matrix (Fin D) (Fin D) ℂ}
    (hψ : ψ ∈ chainGroundSpace A L N) (hψX : ψ = groundSpaceMap A N X) :
    ∃ Ywrap Ymirror : (Fin N → Fin d) → Matrix (Fin D) (Fin D) ℂ,
      (∀ (j : Fin d) (τ : Fin N → Fin d),
        evalWord A (List.ofFn (fun k : Fin (N - (L₀ + 1)) =>
          τ ⟨k.val + L₀, by omega⟩)) * A j * X = Ywrap τ * A j) ∧
      (∀ (j : Fin d) (τ : Fin N → Fin d),
        X * A j * evalWord A (List.ofFn (fun k : Fin (N - (L₀ + 1)) =>
          τ ⟨k.val + 1, by omega⟩)) = A j * Ymirror τ) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hN0 : 0 < M + 1 := by omega
  have hL₀N : L₀ + 1 ≤ M + 1 := by omega
  have hM : L₀ ≤ M := by omega
  have hψmap : groundSpaceMap A (M + 1) X ∈ chainGroundSpace A L (M + 1) := by
    simpa [hψX] using hψ
  have hψred : groundSpaceMap A (M + 1) X ∈ chainGroundSpace A (L₀ + 1) (M + 1) :=
    chainGroundSpace_le_chainGroundSpace_of_le (A := A) hN0
      (by omega : L₀ + 1 ≤ L) hLN hψmap
  rw [chainGroundSpace, dif_pos ⟨hN0, hL₀N⟩] at hψred
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hψred
  have hGSAt : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      ∃ Y : Matrix (Fin D) (Fin D) ℂ,
        ∀ σ_w : Fin (L₀ + 1) → Fin d,
          Matrix.trace (evalWord A (List.ofFn
            (cyclicCfg hN0 (L₀ + 1) i σ_w τ)) * X) =
          Matrix.trace (evalWord A (List.ofFn σ_w) * Y) := by
    intro i τ
    have hmem := hψred i τ
    rw [groundSpace, LinearMap.mem_range] at hmem
    obtain ⟨Y, hY⟩ := hmem
    refine ⟨Y, fun σ_w => ?_⟩
    have : cyclicRestrictₗ hN0 (L₀ + 1) i τ
        (groundSpaceMap A (M + 1) X) σ_w = groundSpaceMap A (L₀ + 1) Y σ_w := by
      rw [← hY]
    simp only [cyclicRestrictₗ_apply, groundSpaceMap_apply] at this
    exact this
  choose YAt hYAt using hGSAt
  let wrapPos : Fin (M + 1) := ⟨M, by omega⟩
  let mirrorPos : Fin (M + 1) := ⟨M + 1 - L₀, by omega⟩
  have hWrap := wrapping_window_compatibility_of_isNBlkInjective
    (A := A) hInj hL₀ hM (YAt wrapPos) (fun τ σ_w => hYAt wrapPos τ σ_w)
  have hMirror := wrapping_window_mirror_compatibility_of_isNBlkInjective
    (A := A) hInj hL₀ hM (YAt mirrorPos) (fun τ σ_w => hYAt mirrorPos τ σ_w)
  exact ⟨YAt wrapPos, YAt mirrorPos, hWrap, hMirror⟩

/-- Long-word commutation is enough to place an open-chain boundary vector in
`ℂ V^{(N)}(A)`.

After the reduced cyclic-window compatibilities at the boundary have been converted into a
family of identities \(XA^\omega=A^\omega X\) for one word length \(m \ge L₀\),
the existing block-stripping theorem makes \(X\) commute with the full matrix
algebra. Hence \(X\) is scalar and
\(\Gamma_N(X)\in \mathbb C\,V^{(N)}(A)\). -/
theorem groundSpaceMap_mem_mpvSubmodule_of_isNBlkInjective_of_long_word_commutes
    {A : MPSTensor d D} {L₀ m N : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hm : L₀ ≤ m)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (hComm : ∀ ω : Fin m → Fin d,
      X * evalWord A (List.ofFn ω) = evalWord A (List.ofFn ω) * X) :
    groundSpaceMap A N X ∈ mpvSubmodule A N := by
  have hAll : ∀ M : Matrix (Fin D) (Fin D) ℂ, X * M = M * X :=
    commutes_all_of_commutes_long_words_of_isNBlkInjective
      (A := A) hInj hL₀ hm hComm
  have hCenter : X ∈ Set.center (Matrix (Fin D) (Fin D) ℂ) := by
    rw [Semigroup.mem_center_iff]
    intro M
    exact (hAll M).symm
  rw [Matrix.center_eq_range] at hCenter
  obtain ⟨c, hc⟩ := hCenter
  have hX_eq : X = c • (1 : Matrix (Fin D) (Fin D) ℂ) := by
    rw [← hc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
  rw [mpvSubmodule, Submodule.mem_span_singleton]
  refine ⟨c, ?_⟩
  ext σ
  simp only [groundSpaceMap_apply, Pi.smul_apply, smul_eq_mul, mpv, coeff]
  rw [hX_eq, Algebra.mul_smul_comm, mul_one, Matrix.trace_smul, smul_eq_mul]

/-- The open-chain vector lies in \(\mathbb C\,V^{(N)}(A)\) when \(X\) commutes with words of
some positive length.

If \(X\) commutes with all words of any positive length \(m\), then chunking gives
commutation at the multiple \(L₀m\), which is at least \(L₀\). The long-word
centrality theorem then makes \(X\) scalar. -/
theorem groundSpaceMap_mem_mpvSubmodule_of_isNBlkInjective_of_positive_word_commutes
    {A : MPSTensor d D} {L₀ m N : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hm : 0 < m)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (hComm : ∀ ω : Fin m → Fin d,
      X * evalWord A (List.ofFn ω) = evalWord A (List.ofFn ω) * X) :
    groundSpaceMap A N X ∈ mpvSubmodule A N := by
  have hCommMul : ∀ ω : Fin (L₀ * m) → Fin d,
      X * evalWord A (List.ofFn ω) = evalWord A (List.ofFn ω) * X :=
    commutes_words_mul_of_commutes_words (A := A) (m := m) (q := L₀) hComm
  exact groundSpaceMap_mem_mpvSubmodule_of_isNBlkInjective_of_long_word_commutes
    (A := A) (L₀ := L₀) (m := L₀ * m) (N := N) hInj hL₀
    (Nat.le_mul_of_pos_right L₀ hm) hCommMul

/-- Two-sided compatibilities put the boundary vector in
\(\mathbb C\,V^{(N)}(A)\).

If
\[
  A^\mu A^j X = Y_\mu A^j,
  \qquad
  X A^j A^\mu = A^jY_\mu
\]
for the same matrix \(Y_\mu\), then positive-length commutation gives
\(\Gamma_N(X)\in \mathbb C\,V^{(N)}(A)\). -/
theorem groundSpaceMap_mem_mpvSubmodule_of_isNBlkInjective_of_two_sided_middle_compatibility
    {A : MPSTensor d D} {L₀ m N : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (Y : (Fin m → Fin d) → Matrix (Fin D) (Fin D) ℂ)
    (hLeft : ∀ (j : Fin d) (μ : Fin m → Fin d),
      evalWord A (List.ofFn μ) * A j * X = Y μ * A j)
    (hRight : ∀ (j : Fin d) (μ : Fin m → Fin d),
      X * A j * evalWord A (List.ofFn μ) = A j * Y μ) :
    groundSpaceMap A N X ∈ mpvSubmodule A N := by
  have hComm : ∀ ω : Fin (m + 2) → Fin d,
      X * evalWord A (List.ofFn ω) = evalWord A (List.ofFn ω) * X :=
    commutes_words_of_two_sided_middle_compatibility (A := A) (X := X) Y hLeft hRight
  exact groundSpaceMap_mem_mpvSubmodule_of_isNBlkInjective_of_positive_word_commutes
    (A := A) (L₀ := L₀) (m := m + 2) (N := N) hInj hL₀ (by omega) hComm

/-- Reindexed boundary-closing comparison puts the boundary vector in
\(\mathbb C\,V^{(N)}(A)\).

The inputs are \(A^\mu A^j X=Y^+_{\tau^+_\eta(\mu)}A^j\),
\(X A^j A^\mu=A^jY^-_{\tau^-_\eta(\mu)}\), and
\(Y^+_{\tau^+_\eta(\mu)}=Y^-_{\tau^-_\eta(\mu)}\) for the same word \(\mu\).
These equations put \(\Gamma_N(X)\) in \(\mathbb C\,V^{(N)}(A)\). -/
theorem groundSpaceMap_mem_mpvSubmodule_of_isNBlkInjective_of_wrapped_witness_comparison
    {A : MPSTensor d D} {L₀ N : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (η : Fin d)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (Ywrap Ymirror : (Fin N → Fin d) → Matrix (Fin D) (Fin D) ℂ)
    (hWrap : ∀ (j : Fin d) (τ : Fin N → Fin d),
      evalWord A (List.ofFn (fun k : Fin (N - (L₀ + 1)) =>
        τ ⟨k.val + L₀, by omega⟩)) * A j * X = Ywrap τ * A j)
    (hMirror : ∀ (j : Fin d) (τ : Fin N → Fin d),
      X * A j * evalWord A (List.ofFn (fun k : Fin (N - (L₀ + 1)) =>
        τ ⟨k.val + 1, by omega⟩)) = A j * Ymirror τ)
    (hCompare : ∀ μ : Fin (N - (L₀ + 1)) → Fin d,
      Ywrap (wrappedMiddleBackground L₀ N η μ) =
        Ymirror (mirrorMiddleBackground L₀ N η μ)) :
    groundSpaceMap A N X ∈ mpvSubmodule A N := by
  obtain ⟨Y, hLeft, hRight⟩ :=
    two_sided_middle_compatibility_of_wrapped_witness_comparison
      (A := A) (L₀ := L₀) (N := N) η Ywrap Ymirror hWrap hMirror hCompare
  exact groundSpaceMap_mem_mpvSubmodule_of_isNBlkInjective_of_two_sided_middle_compatibility
    (A := A) (L₀ := L₀) (m := N - (L₀ + 1)) (N := N) hInj hL₀ Y hLeft hRight

/-- Closure-property step for periodic chains in arXiv:2011.12127,
Section IV.C, lines 2078--2090.

The cyclic-to-open-chain reduction produces a boundary matrix \(X\). The two
boundary-crossing local constraints give
\[
  A^\mu A^j X = Y^+_{\tau^+_\eta(\mu)}A^j,
  \qquad
  X A^j A^\mu = A^jY^-_{\tau^-_\eta(\mu)}.
\]
If the closure-property equality
\(Y^+_{\tau^+_\eta(\mu)}=Y^-_{\tau^-_\eta(\mu)}\) holds for each complementary
word \(\mu\), then the chain state lies in
\(\mathbb C\,V^{(N)}(A)\). -/
theorem chainGroundSpace_le_mpvSubmodule_of_isNBlkInjective_of_wrapped_witness_comparison
    {A : MPSTensor d D} [NeZero D] {L₀ L N : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    (hN : 2 ≤ N) (hL : L₀ < L) (hLN : L ≤ N)
    (hCompare :
      ∀ {ψ : NSiteSpace d N} {X : Matrix (Fin D) (Fin D) ℂ} (η : Fin d),
        (hψ : ψ ∈ chainGroundSpace A L N) →
        (hψX : ψ = groundSpaceMap A N X) →
        (Ywrap Ymirror : (Fin N → Fin d) → Matrix (Fin D) (Fin D) ℂ) →
        (∀ (j : Fin d) (τ : Fin N → Fin d),
          evalWord A (List.ofFn (fun k : Fin (N - (L₀ + 1)) =>
            τ ⟨k.val + L₀, by omega⟩)) * A j * X = Ywrap τ * A j) →
        (∀ (j : Fin d) (τ : Fin N → Fin d),
          X * A j * evalWord A (List.ofFn (fun k : Fin (N - (L₀ + 1)) =>
            τ ⟨k.val + 1, by omega⟩)) = A j * Ymirror τ) →
        ∀ μ : Fin (N - (L₀ + 1)) → Fin d,
          Ywrap (wrappedMiddleBackground L₀ N η μ) =
            Ymirror (mirrorMiddleBackground L₀ N η μ)) :
    chainGroundSpace A L N ≤ mpvSubmodule A N := by
  intro ψ hψ
  have hψGS : ψ ∈ groundSpace A N :=
    chainGroundSpace_le_groundSpace_of_isNBlkInjective hInj hL₀ (by omega : 0 < N) hL hLN hψ
  rw [groundSpace, LinearMap.mem_range] at hψGS
  obtain ⟨X, hX⟩ := hψGS
  haveI : NeZero d := neZero_d_of_isNBlkInjective hInj hL₀
  let η : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  obtain ⟨Ywrap, Ymirror, hWrap, hMirror⟩ :=
    chainGroundSpace_wrapped_boundary_compatibilities_of_isNBlkInjective
      (A := A) hInj hL₀ hN hL hLN hψ hX.symm
  have hCompare' : ∀ μ : Fin (N - (L₀ + 1)) → Fin d,
      Ywrap (wrappedMiddleBackground L₀ N η μ) =
        Ymirror (mirrorMiddleBackground L₀ N η μ) :=
    hCompare (ψ := ψ) (X := X) η hψ hX.symm Ywrap Ymirror hWrap hMirror
  rw [← hX]
  exact groundSpaceMap_mem_mpvSubmodule_of_isNBlkInjective_of_wrapped_witness_comparison
    (A := A) (L₀ := L₀) (N := N) hInj hL₀ η Ywrap Ymirror hWrap hMirror hCompare'

/-- Right-products with all one-site tensors determine the compared boundary
conditions.

This is the final algebraic reduction of the closure-property comparison from
arXiv:2011.12127, Section IV.C, lines 2078--2090.  The input is
\[
  Y^+_{\tau^+_\eta(\mu)} A^j
  =
  Y^-_{\tau^-_\eta(\mu)} A^j
\]
for every letter \(j\).  Since block-injectivity gives
\[
  \operatorname{span}\{A^w: |w|=L₀\}=M_D(\mathbb C),
\]
this implies
\[
  Y^+_{\tau^+_\eta(\mu)}=Y^-_{\tau^-_\eta(\mu)}.
\] -/
theorem wrapped_mirror_witness_agree_of_right_products
    {A : MPSTensor d D} {L₀ N : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    (Ywrap Ymirror : (Fin N → Fin d) → Matrix (Fin D) (Fin D) ℂ)
    (η : Fin d) (μ : Fin (N - (L₀ + 1)) → Fin d)
    (hProd : ∀ j : Fin d,
      Ywrap (wrappedMiddleBackground L₀ N η μ) * A j =
        Ymirror (mirrorMiddleBackground L₀ N η μ) * A j) :
    Ywrap (wrappedMiddleBackground L₀ N η μ) =
      Ymirror (mirrorMiddleBackground L₀ N η μ) := by
  exact right_witness_unique_of_isNBlkInjective (A := A) hInj hL₀ hProd

/-- The full boundary-closing restriction equality follows from equality after
fixing each first physical index.  This isolates the
closing-boundary comparison discussed in arXiv:2011.12127, Section IV.C,
lines 2078--2090. -/
theorem closure_property_boundary_restriction_eq_of_fixed_boundary_letters
    {L₀ M : ℕ} (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {ψ : NSiteSpace d (M + 1)}
    (η : Fin d) (μ : Fin (M + 1 - (L₀ + 1)) → Fin d)
    (hfixed : ∀ j : Fin d,
      cyclicRestrictₗ (show 0 < M + 1 by omega) L₀
          (cyclicForwardSite (⟨M, by omega⟩ : Fin (M + 1)) 1)
          (fun k => if (k.val + (M + 1) - (⟨M, by omega⟩ : Fin (M + 1)).val) %
                (M + 1) = 0 then j else wrappedMiddleBackground L₀ (M + 1) η μ k) ψ =
        cyclicRestrictₗ (show 0 < M + 1 by omega) L₀
          (cyclicForwardSite (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1)) 1)
          (fun k => if (k.val + (M + 1) -
                (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1)).val) % (M + 1) = 0 then j
              else mirrorMiddleBackground L₀ (M + 1) η μ k) ψ) :
    cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
        ⟨M, by omega⟩
        (wrappedMiddleBackground L₀ (M + 1) η μ) ψ =
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
        ⟨M + 1 - L₀, by omega⟩
        (mirrorMiddleBackground L₀ (M + 1) η μ) ψ := by
  apply eq_of_forall_restrictFirst_eq
  intro j
  rw [cyclicRestrictₗ_restrictFirst
      (show 0 < M + 1 by omega) (show L₀ + 1 ≤ M + 1 by omega)
      (⟨M, by omega⟩ : Fin (M + 1))
      (wrappedMiddleBackground L₀ (M + 1) η μ) ψ j]
  rw [cyclicRestrictₗ_restrictFirst
      (show 0 < M + 1 by omega) (show L₀ + 1 ≤ M + 1 by omega)
      (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1))
      (mirrorMiddleBackground L₀ (M + 1) η μ) ψ j]
  exact hfixed j

/-- Boundary-closing word equation for the closure property of arXiv:2011.12127,
lines 2078--2090. The matrices `YAt i τ` represent local restrictions, and the
displayed equation is the algebraic form that remains before block injectivity
strips the final length-`L₀` word.

**Open gap:** Prove the adjacent-overlap iteration around the boundary; see
`docs/paper-gaps/cpgsv21_normal_range_reduction.tex` and #2405. -/
theorem closure_property_boundary_right_annihilation_of_chainGroundSpace
    {A : MPSTensor d D} [NeZero D] {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {ψ : NSiteSpace d (M + 1)} {X : Matrix (Fin D) (Fin D) ℂ}
    (hψ : ψ ∈ chainGroundSpace A (L₀ + 1) (M + 1))
    (hψX : ψ = groundSpaceMap A (M + 1) X)
    (YAt : (i : Fin (M + 1)) → (Fin (M + 1) → Fin d) →
      Matrix (Fin D) (Fin D) ℂ)
    (hYAt : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ =
        groundSpaceMap A (L₀ + 1) (YAt i τ))
    (η : Fin d) (μ : Fin (M + 1 - (L₀ + 1)) → Fin d) :
    ∀ (j : Fin d) (σ : Fin L₀ → Fin d),
      (YAt ⟨M, by omega⟩ (wrappedMiddleBackground L₀ (M + 1) η μ) * A j -
          YAt ⟨M + 1 - L₀, by omega⟩
            (mirrorMiddleBackground L₀ (M + 1) η μ) * A j) *
        evalWord A (List.ofFn σ) = 0 := by
  sorry

/-- Matrix form of the closure property, arXiv:2011.12127, lines 2078--2090.
It follows from the boundary-closing word equation and block injectivity.

**Open gap:** Inherits the unproved boundary-closing word equation above; see
`docs/paper-gaps/cpgsv21_normal_range_reduction.tex` and #2405. -/
theorem closure_property_boundary_tensor_products_eq_of_chainGroundSpace
    {A : MPSTensor d D} [NeZero D] {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {ψ : NSiteSpace d (M + 1)} {X : Matrix (Fin D) (Fin D) ℂ}
    (hψ : ψ ∈ chainGroundSpace A (L₀ + 1) (M + 1))
    (hψX : ψ = groundSpaceMap A (M + 1) X)
    (YAt : (i : Fin (M + 1)) → (Fin (M + 1) → Fin d) →
      Matrix (Fin D) (Fin D) ℂ)
    (hYAt : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ =
        groundSpaceMap A (L₀ + 1) (YAt i τ))
    (η : Fin d) (μ : Fin (M + 1 - (L₀ + 1)) → Fin d) :
    ∀ j : Fin d,
      YAt ⟨M, by omega⟩ (wrappedMiddleBackground L₀ (M + 1) η μ) * A j =
        YAt ⟨M + 1 - L₀, by omega⟩
          (mirrorMiddleBackground L₀ (M + 1) η μ) * A j := by
  intro j
  have hzero : ∀ σ : Fin L₀ → Fin d,
      (YAt ⟨M, by omega⟩ (wrappedMiddleBackground L₀ (M + 1) η μ) * A j -
          YAt ⟨M + 1 - L₀, by omega⟩
            (mirrorMiddleBackground L₀ (M + 1) η μ) * A j) *
        evalWord A (List.ofFn σ) = 0 :=
    closure_property_boundary_right_annihilation_of_chainGroundSpace
      (A := A) hInj hL₀ hM hψ hψX YAt hYAt η μ j
  have hsub :
      YAt ⟨M, by omega⟩ (wrappedMiddleBackground L₀ (M + 1) η μ) * A j -
          YAt ⟨M + 1 - L₀, by omega⟩
            (mirrorMiddleBackground L₀ (M + 1) η μ) * A j = 0 :=
    eq_zero_of_mul_evalWord_eq_zero_of_isNBlkInjective_of_le_mul
      (A := A) (L₀ := L₀) (k := L₀) (q := 1) hInj (by omega) (by omega) hzero
  exact sub_eq_zero.mp hsub

/-- Auxiliary first-letter form of the closure property of arXiv:2011.12127,
lines 2078--2090. It follows by restricting the displayed matrix equation at
the first physical index.

**Open gap:** Inherits the unproved boundary-closing word equation above; see
`docs/paper-gaps/cpgsv21_normal_range_reduction.tex` and #2405. -/
theorem closure_property_fixed_boundary_letter_eq_of_chainGroundSpace
    {A : MPSTensor d D} [NeZero D] {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {ψ : NSiteSpace d (M + 1)} {X : Matrix (Fin D) (Fin D) ℂ}
    (hψ : ψ ∈ chainGroundSpace A (L₀ + 1) (M + 1))
    (hψX : ψ = groundSpaceMap A (M + 1) X)
    (η : Fin d) (μ : Fin (M + 1 - (L₀ + 1)) → Fin d) (j : Fin d) :
    cyclicRestrictₗ (show 0 < M + 1 by omega) L₀
        (cyclicForwardSite ⟨M, by omega⟩ 1)
        (fun k => if (k.val + (M + 1) - (⟨M, by omega⟩ : Fin (M + 1)).val) %
              (M + 1) = 0 then j else wrappedMiddleBackground L₀ (M + 1) η μ k) ψ =
      cyclicRestrictₗ (show 0 < M + 1 by omega) L₀
        (cyclicForwardSite ⟨M + 1 - L₀, by omega⟩ 1)
        (fun k => if (k.val + (M + 1) -
              (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1)).val) % (M + 1) = 0 then j
            else mirrorMiddleBackground L₀ (M + 1) η μ k) ψ := by
  obtain ⟨YAt, hYAt⟩ :=
    chainGroundSpace_window_witnesses A (show 0 < M + 1 by omega)
      (show L₀ + 1 ≤ M + 1 by omega) hψ
  have hLeft := cyclicRestrictₗ_restrictFirst_groundSpaceMap
    (A := A) (show 0 < M + 1 by omega) (show L₀ + 1 ≤ M + 1 by omega)
    (⟨M, by omega⟩ : Fin (M + 1))
    (wrappedMiddleBackground L₀ (M + 1) η μ) ψ
    (hYAt ⟨M, by omega⟩ (wrappedMiddleBackground L₀ (M + 1) η μ)) j
  have hRight := cyclicRestrictₗ_restrictFirst_groundSpaceMap
    (A := A) (show 0 < M + 1 by omega) (show L₀ + 1 ≤ M + 1 by omega)
    (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1))
    (mirrorMiddleBackground L₀ (M + 1) η μ) ψ
    (hYAt ⟨M + 1 - L₀, by omega⟩ (mirrorMiddleBackground L₀ (M + 1) η μ)) j
  have hProd := closure_property_boundary_tensor_products_eq_of_chainGroundSpace
    (A := A) hInj hL₀ hM hψ hψX YAt hYAt η μ j
  exact hLeft.trans ((congrArg (fun Y => groundSpaceMap A L₀ Y) hProd).trans hRight.symm)

/-- Restriction form of the closure property of arXiv:2011.12127,
lines 2078--2090, obtained from the first-letter family.

**Open gap:** Inherits the unproved boundary-closing word equation above; see
`docs/paper-gaps/cpgsv21_normal_range_reduction.tex` and #2405. -/
theorem closure_property_boundary_restriction_eq_of_chainGroundSpace
    {A : MPSTensor d D} [NeZero D] {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {ψ : NSiteSpace d (M + 1)} {X : Matrix (Fin D) (Fin D) ℂ}
    (hψ : ψ ∈ chainGroundSpace A (L₀ + 1) (M + 1))
    (hψX : ψ = groundSpaceMap A (M + 1) X)
    (η : Fin d) (μ : Fin (M + 1 - (L₀ + 1)) → Fin d) :
    cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
        ⟨M, by omega⟩
        (wrappedMiddleBackground L₀ (M + 1) η μ) ψ =
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
        ⟨M + 1 - L₀, by omega⟩
        (mirrorMiddleBackground L₀ (M + 1) η μ) ψ := by
  exact closure_property_boundary_restriction_eq_of_fixed_boundary_letters
    hL₀ hM η μ fun j =>
      closure_property_fixed_boundary_letter_eq_of_chainGroundSpace
        (A := A) hInj hL₀ hM hψ hψX η μ j

/-- The two boundary-condition matrix families agree in the closure property,
reduced to the \(Y A^j\) equation above.
**Open gap:** Depends on the restriction equality above; see
`docs/paper-gaps/cpgsv21_normal_range_reduction.tex` and #2405. -/
theorem wrapped_mirror_witness_agree_of_chainGroundSpace
    {A : MPSTensor d D} [NeZero D] {L₀ L N : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    (hN : 2 ≤ N) (hL : L₀ < L) (hLN : L ≤ N)
    {ψ : NSiteSpace d N} {X : Matrix (Fin D) (Fin D) ℂ}
    (hψ : ψ ∈ chainGroundSpace A L N) (hψX : ψ = groundSpaceMap A N X)
    (Ywrap Ymirror : (Fin N → Fin d) → Matrix (Fin D) (Fin D) ℂ)
    (hWrap : ∀ (j : Fin d) (τ : Fin N → Fin d),
      evalWord A (List.ofFn (fun k : Fin (N - (L₀ + 1)) =>
        τ ⟨k.val + L₀, by omega⟩)) * A j * X = Ywrap τ * A j)
    (hMirror : ∀ (j : Fin d) (τ : Fin N → Fin d),
      X * A j * evalWord A (List.ofFn (fun k : Fin (N - (L₀ + 1)) =>
        τ ⟨k.val + 1, by omega⟩)) = A j * Ymirror τ)
    (η : Fin d) (μ : Fin (N - (L₀ + 1)) → Fin d) :
    Ywrap (wrappedMiddleBackground L₀ N η μ) =
      Ymirror (mirrorMiddleBackground L₀ N η μ) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  refine wrapped_mirror_witness_agree_of_right_products (A := A) hInj hL₀
    Ywrap Ymirror η μ ?_
  intro j
  have hψred : ψ ∈ chainGroundSpace A (L₀ + 1) (M + 1) :=
    chainGroundSpace_le_chainGroundSpace_of_le (A := A) (by omega) (by omega) hLN hψ
  obtain ⟨YAt, hYAt⟩ := chainGroundSpace_window_witnesses A (by omega) (by omega) hψred
  let wrapPos : Fin (M + 1) := ⟨M, by omega⟩
  let mirrorPos : Fin (M + 1) := ⟨M + 1 - L₀, by omega⟩
  let τp := wrappedMiddleBackground L₀ (M + 1) η μ
  let τm := mirrorMiddleBackground L₀ (M + 1) η μ
  have hWrapAt := wrapping_window_compatibility_of_isNBlkInjective
    (A := A) hInj hL₀ (by omega : L₀ ≤ M) (YAt wrapPos)
      (fun τ σ_w => by
        simpa [groundSpaceMap_apply, cyclicRestrictₗ_apply, hψX]
          using congr_fun (hYAt wrapPos τ) σ_w)
  have hMirrorAt := wrapping_window_mirror_compatibility_of_isNBlkInjective
    (A := A) hInj hL₀ (by omega : L₀ ≤ M) (YAt mirrorPos)
      (fun τ σ_w => by
        simpa [groundSpaceMap_apply, cyclicRestrictₗ_apply, hψX]
          using congr_fun (hYAt mirrorPos τ) σ_w)
  have hYwrap_eq : Ywrap τp = YAt wrapPos τp :=
    right_witness_unique_of_isNBlkInjective (A := A) hInj hL₀
      (fun a => (hWrap a τp).symm.trans (hWrapAt a τp))
  have hYmirror_eq : Ymirror τm = YAt mirrorPos τm :=
    left_witness_unique_of_isNBlkInjective (A := A) hInj hL₀
      (fun a => (hMirror a τm).symm.trans (hMirrorAt a τm))
  rw [hYwrap_eq, hYmirror_eq]
  exact closure_property_boundary_tensor_products_eq_of_chainGroundSpace
    (A := A) hInj hL₀ (by omega : L₀ ≤ M) hψred hψX YAt hYAt η μ j

/-- Closure-property containment step:
\(\mathcal G_{N,L}(A) \subseteq \mathbb C\,\Omega_N(A)\) for \(L>L₀\).  This is
the closure-property step of arXiv:2011.12127.

**Open gap:** Depends on the closure-property boundary-condition comparison; see
`docs/paper-gaps/cpgsv21_normal_range_reduction.tex` and #2405. -/
theorem chainGroundSpace_le_mpvSubmodule_of_normal_range_reduction
    {A : MPSTensor d D} [NeZero D]
    (_hA : IsNormal A) {L₀ : ℕ} (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    {L N : ℕ} (hN : 2 ≤ N) (hL : L₀ < L) (hLN : L ≤ N) :
    chainGroundSpace A L N ≤ mpvSubmodule A N := by
  have hNpos : 0 < N := by omega
  intro ψ hψ
  have hψGS : ψ ∈ groundSpace A N :=
    chainGroundSpace_le_groundSpace_of_isNBlkInjective hInj hL₀ hNpos hL hLN hψ
  rw [groundSpace, LinearMap.mem_range] at hψGS
  obtain ⟨X, hX⟩ := hψGS
  haveI : NeZero d := neZero_d_of_isNBlkInjective hInj hL₀
  let η : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  obtain ⟨Ywrap, Ymirror, hWrap, hMirror⟩ :=
    chainGroundSpace_wrapped_boundary_compatibilities_of_isNBlkInjective
      (A := A) hInj hL₀ hN hL hLN hψ hX.symm
  have hCompare : ∀ μ : Fin (N - (L₀ + 1)) → Fin d,
      Ywrap (wrappedMiddleBackground L₀ N η μ) =
        Ymirror (mirrorMiddleBackground L₀ N η μ) := by
    intro μ
    exact wrapped_mirror_witness_agree_of_chainGroundSpace
      (A := A) hInj hL₀ hN hL hLN hψ hX.symm Ywrap Ymirror hWrap hMirror η μ
  rw [← hX]
  exact groundSpaceMap_mem_mpvSubmodule_of_isNBlkInjective_of_wrapped_witness_comparison
    (A := A) (L₀ := L₀) (N := N) hInj hL₀ η Ywrap Ymirror hWrap hMirror hCompare

/-- On a periodic chain, the normal parent-Hamiltonian ground space satisfies
\[
  \mathcal G_{N,L}(A)=\mathbb C\,\Omega_N(A)
\]
for every \(L>L₀\), by the intersection property and closure property of
arXiv:2011.12127, Section IV.C, lines 2078--2090.

**Open gap:** The containment direction depends on the closure property; see
`docs/paper-gaps/cpgsv21_normal_range_reduction.tex` and #2405. -/
theorem chainGroundSpace_eq_mpvSubmodule_normal {A : MPSTensor d D} [NeZero D]
    (hA : IsNormal A) {L₀ : ℕ} (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    {L N : ℕ} (hN : 2 ≤ N) (hL : L₀ < L) (hLN : L ≤ N) :
    chainGroundSpace A L N = mpvSubmodule A N := by
  apply le_antisymm
  · exact chainGroundSpace_le_mpvSubmodule_of_normal_range_reduction
      hA hInj hL₀ hN hL hLN
  · intro ψ hψ
    rw [mpvSubmodule, Submodule.mem_span_singleton] at hψ
    obtain ⟨c, rfl⟩ := hψ
    exact Submodule.smul_mem _ c (mpv_mem_chainGroundSpace A L N (by omega) hLN)

/-- Unique periodic ground state for an injective tensor:
\(\mathcal G_{N,L}(A)=\mathbb C\,V^{(N)}(A)\).

The proof writes \(\psi(\sigma)=\operatorname{tr}(A^\sigma X)\), closing the
boundary gives \(XA^i=A^iX\) for all \(i\), and injectivity gives
\(X=\lambda I\). -/
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

/-- Unique ground state for \(L₀\)-block-injective tensors at range \(2L₀\).

**Open gap:** This uses the normal range-reduction equality; see
`docs/paper-gaps/cpgsv21_normal_range_reduction.tex` and #2405. -/
theorem parentHamiltonian_unique_gs_injective {A : MPSTensor d D} [NeZero D]
    {L₀ : ℕ} (hA : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    {N : ℕ} (hN : 2 * L₀ ≤ N) :
    HasUniqueGroundState (chainGroundSpace A (2 * L₀) N) := by
  have hNormal : IsNormal A := ⟨L₀, hA⟩
  have hN' : L₀ + 1 ≤ N := by omega
  rw [HasUniqueGroundState,
    chainGroundSpace_eq_mpvSubmodule_normal hNormal hA hL₀ (by omega) (by omega) hN]
  have hmpv := mpv_ne_zero_of_isNBlkInjective hA hL₀ hN'
  simpa [mpvSubmodule] using finrank_span_singleton (K := ℂ) hmpv

/-- Unique ground state for normal tensors at range \(L₀+1\):
\[
  \dim \mathcal G_{N,L₀+1}(A)=1.
\]

**Open gap:** This depends on the normal range-reduction equality above; see
`docs/paper-gaps/cpgsv21_normal_range_reduction.tex` and #2405. -/
theorem parentHamiltonian_unique_gs_normal {A : MPSTensor d D} [NeZero D]
    {L₀ : ℕ} (hA : IsNormal A) (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    {N : ℕ} (hN : L₀ + 1 ≤ N) :
    HasUniqueGroundState (chainGroundSpace A (L₀ + 1) N) := by
  rw [HasUniqueGroundState,
    chainGroundSpace_eq_mpvSubmodule_normal hA hInj hL₀ (by omega) (by omega) hN]
  have hmpv := mpv_ne_zero_of_isNBlkInjective hInj hL₀ hN
  simpa [mpvSubmodule] using finrank_span_singleton (K := ℂ) hmpv

end MPSTensor
