/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.GroundSpace.ParentHamiltonian
import TNLean.MPS.Tensor.GroundSpace.ParentHamiltonianBasic
import TNLean.MPS.Tensor.GroundSpace.CyclicWindow
import QICLean.Analysis.Projection.Geometry
import QICLean.Analysis.TraceNorm.TraceNormAbs
import TNLean.MPS.Operator.Simple.CommutingForm
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Cyclic restrictions, the local parent interaction and the parent interaction on the ring

The Hilbert-space ingredients of the parent-Hamiltonian martingale method:

* `cyclicRestrictES` — cyclic-window restriction, and the cyclic average of the conjugates
  \(R_{i,\tau}^\dagger T R_{i,\tau}\) of an operator on a window;
* `restrictLast_eq_cyclicRestrictES_zero` and
  `restrictFirst_eq_cyclicRestrictES_one` — the endpoint coordinate
  identifications used for adjacent open-chain conditions;
* the local parent interaction `LinearMap.toMatrix' (parentInteraction A L)`, whose operator
  is the orthogonal projection onto the complement of the local ground space, with its
  positivity and kernel;
* the terms and Hamiltonian of the parent interaction on the ring
  `parentRingInteraction A L N`: positivity, idempotence and symmetric-projection structure of
  the terms, their kernels through cyclic restrictions, commutation and non-overlap
  positivity for disjoint cyclic windows;
* kernel identification: the ground space at energy \(0\) of the Hamiltonian of the parent
  interaction on the ring is the kernel of the finite parent Hamiltonian, read in the Euclidean
  space.

## Nonzero canonical parent interactions

The local MPS ground space has dimension at most \(D^2\). When the ambient
dimension \(d^L\) is larger, its complementary orthogonal projection is nonzero,
both as a matrix and in function-space coordinates.

It also contains the following results.

* `MPSTensor.localTerm_eq_toLin'_placeAlong_ringWindow`,
  `MPSTensor.parentInteraction_toMatrix'_norm_le_one`: matrix coordinates for canonical parent
  Hamiltonians.
-/

section Transport

section

open scoped BigOperators ComplexOrder InnerProductSpace

namespace MPSTensor

variable {d D : ℕ}

/-! ### Cyclic restrictions -/

/-- The cyclic window restriction map transported from `NSiteSpace` to the
Hilbert-space model `EuclideanSpace`. -/
noncomputable def cyclicRestrictES {N : ℕ} (hN : 0 < N) (L : ℕ) (i : Fin N)
    (τ : Fin N → Fin d) :
    EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d L) :=
  LinearMap.withLpMap 2 (cyclicRestrictₗ (d := d) hN L i τ)

/-! ### Disjoint cyclic windows and the ground space of the parent Hamiltonian -/

/-- Site-disjointness for two cyclic \(L\)-windows on an \(N\)-site periodic chain.

The window starting at \(i\) contains exactly the sites whose cyclic offset from \(i\)
is \(< L\).  Thus `CyclicWindowsDisjoint L i j` says that no site has offset \(< L\)
from both starting points.  This is the non-overlap condition used by the
finite-overlap martingale reduction. -/
def CyclicWindowsDisjoint {N : ℕ} (L : ℕ) (i j : Fin N) : Prop :=
  ∀ k : Fin N,
    ((k.val + N - i.val) % N < L) → ((k.val + N - j.val) % N < L) → False

/-- Cyclic-window disjointness is symmetric. -/
theorem CyclicWindowsDisjoint.symm {N : ℕ} {L : ℕ} {i j : Fin N}
    (hij : CyclicWindowsDisjoint L i j) : CyclicWindowsDisjoint L j i :=
  fun k hj hi => hij k hi hj

/-- If the cyclic supports of two windows do not overlap, then the windows are site-disjoint. -/
theorem CyclicWindowsDisjoint.of_not_cyclicWindowsOverlap {N L : ℕ}
    {i j : Fin N} (hij : ¬ cyclicWindowsOverlap N L i j) :
    CyclicWindowsDisjoint L i j := by
  intro k hki hkj
  apply hij
  refine ⟨k, ?_, ?_⟩
  · rw [cyclicWindowSupport, Finset.mem_image]
    refine ⟨(k.val + N - i.val) % N, Finset.mem_range.mpr hki, ?_⟩
    exact (eq_cyclic_site_of_offset_eq (Fin.pos i) (i := i) (k := k)
      (r := (k.val + N - i.val) % N) rfl).symm
  · rw [cyclicWindowSupport, Finset.mem_image]
    refine ⟨(k.val + N - j.val) % N, Finset.mem_range.mpr hkj, ?_⟩
    exact (eq_cyclic_site_of_offset_eq (Fin.pos j) (i := j) (k := k)
      (r := (k.val + N - j.val) % N) rfl).symm

attribute [local instance] Classical.propDecidable

private theorem cyclicCfg_eq_replaceWindow {N : ℕ} (hN : 0 < N) (L : ℕ)
    (hLN : L ≤ N) (i : Fin N) (σ : Cfg d L) (τ : Cfg d N) :
    cyclicCfg hN L i σ τ = replaceWindow L hLN i τ σ := by
  rfl

@[simp] private theorem cyclicRestrictES_apply {N : ℕ} (hN : 0 < N) (L : ℕ)
    (i : Fin N) (τ : Cfg d N) (v : EuclideanSpace ℂ (Cfg d N)) (ω : Cfg d L) :
    cyclicRestrictES (d := d) hN L i τ v ω = v (cyclicCfg hN L i ω τ) := rfl

private def SameOutsideWindow {N : ℕ} (L : ℕ) (i : Fin N) (σ τ : Cfg d N) : Prop :=
  ∀ k : Fin N, ¬ ((k.val + N - i.val) % N < L) → τ k = σ k

private theorem cyclicRestrictES_eq_of_sameOutsideWindow {N : ℕ} (hN : 0 < N)
    {L : ℕ} (i : Fin N) {σ τ : Cfg d N}
    (hστ : SameOutsideWindow (L := L) i σ τ) :
    cyclicRestrictES (d := d) hN L i τ = cyclicRestrictES hN L i σ := by
  ext v ω
  change v.ofLp (cyclicCfg hN L i ω τ) = v.ofLp (cyclicCfg hN L i ω σ)
  exact congrArg v.ofLp <| by
    ext k
    by_cases hk : ((k.val + N - i.val) % N) < L
    · simp [cyclicCfg, hk]
    · simp [cyclicCfg, hk, hστ k hk]

private theorem sameOutsideWindow_of_cyclicCfg_eq {N : ℕ} (hN : 0 < N) {L : ℕ}
    (i : Fin N) {σ τ : Cfg d N} {ω : Cfg d L}
    (hEq : cyclicCfg hN L i ω τ = σ) :
    SameOutsideWindow (L := L) i σ τ := by
  intro k hk
  have hEqk := congrFun hEq k
  simpa [cyclicCfg, hk] using hEqk

private theorem cyclic_offset_window_site_lt {N L : ℕ} (hLN : L ≤ N) (i : Fin N)
    (r : Fin L) :
    (((i.val + r.val) % N + N - i.val) % N) < L := by
  rw [offset_mod_eq i.isLt (Nat.lt_of_lt_of_le r.isLt hLN)]
  exact r.isLt

private theorem extractWindow_replaceWindow_of_cyclic_windows_disjoint {N L : ℕ}
    (hLN : L ≤ N) {i j : Fin N} (hij : CyclicWindowsDisjoint L i j)
    (σ : Cfg d N) (τ : Cfg d L) :
    extractWindow L i (replaceWindow L hLN j σ τ) = extractWindow L i σ := by
  funext r
  unfold extractWindow replaceWindow
  have hi : (((i.val + r.val) % N + N - i.val) % N) < L :=
    cyclic_offset_window_site_lt hLN i r
  have hnotj : ¬ (((i.val + r.val) % N + N - j.val) % N < L) := by
    intro hj
    exact hij ⟨(i.val + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩ hi hj
  rw [dite_eq_right hnotj]

private theorem replaceWindow_commute_of_cyclic_windows_disjoint {N L : ℕ}
    (hLN : L ≤ N) {i j : Fin N} (hij : CyclicWindowsDisjoint L i j)
    (σ : Cfg d N) (α β : Cfg d L) :
    replaceWindow L hLN j (replaceWindow L hLN i σ α) β =
      replaceWindow L hLN i (replaceWindow L hLN j σ β) α := by
  funext k
  by_cases hi : ((k.val + N - i.val) % N < L)
  · have hnotj : ¬ ((k.val + N - j.val) % N < L) := fun hj => hij k hi hj
    simp [replaceWindow, hi, hnotj]
  · by_cases hj : ((k.val + N - j.val) % N < L) <;> simp [replaceWindow, hi, hj]

private theorem linearMap_apply_eq_sum {α : Type*} [Fintype α] [DecidableEq α]
    (P : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α)
    (x : EuclideanSpace ℂ α) (a : α) :
    P x a = ∑ a' : α, x a' * P (EuclideanSpace.single a' (1 : ℂ)) a := by
  conv_lhs =>
    rw [show x = ∑ a' : α, x a' • EuclideanSpace.single a' (1 : ℂ) by
      simpa using ((EuclideanSpace.basisFun α ℂ).sum_repr x).symm]
  simp [Finset.sum_apply]

private theorem scalar_sum_comm {α β : Type*} [Fintype α] [Fintype β]
    (F : α → β → ℂ) (p : α → ℂ) (q : β → ℂ) :
    (∑ a, (∑ b, F a b * q b) * p a) =
      ∑ b, (∑ a, F a b * p a) * q b := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_right_comm]

private theorem separateLinearMap_apply_commute
    {α β : Type*} [Finite α] [Finite β]
    (P : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α)
    (Q : EuclideanSpace ℂ β →ₗ[ℂ] EuclideanSpace ℂ β)
    (F : α → β → ℂ) (a : α) (b : β) :
    P (WithLp.toLp 2 (fun a' => Q (WithLp.toLp 2 (fun b' => F a' b')) b)) a =
      Q (WithLp.toLp 2 (fun b' => P (WithLp.toLp 2 (fun a' => F a' b')) a)) b := by
  classical
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  calc
    P (WithLp.toLp 2 (fun a' => Q (WithLp.toLp 2 (fun b' => F a' b')) b)) a
        = ∑ a', (Q (WithLp.toLp 2 (fun b' => F a' b')) b) *
            P (EuclideanSpace.single a' (1 : ℂ)) a := by
      rw [linearMap_apply_eq_sum]
    _ = ∑ a', (∑ b', F a' b' * Q (EuclideanSpace.single b' (1 : ℂ)) b) *
            P (EuclideanSpace.single a' (1 : ℂ)) a := by
      refine Finset.sum_congr rfl ?_
      intro a' _
      rw [linearMap_apply_eq_sum]
    _ = ∑ b', (∑ a', F a' b' * P (EuclideanSpace.single a' (1 : ℂ)) a) *
            Q (EuclideanSpace.single b' (1 : ℂ)) b := by
      exact scalar_sum_comm F
        (fun a' => P (EuclideanSpace.single a' (1 : ℂ)) a)
        (fun b' => Q (EuclideanSpace.single b' (1 : ℂ)) b)
    _ = ∑ b', (P (WithLp.toLp 2 (fun a' => F a' b')) a) *
            Q (EuclideanSpace.single b' (1 : ℂ)) b := by
      refine Finset.sum_congr rfl ?_
      intro b' _
      have hP : (∑ a', F a' b' * P (EuclideanSpace.single a' (1 : ℂ)) a) =
          P (WithLp.toLp 2 (fun a' => F a' b')) a := by
        simpa using
          (linearMap_apply_eq_sum P (WithLp.toLp 2 (fun a' => F a' b')) a).symm
      rw [hP]
    _ = Q (WithLp.toLp 2 (fun b' => P (WithLp.toLp 2 (fun a' => F a' b')) a)) b := by
      rw [linearMap_apply_eq_sum]

private theorem cyclicRestrictES_single_of_sameOutsideWindow {N : ℕ} (hN : 0 < N) {L : ℕ}
    (hLN : L ≤ N) (i : Fin N) (σ τ : Cfg d N)
    (hστ : SameOutsideWindow (L := L) i σ τ) :
    cyclicRestrictES (d := d) hN L i τ (EuclideanSpace.single σ (1 : ℂ)) =
      EuclideanSpace.single (extractWindow L i σ) (1 : ℂ) := by
  ext ω
  by_cases hω : ω = extractWindow L i σ
  · subst hω
    have hreplace : replaceWindow L hLN i τ (extractWindow L i σ) =
        replaceWindow L hLN i σ (extractWindow L i σ) := by
      ext k
      by_cases hk : ((k.val + N - i.val) % N) < L
      · simp [replaceWindow, hk]
      · simp [replaceWindow, hk, hστ k hk]
    have hEq : cyclicCfg hN L i (extractWindow L i σ) τ = σ := by
      rw [cyclicCfg_eq_replaceWindow hN L hLN]
      simpa using hreplace.trans (replaceWindow_extractWindow L hLN i σ)
    rw [PiLp.single_apply]
    simp [hEq]
  · have hneq : cyclicCfg hN L i ω τ ≠ σ := by
      intro hEq
      apply hω
      have hextract := congrArg (extractWindow L i) hEq
      simpa [cyclicCfg_eq_replaceWindow, hLN] using hextract
    simp [cyclicRestrictES, hneq, hω]

private theorem cyclicRestrictES_single_of_not_sameOutsideWindow {N : ℕ} (hN : 0 < N) {L : ℕ}
    (i : Fin N) (σ τ : Cfg d N)
    (hστ : ¬ SameOutsideWindow (L := L) i σ τ) :
    cyclicRestrictES (d := d) hN L i τ (EuclideanSpace.single σ (1 : ℂ)) = 0 := by
  ext ω
  have hneq : cyclicCfg hN L i ω τ ≠ σ := by
    intro hEq
    exact hστ (sameOutsideWindow_of_cyclicCfg_eq hN i hEq)
  simp [cyclicRestrictES, hneq]

private theorem cyclicRestrictES_adjoint_apply {N : ℕ} (hN : 0 < N) {L : ℕ}
    (hLN : L ≤ N) (i : Fin N) (σ τ : Cfg d N)
    (v : EuclideanSpace ℂ (Cfg d L)) :
    ((cyclicRestrictES (d := d) hN L i τ).adjoint v) σ =
      if SameOutsideWindow (L := L) i σ τ then v (extractWindow L i σ) else 0 := by
  classical
  have h : ((cyclicRestrictES (d := d) hN L i τ).adjoint v) σ =
      ⟪cyclicRestrictES (d := d) hN L i τ (EuclideanSpace.single σ (1 : ℂ)), v⟫_ℂ := by
    rw [← LinearMap.adjoint_inner_right]
    simpa using (EuclideanSpace.inner_single_left σ (1 : ℂ)
      ((cyclicRestrictES (d := d) hN L i τ).adjoint v)).symm
  split_ifs with hστ
  · rw [h, cyclicRestrictES_single_of_sameOutsideWindow hN hLN i σ τ hστ]
    simpa using EuclideanSpace.inner_single_left (extractWindow L i σ) (1 : ℂ) v
  · rw [h, cyclicRestrictES_single_of_not_sameOutsideWindow hN i σ τ hστ, inner_zero_left]

/-- At site \(0\) of an \((L+1)\)-site chain, fixing the final site is the
cyclic length-\(L\) restriction in the canonical Hilbert-space coordinates.

This realizes the left open-chain ground projection in Nachtergaele,
arXiv:cond-mat/9410110, eq. (2.4). -/
theorem restrictLast_eq_cyclicRestrictES_zero {L : ℕ}
    (v : EuclideanSpace ℂ (Cfg d (L + 1))) (τ : Cfg d (L + 1)) :
    restrictLast ((WithLp.linearEquiv 2 ℂ (NSiteSpace d (L + 1))) v) (τ (Fin.last L)) =
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d L))
        (cyclicRestrictES (d := d) (Fin.pos (0 : Fin (L + 1))) L (0 : Fin (L + 1))
          τ v) := by
  ext σ
  change v.ofLp (Fin.snoc σ (τ (Fin.last L))) = v.ofLp
    (cyclicCfg (d := d) (Fin.pos (0 : Fin (L + 1))) L (0 : Fin (L + 1)) σ τ)
  apply congrArg v.ofLp
  funext k
  rcases Fin.eq_castSucc_or_eq_last k with ⟨r, rfl⟩ | rfl
  · have hmod : r.val % (L + 1) = r.val := Nat.mod_eq_of_lt (by omega)
    simp [cyclicCfg, hmod]
  · simp [cyclicCfg]

/-- If \(L>0\), then at site \(1\) of an \((L+1)\)-site chain, fixing the
first site is the cyclic length-\(L\) restriction in the canonical Hilbert-space
coordinates.

This realizes the tail open-chain ground projection in Nachtergaele,
arXiv:cond-mat/9410110, eq. (2.4). -/
theorem restrictFirst_eq_cyclicRestrictES_one {L : ℕ} (hL : 0 < L)
    (v : EuclideanSpace ℂ (Cfg d (L + 1))) (τ : Cfg d (L + 1)) :
    restrictFirst ((WithLp.linearEquiv 2 ℂ (NSiteSpace d (L + 1))) v) (τ 0) =
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d L))
        (cyclicRestrictES (d := d) (Fin.pos (1 : Fin (L + 1))) L (1 : Fin (L + 1))
          τ v) := by
  ext σ
  change v.ofLp (Fin.cons (τ 0) σ) = v.ofLp
    (cyclicCfg (d := d) (Fin.pos (1 : Fin (L + 1))) L (1 : Fin (L + 1)) σ τ)
  apply congrArg v.ofLp
  funext k
  have hOneNat : 1 % (L + 1) = 1 := Nat.mod_eq_of_lt (Nat.succ_lt_succ hL)
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨r, rfl⟩
  · simp [cyclicCfg, hOneNat]
  · have hmod : (r.val + 1 + L) % (L + 1) = r.val := by
      rw [show r.val + 1 + L = r.val + (L + 1) by omega]
      rw [Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (Nat.lt_succ_of_lt r.isLt)
    simp [cyclicCfg, hOneNat, hmod]

private theorem sameOutsideWindow_card {N : ℕ} {L : ℕ} (hLN : L ≤ N)
    (i : Fin N) (σ : Cfg d N) :
    Fintype.card {τ : Cfg d N // SameOutsideWindow (L := L) i σ τ} = d ^ L := by
  let f : Cfg d L → {τ : Cfg d N // SameOutsideWindow (L := L) i σ τ} :=
    fun ω => ⟨replaceWindow L hLN i σ ω, by
      intro k hk
      simp [replaceWindow, hk]⟩
  have hf : Function.Bijective f := by
    constructor
    · intro ω₁ ω₂ h
      have h' := congrArg (fun τ : {τ : Cfg d N // SameOutsideWindow (L := L) i σ τ} =>
        extractWindow L i τ.1) h
      simpa [f] using h'
    · intro τ
      refine ⟨extractWindow L i τ.1, ?_⟩
      apply Subtype.ext
      have hreplace : replaceWindow L hLN i σ (extractWindow L i τ.1) =
          replaceWindow L hLN i τ.1 (extractWindow L i τ.1) := by
        ext k
        by_cases hk : ((k.val + N - i.val) % N) < L
        · simp [replaceWindow, hk]
        · simp [replaceWindow, hk, τ.2 k hk]
      simpa [f] using hreplace.trans (replaceWindow_extractWindow L hLN i τ.1)
  calc
    Fintype.card {τ : Cfg d N // SameOutsideWindow (L := L) i σ τ}
        = Fintype.card (Cfg d L) := (Fintype.card_of_bijective (f := f) hf).symm
    _ = d ^ L := by simp [Cfg]

/-- The cyclic average of the conjugates \(R_{i,\tau}^\dagger T R_{i,\tau}\) of an operator
\(T\) on \(L\) sites by the restrictions to the window starting at \(i\) applies \(T\) to the
section of the vector on that window. -/
theorem inv_smul_sum_adjoint_comp_cyclicRestrictES_apply {N L : ℕ} (hLN : L ≤ N) (i : Fin N)
    (T : EuclideanSpace ℂ (Cfg d L) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d L))
    (v : EuclideanSpace ℂ (Cfg d N)) (σ : Cfg d N) :
    ((((d ^ L : ℕ) : ℂ)⁻¹) • ∑ τ : Cfg d N,
      (cyclicRestrictES (Fin.pos i) L i τ).adjoint ∘ₗ T ∘ₗ
        cyclicRestrictES (Fin.pos i) L i τ) v σ =
      T (cyclicRestrictES (Fin.pos i) L i σ v) (extractWindow L i σ) := by
  classical
  have hsummand (τ : Cfg d N) :
      ((cyclicRestrictES (Fin.pos i) L i τ).adjoint
        (T (cyclicRestrictES (Fin.pos i) L i τ v))) σ =
        if SameOutsideWindow (L := L) i σ τ then
          T (cyclicRestrictES (Fin.pos i) L i σ v) (extractWindow L i σ) else 0 := by
    rw [cyclicRestrictES_adjoint_apply (Fin.pos i) hLN i σ τ]
    by_cases hστ : SameOutsideWindow (L := L) i σ τ
    · rw [ite_eq_left hστ, ite_eq_left hστ,
        cyclicRestrictES_eq_of_sameOutsideWindow (Fin.pos i) i hστ]
    · rw [ite_eq_right hστ, ite_eq_right hστ]
  have hne : (((d ^ L : ℕ) : ℂ)) ≠ 0 := by
    have hcard : Fintype.card (Cfg d L) = d ^ L := by simp [Cfg]
    have : Fintype.card (Cfg d L) ≠ 0 := by
      let _ : Nonempty (Cfg d L) := ⟨extractWindow L i σ⟩
      exact Fintype.card_ne_zero
    rw [hcard] at this
    exact_mod_cast this
  have happly : ((((d ^ L : ℕ) : ℂ)⁻¹) • ∑ τ : Cfg d N,
      (cyclicRestrictES (Fin.pos i) L i τ).adjoint ∘ₗ T ∘ₗ
        cyclicRestrictES (Fin.pos i) L i τ) v σ =
      (((d ^ L : ℕ) : ℂ)⁻¹) * ∑ τ : Cfg d N,
        ((cyclicRestrictES (Fin.pos i) L i τ).adjoint
          (T (cyclicRestrictES (Fin.pos i) L i τ v))) σ := by
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply, PiLp.smul_apply,
      WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul]
  rw [happly]
  simp_rw [hsummand]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, ← Fintype.card_subtype,
    sameOutsideWindow_card hLN i σ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-! ### The local parent interaction and the parent interaction on the ring

The local parent interaction \(h_L\) is the matrix `LinearMap.toMatrix' (parentInteraction A L)`;
as an operator on the Euclidean space it is the orthogonal projection onto the orthogonal
complement of the local ground space \(G_L(A)\). The terms of the parent interaction on the ring
(`parentRingInteraction`) are its placements on the cyclic windows, and its Hamiltonian is the
parent Hamiltonian. The statements below are made for these matrices; the Euclidean operator of a
matrix is taken with `Matrix.toEuclideanLin` where a statement is about vectors. -/

/-- The operator of the local parent interaction is the orthogonal projection onto the orthogonal
complement of the local ground space \(G_L(A)\). -/
theorem toEuclideanLin_toMatrix'_parentInteraction (A : MPSTensor d D) (L : ℕ) :
    Matrix.toEuclideanLin (LinearMap.toMatrix' (parentInteraction A L)) =
      (groundSpaceES A L)ᗮ.starProjection.toLinearMap := by
  ext v σ
  simp [Matrix.toEuclideanLin, parentInteraction]

/-- The operator of the local parent interaction is a symmetric projection. -/
theorem isSymmetricProjection_toEuclideanLin_toMatrix'_parentInteraction (A : MPSTensor d D)
    (L : ℕ) :
    (Matrix.toEuclideanLin (LinearMap.toMatrix' (parentInteraction A L))).IsSymmetricProjection :=
  toEuclideanLin_toMatrix'_parentInteraction A L ▸
    Submodule.isSymmetricProjection_starProjection _

/-- The local parent interaction is an orthogonal projection. Source: arXiv:1010.3732,
Section II.B, the choice of the local term as a projector. -/
theorem isStarProjection_toMatrix'_parentInteraction (A : MPSTensor d D) (L : ℕ) :
    IsStarProjection (LinearMap.toMatrix' (parentInteraction A L)) := by
  have h := isSymmetricProjection_toEuclideanLin_toMatrix'_parentInteraction A L
  refine ⟨Matrix.toEuclideanLin.injective ?_, ?_⟩
  · rw [Matrix.toEuclideanLin_mul]
    exact h.isIdempotentElem.eq
  · exact (Matrix.isSymmetric_toEuclideanLin_iff.mp h.isSymmetric).isSelfAdjoint

/-- The local parent interaction is positive semidefinite. -/
theorem posSemidef_toMatrix'_parentInteraction (A : MPSTensor d D) (L : ℕ) :
    (LinearMap.toMatrix' (parentInteraction A L)).PosSemidef :=
  Matrix.isPositive_toEuclideanLin_iff.mp
    (isSymmetricProjection_toEuclideanLin_toMatrix'_parentInteraction A L).isPositive

/-- The kernel of the local parent interaction is the local ground space \(G_L(A)\). -/
theorem toEuclideanLin_toMatrix'_parentInteraction_apply_eq_zero_iff (A : MPSTensor d D)
    (L : ℕ) (v : EuclideanSpace ℂ (Cfg d L)) :
    Matrix.toEuclideanLin (LinearMap.toMatrix' (parentInteraction A L)) v = 0 ↔
      v ∈ groundSpaceES A L := by
  rw [toEuclideanLin_toMatrix'_parentInteraction]
  change (groundSpaceES A L)ᗮ.starProjection v = 0 ↔ v ∈ groundSpaceES A L
  rw [Submodule.starProjection_orthogonal']
  simp only [sub_apply, one_apply_eq_self]
  rw [sub_eq_zero, eq_comm, Submodule.starProjection_eq_self_iff]

/-- A term of the parent interaction on the ring acts at a configuration \(σ\) as the local
parent interaction on the cyclic restriction to its window, read at the window of \(σ\). -/
theorem toEuclideanLin_parentRingInteraction_term_apply (A : MPSTensor d D) {L N : ℕ}
    (hLN : L ≤ N) (i : Fin N) (v : EuclideanSpace ℂ (Cfg d N)) (σ : Cfg d N) :
    haveI : NeZero N := NeZero.of_pos i.pos;
    Matrix.toEuclideanLin ((parentRingInteraction A L N).term i) v σ =
      Matrix.toEuclideanLin (LinearMap.toMatrix' (parentInteraction A L))
        (cyclicRestrictES (Fin.pos i) L i σ v) (extractWindow L i σ) := by
  have : NeZero N := NeZero.of_pos i.pos
  have h1 : Matrix.toEuclideanLin ((parentRingInteraction A L N).term i) v σ =
      localTerm A L N i v.ofLp σ := by
    rw [localTerm_eq_toLin'_term A L i]
    rfl
  rw [h1, localTerm_apply_of_le A L N hLN]
  change _ = (Matrix.toLin' (LinearMap.toMatrix' (parentInteraction A L))) _ _
  rw [Matrix.toLin'_toMatrix']
  rfl

private theorem cyclicRestrictES_toEuclideanLin_parentRingInteraction_term (A : MPSTensor d D)
    {L N : ℕ} (hLN : L ≤ N) (i : Fin N) (τ : Cfg d N) (v : EuclideanSpace ℂ (Cfg d N)) :
    haveI : NeZero N := NeZero.of_pos i.pos;
    cyclicRestrictES (Fin.pos i) L i τ
        (Matrix.toEuclideanLin ((parentRingInteraction A L N).term i) v) =
      Matrix.toEuclideanLin (LinearMap.toMatrix' (parentInteraction A L))
        (cyclicRestrictES (Fin.pos i) L i τ v) := by
  have : NeZero N := NeZero.of_pos i.pos
  ext ω
  rw [cyclicRestrictES_apply,
    toEuclideanLin_parentRingInteraction_term_apply A hLN i v (cyclicCfg (Fin.pos i) L i ω τ)]
  have hsame : SameOutsideWindow (L := L) i (cyclicCfg (d := d) (Fin.pos i) L i ω τ) τ :=
    sameOutsideWindow_of_cyclicCfg_eq (d := d) (Fin.pos i) i rfl
  have hrestrict : cyclicRestrictES (d := d) (Fin.pos i) L i τ =
      cyclicRestrictES (Fin.pos i) L i (cyclicCfg (d := d) (Fin.pos i) L i ω τ) :=
    cyclicRestrictES_eq_of_sameOutsideWindow (d := d) (Fin.pos i) i hsame
  have hextract : extractWindow L i (cyclicCfg (d := d) (Fin.pos i) L i ω τ) = ω := by
    rw [cyclicCfg_eq_replaceWindow (d := d) (Fin.pos i) L hLN]
    exact extractWindow_replaceWindow L hLN i τ ω
  rw [← hrestrict, hextract]

/-- A term of the parent interaction on the ring annihilates a vector exactly when every
boundary-filled cyclic restriction of the vector to the window of the term lies in the local
ground space \(G_L(A)\). -/
theorem toEuclideanLin_parentRingInteraction_term_eq_zero_iff (A : MPSTensor d D) {L N : ℕ}
    (hLN : L ≤ N) (i : Fin N) (v : EuclideanSpace ℂ (Cfg d N)) :
    haveI : NeZero N := NeZero.of_pos i.pos;
    Matrix.toEuclideanLin ((parentRingInteraction A L N).term i) v = 0 ↔
      ∀ τ : Cfg d N, cyclicRestrictES (Fin.pos i) L i τ v ∈ groundSpaceES A L := by
  have : NeZero N := NeZero.of_pos i.pos
  constructor
  · intro hv τ
    rw [← toEuclideanLin_toMatrix'_parentInteraction_apply_eq_zero_iff,
      ← cyclicRestrictES_toEuclideanLin_parentRingInteraction_term A hLN i τ v, hv, map_zero]
  · intro hv
    ext σ
    rw [toEuclideanLin_parentRingInteraction_term_apply A hLN i v σ,
      (toEuclideanLin_toMatrix'_parentInteraction_apply_eq_zero_iff A L _).2 (hv σ)]
    rfl

/-- If a term of the parent interaction on the ring annihilates a vector, every cyclic
restriction of the vector to the window of the term lies in the local ground space. -/
theorem cyclicRestrictES_mem_groundSpaceES_of_parentRingInteraction_term_eq_zero
    (A : MPSTensor d D) {L N : ℕ} (hLN : L ≤ N) (i : Fin N) {v : EuclideanSpace ℂ (Cfg d N)}
    (hv : haveI : NeZero N := NeZero.of_pos i.pos;
      Matrix.toEuclideanLin ((parentRingInteraction A L N).term i) v = 0) (τ : Cfg d N) :
    cyclicRestrictES (Fin.pos i) L i τ v ∈ groundSpaceES A L :=
  haveI : NeZero N := NeZero.of_pos i.pos
  (toEuclideanLin_parentRingInteraction_term_eq_zero_iff A hLN i v).1 hv τ

/-- **Adjacent terms.** On a chain of \(L+1\) sites, if the two terms of the parent interaction on
the ring based at `0` and `1` annihilate a vector, the vector lies in the \((L+1)\)-site ground
space. This is the open-chain intersection property `groundSpace_intersection` in the language of
the local terms. -/
theorem mem_groundSpaceES_succ_of_parentRingInteraction_term_zero_one_eq_zero
    {A : MPSTensor d D} (hA : Kraus.IsInjective A) {L : ℕ} (hL : 1 < L)
    {v : EuclideanSpace ℂ (Cfg d (L + 1))}
    (hleft : Matrix.toEuclideanLin ((parentRingInteraction A L (L + 1)).term 0) v = 0)
    (hright : Matrix.toEuclideanLin ((parentRingInteraction A L (L + 1)).term 1) v = 0) :
    v ∈ groundSpaceES A (L + 1) := by
  let eN := WithLp.linearEquiv 2 ℂ (NSiteSpace d (L + 1))
  have hLeft : InLeftGround A L (eN v) := by
    intro j
    have hmemNS := (mem_groundSpaceES_iff A L _).1
      (cyclicRestrictES_mem_groundSpaceES_of_parentRingInteraction_term_eq_zero A L.le_succ 0
        hleft fun _ => j)
    rwa [restrictLast_eq_cyclicRestrictES_zero v (fun _ => j)]
  have hRight : InRightGround A L (eN v) := by
    intro i
    have hmemNS := (mem_groundSpaceES_iff A L _).1
      (cyclicRestrictES_mem_groundSpaceES_of_parentRingInteraction_term_eq_zero A L.le_succ 1
        hright fun _ => i)
    rwa [restrictFirst_eq_cyclicRestrictES_one (by omega : 0 < L) v (fun _ => i)]
  exact (mem_groundSpaceES_iff A (L + 1) v).2 (groundSpace_intersection hA hL hLeft hRight)

/-- Vectors of the \((L+1)\)-site ground space are annihilated by the two terms of the parent
interaction on the ring based at `0` and `1`. -/
theorem parentRingInteraction_term_zero_one_eq_zero_of_mem_groundSpaceES_succ
    (A : MPSTensor d D) {L : ℕ} (hL : 0 < L) {v : EuclideanSpace ℂ (Cfg d (L + 1))}
    (hv : v ∈ groundSpaceES A (L + 1)) :
    Matrix.toEuclideanLin ((parentRingInteraction A L (L + 1)).term 0) v = 0 ∧
      Matrix.toEuclideanLin ((parentRingInteraction A L (L + 1)).term 1) v = 0 := by
  have hψ := (mem_groundSpaceES_iff A (L + 1) v).1 hv
  constructor
  · rw [toEuclideanLin_parentRingInteraction_term_eq_zero_iff A L.le_succ]
    intro τ
    rw [mem_groundSpaceES_iff, ← restrictLast_eq_cyclicRestrictES_zero v τ]
    exact groundSpace_inLeftGround A L hψ (τ (Fin.last L))
  · rw [toEuclideanLin_parentRingInteraction_term_eq_zero_iff A L.le_succ]
    intro τ
    rw [mem_groundSpaceES_iff, ← restrictFirst_eq_cyclicRestrictES_one hL v τ]
    exact groundSpace_inRightGround A L hψ (τ 0)

/-- Adjacent terms of the parent interaction on the ring of \(L+1\) sites have the
\((L+1)\)-site ground space as their common kernel. -/
theorem parentRingInteraction_term_zero_one_eq_zero_iff_mem_groundSpaceES_succ
    {A : MPSTensor d D} (hA : Kraus.IsInjective A) {L : ℕ} (hL : 1 < L)
    {v : EuclideanSpace ℂ (Cfg d (L + 1))} :
    Matrix.toEuclideanLin ((parentRingInteraction A L (L + 1)).term 0) v = 0 ∧
      Matrix.toEuclideanLin ((parentRingInteraction A L (L + 1)).term 1) v = 0 ↔
        v ∈ groundSpaceES A (L + 1) :=
  ⟨fun h ↦ mem_groundSpaceES_succ_of_parentRingInteraction_term_zero_one_eq_zero hA hL h.1 h.2,
    parentRingInteraction_term_zero_one_eq_zero_of_mem_groundSpaceES_succ A (by omega)⟩

/-- Every term of the parent interaction on the ring is an orthogonal projection. -/
theorem isStarProjection_parentRingInteraction_term (A : MPSTensor d D) (L : ℕ) {N : ℕ}
    (i : Fin N) :
    haveI : NeZero N := NeZero.of_pos i.pos;
    IsStarProjection ((parentRingInteraction A L N).term i) := by
  have : NeZero N := NeZero.of_pos i.pos
  have hP := isStarProjection_toMatrix'_parentInteraction A L
  refine ManyBody.Interaction.forall_translationInvariant_term (P := IsStarProjection)
    ⟨IsIdempotentElem.zero, IsSelfAdjoint.zero _⟩ (fun hLN i ↦ ⟨?_, ?_⟩) i
  · rw [IsIdempotentElem, ← ManyBody.placeAlong_mul, hP.isIdempotentElem.eq]
  · rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, ← ManyBody.placeAlong_conjTranspose,
      ← Matrix.star_eq_conjTranspose, hP.isSelfAdjoint.star_eq]

/-- The operator of every term of the parent interaction on the ring is a symmetric
projection. -/
theorem isSymmetricProjection_toEuclideanLin_parentRingInteraction_term (A : MPSTensor d D)
    (L : ℕ) {N : ℕ} (i : Fin N) :
    haveI : NeZero N := NeZero.of_pos i.pos;
    (Matrix.toEuclideanLin ((parentRingInteraction A L N).term i)).IsSymmetricProjection :=
  haveI : NeZero N := NeZero.of_pos i.pos
  Matrix.isSymmetricProjection_toEuclideanLin_iff.mpr
    (isStarProjection_parentRingInteraction_term A L i)

/-- Every term of the parent interaction on the ring is positive semidefinite. -/
theorem posSemidef_parentRingInteraction_term (A : MPSTensor d D) (L : ℕ) {N : ℕ}
    (i : Fin N) :
    haveI : NeZero N := NeZero.of_pos i.pos;
    ((parentRingInteraction A L N).term i).PosSemidef :=
  haveI : NeZero N := NeZero.of_pos i.pos
  Matrix.isPositive_toEuclideanLin_iff.mp
    (isSymmetricProjection_toEuclideanLin_parentRingInteraction_term A L i).isPositive

/-- The Hamiltonian of the parent interaction on the ring is positive semidefinite. -/
theorem posSemidef_hamiltonian_parentRingInteraction (A : MPSTensor d D) (L N : ℕ) [NeZero N] :
    (parentRingInteraction A L N).hamiltonian.PosSemidef :=
  ManyBody.Interaction.posSemidef_hamiltonian fun i ↦ posSemidef_parentRingInteraction_term A L i

/-- **Disjoint windows.** Terms of the parent interaction on the ring whose cyclic windows have
no common site commute. This is the non-overlap commutation input for the finite-overlap
martingale reduction. -/
theorem commute_parentRingInteraction_term_of_cyclic_windows_disjoint (A : MPSTensor d D)
    {L N : ℕ} (hLN : L ≤ N) {i j : Fin N} (hij : CyclicWindowsDisjoint L i j) :
    haveI : NeZero N := NeZero.of_pos i.pos;
    Commute ((parentRingInteraction A L N).term i) ((parentRingInteraction A L N).term j) := by
  have : NeZero N := NeZero.of_pos i.pos
  rw [ManyBody.Interaction.translationInvariant_term_of_le _ hLN,
    ManyBody.Interaction.translationInvariant_term_of_le _ hLN]
  refine ManyBody.commute_placeAlong_of_disjoint (X := fun _ ↦ Fin d) _
    (Finset.disjoint_left.mpr fun k hki hkj ↦ ?_) _ _
  exact hij k ((mem_map_ringWindow_iff hLN i k).mp hki) ((mem_map_ringWindow_iff hLN j k).mp hkj)

/-- Local parent-Hamiltonian terms with disjoint cyclic supports commute. -/
theorem localTerm_commute_of_cyclic_windows_disjoint {N : ℕ} (A : MPSTensor d D)
    {L : ℕ} (hLN : L ≤ N) {i j : Fin N} (hij : CyclicWindowsDisjoint L i j) :
    localTerm A L N i * localTerm A L N j =
      localTerm A L N j * localTerm A L N i := by
  have : NeZero N := NeZero.of_pos i.pos
  rw [localTerm_eq_toLin'_term A L, localTerm_eq_toLin'_term A L, Module.End.mul_eq_comp,
    Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul,
    (commute_parentRingInteraction_term_of_cyclic_windows_disjoint A hLN hij).eq]

/-- **Non-overlap positivity.** For terms of the parent interaction on the ring whose cyclic
windows have no common site, the ordered cross term is nonnegative:
\(0 ≤ \operatorname{Re}\langle h_i v, h_j v\rangle\). -/
theorem re_inner_parentRingInteraction_term_nonneg_of_cyclic_windows_disjoint
    (A : MPSTensor d D) {L N : ℕ} (hLN : L ≤ N) {i j : Fin N}
    (hij : CyclicWindowsDisjoint L i j) (v : EuclideanSpace ℂ (Cfg d N)) :
    haveI : NeZero N := NeZero.of_pos i.pos;
    0 ≤ (⟪Matrix.toEuclideanLin ((parentRingInteraction A L N).term i) v,
      Matrix.toEuclideanLin ((parentRingInteraction A L N).term j) v⟫_ℂ).re :=
  haveI : NeZero N := NeZero.of_pos i.pos
  LinearMap.IsSymmetricProjection.re_inner_apply_apply_nonneg_of_commute
    (isSymmetricProjection_toEuclideanLin_parentRingInteraction_term A L i)
    (isSymmetricProjection_toEuclideanLin_parentRingInteraction_term A L j)
    (fun w ↦ by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, Module.End.mul_eq_comp,
        Module.End.mul_eq_comp, ← Matrix.toEuclideanLin_mul, ← Matrix.toEuclideanLin_mul,
        (commute_parentRingInteraction_term_of_cyclic_windows_disjoint A hLN hij).eq]) v

/-- Non-overlap positivity for the cyclic-window overlap predicate: when the windows of the
terms based at `i` and `j` do not overlap, their ordered cross term is nonnegative. -/
theorem re_inner_parentRingInteraction_term_nonneg_of_not_cyclicWindowsOverlap
    (A : MPSTensor d D) {L N : ℕ} (hLN : L ≤ N) {i j : Fin N}
    (hij : ¬ cyclicWindowsOverlap N L i j) (v : EuclideanSpace ℂ (Cfg d N)) :
    haveI : NeZero N := NeZero.of_pos i.pos;
    0 ≤ (⟪Matrix.toEuclideanLin ((parentRingInteraction A L N).term i) v,
      Matrix.toEuclideanLin ((parentRingInteraction A L N).term j) v⟫_ℂ).re :=
  re_inner_parentRingInteraction_term_nonneg_of_cyclic_windows_disjoint A hLN
    (CyclicWindowsDisjoint.of_not_cyclicWindowsOverlap hij) v

/-- **The parent interaction on the ring is frustration free** whenever the periodic MPS vector
on \(N\) sites is nonzero: its terms are positive semidefinite and annihilate that vector. This
is the statement that every MPS is a ground state of a frustration-free parent Hamiltonian,
[PGVWC07] (quant-ph/0608197), `MPSarchive.tex`, lines 311--330, and arXiv:2011.12127,
`TN-Review-main.tex`, line 537. -/
theorem isFrustrationFree_parentRingInteraction (A : MPSTensor d D) (L N : ℕ) [NeZero N]
    (hA : (mpv A : NSiteSpace d N) ≠ 0) : (parentRingInteraction A L N).IsFrustrationFree :=
  ManyBody.Interaction.isFrustrationFree_of_zeroSpace_ne_bot
    (fun i ↦ posSemidef_parentRingInteraction_term A L i)
    ((Submodule.ne_bot_iff _).mpr
      ⟨_, toLp_mpv_mem_zeroSpace_parentRingInteraction A L N, by simpa using hA⟩)

/-- The ground space at energy \(0\) of the Hamiltonian of the parent interaction on the ring
is the kernel of the parent Hamiltonian, read in the Euclidean space. -/
theorem groundSpace_hamiltonian_parentRingInteraction_eq_map_ker
    (A : MPSTensor d D) (L N : ℕ) [NeZero N] :
    ManyBody.groundSpace (parentRingInteraction A L N).hamiltonian 0 =
      (LinearMap.ker (parentHamiltonian A L N)).map
        (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm.toLinearMap := by
  ext v
  rw [ManyBody.mem_groundSpace_iff_mulVec, parentHamiltonian_eq_toLin'_hamiltonian A L,
    Submodule.mem_map_equiv, LinearEquiv.symm_symm, LinearMap.mem_ker, Complex.ofReal_zero,
    zero_smul]
  rfl

/-- The one-site ground space for the two-site parent interaction is the full
one-site Hilbert space under the project's zero convention.

**Scope restriction (one-site chain):** This is a consequence of
`parentHamiltonian_two_one_eq_zero`. Beigi, J. Phys. A 45 (2012) 025306,
Section III, does not specify a one-site action for its two-site
interaction, while CPSV16, arXiv:1606.00608, Theorem 3.10(iii), source lines
534--540, only uses chain lengths greater than two. This restriction is documented
in `docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`. -/
@[simp] theorem groundSpace_hamiltonian_parentRingInteraction_two_one_eq_top
    (A : MPSTensor d D) :
    ManyBody.groundSpace (parentRingInteraction A 2 1).hamiltonian 0 = ⊤ := by
  simp [groundSpace_hamiltonian_parentRingInteraction_eq_map_ker]

end MPSTensor

end

section

namespace MPSTensor

variable {d D : ℕ}

/-- If \(d^L > D^2\), the matrix of the canonical parent interaction is nonzero. -/
theorem toMatrix'_parentInteraction_ne_zero (A : MPSTensor d D) (L : ℕ)
    (hDim : d ^ L > D ^ 2) : LinearMap.toMatrix' (parentInteraction A L) ≠ 0 := by
  intro hzero
  apply groundSpace_ne_top A L hDim
  apply top_unique
  intro v _
  have hmem := (toEuclideanLin_toMatrix'_parentInteraction_apply_eq_zero_iff A L
    ((WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm v)).mp
      (by simp only [hzero, map_zero, LinearMap.zero_apply])
  simpa using (mem_groundSpaceES_iff A L _).mp hmem

/-- If \(d^L > D^2\), the canonical parent interaction is nonzero in the
original function-space coordinates. -/
theorem parentInteraction_ne_zero (A : MPSTensor d D) (L : ℕ)
    (hDim : d ^ L > D ^ 2) : parentInteraction A L ≠ 0 := fun hzero ↦
  toMatrix'_parentInteraction_ne_zero A L hDim (by rw [hzero, map_zero])

end MPSTensor

end

end Transport

section MatrixRepresentation

/-!
## Matrix coordinates for canonical parent Hamiltonians

The canonical local projection and its cyclic translates admit identical
matrix descriptions in the configuration basis and the Euclidean Hilbert
space. These identities connect the parent-Hamiltonian gap estimates to
the matrix formulation of local interactions used in arXiv:1010.3732,
Section II.B (`Papers/1010.3732/paper_v3.tex`, lines 357--390).
-/

open scoped Matrix.Norms.L2Operator

namespace MPSTensor

variable {d D : ℕ}

/-- A cyclic parent term is the matrix of its local interaction placed on the window of `L`
consecutive sites starting at `i`. Source: arXiv:1010.3732, Section II.B, the local Hamiltonian
sum. -/
theorem localTerm_eq_toLin'_placeAlong_ringWindow (A : MPSTensor d D)
    {L N : ℕ} (hLN : L ≤ N) (i : Fin N) :
    localTerm A L N i = Matrix.toLin'
      (ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hLN i)
        (LinearMap.toMatrix' (parentInteraction A L))) := by
  have : NeZero N := NeZero.of_pos i.pos
  rw [localTerm_eq_toLin'_term A L i,
    ManyBody.Interaction.translationInvariant_term_of_le _ hLN i]

/-- Canonical parent interactions have Hilbert-space operator norm at most
one, as do the projector local terms of arXiv:1010.3732, Section II.B. -/
theorem parentInteraction_toMatrix'_norm_le_one (A : MPSTensor d D) (L : ℕ) :
    ‖LinearMap.toMatrix' (parentInteraction A L)‖ ≤ 1 :=
  (isStarProjection_toMatrix'_parentInteraction A L).norm_le _

end MPSTensor

end MatrixRepresentation
