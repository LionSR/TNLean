/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.Defs
import TNLean.MPS.ParentHamiltonian.Basic
import TNLean.MPS.ParentHamiltonian.CyclicWindow
import TNLean.Analysis.ProjectionGeometry

/-!
# Euclidean local projectors and ground-space / Hamiltonian transport

**Root-only.** This file provides the `EuclideanSpace`-based definitions
and supporting lemmas for the parent-Hamiltonian martingale method:

* `parentInteractionES` — the `L`-site parent interaction as an orthogonal
  projector on the Hilbert-space model `EuclideanSpace ℂ (Cfg d L)`;
* `cyclicRestrictES` and `localTermESSummand` — cyclic-window restriction
  and the conjugated `Rᵢ,τ† P_L Rᵢ,τ` summands;
* `localTermES` and `parentHamiltonianES` — transported local terms and the
  full transported parent Hamiltonian on `EuclideanSpace`;
* positivity, idempotence, and symmetric-projection structure of the
  transported local terms;
* commutation and non-overlap positivity for disjoint cyclic windows;
* kernel identification: the transported ground space equals `ker(H_ES)`.

The private lemmas in this file handle the technical cyclic-window and
`SameOutsideWindow` combinatorics needed by the public theorems; they
are not exposed to downstream modules.
-/

open scoped BigOperators InnerProductSpace

namespace MPSTensor

variable {d D : ℕ}

/-! ### Euclidean local projector ingredients -/

/-- The `L`-site parent interaction viewed directly on the Hilbert-space model
`EuclideanSpace ℂ (Cfg d L)`. Equivalently, this is the orthogonal projector
onto `(groundSpaceES A L)ᗮ`. -/
noncomputable def parentInteractionES (A : MPSTensor d D) (L : ℕ) :
    EuclideanSpace ℂ (Cfg d L) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d L) :=
  ((groundSpaceES A L)ᗮ.starProjection.toLinearMap)

/-- The `EuclideanSpace` parent interaction is the symmetric projection onto
`(groundSpaceES A L)ᗮ`. -/
theorem parentInteractionES_isSymmetricProjection (A : MPSTensor d D) (L : ℕ) :
    (parentInteractionES A L).IsSymmetricProjection :=
  Submodule.isSymmetricProjection_starProjection ((groundSpaceES A L)ᗮ)

/-- The `EuclideanSpace` parent interaction is positive because it is an
orthogonal projection. -/
theorem parentInteractionES_isPositive (A : MPSTensor d D) (L : ℕ) :
    (parentInteractionES A L).IsPositive :=
  (parentInteractionES_isSymmetricProjection A L).isPositive

/-- The kernel of the Euclidean parent interaction is exactly the Euclidean MPS
local ground space. -/
theorem parentInteractionES_apply_eq_zero_iff (A : MPSTensor d D) (L : ℕ)
    (v : EuclideanSpace ℂ (Cfg d L)) :
    parentInteractionES A L v = 0 ↔ v ∈ groundSpaceES A L := by
  change (groundSpaceES A L)ᗮ.starProjection v = 0 ↔ v ∈ groundSpaceES A L
  rw [Submodule.starProjection_orthogonal']
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
  rw [sub_eq_zero, eq_comm, Submodule.starProjection_eq_self_iff]

/-- The cyclic window restriction map transported from `NSiteSpace` to the
Hilbert-space model `EuclideanSpace`. -/
noncomputable def cyclicRestrictES {N : ℕ} (hN : 0 < N) (L : ℕ) (i : Fin N)
    (τ : Fin N → Fin d) :
    EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d L) :=
  LinearMap.withLpMap 2 (cyclicRestrictₗ (d := d) hN L i τ)

/-- One positive summand in the future averaged `EuclideanSpace` formula for a
local parent-Hamiltonian term.

This is the conjugate `Rᵢ,τ† P_L Rᵢ,τ` of the local orthogonal projector
`P_L = parentInteractionES A L` by the transported cyclic restriction map
`Rᵢ,τ = cyclicRestrictES hN L i τ`. -/
noncomputable def localTermESSummand {N : ℕ} (A : MPSTensor d D) (hN : 0 < N)
    (L : ℕ) (i : Fin N) (τ : Fin N → Fin d) :
    EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  (cyclicRestrictES (d := d) hN L i τ).adjoint ∘ₗ
    parentInteractionES A L ∘ₗ
    cyclicRestrictES (d := d) hN L i τ

/-- Each conjugated cyclic-restriction summand `Rᵢ,τ† P_L Rᵢ,τ` is positive. -/
theorem localTermESSummand_isPositive {N : ℕ} (A : MPSTensor d D) (hN : 0 < N)
    (L : ℕ) (i : Fin N) (τ : Fin N → Fin d) :
    (localTermESSummand A hN L i τ).IsPositive := by
  simpa [localTermESSummand, LinearMap.adjoint_adjoint] using
    (LinearMap.IsPositive.conj_adjoint
      (hT := parentInteractionES_isPositive A L)
      ((cyclicRestrictES (d := d) hN L i τ).adjoint))

/-- The unnormalised finite sum of the future averaging summands is positive. -/
theorem localTermESSummand_sum_isPositive {N : ℕ} (A : MPSTensor d D) (hN : 0 < N)
    (L : ℕ) (i : Fin N) :
    (∑ τ : Cfg d N, localTermESSummand A hN L i τ).IsPositive := by
  exact LinearMap.isPositive_sum _ fun τ _ =>
    localTermESSummand_isPositive A hN L i τ

/-! ### Ground-space and Hamiltonian transport to `EuclideanSpace` -/

/-- The translated local parent-Hamiltonian term transported to the
`EuclideanSpace` model. -/
noncomputable def localTermES {N : ℕ} (A : MPSTensor d D) (L : ℕ) (i : Fin N) :
    EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  let e := (WithLp.linearEquiv 2 ℂ (NSiteSpace d N))
  e.symm.toLinearMap.comp ((localTerm A L N i).comp e.toLinearMap)

/-- Site-disjointness for two cyclic `L`-windows on an `N`-site periodic chain.

The window starting at `i` contains exactly the sites whose cyclic offset from `i`
is `< L`.  Thus `CyclicWindowsDisjoint L i j` says that no site has offset `< L`
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

/-- Ground-space submodule for the finite-size parent Hamiltonian,
transported to the `EuclideanSpace` (inner-product) setting so that
orthogonal complements are available. -/
noncomputable def parentHamiltonianGroundSpaceES (A : MPSTensor d D)
    (L N : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Cfg d N)) :=
  (LinearMap.ker (parentHamiltonian A L N)).map
    (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm.toLinearMap

/-- The parent Hamiltonian transported to `EuclideanSpace`. -/
noncomputable def parentHamiltonianES (A : MPSTensor d D) (L N : ℕ) :
    EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  let e := (WithLp.linearEquiv 2 ℂ (NSiteSpace d N))
  e.symm.toLinearMap.comp ((parentHamiltonian A L N).comp e.toLinearMap)

/-- The transported parent Hamiltonian is the sum of the transported local
terms. -/
theorem parentHamiltonianES_eq_sum_localTermES (A : MPSTensor d D) (L N : ℕ) :
    parentHamiltonianES A L N = ∑ i : Fin N, localTermES A L i := by
  ext v σ
  simp [parentHamiltonianES, parentHamiltonian, localTermES]

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
  rw [dif_neg hnotj]

private theorem replaceWindow_commute_of_cyclic_windows_disjoint {N L : ℕ}
    (hLN : L ≤ N) {i j : Fin N} (hij : CyclicWindowsDisjoint L i j)
    (σ : Cfg d N) (α β : Cfg d L) :
    replaceWindow L hLN j (replaceWindow L hLN i σ α) β =
      replaceWindow L hLN i (replaceWindow L hLN j σ β) α := by
  funext k
  by_cases hi : ((k.val + N - i.val) % N < L)
  · have hnotj : ¬ ((k.val + N - j.val) % N < L) := fun hj => hij k hi hj
    simp [replaceWindow, hi, hnotj]
  · by_cases hj : ((k.val + N - j.val) % N < L)
    · simp [replaceWindow, hi, hj]
    · simp [replaceWindow, hi, hj]

private theorem euclideanSpace_eq_sum_single {α : Type*} [Fintype α] [DecidableEq α]
    (x : EuclideanSpace ℂ α) :
    x = ∑ a : α, x a • EuclideanSpace.single a (1 : ℂ) := by
  ext a
  simp [Finset.sum_apply, Pi.single_apply]

private theorem linearMap_apply_eq_sum {α : Type*} [Fintype α] [DecidableEq α]
    (P : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α)
    (x : EuclideanSpace ℂ α) (a : α) :
    P x a = ∑ a' : α, x a' * P (EuclideanSpace.single a' (1 : ℂ)) a := by
  conv_lhs => rw [euclideanSpace_eq_sum_single x]
  simp [Finset.sum_apply]

private theorem scalar_sum_comm {α β : Type*} [Fintype α] [Fintype β]
    (F : α → β → ℂ) (p : α → ℂ) (q : β → ℂ) :
    (∑ a, (∑ b, F a b * q b) * p a) =
      ∑ b, (∑ a, F a b * p a) * q b := by
  calc
    (∑ a, (∑ b, F a b * q b) * p a)
        = ∑ a, ∑ b, F a b * q b * p a := by
      simp_rw [Finset.sum_mul]
    _ = ∑ b, ∑ a, F a b * q b * p a := by
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ a, F a b * p a * q b := by
      refine Finset.sum_congr rfl ?_
      intro b _
      refine Finset.sum_congr rfl ?_
      intro a _
      ring
    _ = ∑ b, (∑ a, F a b * p a) * q b := by
      simp_rw [Finset.sum_mul]

private theorem separateLinearMap_apply_commute
    {α β : Type*} [Fintype α] [Fintype β]
    (P : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α)
    (Q : EuclideanSpace ℂ β →ₗ[ℂ] EuclideanSpace ℂ β)
    (F : α → β → ℂ) (a : α) (b : β) :
    P (WithLp.toLp 2 (fun a' => Q (WithLp.toLp 2 (fun b' => F a' b')) b)) a =
      Q (WithLp.toLp 2 (fun b' => P (WithLp.toLp 2 (fun a' => F a' b')) a)) b := by
  classical
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
  by_cases hστ : SameOutsideWindow (L := L) i σ τ
  · calc
      ((cyclicRestrictES (d := d) hN L i τ).adjoint v) σ
          = ⟪EuclideanSpace.single σ (1 : ℂ),
              (cyclicRestrictES (d := d) hN L i τ).adjoint v⟫_ℂ := by
              simpa using (EuclideanSpace.inner_single_left σ (1 : ℂ)
                ((cyclicRestrictES (d := d) hN L i τ).adjoint v)).symm
      _ = ⟪cyclicRestrictES (d := d) hN L i τ
              (EuclideanSpace.single σ (1 : ℂ)), v⟫_ℂ := by
            rw [LinearMap.adjoint_inner_right]
      _ = ⟪EuclideanSpace.single (extractWindow L i σ) (1 : ℂ), v⟫_ℂ := by
            rw [cyclicRestrictES_single_of_sameOutsideWindow hN hLN i σ τ hστ]
      _ = if SameOutsideWindow (L := L) i σ τ then v (extractWindow L i σ) else 0 := by
            simpa [hστ] using
              (EuclideanSpace.inner_single_left (extractWindow L i σ) (1 : ℂ) v)
  · calc
      ((cyclicRestrictES (d := d) hN L i τ).adjoint v) σ
          = ⟪EuclideanSpace.single σ (1 : ℂ),
              (cyclicRestrictES (d := d) hN L i τ).adjoint v⟫_ℂ := by
              simpa using (EuclideanSpace.inner_single_left σ (1 : ℂ)
                ((cyclicRestrictES (d := d) hN L i τ).adjoint v)).symm
      _ = ⟪cyclicRestrictES (d := d) hN L i τ
              (EuclideanSpace.single σ (1 : ℂ)), v⟫_ℂ := by
            rw [LinearMap.adjoint_inner_right]
      _ = ⟪0, v⟫_ℂ := by
            rw [cyclicRestrictES_single_of_not_sameOutsideWindow hN i σ τ hστ]
      _ = if SameOutsideWindow (L := L) i σ τ then v (extractWindow L i σ) else 0 := by
            simp [hστ]

@[simp] private theorem localTermES_apply {N : ℕ} (A : MPSTensor d D) (L : ℕ) (i : Fin N)
    (hLN : L ≤ N) (v : EuclideanSpace ℂ (Cfg d N)) (σ : Cfg d N) :
    localTermES A L i v σ =
      parentInteractionES A L ((cyclicRestrictES (d := d) (Fin.pos i) L i σ) v)
        (extractWindow L i σ) := by
  have hcfg :
      WithLp.toLp 2 ((LinearMap.pi fun τ =>
        (LinearMap.proj (replaceWindow L hLN i σ τ) : NSiteSpace d N →ₗ[ℂ] ℂ)) v.ofLp) =
      (cyclicRestrictES (d := d) (Fin.pos i) L i σ) v := by
    ext τ
    simp [cyclicRestrictES, cyclicCfg_eq_replaceWindow, hLN]
  have hself : cyclicCfg (d := d) (Fin.pos i) L i (extractWindow L i σ) σ = σ := by
    rw [cyclicCfg_eq_replaceWindow (d := d) (Fin.pos i) L hLN]
    exact replaceWindow_extractWindow L hLN i σ
  simp [localTermES, localTerm, hLN, parentInteraction, parentInteractionES]
  simp [hcfg, hself]

private theorem cyclicRestrictES_localTermES {N : ℕ} (A : MPSTensor d D) {L : ℕ}
    (hLN : L ≤ N) (i : Fin N) (τ : Cfg d N) (v : EuclideanSpace ℂ (Cfg d N)) :
    cyclicRestrictES (d := d) (Fin.pos i) L i τ (localTermES A L i v) =
      parentInteractionES A L (cyclicRestrictES (d := d) (Fin.pos i) L i τ v) := by
  ext ω
  rw [cyclicRestrictES_apply]
  rw [localTermES_apply A L i hLN v (cyclicCfg (d := d) (Fin.pos i) L i ω τ)]
  have hsame : SameOutsideWindow (L := L) i (cyclicCfg (d := d) (Fin.pos i) L i ω τ) τ :=
    sameOutsideWindow_of_cyclicCfg_eq (d := d) (Fin.pos i) i rfl
  have hrestrict :
      cyclicRestrictES (d := d) (Fin.pos i) L i τ =
        cyclicRestrictES (d := d) (Fin.pos i) L i (cyclicCfg (d := d) (Fin.pos i) L i ω τ) :=
    cyclicRestrictES_eq_of_sameOutsideWindow (d := d) (Fin.pos i) i hsame
  have hextract : extractWindow L i (cyclicCfg (d := d) (Fin.pos i) L i ω τ) = ω := by
    rw [cyclicCfg_eq_replaceWindow (d := d) (Fin.pos i) L hLN]
    exact extractWindow_replaceWindow L hLN i τ ω
  rw [← hrestrict, hextract]

/-- A transported local term vanishes exactly when every boundary-filled cyclic
restriction to its window lies in the `L`-site MPS ground space. -/
theorem localTermES_eq_zero_iff_forall_cyclicRestrictES_mem_groundSpaceES {N : ℕ}
    (A : MPSTensor d D) {L : ℕ} (hLN : L ≤ N) (i : Fin N)
    (v : EuclideanSpace ℂ (Cfg d N)) :
    localTermES A L i v = 0 ↔
      ∀ τ : Cfg d N,
        cyclicRestrictES (d := d) (Fin.pos i) L i τ v ∈ groundSpaceES A L := by
  constructor
  · intro hv τ
    rw [← parentInteractionES_apply_eq_zero_iff]
    rw [← cyclicRestrictES_localTermES A hLN i τ v, hv, map_zero]
  · intro hv
    ext σ
    rw [localTermES_apply A L i hLN v σ]
    have hker := (parentInteractionES_apply_eq_zero_iff A L
      (cyclicRestrictES (d := d) (Fin.pos i) L i σ v)).2 (hv σ)
    rw [hker]
    rfl

/-- If a transported local term vanishes, every cyclic restriction to its window
is an element of the corresponding MPS ground space. -/
theorem cyclicRestrictES_mem_groundSpaceES_of_localTermES_eq_zero {N : ℕ}
    (A : MPSTensor d D) {L : ℕ} (hLN : L ≤ N) (i : Fin N)
    {v : EuclideanSpace ℂ (Cfg d N)} (hv : localTermES A L i v = 0)
    (τ : Cfg d N) :
    cyclicRestrictES (d := d) (Fin.pos i) L i τ v ∈ groundSpaceES A L :=
  (localTermES_eq_zero_iff_forall_cyclicRestrictES_mem_groundSpaceES A hLN i v).1 hv τ

private theorem restrictLast_eq_cyclicRestrictES_zero {L : ℕ}
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

private theorem restrictFirst_eq_cyclicRestrictES_one {L : ℕ} (hL : 0 < L)
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
  have hOneNat : 1 % (L + 1) = 1 := Nat.mod_eq_of_lt (by omega)
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨r, rfl⟩
  · simp [cyclicCfg, hOneNat]
  · have hmod : (r.val + 1 + L) % (L + 1) = r.val := by
      rw [show r.val + 1 + L = r.val + (L + 1) by omega]
      rw [Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    simp [cyclicCfg, hOneNat, hmod]

/-- Forward local intersection property for adjacent transported local terms.

On an `(L+1)`-site chain, if the two overlapping `L`-site local terms based at
`0` and `1` both annihilate a vector, then the vector lies in the `(L+1)`-site
MPS ground space.  This is the Euclidean/local-projector form of the
open-chain intersection property `groundSpace_intersection`; it is a structural
predecessor to the quantitative Friedrichs-angle estimate for overlapping
windows. -/
theorem mem_groundSpaceES_succ_of_adjacent_localTermES_eq_zero {A : MPSTensor d D}
    (hA : IsInjective A) {L : ℕ} (hL : 1 < L)
    {v : EuclideanSpace ℂ (Cfg d (L + 1))}
    (hleft : localTermES A L (0 : Fin (L + 1)) v = 0)
    (hright : localTermES A L (1 : Fin (L + 1)) v = 0) :
    v ∈ groundSpaceES A (L + 1) := by
  let eN := WithLp.linearEquiv 2 ℂ (NSiteSpace d (L + 1))
  have hLN : L ≤ L + 1 := by omega
  have hLeft : InLeftGround A L (eN v) := by
    intro j
    have hmemES : cyclicRestrictES (d := d) (Fin.pos (0 : Fin (L + 1))) L
        (0 : Fin (L + 1)) (fun _ => j) v ∈ groundSpaceES A L :=
      cyclicRestrictES_mem_groundSpaceES_of_localTermES_eq_zero A hLN
        (0 : Fin (L + 1)) hleft (fun _ => j)
    have hmemNS := (mem_groundSpaceES_iff A L _).1 hmemES
    rwa [restrictLast_eq_cyclicRestrictES_zero v (fun _ => j)]
  have hRight : InRightGround A L (eN v) := by
    intro i
    have hmemES : cyclicRestrictES (d := d) (Fin.pos (1 : Fin (L + 1))) L
        (1 : Fin (L + 1)) (fun _ => i) v ∈ groundSpaceES A L :=
      cyclicRestrictES_mem_groundSpaceES_of_localTermES_eq_zero A hLN
        (1 : Fin (L + 1)) hright (fun _ => i)
    have hmemNS := (mem_groundSpaceES_iff A L _).1 hmemES
    rwa [restrictFirst_eq_cyclicRestrictES_one (by omega : 0 < L) v (fun _ => i)]
  have hψ : eN v ∈ groundSpace A (L + 1) :=
    groundSpace_intersection hA hL hLeft hRight
  exact (mem_groundSpaceES_iff A (L + 1) v).2 hψ

/-- Vectors in the `(L+1)`-site MPS ground space are killed by the two adjacent
`L`-site transported local terms. -/
theorem adjacent_localTermES_eq_zero_of_mem_groundSpaceES_succ
    (A : MPSTensor d D) {L : ℕ} (hL : 0 < L)
    {v : EuclideanSpace ℂ (Cfg d (L + 1))} (hv : v ∈ groundSpaceES A (L + 1)) :
    localTermES A L (0 : Fin (L + 1)) v = 0 ∧
      localTermES A L (1 : Fin (L + 1)) v = 0 := by
  let eN := WithLp.linearEquiv 2 ℂ (NSiteSpace d (L + 1))
  have hψ : eN v ∈ groundSpace A (L + 1) := (mem_groundSpaceES_iff A (L + 1) v).1 hv
  have hLN : L ≤ L + 1 := by omega
  constructor
  · rw [localTermES_eq_zero_iff_forall_cyclicRestrictES_mem_groundSpaceES A hLN
      (0 : Fin (L + 1)) v]
    intro τ
    rw [mem_groundSpaceES_iff]
    rw [← restrictLast_eq_cyclicRestrictES_zero v τ]
    exact groundSpace_inLeftGround A L hψ (τ (Fin.last L))
  · rw [localTermES_eq_zero_iff_forall_cyclicRestrictES_mem_groundSpaceES A hLN
      (1 : Fin (L + 1)) v]
    intro τ
    rw [mem_groundSpaceES_iff]
    rw [← restrictFirst_eq_cyclicRestrictES_one hL v τ]
    exact groundSpace_inRightGround A L hψ (τ 0)

/-- Adjacent local kernels on an `(L+1)`-site chain intersect in the MPS ground
space.  This restates the open-chain intersection property in the same
Euclidean local-projector language used by the martingale proof. -/
theorem adjacent_localTermES_eq_zero_iff_mem_groundSpaceES_succ {A : MPSTensor d D}
    (hA : IsInjective A) {L : ℕ} (hL : 1 < L)
    {v : EuclideanSpace ℂ (Cfg d (L + 1))} :
    localTermES A L (0 : Fin (L + 1)) v = 0 ∧
      localTermES A L (1 : Fin (L + 1)) v = 0 ↔
        v ∈ groundSpaceES A (L + 1) := by
  constructor
  · intro h
    exact mem_groundSpaceES_succ_of_adjacent_localTermES_eq_zero hA hL h.1 h.2
  · intro hv
    exact adjacent_localTermES_eq_zero_of_mem_groundSpaceES_succ A (by omega : 0 < L) hv

@[simp] private theorem localTermESSummand_apply {N : ℕ} (A : MPSTensor d D) (hN : 0 < N)
    {L : ℕ} (hLN : L ≤ N) (i : Fin N) (τ v σ) :
    localTermESSummand A hN L i τ v σ =
      if SameOutsideWindow (L := L) i σ τ then localTermES A L i v σ else 0 := by
  classical
  rw [localTermESSummand]
  simp only [LinearMap.comp_apply]
  by_cases hστ : SameOutsideWindow (L := L) i σ τ
  · rw [cyclicRestrictES_adjoint_apply hN hLN i σ τ]
    rw [if_pos hστ, localTermES_apply A L i hLN v σ]
    simp [hστ, cyclicRestrictES_eq_of_sameOutsideWindow hN i hστ]
  · rw [cyclicRestrictES_adjoint_apply hN hLN i σ τ, if_neg hστ]
    simp [hστ]

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

/-- The transported local term is the cyclic average of the positive Euclidean
summands `Rᵢ,τ† P_L Rᵢ,τ`. -/
theorem localTermES_eq_average_localTermESSummand {N : ℕ} (A : MPSTensor d D)
    {L : ℕ} (hLN : L ≤ N) (i : Fin N) :
    localTermES A L i =
      ((((d ^ L : ℕ) : ℂ)⁻¹) •
        (∑ τ : Cfg d N, localTermESSummand A (Fin.pos i) L i τ)) := by
  classical
  ext v σ
  let q : Cfg d N → Prop := SameOutsideWindow (L := L) i σ
  let sq : Finset (Cfg d N) := Finset.univ.filter q
  have hfilter :
      (∑ τ : Cfg d N, if q τ then localTermES A L i v σ else 0) =
        sq.sum (fun _ => localTermES A L i v σ) := by
    dsimp [sq]
    symm
    simpa using (Finset.sum_filter (s := Finset.univ) (p := q)
      (f := fun _ => localTermES A L i v σ))
  have hsconst :
      sq.sum (fun _ => localTermES A L i v σ) =
        sq.card • localTermES A L i v σ := by
    exact Finset.sum_const (s := sq) (b := localTermES A L i v σ)
  have hcard_filter : sq.card = Fintype.card {τ : Cfg d N // q τ} := by
    dsimp [sq]
    symm
    simpa using (Fintype.card_subtype q)
  have hne_nat : (d ^ L : ℕ) ≠ 0 := by
    have hcard : Fintype.card (Cfg d L) = d ^ L := by
      simp [Cfg]
    have : Fintype.card (Cfg d L) ≠ 0 := by
      let _ : Nonempty (Cfg d L) := ⟨extractWindow L i σ⟩
      exact Fintype.card_ne_zero
    rwa [hcard] at this
  have hne : (((d ^ L : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast hne_nat
  calc
    localTermES A L i v σ
        = (((d ^ L : ℕ) : ℂ)⁻¹) * ((d ^ L) • localTermES A L i v σ) := by
            symm
            rw [nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    _ = (((d ^ L : ℕ) : ℂ)⁻¹) *
          (Fintype.card {τ : Cfg d N // q τ} • localTermES A L i v σ) := by
            rw [sameOutsideWindow_card hLN i σ]
    _ = (((d ^ L : ℕ) : ℂ)⁻¹) *
          (sq.card • localTermES A L i v σ) := by rw [hcard_filter]
    _ = (((d ^ L : ℕ) : ℂ)⁻¹) *
          (sq.sum (fun _ => localTermES A L i v σ)) := by rw [hsconst]
    _ = (((d ^ L : ℕ) : ℂ)⁻¹) *
          (∑ τ : Cfg d N, if q τ then localTermES A L i v σ else 0) := by rw [hfilter]
    _ = (((d ^ L : ℕ) : ℂ)⁻¹) *
          (∑ τ : Cfg d N, localTermESSummand A (Fin.pos i) L i τ v σ) := by
            simp [q, localTermESSummand_apply, hLN]
    _ = ((((d ^ L : ℕ) : ℂ)⁻¹) • (∑ τ : Cfg d N,
          localTermESSummand A (Fin.pos i) L i τ)) v σ := by
            simp

private theorem isPositive_smul_of_real_re_nonneg {ι : Type*} [Fintype ι]
    {T : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι} (hT : T.IsPositive) {c : ℂ}
    (hc_star : star c = c) (hc_re : 0 ≤ c.re) :
    (c • T).IsPositive := by
  refine ⟨hT.left.smul hc_star, fun x => ?_⟩
  have him : c.im = 0 := by
    have him' := congrArg Complex.im hc_star
    simp at him'
    linarith
  have himstar : RCLike.im ((starRingEnd ℂ) c) = 0 := by
    simp [him]
  have hre : RCLike.re ((starRingEnd ℂ) c) = c.re := by
    simp
  change 0 ≤ RCLike.re ⟪c • T x, x⟫_ℂ
  rw [inner_smul_left, RCLike.mul_re, himstar, zero_mul, sub_zero, hre]
  exact mul_nonneg hc_re (hT.re_inner_nonneg_left x)

/-- The transported local term is positive because it is a finite cyclic average
of the positive summands `Rᵢ,τ† P_L Rᵢ,τ`. -/
theorem localTermES_isPositive {N : ℕ} (A : MPSTensor d D) (L : ℕ) (i : Fin N) :
    (localTermES A L i).IsPositive := by
  by_cases hLN : L ≤ N
  · rw [localTermES_eq_average_localTermESSummand A hLN i]
    refine isPositive_smul_of_real_re_nonneg
      (localTermESSummand_sum_isPositive A (Fin.pos i) L i) ?_ ?_
    · simp
    · rw [Complex.inv_re, Complex.normSq_natCast]
      have hnonneg : 0 ≤ ((d ^ L : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le (d ^ L)
      exact div_nonneg hnonneg (mul_nonneg hnonneg hnonneg)
  · simp [localTermES, localTerm, hLN]

private theorem localTermES_isIdempotentElem {N : ℕ} (A : MPSTensor d D) (L : ℕ)
    (i : Fin N) : IsIdempotentElem (localTermES A L i) := by
  by_cases hLN : L ≤ N
  · rw [isIdempotentElem_iff]
    ext v σ
    change localTermES A L i (localTermES A L i v) σ = localTermES A L i v σ
    rw [localTermES_apply A L i hLN (localTermES A L i v) σ]
    rw [cyclicRestrictES_localTermES A hLN i σ v]
    rw [localTermES_apply A L i hLN v σ]
    have hPapply :
        parentInteractionES A L
            (parentInteractionES A L ((cyclicRestrictES (d := d) (Fin.pos i) L i σ) v)) =
          parentInteractionES A L ((cyclicRestrictES (d := d) (Fin.pos i) L i σ) v) := by
      simpa [Module.End.mul_apply] using
        LinearMap.congr_fun
          (parentInteractionES_isSymmetricProjection A L).isIdempotentElem.eq
          ((cyclicRestrictES (d := d) (Fin.pos i) L i σ) v)
    rw [hPapply]
  · simpa [localTermES, localTerm, hLN] using
      (IsIdempotentElem.zero :
        IsIdempotentElem
          (0 : EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N)))

/-- Each transported local parent-Hamiltonian term is a symmetric projection.

This is the Euclidean-space version of the fact that the local term is the
orthogonal projector onto the complement of the translated local ground space.
For `L ≤ N`, idempotence follows by restricting to the cyclic window, applying
the local projector `parentInteractionES`, and using `P_L^2 = P_L`; for `L > N`
the definition gives the zero projection. -/
theorem localTermES_isSymmetricProjection {N : ℕ} (A : MPSTensor d D) (L : ℕ)
    (i : Fin N) : (localTermES A L i).IsSymmetricProjection :=
  ⟨localTermES_isIdempotentElem A L i, (localTermES_isPositive A L i).isSymmetric⟩

/-- Transported local terms on site-disjoint cyclic windows commute pointwise.

If `L ≤ N` and no site belongs to both cyclic windows based at `i` and `j`, then
applying the two transported local ES terms in either order gives the same vector.
This is the non-overlap commutation input for the finite-overlap martingale
reduction. -/
theorem localTermES_commute_of_cyclic_windows_disjoint {N : ℕ} (A : MPSTensor d D)
    {L : ℕ} (hLN : L ≤ N) {i j : Fin N} (hij : CyclicWindowsDisjoint L i j)
    (v : EuclideanSpace ℂ (Cfg d N)) :
    localTermES A L i (localTermES A L j v) =
      localTermES A L j (localTermES A L i v) := by
  ext σ
  let P := parentInteractionES A L
  let F : Cfg d L → Cfg d L → ℂ := fun α β =>
    v (replaceWindow L hLN j (replaceWindow L hLN i σ α) β)
  have hleft :
      cyclicRestrictES (d := d) (Fin.pos i) L i σ (localTermES A L j v) =
        WithLp.toLp 2 (fun α => P (WithLp.toLp 2 (fun β => F α β))
          (extractWindow L j σ)) := by
    ext α
    rw [cyclicRestrictES_apply]
    rw [cyclicCfg_eq_replaceWindow (d := d) (Fin.pos i) L hLN]
    rw [localTermES_apply A L j hLN v (replaceWindow L hLN i σ α)]
    rw [extractWindow_replaceWindow_of_cyclic_windows_disjoint (d := d) hLN hij.symm σ α]
    have hrestrict :
        cyclicRestrictES (d := d) (Fin.pos j) L j (replaceWindow L hLN i σ α) v =
          WithLp.toLp 2 (fun β => F α β) := by
      ext β
      rw [cyclicRestrictES_apply]
      rw [cyclicCfg_eq_replaceWindow (d := d) (Fin.pos j) L hLN]
    rw [hrestrict]
  have hright :
      cyclicRestrictES (d := d) (Fin.pos j) L j σ (localTermES A L i v) =
        WithLp.toLp 2 (fun β => P (WithLp.toLp 2 (fun α => F α β))
          (extractWindow L i σ)) := by
    ext β
    rw [cyclicRestrictES_apply]
    rw [cyclicCfg_eq_replaceWindow (d := d) (Fin.pos j) L hLN]
    rw [localTermES_apply A L i hLN v (replaceWindow L hLN j σ β)]
    rw [extractWindow_replaceWindow_of_cyclic_windows_disjoint (d := d) hLN hij σ β]
    have hrestrict :
        cyclicRestrictES (d := d) (Fin.pos i) L i (replaceWindow L hLN j σ β) v =
          WithLp.toLp 2 (fun α => F α β) := by
      ext α
      rw [cyclicRestrictES_apply]
      rw [cyclicCfg_eq_replaceWindow (d := d) (Fin.pos i) L hLN]
      simp only [F]
      rw [← replaceWindow_commute_of_cyclic_windows_disjoint (d := d) hLN hij σ α β]
    rw [hrestrict]
  rw [localTermES_apply A L i hLN (localTermES A L j v) σ]
  rw [localTermES_apply A L j hLN (localTermES A L i v) σ]
  rw [hleft, hright]
  simpa [P] using separateLinearMap_apply_commute P P F (extractWindow L i σ)
    (extractWindow L j σ)

/-- Non-overlap positivity for transported local terms on disjoint cyclic windows.

For `L ≤ N`, if the cyclic windows based at `i` and `j` have no common site, then
the ordered cross term of the corresponding transported local ES projections is
nonnegative: `0 ≤ Re ⟪h_i v, h_j v⟫`. -/
theorem localTermES_re_inner_nonneg_of_cyclic_windows_disjoint {N : ℕ}
    (A : MPSTensor d D) {L : ℕ} (hLN : L ≤ N) {i j : Fin N}
    (hij : CyclicWindowsDisjoint L i j) (v : EuclideanSpace ℂ (Cfg d N)) :
    0 ≤ (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re :=
  LinearMap.IsSymmetricProjection.re_inner_apply_apply_nonneg_of_commute
    (localTermES_isSymmetricProjection A L i)
    (localTermES_isSymmetricProjection A L j)
    (localTermES_commute_of_cyclic_windows_disjoint A hLN hij) v

/-- Non-overlap positivity for the concrete cyclic-window overlap predicate.

When `cyclicWindowsOverlap N L i j` fails and `L ≤ N`, the two windows are
site-disjoint, so the transported local terms commute and have nonnegative ordered
cross term. -/
theorem localTermES_re_inner_nonneg_of_not_cyclicWindowsOverlap {N : ℕ}
    (A : MPSTensor d D) {L : ℕ} (hLN : L ≤ N) {i j : Fin N}
    (hij : ¬ cyclicWindowsOverlap N L i j) (v : EuclideanSpace ℂ (Cfg d N)) :
    0 ≤ (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re :=
  localTermES_re_inner_nonneg_of_cyclic_windows_disjoint A hLN
    (CyclicWindowsDisjoint.of_not_cyclicWindowsOverlap hij) v

/-- The full transported parent Hamiltonian is positive because it is a finite
sum of positive transported local terms. -/
theorem parentHamiltonianES_isPositive (A : MPSTensor d D) (L N : ℕ) :
    (parentHamiltonianES A L N).IsPositive := by
  rw [parentHamiltonianES_eq_sum_localTermES]
  exact LinearMap.isPositive_sum _ fun i _ => localTermES_isPositive A L i

/-- The transported parent-Hamiltonian ground space is exactly the kernel of the
transported parent Hamiltonian. -/
theorem parentHamiltonianGroundSpaceES_eq_ker_parentHamiltonianES
    (A : MPSTensor d D) (L N : ℕ) :
    parentHamiltonianGroundSpaceES A L N =
      LinearMap.ker (parentHamiltonianES A L N) := by
  let e := WithLp.linearEquiv 2 ℂ (NSiteSpace d N)
  ext v
  constructor
  · intro hv
    rw [parentHamiltonianGroundSpaceES, Submodule.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    rw [LinearMap.mem_ker] at hw ⊢
    simpa [parentHamiltonianES, e] using congrArg e.symm hw
  · intro hv
    rw [LinearMap.mem_ker] at hv
    rw [parentHamiltonianGroundSpaceES, Submodule.mem_map]
    refine ⟨e v, ?_, by simp [e]⟩
    rw [LinearMap.mem_ker]
    have hv' := congrArg e hv
    simpa [parentHamiltonianES, e] using hv'

@[simp] theorem mem_parentHamiltonianGroundSpaceES_iff
    (A : MPSTensor d D) (L N : ℕ) (v : EuclideanSpace ℂ (Cfg d N)) :
    v ∈ parentHamiltonianGroundSpaceES A L N ↔ parentHamiltonianES A L N v = 0 := by
  rw [parentHamiltonianGroundSpaceES_eq_ker_parentHamiltonianES, LinearMap.mem_ker]

end MPSTensor
