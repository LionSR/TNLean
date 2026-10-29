/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleBoundaryIntersection
import TNLean.MPS.ParentHamiltonian.UnclePeriodicClosure
import TNLean.MPS.ParentHamiltonian.UncleKernelConditions
import Mathlib.Algebra.Group.Fin.Basic

/-!
# The actual periodic uncle Hamiltonian ground space

The actual cyclic local-kernel conditions imply membership in the open
single-wall boundary space by the existing generic intersection iteration.
Applying the same argument to one cyclic translate gives the source closure
intersection, which contains exactly the two periodic MPS sectors.

Source: arXiv:1210.6613, Theorem thm:gs-subspace-uncle, lines 1043–1150.
The finite periodic length is at least two. Only the source's full
injective-perturbation condition is assumed; no intersection, closure or
kernel equality is supplied as an extra hypothesis.
-/

noncomputable section

open scoped Matrix BigOperators

namespace MPSTensor

variable {d a b : ℕ}

private theorem blockedConfigEquiv_one_two (σ : Cfg (blockPhysDim d 2) 1) :
    blockedConfigEquiv d 1 2 σ = decodeBlock d 2 (σ 0) := by
  apply List.ofFn_injective
  rw [ofFn_blockedConfigEquiv]
  simp only [List.ofFn_succ, List.ofFn_zero, flattenBlockedWord_cons,
    flattenBlockedWord_nil, List.append_nil]

/-- The actual two-site uncle boundary space is exactly the local projector
kernel in the original physical coordinates. Source: arXiv:1210.6613,
equation Sn-def and the local starting point in thm:gs-subspace-uncle,
lines 1073–1105. -/
theorem mem_uncleBoundarySpace_two_iff
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (ψ : NSiteSpace d 2) :
    ψ ∈ uncleBoundarySpace A B R L 2 ↔
      uncleInteractionES A B R L
        ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm ψ) = 0 := by
  let f : NSiteSpace d 2 ≃ₗ[ℂ] NSiteSpace (blockPhysDim d 2) 1 :=
    LinearEquiv.funCongrLeft ℂ ℂ (blockedConfigEquiv d 1 2)
  have hmap (X : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) :
      f (uncleBoundaryMap A B R L 2 X) =
        groundSpaceMap (uncleTensor A B R L) 1 X := by
    ext σ
    change uncleBoundaryMap A B R L 2 X (blockedConfigEquiv d 1 2 σ) = _
    rw [uncleBoundaryMap_two, blockedConfigEquiv_one_two]
    have hcfg : (fun _ : Fin 1 ↦ (decodeBlockEquiv d 2).symm
        (decodeBlock d 2 (σ 0))) = σ := by
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact (decodeBlockEquiv d 2).symm_apply_apply (σ 0)
    rw [hcfg]
  rw [uncleInteractionES_apply_eq_zero_iff, mem_groundSpaceES_iff]
  change ψ ∈ uncleBoundarySpace A B R L 2 ↔
    f ψ ∈ groundSpace (uncleTensor A B R L) 1
  constructor
  · rintro ⟨X, rfl⟩
    exact ⟨X, (hmap X).symm⟩
  · rintro ⟨X, hX⟩
    exact ⟨X, f.injective ((hmap X).trans hX)⟩

/-- The actual finite Hamiltonian kernel imposes precisely the cyclic
length-two source boundary constraints. Source: arXiv:1210.6613,
thm:gs-subspace-uncle, lines 1050–1073. -/
theorem uncleHamiltonianES_apply_eq_zero_iff_boundary_windows
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    {N : ℕ} (hN : 2 ≤ N) (ψ : NSiteSpace d N) :
    uncleHamiltonianES A B R L N
        ((WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm ψ) = 0 ↔
      ∀ (i : Fin N) (τ : Cfg d N),
        cyclicRestrictₗ (Fin.pos i) 2 i τ ψ ∈ uncleBoundarySpace A B R L 2 := by
  rw [uncleHamiltonianES_apply_eq_zero_iff A B R L hN]
  apply forall_congr' fun i ↦ forall_congr' fun τ ↦ ?_
  simpa [cyclicRestrictES, LinearMap.withLpMap] using
    (mem_uncleBoundarySpace_two_iff A B R L
      (cyclicRestrictₗ (Fin.pos i) 2 i τ ψ)).symm

/-- The source's derived intersection property reconstructs the full open
boundary space from nonwrapping two-site constraints. Source:
arXiv:1210.6613, thm:gs-subspace-uncle, lines 1098–1113. -/
theorem mem_uncleBoundarySpace_of_cyclic_windows
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (uncleBoundaryLetter A B R L))
    {N : ℕ} (hN : 2 ≤ N) (ψ : NSiteSpace d N)
    (hwindow : ∀ (i : Fin N) (τ : Cfg d N),
      cyclicRestrictₗ (Fin.pos i) 2 i τ ψ ∈ uncleBoundarySpace A B R L 2) :
    ψ ∈ uncleBoundarySpace A B R L N := by
  by_cases hd : d = 0
  · subst d
    have hψ : ψ = 0 := by
      ext σ
      exact Fin.elim0 (σ ⟨0, by omega⟩)
    rw [hψ]
    exact Submodule.zero_mem _
  letI : NeZero d := ⟨hd⟩
  apply contiguous_mem_of_restriction_intersection_submodules
    (uncleBoundarySpace A B R L) (by omega : 0 < 2) hN
  · intro M hM
    simpa only [show M - 2 + 2 = M by omega,
      show M - 2 + 3 = M + 1 by omega] using
      uncleBoundarySpace_intersection A B R L hPert (M - 2)
  · intro s hs τ
    let i : Fin N := ⟨s, by omega⟩
    have h := hwindow i τ
    rw [cyclicRestrictₗ_eq_contiguousRestrictₗ (Fin.pos i) hN
      (show i.val + 2 ≤ N from hs)] at h
    exact h

/-- The actual periodic uncle Hamiltonian kernel is the span of the two
sector MPS vectors. This is arXiv:1210.6613, Theorem
thm:gs-subspace-uncle, lines 1043–1150, at every length n+2.
The intersection and closure properties are derived from the injective
perturbation; neither is a premise of this statement. -/
theorem ker_uncleHamiltonianES_eq_span_mpv
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (uncleBoundaryLetter A B R L)) (n : ℕ) :
    LinearMap.ker (uncleHamiltonianES A B R L (n + 2)).toLinearMap =
      Submodule.span ℂ
        {(WithLp.linearEquiv 2 ℂ (NSiteSpace d (n + 2))).symm (mpv A),
          (WithLp.linearEquiv 2 ℂ (NSiteSpace d (n + 2))).symm (mpv B)} := by
  apply le_antisymm
  · intro v hv
    change uncleHamiltonianES A B R L (n + 2) v = 0 at hv
    let ψ : NSiteSpace d (n + 2) := (WithLp.linearEquiv 2 ℂ _) v
    have hψ : (WithLp.linearEquiv 2 ℂ (NSiteSpace d (n + 2))).symm ψ = v :=
      LinearEquiv.symm_apply_apply _ v
    have hwindow := (uncleHamiltonianES_apply_eq_zero_iff_boundary_windows
      A B R L (by omega) ψ).mp (by simpa only [hψ] using hv)
    have hleft := mem_uncleBoundarySpace_of_cyclic_windows A B R L hPert (by omega) ψ hwindow
    let t : Fin (n + 2) := 1
    have hshift : ∀ (i : Fin (n + 2)) (τ : Cfg d (n + 2)),
        cyclicRestrictₗ (Fin.pos i) 2 i τ (cyclicTranslateState (-t) ψ) ∈
          uncleBoundarySpace A B R L 2 := by
      intro i τ
      rw [cyclicRestrictₗ_cyclicTranslateState]
      exact hwindow _ _
    have hright := mem_uncleBoundarySpace_of_cyclic_windows A B R L hPert
      (by omega) (cyclicTranslateState (-t) ψ) hshift
    have hclose : ψ ∈ uncleBoundarySpace A B R L (n + 2) ⊓
        (uncleBoundarySpace A B R L (n + 2)).map (cyclicTranslateState t) := by
      refine ⟨hleft, cyclicTranslateState (-t) ψ, hright, ?_⟩
      rw [cyclicTranslateState_add, add_neg_cancel]
      simp [cyclicTranslateState, cyclicTranslateCfg]
    rw [uncleBoundarySpace_inf_cyclicTranslate A B R L hPert n] at hclose
    have hm := Submodule.mem_map_of_mem
      (f := (WithLp.linearEquiv 2 ℂ (NSiteSpace d (n + 2))).symm.toLinearMap) hclose
    rw [Submodule.map_span] at hm
    simpa only [Set.image_insert_eq, Set.image_singleton, hψ] using hm
  · exact span_mpv_le_ker_uncleHamiltonianES A B R L (by omega)

end MPSTensor
