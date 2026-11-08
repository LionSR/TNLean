/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.ShortMomentum.ShortIntersections
import TNLean.MPS.Examples.ShortMomentum.CyclicBoundaryClosure
import TNLean.MPS.Examples.ShortMomentum.LongIntersection
import TNLean.MPS.ParentHamiltonian.CyclicSubmoduleIteration
import TNLean.MPS.ParentHamiltonian.CyclicTranslation
import TNLean.MPS.ParentHamiltonian.KernelChainGroundSpace

/-!
# Actual periodic kernels of the seven-site Weyl parent interaction

The two exceptional overlap identities and the actual long-window
intersection imply global boundary-space membership from the actual
seven-site local constraints. Cyclic closure then identifies the
periodic kernel with the trace-MPS line. At length seven it is zero;
at every longer length the actual trace vector is nonzero.

This is the main physical sector only. A fixed interaction on the
combined physical sectors and its full all-volume uniqueness are not
asserted here. Source context: SPWC10, arXiv:0909.5347, Theorem 5,
main.tex lines 850--880; see
`docs/audits/2026-10-29_weyl_short_volume_candidate.md`.
-/

namespace MPSTensor.ShortMomentum

/-- The actual one-step boundary-space intersection holds from the
seven-site range onward, including both exceptional short overlaps. -/
theorem groundSpace_restriction_intersection_threeLetterTensor {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ 5) (M : ℕ) (hM : 7 ≤ M) :
    ((⨅ b : Fin 3, (groundSpace (threeLetterTensor ζ) M).comap (restrictLastₗ b)) ⊓
      (⨅ a : Fin 3, (groundSpace (threeLetterTensor ζ) M).comap (restrictFirstₗ a))) =
      groundSpace (threeLetterTensor ζ) (M + 1) := by
  apply le_antisymm
  · intro ψ hψ
    simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at hψ
    by_cases hseven : M = 7
    · subst M
      exact groundSpace_intersection_threeLetterTensor_eight hζ hψ.1 hψ.2
    by_cases height : M = 8
    · subst M
      exact groundSpace_intersection_threeLetterTensor_nine hζ hψ.1 hψ.2
    obtain ⟨K, rfl⟩ : ∃ K, M = K + 1 := ⟨M - 1, by omega⟩
    exact groundSpace_intersection_threeLetterTensor_of_eight_le hζ (by omega) hψ.1 hψ.2
  · intro ψ hψ
    simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
    exact ⟨groundSpace_inLeftGround (threeLetterTensor ζ) M hψ,
      groundSpace_inRightGround (threeLetterTensor ζ) M hψ⟩

/-- Actual contiguous seven-site constraints imply the actual global
boundary space. The one-step intersection is derived internally. -/
theorem mem_groundSpace_of_seven_contiguous_constraints {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ 5) {N : ℕ} (hN : 7 ≤ N) {ψ : NSiteSpace 3 N}
    (hwindow : ∀ (s : ℕ) (hs : s + 7 ≤ N) (τ : Cfg 3 N),
      contiguousRestrictₗ s 7 hs τ ψ ∈ groundSpace (threeLetterTensor ζ) 7) :
    ψ ∈ groundSpace (threeLetterTensor ζ) N := by
  exact contiguous_mem_of_restriction_intersection_submodules
    (fun M ↦ groundSpace (threeLetterTensor ζ) M) (by omega) hN
    (groundSpace_restriction_intersection_threeLetterTensor hζ) hwindow

/-- The actual cyclic seven-site constraints imply global boundary-space
membership, with no supplied open-chain reconstruction premise. -/
theorem chainGroundSpace_seven_le_groundSpace_threeLetterTensor {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ 5) {N : ℕ} (hN : 7 ≤ N) :
    chainGroundSpace (threeLetterTensor ζ) 7 N ≤ groundSpace (threeLetterTensor ζ) N := by
  exact chainGroundSpace_le_of_local_le_restriction_intersection_submodules
    (threeLetterTensor ζ) (fun M ↦ groundSpace (threeLetterTensor ζ) M)
    (by omega) (by omega) hN le_rfl
    (groundSpace_restriction_intersection_threeLetterTensor hζ)

private theorem cyclicTranslateCfg_last_snoc {n : ℕ} (i : Fin 3) (σ : Cfg 3 n) :
    cyclicTranslateCfg (⟨n, by omega⟩ : Fin (n + 1)) (Fin.snoc σ i) = Fin.cons i σ := by
  have h := cyclicTranslateCfg_fin_append (K := n) (S := 1) (by omega)
    σ (fun _ : Fin 1 ↦ i)
  rw [Fin.append_right_eq_snoc, Fin.append_left_eq_cons] at h
  funext k
  simpa only [Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self] using congrFun h k

/-- The actual periodic main-sector parent space is the trace-MPS line
at every permitted length; at seven that line is zero. -/
theorem chainGroundSpace_seven_threeLetterTensor_eq_mpvSubmodule {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ 5) {N : ℕ} (hN : 7 ≤ N) :
    chainGroundSpace (threeLetterTensor ζ) 7 N = mpvSubmodule (threeLetterTensor ζ) N := by
  apply le_antisymm
  · intro ψ hψ
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    let s : Fin (n + 1) := ⟨n, by omega⟩
    have hlocal := chainGroundSpace_seven_le_groundSpace_threeLetterTensor hζ hN hψ
    have htranslated := cyclicTranslateState_mem_chainGroundSpace
      (threeLetterTensor ζ) (by omega) hN s hψ
    have hother := chainGroundSpace_seven_le_groundSpace_threeLetterTensor hζ hN htranslated
    obtain ⟨c, hc⟩ := exists_smul_mpv_of_cyclic_agreement hζ (by omega) ψ
      (cyclicTranslateState s ψ) hlocal hother (fun i σ ↦ by
        change ψ (Fin.cons i σ) = ψ (cyclicTranslateCfg s (Fin.snoc σ i))
        rw [cyclicTranslateCfg_last_snoc])
    rw [hc]
    exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _))
  · intro ψ hψ
    rw [mpvSubmodule, Submodule.mem_span_singleton] at hψ
    obtain ⟨c, rfl⟩ := hψ
    exact Submodule.smul_mem _ c
      (mpv_mem_chainGroundSpace (threeLetterTensor ζ) 7 N (by omega) hN)

/-- The actual Euclidean parent-Hamiltonian kernel is the periodic trace
line at every length at least eight. -/
theorem ker_parentHamiltonianES_threeLetterTensor_eq_span {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ 5) (N : ℕ) (hN : 8 ≤ N) :
    LinearMap.ker (parentHamiltonianES (threeLetterTensor ζ) 7 N) =
      Submodule.span ℂ {mpvState (threeLetterTensor ζ) N} := by
  have hstate : (WithLp.linearEquiv 2 ℂ (NSiteSpace 3 N)).symm
      (mpv (threeLetterTensor ζ)) = mpvState (threeLetterTensor ζ) N := by
    ext σ
    exact (mpvState_apply (threeLetterTensor ζ) N σ).symm
  rw [← parentHamiltonianGroundSpaceES_eq_ker_parentHamiltonianES,
    parentHamiltonianGroundSpaceES,
    ker_parentHamiltonian_eq_chainGroundSpace _ (by omega) (by omega),
    chainGroundSpace_seven_threeLetterTensor_eq_mpvSubmodule hζ (by omega),
    mpvSubmodule, Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe, hstate]

/-- The actual main-sector parent Hamiltonian has zero kernel at length seven. -/
theorem ker_parentHamiltonianES_threeLetterTensor_seven_eq_bot {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ 5) :
    LinearMap.ker (parentHamiltonianES (threeLetterTensor ζ) 7 7) = ⊥ := by
  rw [← parentHamiltonianGroundSpaceES_eq_ker_parentHamiltonianES,
    parentHamiltonianGroundSpaceES,
    ker_parentHamiltonian_eq_chainGroundSpace _ (by omega) (by omega),
    chainGroundSpace_threeLetterTensor_seven_eq_bot hζ, Submodule.map_bot]

/-- The actual periodic trace vector is nonzero at every length at least eight. -/
theorem mpvState_threeLetterTensor_ne_zero {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5)
    (N : ℕ) (hN : 8 ≤ N) : mpvState (threeLetterTensor ζ) N ≠ 0 := by
  obtain ⟨w, hw, htrace⟩ := exists_trace_evalWord_ne_zero_of_eight_le hζ N hN
  obtain ⟨m, σ, rfl⟩ := List.exists_eq_ofFn w
  have hm : m = N := by simpa only [List.length_ofFn] using hw
  subst hm
  intro hzero
  apply htrace
  have hcoeff := congrArg (fun v : MPVSpace 3 m ↦ v σ) hzero
  change mpvState (threeLetterTensor ζ) m σ = 0 at hcoeff
  simpa only [mpvState_apply, mpv, coeff] using hcoeff

end MPSTensor.ShortMomentum
