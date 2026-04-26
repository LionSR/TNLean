import TNLean.MPS.ParentHamiltonian.Defs

/-!
# Basic parent-Hamiltonian properties

The parent interaction is the orthogonal projector onto `(groundSpace A L)ᗮ`.
It therefore annihilates any vector in the ground space. The MPS state `mpv A`
lies in the ground space at every window, which gives frustration-freeness.
-/

open scoped BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ### Key lemma: parent interaction kills ground space elements -/

/-- The parent interaction annihilates any vector in the ground space.
This is the core property: `parentInteraction A L` is the orthogonal projector
onto `(groundSpace A L)ᗮ`, so it kills everything in `groundSpace A L`. -/
lemma parentInteraction_apply_mem_groundSpace (A : MPSTensor d D) (L : ℕ)
    (v : NSiteSpace d L) (hv : v ∈ groundSpace A L) :
    parentInteraction A L v = 0 := by
  have hmem : (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm v ∈ groundSpaceES A L := by
    simp only [groundSpaceES, Submodule.mem_map]
    exact ⟨v, hv, rfl⟩
  have hkill : (groundSpaceES A L)ᗮ.starProjection
      ((WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm v) = 0 := by
    rw [Submodule.starProjection_orthogonal']
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    rw [sub_eq_zero]
    exact (Submodule.starProjection_eq_self_iff.mpr hmem).symm
  -- Unfold `parentInteraction` to expose the equiv ∘ projection ∘ equiv⁻¹ structure.
  -- This `change` is definitional; update it if `parentInteraction` is refactored.
  change (WithLp.linearEquiv 2 ℂ (NSiteSpace d L))
    ((groundSpaceES A L)ᗮ.starProjection
      ((WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm v)) = 0
  rw [hkill, map_zero]

/-! ### Cyclic trace invariance -/

/-- Trace of evalWord is invariant under cyclic swap of concatenated words. -/
private lemma trace_evalWord_append_comm (A : MPSTensor d D) (w₁ w₂ : List (Fin d)) :
    Matrix.trace (evalWord A (w₁ ++ w₂)) = Matrix.trace (evalWord A (w₂ ++ w₁)) := by
  rw [evalWord_append, evalWord_append, Matrix.trace_mul_comm]

/-! ### MPS window membership -/

/-- The MPS state restricted to any window of `L` sites lies in `groundSpace A L`.

The witness is the "complement matrix": the product of `A`-matrices on sites
outside the `L`-site window, cyclically ordered starting from `i + L`. The proof
uses trace cyclicity to rotate the full `N`-site product so that the window
indices come first, matching the `groundSpaceMap` definition. -/
lemma mpv_window_mem_groundSpace (A : MPSTensor d D) (L N : ℕ) (hLN : L ≤ N)
    (i : Fin N) (σ : Cfg d N) :
    (fun τ => mpv A (replaceWindow L hLN i σ τ)) ∈ groundSpace A L := by
  rw [groundSpace, LinearMap.mem_range]
  have hN : 0 < N := Nat.lt_of_lt_of_le (Fin.pos i) le_rfl
  refine ⟨evalWord A (List.ofFn fun (j : Fin (N - L)) =>
    σ ⟨(i.val + L + j.val) % N, Nat.mod_lt _ (by omega)⟩), ?_⟩
  ext τ
  simp only [groundSpaceMap_apply, mpv, coeff]
  rw [← evalWord_append]
  -- Goal: tr(evalWord A (List.ofFn τ ++ compList))
  --     = tr(evalWord A (List.ofFn (replaceWindow L hLN i σ τ)))
  set compList := List.ofFn fun (j : Fin (N - L)) =>
    σ ⟨(i.val + L + j.val) % N, Nat.mod_lt _ (by omega)⟩
  -- Rotate the RHS by i positions using trace cyclicity
  suffices hlist :
      (List.ofFn (replaceWindow L hLN i σ τ)).rotate i.val =
      List.ofFn τ ++ compList by
    have hle : i.val ≤ (List.ofFn (replaceWindow L hLN i σ τ)).length := by
      simp [List.length_ofFn]
    rw [← hlist, List.rotate_eq_drop_append_take hle,
        trace_evalWord_append_comm, List.take_append_drop]
  -- Prove the rotated list equals τ ++ complement elementwise
  apply List.ext_getElem
  · have : compList.length = N - L := by simp [compList, List.length_ofFn]
    simp only [List.length_rotate, List.length_append, List.length_ofFn]
    omega
  · intro k hk1 hk2
    have hkN : k < N := by simp only [List.length_rotate, List.length_ofFn] at hk1; exact hk1
    simp only [List.getElem_rotate, List.getElem_ofFn, List.length_ofFn]
    -- Unfold replaceWindow at position ⟨(k + i) % N, _⟩
    change (if h : ((k + i.val) % N + N - i.val) % N < L
      then τ ⟨((k + i.val) % N + N - i.val) % N, h⟩
      else σ ⟨(k + i.val) % N, Nat.mod_lt _ hN⟩) = _
    -- The offset always equals k (regardless of wrapping)
    have hoffset : ((k + i.val) % N + N - i.val) % N = k := by
      simpa [Nat.add_comm] using offset_mod_eq i.isLt hkN
    rw [hoffset]
    by_cases hkL : k < L
    · -- Window part → τ
      rw [dif_pos hkL, List.getElem_append_left (by simp only [List.length_ofFn]; exact hkL),
          List.getElem_ofFn]
    · -- Complement part → σ
      rw [dif_neg hkL, List.getElem_append_right (by simp; omega), List.getElem_ofFn]
      simp only [List.length_ofFn]
      congr 1; apply Fin.ext
      change (k + i.val) % N = (i.val + L + (k - L)) % N
      rw [show i.val + L + (k - L) = k + i.val from by omega]

/-- Each local term annihilates the MPV state. -/
lemma localTerm_annihilates_mpv (A : MPSTensor d D) (L N : ℕ) (hLN : L ≤ N) (i : Fin N) :
    localTerm A L N i (mpv A) = 0 := by
  ext σ
  simp only [localTerm, hLN, ↓reduceDIte, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Pi.zero_apply]
  have hmem := mpv_window_mem_groundSpace A L N hLN i σ
  have hkill := parentInteraction_apply_mem_groundSpace A L _ hmem
  change (parentInteraction A L (fun τ => mpv A (replaceWindow L hLN i σ τ)))
    (extractWindow L i σ) = 0
  rw [hkill]
  rfl

/-- The parent Hamiltonian annihilates the MPV state: `H_N |ψ(A)⟩ = 0`. -/
lemma parentHamiltonian_annihilates (A : MPSTensor d D) (L N : ℕ) (hLN : L ≤ N) :
    parentHamiltonian A L N (mpv A) = 0 := by
  simp only [parentHamiltonian, LinearMap.sum_apply]
  exact Finset.sum_eq_zero fun i _ => localTerm_annihilates_mpv A L N hLN i

/-- The parent Hamiltonian model is frustration-free on the MPV state:
each local term individually annihilates `mpv A`. -/
lemma parentHamiltonian_frustrationFree (A : MPSTensor d D) (L N : ℕ) (hLN : L ≤ N) :
    IsFrustrationFree A L N (mpv A) :=
  fun i => localTerm_annihilates_mpv A L N hLN i

end MPSTensor
