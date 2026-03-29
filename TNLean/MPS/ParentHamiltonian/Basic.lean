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
  -- v ∈ groundSpace means e.symm v ∈ groundSpaceES
  have hmem : (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm v ∈ groundSpaceES A L := by
    simp only [groundSpaceES, Submodule.mem_map]
    exact ⟨v, hv, rfl⟩
  -- The starProjection of Vᗮ kills elements of V:
  -- Uᗮ.starProjection = 1 - U.starProjection, and U.starProjection fixes members of U.
  have hkill : (groundSpaceES A L)ᗮ.starProjection
      ((WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm v) = 0 := by
    rw [Submodule.starProjection_orthogonal']
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    rw [sub_eq_zero]
    exact (Submodule.starProjection_eq_self_iff.mpr hmem).symm
  -- parentInteraction unfolds to e ∘ starProjection.toLinearMap ∘ e⁻¹
  change (WithLp.linearEquiv 2 ℂ (NSiteSpace d L))
    ((groundSpaceES A L)ᗮ.starProjection
      ((WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm v)) = 0
  rw [hkill, map_zero]

/-- The MPS state restricted to any window of `L` sites lies in `groundSpace A L`.
This is because `mpv A (replaceWindow L i σ τ)` has the form
`tr(evalWord A (List.ofFn τ) * X)` where `X` is the product of matrices on the
complement sites — exactly the structure of `groundSpaceMap A L`.

**Status: sorry** — Proof strategy (trace cyclicity argument):
1. Show `List.ofFn (replaceWindow L i σ τ)` decomposes into window and complement
   segments via `List.ofFn_fin_append` / periodic reindexing.
2. Apply `evalWord_append` to factor the matrix product into window × complement.
3. Use `Matrix.trace_mul_comm` (trace cyclicity) to rewrite
   `tr(M_before * M_window * M_after)` as `tr(M_window * M_after * M_before)`.
4. Identify the result as `groundSpaceMap A L X τ` where
   `X = evalWord A (complement_after) * evalWord A (complement_before)`.
5. Conclude via `LinearMap.mem_range`.

Dependencies: needs round-trip / decomposition lemmas for `extractWindow`/`replaceWindow`
relating `List.ofFn (replaceWindow L i σ τ)` to `List.ofFn τ` and complement indices.
Requires `L ≤ N` hypothesis (or `N`-periodicity argument). -/
lemma mpv_window_mem_groundSpace (A : MPSTensor d D) (L N : ℕ) (hLN : L ≤ N)
    (i : Fin N) (σ : Cfg d N) :
    (fun τ => mpv A (replaceWindow L hLN i σ τ)) ∈ groundSpace A L := by
  sorry

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
