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

The witness is the "complement matrix": the product of `A`-matrices on sites
outside the `L`-site window, cyclically ordered starting from `i + L`:
`X = evalWord A [σ(i+L), σ(i+L+1), …, σ(i-1)]` (indices mod `N`).

Then `groundSpaceMap A L X τ = tr(evalWord A (List.ofFn τ) * X)`, and we need
this to equal `mpv A (replaceWindow L hLN i σ τ) = tr(evalWord A (List.ofFn (replaceWindow …)))`.

**Status: sorry** — The remaining proof obligation is:
```
tr(evalWord A (List.ofFn τ) * complementMatrix) = tr(evalWord A (List.ofFn (replaceWindow …)))
```
which follows from:
1. `List.ofFn (replaceWindow L hLN i σ τ)` decomposes as `before_σ ++ List.ofFn τ ++ after_σ`
   (non-wrapping case; wrapping case needs periodic reindexing).
2. `evalWord_append` factors the matrix product into three pieces.
3. `Matrix.trace_mul_cycle` rewrites `tr(before * window * after)` as
   `tr(window * after * before)`.
4. `after ++ before` is exactly the complement list. -/
lemma mpv_window_mem_groundSpace (A : MPSTensor d D) (L N : ℕ) (hLN : L ≤ N)
    (i : Fin N) (σ : Cfg d N) :
    (fun τ => mpv A (replaceWindow L hLN i σ τ)) ∈ groundSpace A L := by
  rw [groundSpace, LinearMap.mem_range]
  -- Witness: product of A-matrices on complement sites (i+L to i-1 cyclically)
  refine ⟨evalWord A (List.ofFn fun (j : Fin (N - L)) =>
    σ ⟨(i.val + L + j.val) % N, Nat.mod_lt _ (by have := i.isLt; omega)⟩), ?_⟩
  ext τ
  simp only [groundSpaceMap_apply, mpv, coeff]
  -- Remaining: tr(evalWord A (List.ofFn τ) * complementMatrix)
  --          = tr(evalWord A (List.ofFn (replaceWindow L hLN i σ τ)))
  -- Requires list decomposition + trace cyclicity (see docstring).
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
