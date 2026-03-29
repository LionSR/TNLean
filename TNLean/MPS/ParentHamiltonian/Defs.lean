import TNLean.MPS.ParentHamiltonian.GroundSpace

import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Parent interaction and parent Hamiltonian (definitions)

This file introduces the parent interaction projector, translated local terms,
and the finite-chain parent Hamiltonian.

## Main definitions

* `MPSTensor.parentInteraction A L` — the orthogonal projector onto `(groundSpace A L)ᗮ`,
  as a linear map on `NSiteSpace d L`. This is a PSD operator whose kernel is the
  ground space `G_L(A)`.

* `MPSTensor.extractWindow L i σ` — extracts `L` consecutive site values from an `N`-site
  configuration `σ` starting at position `i` (with periodic boundary conditions).

* `MPSTensor.replaceWindow L i σ τ` — replaces the `L` consecutive site values in `σ`
  starting at position `i` with values from `τ`.

* `MPSTensor.localTerm A L N i` — the parent interaction embedded at site `i` on the
  `N`-site periodic chain, acting as `parentInteraction` on the window
  `{i, i+1, …, i+L-1 mod N}` and as the identity on the complement.

* `MPSTensor.parentHamiltonian A L N` — the parent Hamiltonian `H = ∑ᵢ hᵢ`.

* `MPSTensor.IsFrustrationFree A L N ψ` — frustration-freeness: every local term
  annihilates `ψ`.
-/

open scoped BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ### Transport between `NSiteSpace` and `EuclideanSpace`

`NSiteSpace d L = Cfg d L → ℂ` and `EuclideanSpace ℂ (Cfg d L)` is the same underlying
function space equipped with the ℓ²-structure via `WithLp 2` (concretely,
`EuclideanSpace ℂ (Cfg d L) = WithLp 2 (Cfg d L → ℂ)`). We use
`WithLp.linearEquiv` to transport the ground space to `EuclideanSpace`, where Mathlib
provides `InnerProductSpace` and orthogonal projection. -/

/-- The ground space of `A` on `L` sites, viewed as a submodule of
`EuclideanSpace ℂ (Cfg d L)` (same underlying submodule, different typeclass
instances for inner product). -/
noncomputable def groundSpaceES (A : MPSTensor d D) (L : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (Cfg d L)) :=
  (groundSpace A L).map (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm.toLinearMap

/-! ### Parent interaction -/

/-- Parent interaction on `L` consecutive sites: the orthogonal projector onto
`(groundSpace A L)ᗮ` in the `L`-site Hilbert space.

Mathematically, `parentInteraction A L = 𝟙 - P_{G_L(A)}`, where `P_{G_L(A)}` is the
orthogonal projector onto the ground space. This is a PSD operator with
`ker(parentInteraction A L) = groundSpace A L`. -/
noncomputable def parentInteraction (A : MPSTensor d D) (L : ℕ) :
    NSiteSpace d L →ₗ[ℂ] NSiteSpace d L :=
  let e := WithLp.linearEquiv 2 ℂ (NSiteSpace d L)
  e.toLinearMap.comp ((groundSpaceES A L)ᗮ.starProjection.toLinearMap.comp e.symm.toLinearMap)

/-! ### Window extraction and replacement (periodic boundary conditions) -/

/-- Extract `L` consecutive values from an `N`-periodic sequence `σ`,
starting at position `i` with periodic boundary conditions.

Note: when `L > N`, indices wrap and may revisit the same positions. The
intended use case is `L ≤ N` (e.g., the window size is at most the chain
length). -/
def extractWindow (L : ℕ) {N : ℕ} {α : Type*} (i : Fin N) (σ : Fin N → α) : Fin L → α :=
  have hN : 0 < N := i.val.zero_le.trans_lt i.isLt
  fun j => σ ⟨(i.val + j.val) % N, Nat.mod_lt _ hN⟩

variable {N : ℕ}

/-- Replace `L` consecutive values in an `N`-periodic sequence `σ`,
starting at position `i`, with values from `τ` (periodic boundary conditions).

Requires `L ≤ N` to ensure the `L`-site window is represented faithfully. -/
def replaceWindow (L : ℕ) (_hLN : L ≤ N) {α : Type*}
    (i : Fin N) (σ : Fin N → α) (τ : Fin L → α) :
    Fin N → α :=
  fun k =>
    let offset := (k.val + N - i.val) % N
    if h : offset < L then τ ⟨offset, h⟩ else σ k

private lemma offset_mod_eq {a b N : ℕ} (ha : a < N) (hb : b < N) :
    ((a + b) % N + N - a) % N = b := by
  rcases lt_or_ge (a + b) N with hab | hab
  · rw [Nat.mod_eq_of_lt hab, show a + b + N - a = b + N from by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hb]
  · rw [Nat.mod_eq_sub_mod hab, Nat.mod_eq_of_lt (by omega : a + b - N < N),
      show a + b - N + N - a = b from by omega, Nat.mod_eq_of_lt hb]

/-- Extracting a window after replacing it recovers the replacement values. -/
@[simp] lemma extractWindow_replaceWindow (L : ℕ) (hLN : L ≤ N) {α : Type*}
    (i : Fin N) (σ : Fin N → α) (τ : Fin L → α) :
    extractWindow L i (replaceWindow L hLN i σ τ) = τ := by
  funext ⟨j, hj⟩
  unfold extractWindow replaceWindow
  have key : ((i.val + j) % N + N - i.val) % N = j :=
    offset_mod_eq i.isLt (Nat.lt_of_lt_of_le hj hLN)
  rw [dif_pos (show ((i.val + j) % N + N - i.val) % N < L by rw [key]; exact hj)]
  exact congr_arg τ (Fin.ext key)

/-! ### Local term (site embedding) -/

/-- Translated local term on an `N`-site periodic chain: embeds
`parentInteraction A L` at site `i`, acting on the window
`{i, i+1, …, i+L-1 mod N}` and as identity on the complement.

For `f : NSiteSpace d N` and output configuration `σ`:
```
(localTerm A L N i f)(σ) = (parentInteraction A L (fun τ ↦ f (replaceWindow L i σ τ)))
                             (extractWindow L i σ)
``` -/
noncomputable def localTerm (A : MPSTensor d D) (L N : ℕ) (i : Fin N) :
    NSiteSpace d N →ₗ[ℂ] NSiteSpace d N :=
  if hLN : L ≤ N then
  LinearMap.pi fun σ =>
    (LinearMap.proj (extractWindow L i σ) : NSiteSpace d L →ₗ[ℂ] ℂ).comp
      ((parentInteraction A L).comp
        (LinearMap.pi fun τ =>
          (LinearMap.proj (replaceWindow L hLN i σ τ) : NSiteSpace d N →ₗ[ℂ] ℂ)))
  else 0

/-- Parent Hamiltonian on an `N`-site periodic chain:
sum of translated local interaction terms. -/
noncomputable def parentHamiltonian (A : MPSTensor d D) (L N : ℕ) :
    NSiteSpace d N →ₗ[ℂ] NSiteSpace d N :=
  ∑ i : Fin N, localTerm A L N i

/-- Frustration-freeness for the parent model: every local term annihilates the
candidate state. -/
def IsFrustrationFree (A : MPSTensor d D) (L N : ℕ) (ψ : NSiteSpace d N) : Prop :=
  ∀ i : Fin N, localTerm A L N i ψ = 0

end MPSTensor
