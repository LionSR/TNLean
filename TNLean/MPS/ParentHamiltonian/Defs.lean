/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.GroundSpace
import QICLean.Algebra.MatrixStarProjection
import QICLean.Algebra.MatrixToEuclidean
import QICLean.ManyBody.Hamiltonian.FrustrationFree
import QICLean.ManyBody.Hamiltonian.Models

import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Parent interaction and parent Hamiltonian (definitions)

This file introduces the parent interaction projector, the parent interaction on the
ring as a `ManyBody.Interaction`, its translated local terms, and the finite-chain
parent Hamiltonian, which is the Hamiltonian of that interaction.

## Main definitions

* `MPSTensor.parentInteraction A L` — the canonical parent interaction
  \(1 - Π_{G_L(A)}\), represented as the orthogonal projector onto
  \(G_L(A)^\perp\). This positive operator has kernel \(G_L(A)\).

* `MPSTensor.extractWindow L i σ` — extracts \(L\) consecutive site values from an
  \(N\)-site configuration \(\sigma\) starting at position \(i\) (with periodic
  boundary conditions).

* `MPSTensor.replaceWindow L i σ τ` — replaces the \(L\) consecutive site values in
  \(\sigma\) starting at position \(i\) with values from \(\tau\).

* `MPSTensor.parentRingInteraction A L N` — the parent interaction on the ring of
  \(N\) sites: the translation-invariant interaction
  (`ManyBody.Interaction.translationInvariant`) of the matrix of `parentInteraction A L`,
  whose terms vanish when \(L > N\).

* `MPSTensor.localTerm A L N i` — its term with index \(i\), as a linear map: the
  parent interaction placed on the window \(\{i, i+1, \ldots, i+L-1 \bmod N\}\) and the
  identity on the complement.

* `MPSTensor.parentHamiltonian A L N` — its Hamiltonian \(H = ∑ᵢ hᵢ\), as a linear map.

The vectors annihilated by every local term, the frustration-free ground vectors of the parent
model, are the zero space `ManyBody.Interaction.zeroSpace` of the parent interaction on the
ring.
-/

open scoped BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ### Transport between `NSiteSpace` and `EuclideanSpace`

`NSiteSpace d L` is the function space on length-\(L\) configurations with
values in \(\mathbb C\), and
`EuclideanSpace ℂ (Cfg d L)` is the same underlying
function space equipped with the canonical ℓ² inner product via `WithLp 2`
(concretely, `EuclideanSpace ℂ (Cfg d L) = WithLp 2 (Cfg d L → ℂ)`). We use
`WithLp.linearEquiv` to view the local ground space in this ℓ² realization, where
Mathlib provides `InnerProductSpace` and orthogonal projection. -/

/-- The local ground space \(G_L(A)\) in the canonical ℓ² realization of the
\(L\)-site configuration space. -/
noncomputable def groundSpaceES (A : MPSTensor d D) (L : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (Cfg d L)) :=
  (groundSpace A L).map (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm.toLinearMap

/-- Membership in the canonical ℓ² realization of \(G_L(A)\) is the same as
membership of the corresponding function in the original local ground space. -/
theorem mem_groundSpaceES_iff (A : MPSTensor d D) (L : ℕ)
    (v : EuclideanSpace ℂ (Cfg d L)) :
    v ∈ groundSpaceES A L ↔
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)) v ∈ groundSpace A L := by
  rw [groundSpaceES]
  exact Submodule.mem_map_equiv (p := groundSpace A L)
    (e := (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm) (x := v)

/-- The finite-dimensional local ground space \(G_L(A)\) admits an orthogonal projection. -/
theorem groundSpaceES_hasOrthogonalProjection
    (A : MPSTensor d D) (L : ℕ) : (groundSpaceES A L).HasOrthogonalProjection := by
  let : CompleteSpace (groundSpaceES A L) := FiniteDimensional.complete ℂ _
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-! ### Parent interaction -/

/-- Canonical parent interaction on \(L\) consecutive sites: the orthogonal
projector onto \(G_L(A)^\perp\) in the \(L\)-site Hilbert space.

Mathematically, \(h_L = 𝟙 - P_{G_L(A)}\), where \(P_{G_L(A)}\) is the
orthogonal projector onto \(G_L(A)\). This is a PSD operator with
\(\ker h_L = G_L(A)\). -/
noncomputable def parentInteraction (A : MPSTensor d D) (L : ℕ) :
    NSiteSpace d L →ₗ[ℂ] NSiteSpace d L :=
  let e := WithLp.linearEquiv 2 ℂ (NSiteSpace d L)
  e.toLinearMap.comp ((groundSpaceES A L)ᗮ.starProjection.toLinearMap.comp e.symm.toLinearMap)

/-! ### Window extraction and replacement (periodic boundary conditions) -/

/-- Extract \(L\) consecutive values from an \(N\)-periodic sequence \(\sigma\),
starting at position \(i\) with periodic boundary conditions.

Note: when \(L > N\), indices wrap and may revisit the same positions. The
intended use case is \(L ≤ N\) (e.g., the window size is at most the chain
length). -/
def extractWindow (L : ℕ) {N : ℕ} {α : Type*} (i : Fin N) (σ : Fin N → α) : Fin L → α :=
  have hN : 0 < N := i.val.zero_le.trans_lt i.isLt
  fun j => σ ⟨(i.val + j.val) % N, Nat.mod_lt _ hN⟩

variable {N : ℕ}

/-- Replace \(L\) consecutive values in an \(N\)-periodic sequence \(\sigma\),
starting at position \(i\), with values from \(\tau\) (periodic boundary conditions).

Requires \(L ≤ N\) to ensure the \(L\)-site window is represented faithfully.

Note: the offset logic mirrors `cyclicCfg` in `CyclicWindow.lean`, but this
function is type-generic (`α` instead of `Fin d`) and *replaces* a window
rather than constructing a full configuration from one. -/
def replaceWindow (L : ℕ) (_hLN : L ≤ N) {α : Type*}
    (i : Fin N) (σ : Fin N → α) (τ : Fin L → α) :
    Fin N → α :=
  fun k =>
    let offset := (k.val + N - i.val) % N
    if h : offset < L then τ ⟨offset, h⟩ else σ k

/-- If \(a\) and \(b\) are residues modulo \(N\), then the cyclic offset of
\(a + b\) from \(a\) is \(b\). -/
lemma offset_mod_eq {a b N : ℕ} (ha : a < N) (hb : b < N) :
    ((a + b) % N + N - a) % N = b := by
  rcases lt_or_ge (a + b) N with hab | hab
  · rw [Nat.mod_eq_of_lt hab, show a + b + N - a = b + N from by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hb]
  · rw [Nat.mod_eq_sub_mod hab, Nat.mod_eq_of_lt (by omega : a + b - N < N),
      show a + b - N + N - a = b from by omega, Nat.mod_eq_of_lt hb]

/-- Adding the cyclic offset from `a` to `b` modulo `N` recovers `b`. -/
lemma add_offset_mod_eq {a b N : ℕ} (ha : a < N) (hb : b < N) :
    (a + ((b + N - a) % N)) % N = b := by
  rcases lt_or_ge b a with hab | hab
  · have hmod : (b + N - a) % N = b + N - a := by
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [hmod, show a + (b + N - a) = b + N from by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hb]
  · have hsub : b - a < N := lt_of_le_of_lt (Nat.sub_le _ _) hb
    have hmod : (b + N - a) % N = b - a := by
      have : b + N - a = N + (b - a) := by omega
      rw [this, Nat.add_mod, Nat.mod_self]
      simpa using Nat.mod_eq_of_lt hsub
    rw [hmod, Nat.add_sub_of_le hab, Nat.mod_eq_of_lt hb]

/-- Extracting a window after replacing it recovers the replacement values. -/
@[simp] lemma extractWindow_replaceWindow (L : ℕ) (hLN : L ≤ N) {α : Type*}
    (i : Fin N) (σ : Fin N → α) (τ : Fin L → α) :
    extractWindow L i (replaceWindow L hLN i σ τ) = τ := by
  funext ⟨j, hj⟩
  unfold extractWindow replaceWindow
  have key : ((i.val + j) % N + N - i.val) % N = j :=
    offset_mod_eq i.isLt (Nat.lt_of_lt_of_le hj hLN)
  rw [dite_eq_left (show ((i.val + j) % N + N - i.val) % N < L by rw [key]; exact hj)]
  exact congr_arg τ (Fin.ext key)

/-- Replacing a window by the values extracted from the same configuration leaves
that configuration unchanged. -/
@[simp] lemma replaceWindow_extractWindow (L : ℕ) (hLN : L ≤ N) {α : Type*}
    (i : Fin N) (σ : Fin N → α) :
    replaceWindow L hLN i σ (extractWindow L i σ) = σ := by
  funext ⟨k, hk⟩
  unfold replaceWindow extractWindow
  set offset := (k + N - i.val) % N with hoff
  have hN : 0 < N := Fin.pos i
  have hoffN : offset < N := by
    rw [hoff]
    exact Nat.mod_lt _ hN
  by_cases hoffset : offset < L
  · rw [dite_eq_left hoffset]
    have key : (i.val + offset) % N = k := add_offset_mod_eq i.isLt hk
    exact congr_arg σ (Fin.ext key)
  · rw [dite_eq_right hoffset]

/-- Replacing the same cyclic window twice is the same as keeping only the
second replacement. -/
@[simp] lemma replaceWindow_replaceWindow_same (L : ℕ) (hLN : L ≤ N) {α : Type*}
    (i : Fin N) (σ : Fin N → α) (τ υ : Fin L → α) :
    replaceWindow L hLN i (replaceWindow L hLN i σ τ) υ =
      replaceWindow L hLN i σ υ := by
  funext ⟨k, hk⟩
  unfold replaceWindow
  by_cases hoffset : (k + N - i.val) % N < L
  · simp [hoffset]
  · simp [hoffset]

/-! ### Windows of the ring

The window of \(L \le N\) consecutive sites starting at \(i\) is the injection
`ManyBody.ringWindow hLN i`, \(u \mapsto i + u\). Reading a configuration
along it is extracting the window, its image is the set of sites of cyclic offset
less than \(L\) from \(i\), and replacing the window writes the new values at its
image and leaves the other sites unchanged. -/

section RingWindow

variable {L : ℕ} {α : Type*}

/-- Reading a configuration along the window at `i` is extracting that window. -/
theorem extractWindow_eq_comp_ringWindow (hLN : L ≤ N) (i : Fin N) (σ : Fin N → α) :
    extractWindow L i σ = fun u ↦ σ (ManyBody.ringWindow hLN i u) :=
  rfl

/-- The window at `i` starts at `i`. -/
@[simp] theorem ringWindow_zero (hLN : L ≤ N) (i : Fin N) (h : 0 < L) :
    ManyBody.ringWindow hLN i ⟨0, h⟩ = i :=
  Fin.ext (by rw [ManyBody.ringWindow_apply, Fin.val_add, Fin.val_castLE, Nat.add_zero,
    Nat.mod_eq_of_lt i.isLt])

/-- A site lies in the image of the window at `i` exactly when its cyclic offset from
`i` is less than the window length. -/
theorem exists_ringWindow_eq_iff (hLN : L ≤ N) (i k : Fin N) :
    (∃ u, ManyBody.ringWindow hLN i u = k) ↔ (k.val + N - i.val) % N < L := by
  constructor
  · rintro ⟨u, rfl⟩
    rw [ManyBody.ringWindow_apply, Fin.val_add, Fin.val_castLE,
      offset_mod_eq i.isLt (Nat.lt_of_lt_of_le u.isLt hLN)]
    exact u.isLt
  · intro hk
    refine ⟨⟨(k.val + N - i.val) % N, hk⟩, Fin.ext ?_⟩
    rw [ManyBody.ringWindow_apply, Fin.val_add, Fin.val_castLE]
    exact add_offset_mod_eq i.isLt k.isLt

/-- A site lies outside the image of the window at `i` exactly when its cyclic offset
from `i` is at least the window length. -/
theorem forall_ringWindow_ne_iff (hLN : L ≤ N) (i k : Fin N) :
    (∀ u, ManyBody.ringWindow hLN i u ≠ k) ↔ ¬ (k.val + N - i.val) % N < L := by
  rw [← exists_ringWindow_eq_iff hLN, not_exists]

/-- The image of the window at `i` is the set of sites of cyclic offset less than the
window length. -/
theorem mem_map_ringWindow_iff (hLN : L ≤ N) (i k : Fin N) :
    k ∈ Finset.univ.map (ManyBody.ringWindow hLN i) ↔ (k.val + N - i.val) % N < L := by
  simp only [Finset.mem_map, Finset.mem_univ, true_and]
  exact exists_ringWindow_eq_iff hLN i k

/-- Two configurations agree outside the window at `i` exactly when they agree at every
site of cyclic offset at least the window length. -/
theorem forall_ringWindow_ne_imp_iff (hLN : L ≤ N) (i : Fin N) (σ τ : Fin N → α) :
    (∀ v, (∀ u, ManyBody.ringWindow hLN i u ≠ v) → σ v = τ v) ↔
      ∀ k : Fin N, ¬ (k.val + N - i.val) % N < L → τ k = σ k := by
  refine forall_congr' fun k ↦ ?_
  rw [forall_ringWindow_ne_iff hLN, eq_comm]

/-- Replacing the window at `i` writes the new values at the sites of the window. -/
@[simp] theorem replaceWindow_ringWindow (hLN : L ≤ N) (i : Fin N) (σ : Fin N → α)
    (τ : Fin L → α) (u : Fin L) :
    replaceWindow L hLN i σ τ (ManyBody.ringWindow hLN i u) = τ u :=
  congrFun (extractWindow_replaceWindow L hLN i σ τ) u

/-- Replacing the window at `i` leaves the sites outside the window unchanged. -/
theorem replaceWindow_of_forall_ringWindow_ne (hLN : L ≤ N) (i : Fin N) (σ : Fin N → α)
    (τ : Fin L → α) {v : Fin N} (hv : ∀ u, ManyBody.ringWindow hLN i u ≠ v) :
    replaceWindow L hLN i σ τ v = σ v := by
  rw [replaceWindow, dite_eq_right ((forall_ringWindow_ne_iff hLN i v).mp hv)]

/-- Two configurations agree outside the window at `i` exactly when replacing the window
of the second by the window of the first gives the first. -/
theorem forall_ringWindow_ne_imp_iff_replaceWindow (hLN : L ≤ N) (i : Fin N)
    (σ τ : Fin N → α) :
    (∀ v, (∀ u, ManyBody.ringWindow hLN i u ≠ v) → σ v = τ v) ↔
      replaceWindow L hLN i τ (extractWindow L i σ) = σ := by
  constructor
  · intro h
    funext v
    by_cases hv : ∃ u, ManyBody.ringWindow hLN i u = v
    · obtain ⟨u, rfl⟩ := hv
      exact replaceWindow_ringWindow hLN i τ _ u
    · rw [replaceWindow_of_forall_ringWindow_ne hLN i τ _ (not_exists.mp hv)]
      exact (h v (not_exists.mp hv)).symm
  · intro h v hv
    exact (congrFun h v).symm.trans (replaceWindow_of_forall_ringWindow_ne hLN i τ _ hv)

end RingWindow

/-! ### The parent interaction on the ring -/

/-- **The parent interaction on the ring.** On the ring of \(N\) sites, the
translation-invariant interaction whose term with index \(i\) is, for \(L \le N\), the matrix
of the canonical parent interaction \(h_L\) placed on the window of \(L\) consecutive sites
starting at \(i\), and zero for \(L > N\) (`ManyBody.Interaction.translationInvariant`). Its
terms are the translated local terms and its Hamiltonian is the parent Hamiltonian; the
frustration-free ground vectors of the parent model are the vectors of its zero space
(`ManyBody.Interaction.zeroSpace`). -/
noncomputable abbrev parentRingInteraction (A : MPSTensor d D) (L N : ℕ) [NeZero N] :=
  ManyBody.Interaction.translationInvariant (α := Fin d) N
    (LinearMap.toMatrix' (parentInteraction A L))

/-- **The parent interaction on the open chain.** On the open chain of `N` sites, the translates
of the matrix of the canonical parent interaction \(h_L\) along the windows of `L` consecutive
sites starting at `0, …, N - L` (`ManyBody.Interaction.chainTranslates`); it has no term when
`N < L`. Its Hamiltonian is the open-chain parent Hamiltonian of Nachtergaele,
arXiv:cond-mat/9410110, equation (3.12).

**Convention at range zero.** For `L = 0` the windows are the `N + 1` empty windows at the
positions `0, …, N`, so the Hamiltonian is `N + 1` times the one-by-one matrix of \(h_0\)
(which is `0` when `D > 0` and `1` when `D = 0`). The source has no range-zero interaction. -/
noncomputable abbrev parentChainInteraction (A : MPSTensor d D) (L N : ℕ) :
    ManyBody.Interaction (fun _ : Fin N ↦ Fin d) (fun i : Fin (N + 1 - L) ↦
      Finset.univ.map (ManyBody.chainWindow (N := N) (k := L) i.val (by omega))) :=
  ManyBody.Interaction.chainTranslates L N (LinearMap.toMatrix' (parentInteraction A L))

/-! ### Local term and parent Hamiltonian -/

/-- Translated local term on an \(N\)-site periodic chain: the term with index `i` of the
parent interaction on the ring (`parentRingInteraction`), which acts as `parentInteraction A L`
on the window \(\{i, i+1, \ldots, i+L-1 \bmod N\}\) and as the identity on the complement.

**Important:** When \(L > N\) the term of the ring interaction, and hence this definition,
is `0`, which makes `parentHamiltonian` trivially zero and every vector frustration free.
The lemmas in `Basic.lean` carry an explicit \(L ≤ N\) hypothesis; the one-site
two-site result below records the \(L > N\) convention separately.

For \(f\) and output configuration \(\sigma\) (`localTerm_apply_of_le`):
```
(localTerm A L N i f)(σ) = (parentInteraction A L (fun τ ↦ f (replaceWindow L i σ τ)))
                             (extractWindow L i σ)
``` -/
noncomputable def localTerm (A : MPSTensor d D) (L N : ℕ) (i : Fin N) :
    NSiteSpace d N →ₗ[ℂ] NSiteSpace d N :=
  haveI : NeZero N := NeZero.of_pos i.pos
  Matrix.toLin' ((parentRingInteraction A L N).term i)

/-- Parent Hamiltonian on an \(N\)-site periodic chain: the sum of the translated local
terms, which is the Hamiltonian of the parent interaction on the ring
(`parentHamiltonian_eq_toLin'_hamiltonian`). -/
noncomputable def parentHamiltonian (A : MPSTensor d D) (L N : ℕ) :
    NSiteSpace d N →ₗ[ℂ] NSiteSpace d N :=
  ∑ i : Fin N, localTerm A L N i

/-- The translated local term is the term of the parent interaction on the ring. -/
theorem localTerm_eq_toLin'_term (A : MPSTensor d D) (L : ℕ) [NeZero N] (i : Fin N) :
    localTerm A L N i = Matrix.toLin' ((parentRingInteraction A L N).term i) :=
  rfl

/-- For \(L > N\), the translated local term vanishes. -/
theorem localTerm_of_not_le (A : MPSTensor d D) {L : ℕ} (hLN : ¬ L ≤ N) (i : Fin N) :
    localTerm A L N i = 0 := by
  have : NeZero N := NeZero.of_pos i.pos
  rw [localTerm_eq_toLin'_term A L i,
    ManyBody.Interaction.translationInvariant_term_of_not_le _ hLN, map_zero]

/-- Pointwise formula for a translated local term when the window length is at
most the chain length. -/
@[simp] theorem localTerm_apply_of_le (A : MPSTensor d D) (L N : ℕ)
    (hLN : L ≤ N) (i : Fin N) (ψ : NSiteSpace d N) (σ : Cfg d N) :
    localTerm A L N i ψ σ =
      parentInteraction A L
        (fun τ => ψ (replaceWindow L hLN i σ τ)) (extractWindow L i σ) := by
  have : NeZero N := NeZero.of_pos i.pos
  rw [localTerm_eq_toLin'_term A L i, Matrix.toLin'_apply,
    ManyBody.Interaction.translationInvariant_term_of_le _ hLN i,
    ManyBody.placeAlong_mulVec_apply_of _ _ ψ σ (replaceWindow L hLN i σ)
      (replaceWindow_ringWindow hLN i σ)
      (fun τ _ hv ↦ replaceWindow_of_forall_ringWindow_ne hLN i σ τ hv)]
  exact (congrFun (LinearMap.congr_fun (Matrix.toLin'_toMatrix' (parentInteraction A L))
    (fun τ ↦ ψ (replaceWindow L hLN i σ τ))) (extractWindow L i σ))

/-- The parent Hamiltonian is the Hamiltonian of the parent interaction on the ring. -/
theorem parentHamiltonian_eq_toLin'_hamiltonian (A : MPSTensor d D) (L : ℕ) [NeZero N] :
    parentHamiltonian A L N = Matrix.toLin' (parentRingInteraction A L N).hamiltonian := by
  rw [ManyBody.Interaction.hamiltonian, map_sum]
  rfl

/-- The parent Hamiltonian is the sum of the translated local terms. -/
theorem parentHamiltonian_eq_sum_localTerm (A : MPSTensor d D) (L N : ℕ) :
    parentHamiltonian A L N = ∑ i : Fin N, localTerm A L N i :=
  rfl

/-- The two-site parent Hamiltonian on a one-site periodic chain is zero under
the project's convention for a local interaction larger than the chain.

**Scope restriction (one-site chain):** Beigi, J. Phys. A 45 (2012) 025306,
Section III, defines each interaction on two neighboring sites but
does not specify its action when those sites coincide. The zero value here is
the convention in `localTerm`, not a one-site case of Beigi's ordered-cycle
formula. CPSV16, arXiv:1606.00608, Theorem 3.10(iii), source lines 534--540,
only uses chain lengths greater than two. This restriction is documented in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`. -/
@[simp] theorem parentHamiltonian_two_one_eq_zero (A : MPSTensor d D) :
    parentHamiltonian A 2 1 = 0 := by
  exact Finset.sum_eq_zero fun i _ ↦ localTerm_of_not_le A (by norm_num) i

end MPSTensor

/-! ### The Hamiltonian of the open-chain translates

Its dependence on the local matrix. The order and projection properties of
`Matrix.toEuclideanLin` are in `QICLean.Algebra.MatrixToEuclidean` and
`QICLean.Algebra.MatrixStarProjection`, and the sum over the starting positions is
`ManyBody.Interaction.hamiltonian_chainTranslates_eq_sum_range`. -/

namespace ManyBody.Interaction

section ChainTranslates

open scoped MatrixOrder ComplexOrder

variable {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}

/-- The Hamiltonian of the open-chain translates is monotone in the local matrix. -/
theorem hamiltonian_chainTranslates_mono {h h' : Matrix (Fin k → α) (Fin k → α) ℂ} (hle : h ≤ h')
    (N : ℕ) : (chainTranslates k N h).hamiltonian ≤ (chainTranslates k N h').hamiltonian :=
  Finset.sum_le_sum fun _ _ ↦ placeAlong_le_placeAlong (X := fun _ ↦ α) _ hle

/-- The Hamiltonian of the open-chain translates is linear in the local matrix. -/
theorem hamiltonian_chainTranslates_smul (c : ℂ) (h : Matrix (Fin k → α) (Fin k → α) ℂ)
    (N : ℕ) :
    (chainTranslates k N (c • h)).hamiltonian = c • (chainTranslates k N h).hamiltonian := by
  simp only [hamiltonian, ofPlaceAlong_term, placeAlong_smul, Finset.smul_sum]

/-- The open-chain translates of the zero matrix have zero Hamiltonian. -/
theorem hamiltonian_chainTranslates_zero (N : ℕ) :
    (chainTranslates k N (0 : Matrix (Fin k → α) (Fin k → α) ℂ)).hamiltonian = 0 := by
  simp [hamiltonian, ofPlaceAlong_term, placeAlong_zero]

/-- The open-chain translates of a positive semidefinite matrix have a positive semidefinite
Hamiltonian. -/
theorem posSemidef_hamiltonian_chainTranslates {h : Matrix (Fin k → α) (Fin k → α) ℂ}
    (hh : h.PosSemidef) (N : ℕ) : (chainTranslates k N h).hamiltonian.PosSemidef :=
  posSemidef_hamiltonian fun i ↦ Matrix.nonneg_iff_posSemidef.mp
    (ofPlaceAlong_term_nonneg _ (fun _ ↦ Matrix.nonneg_iff_posSemidef.mpr hh) i)

end ChainTranslates

end ManyBody.Interaction
