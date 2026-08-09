/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.OpenChain
import TNLean.MPS.ParentHamiltonian.SuffixWindow

/-!
# Spectator-indexed boundary maps for overlapping MPS windows

This file defines the spectator-indexed tail and left boundary maps that
embed virtual-space data into a common ambient physical Hilbert space, and
proves exact range and word-factorization identities.  These are the maps
required to place overlapping ground spaces in the same ambient
Hilbert space before a spectral-gap estimate can compare their projectors.

All lemmas are purely algebraic and exact; no convergence norm or contraction
estimate is asserted.

## Main definitions

* `MPSTensor.tailBoundaryMap A K L` --- maps a family
  \(\{Y_u\}\) (indexed by \(K\)-site prefix configurations) to a vector
  on \(K+L\) sites via \(\psi(u,\tau)=  \tr(A^{\tau} Y_u)\).
* `MPSTensor.prefixRestrictₗ` --- fixes a suffix \(\tau\) and restricts
  to the prefix (the left-sided analogue of `tailRestrictₗ`).
* `MPSTensor.leftBoundaryMap A K L` --- maps a family
  \(\{Z_{\tau}\}\) (indexed by \(L\)-site suffix configurations) to a vector
  on \(K+L\) sites via \(\psi(u,\tau)=  \tr(A^{u} Z_{\tau})\).

## Main results

* `MPSTensor.tailBoundaryMap_factorization` --- the standard
  length-\((K+L)\) boundary map factors through the tail boundary map:
  \(\Gamma_{K+L}(X)=\Gamma^{\mathrm{tail}}_{K,L}(u\mapsto X A^u)\).
* `MPSTensor.tailBoundaryMap_range_eq` --- the range of the tail boundary
  map is exactly the tail ground space
  \(\{\psi\mid\forall u,\;\operatorname{tail\_restrict}_u\psi\in G_L(A)\}\).
* `MPSTensor.tailBoundaryMap_range_map_symm_eq_openChainTailGroundSpaceES`
  --- after Euclidean-space transport, the tail range identifies with
  `openChainTailGroundSpaceES`.
* `MPSTensor.leftBoundaryMap_factorization` --- the symmetric factorization:
  \(\Gamma_{K+L}(X)=\Gamma^{\mathrm{left}}_{K,L}(\tau\mapsto A^{\tau} X)\).
* `MPSTensor.leftBoundaryMap_range_eq` --- the range of the left boundary
  map is exactly the left ground space
  \(\{\psi\mid\forall \tau,\;\operatorname{prefix\_restrict}_{\tau}\psi\in G_K(A)\}\).
* `MPSTensor.leftBoundaryMap_range_map_symm_eq_openChainLeftGroundSpaceES`
  --- at \(L=1\) (the C3 specialization), the Euclidean-space transport of the
  left range identifies with `openChainLeftGroundSpaceES`.

## Scope restriction (FNW contraction not derived)

The algebraic identities above place both ground spaces as ranges of boundary
maps on the same ambient \(\mathcal{H}_{K+L}\).  The FNW transfer-mixing estimate that
would bound the defect \(\|P_{\mathrm{tail}}\circ P_{\mathrm{left}}
-P_{\mathrm{full}}\|\) using the inverse-Gram range-projector formula
(`GroundSpaceGram.lean`) and the spectral properties of the transfer operator
is not derived here.  Deriving that numerical contraction from the Gram/transfer
identities and inverse-Gram control remains open.  Both boundary maps are
unweighted (Frobenius) and the Gram identities are normalization-neutral; the
contraction estimate may require a second fixed-point metric or weighted
boundary coordinates.

## Open-chain context

For Nachtergaele C3 (arXiv:cond-mat/9410110, eq. (2.4)), take
\(K := n - l\), \(L := l + 1\), and let the common ambient space be
\(\mathcal{H}_{K+L} = \mathcal{H}_{n+1}\).  After Euclidean-space transport,
the tail window is the range of \(\Gamma^{\mathrm{tail}}_{K,L}\), while the
left window (first \(K+L-1\) sites with one final spectator) is the range of
\(\Gamma^{\mathrm{left}}_{K+L-1,1}\).  Thus the two transport theorems below realize
both C3 subspaces as boundary-map ranges in this common ambient space.

## References

* B. Nachtergaele, arXiv:cond-mat/9410110, eqs. (2.4)--(2.5), Theorem 3,
  and Section 6.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-! ### Prefix restriction (left symmetric of `tailRestrictₗ`) -/

/-- Fix a suffix \(τ : Fin L → Fin d\) and restrict a \(K+L\)-site state to its
first \(K\) sites.  This is the left-sided analogue of \(tailRestrictₗ\). -/
def prefixRestrictₗ {d K L : ℕ} (τ : Fin L → Fin d) :
    NSiteSpace d (K + L) →ₗ[ℂ] NSiteSpace d K where
  toFun ψ := fun σ => ψ (Fin.append σ τ)
  map_add' ψ₁ ψ₂ := by ext σ; simp
  map_smul' c ψ := by ext σ; simp

@[simp] theorem prefixRestrictₗ_apply {d K L : ℕ} (τ : Fin L → Fin d)
    (ψ : NSiteSpace d (K + L)) (σ : Fin K → Fin d) :
    prefixRestrictₗ τ ψ σ = ψ (Fin.append σ τ) := rfl

/-- The prefix restriction of a ground-space vector: fixing the suffix τ and
keeping the prefix variable moves the suffix word to the left factor of the
virtual matrix. -/
@[simp] theorem prefixRestrictₗ_groundSpaceMap (A : MPSTensor d D) {K L : ℕ}
    (τ : Fin L → Fin d) (X : Matrix (Fin D) (Fin D) ℂ) :
    prefixRestrictₗ τ (groundSpaceMap A (K + L) X) =
      groundSpaceMap A K (evalWord A (List.ofFn τ) * X) := by
  ext σ
  simp only [prefixRestrictₗ_apply, groundSpaceMap_apply]
  calc
    Matrix.trace (evalWord A (List.ofFn (Fin.append σ τ)) * X)
        = Matrix.trace ((evalWord A (List.ofFn σ) * evalWord A (List.ofFn τ)) * X) := by
          simp [List.ofFn_fin_append, evalWord_append A]
    _ = Matrix.trace (evalWord A (List.ofFn σ) * (evalWord A (List.ofFn τ) * X)) := by
          simp [Matrix.mul_assoc]

/-! ### Tail (prefix-spectator) boundary map -/

/-- Spectator-indexed tail boundary map.

For a family \(Y : (Fin K → Fin d) → Matrix (Fin D) (Fin D) ℂ\) indexed by
\(K\)-site prefix configurations, the map produces a vector on \(K+L\) sites by
\[
  (\Gamma^{\mathrm{tail}}_{K,L}(Y))(u,\tau)
  = \operatorname{tr}\bigl(A^{\tau}\;Y_u\bigr),
\]
where \(u\) is the prefix and \(τ\) is the suffix.
When \(Y_u = X·A^u\) the output equals the standard \(Γ_{K+L}(X)\). -/
noncomputable def tailBoundaryMap (A : MPSTensor d D) (K L : ℕ) :
    ((Fin K → Fin d) → Matrix (Fin D) (Fin D) ℂ) →ₗ[ℂ] NSiteSpace d (K + L) where
  toFun Y σ := Matrix.trace (evalWord A (List.ofFn (σ ∘ Fin.natAdd K)) *
    Y (σ ∘ Fin.castAdd L))
  map_add' Y₁ Y₂ := by ext σ; simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' c Y := by ext σ; simp [Matrix.trace_smul, smul_eq_mul]

@[simp] theorem tailBoundaryMap_apply (A : MPSTensor d D) (K L : ℕ)
    (Y : (Fin K → Fin d) → Matrix (Fin D) (Fin D) ℂ) (σ : Cfg d (K + L)) :
    tailBoundaryMap A K L Y σ =
      Matrix.trace (evalWord A (List.ofFn (σ ∘ Fin.natAdd K)) *
        Y (σ ∘ Fin.castAdd L)) :=
  rfl

/-- The tail boundary map on a prefix–suffix pair reduces to the local
ground-space map on the suffix. -/
theorem tailBoundaryMap_append (A : MPSTensor d D) (K L : ℕ)
    (Y : (Fin K → Fin d) → Matrix (Fin D) (Fin D) ℂ)
    (u : Fin K → Fin d) (τ : Fin L → Fin d) :
    tailBoundaryMap A K L Y (Fin.append u τ) =
      groundSpaceMap A L (Y u) τ := by
  calc
    tailBoundaryMap A K L Y (Fin.append u τ)
        = Matrix.trace (evalWord A
            (List.ofFn ((Fin.append u τ) ∘ Fin.natAdd K)) *
          Y ((Fin.append u τ) ∘ Fin.castAdd L)) := rfl
    _ = Matrix.trace (evalWord A (List.ofFn τ) * Y u) := by
      have h_suffix : (Fin.append u τ) ∘ Fin.natAdd K = τ := by
        ext i; simp [Fin.append_right]
      have h_prefix : (Fin.append u τ) ∘ Fin.castAdd L = u := by
        ext i; simp [Fin.append_left]
      simp [h_suffix, h_prefix]
    _ = groundSpaceMap A L (Y u) τ := by simp [groundSpaceMap_apply]

/-- Restricting the tail boundary map to the suffix for a fixed prefix \(u\)
recovers \(Γ_L(Y_u)\). -/
@[simp] theorem tailRestrictₗ_tailBoundaryMap (A : MPSTensor d D) (K L : ℕ)
    (Y : (Fin K → Fin d) → Matrix (Fin D) (Fin D) ℂ) (u : Fin K → Fin d) :
    tailRestrictₗ u (tailBoundaryMap A K L Y) = groundSpaceMap A L (Y u) := by
  ext τ
  simp [tailBoundaryMap_append A K L Y u τ]

/-- Word-factorization identity: the standard length-\((K+L)\) boundary map
factors through the tail boundary map by \(X ↦ (λ u, X·A^u)\).
\[
  \Gamma_{K+L}(X) = \Gamma^{\mathrm{tail}}_{K,L}(\lambda u,\; X\,A^u).
\] -/
theorem tailBoundaryMap_factorization (A : MPSTensor d D) (K L : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    tailBoundaryMap A K L
      (fun u : Fin K → Fin d => X * evalWord A (List.ofFn u)) =
        groundSpaceMap A (K + L) X := by
  ext σ
  rw [tailBoundaryMap_apply, groundSpaceMap_apply]
  set u := σ ∘ Fin.castAdd L
  set τ := σ ∘ Fin.natAdd K
  have hσ : σ = Fin.append u τ := Fin.append_castAdd_natAdd.symm
  calc
    Matrix.trace (evalWord A (List.ofFn τ) * (X * evalWord A (List.ofFn u)))
        = Matrix.trace (evalWord A (List.ofFn u) *
          (evalWord A (List.ofFn τ) * X)) := by
      rw [Matrix.trace_mul_cycle' (evalWord A (List.ofFn τ)) X
        (evalWord A (List.ofFn u))]
    _ = Matrix.trace ((evalWord A (List.ofFn u) * evalWord A (List.ofFn τ)) * X) := by
      simp [Matrix.mul_assoc]
    _ = Matrix.trace (evalWord A (List.ofFn u ++ List.ofFn τ) * X) := by
      simp [evalWord_append A]
    _ = Matrix.trace (evalWord A (List.ofFn (Fin.append u τ)) * X) := by
      simp [List.ofFn_fin_append]
    _ = groundSpaceMap A (K + L) X σ := by simp [hσ, groundSpaceMap_apply]

/-- The range of the tail boundary map equals the tail ground space:
vectors whose suffix restriction lies in the local ground space for
every prefix configuration. -/
theorem tailBoundaryMap_range_eq (A : MPSTensor d D) (K L : ℕ) :
    (tailBoundaryMap A K L).range =
      {ψ : NSiteSpace d (K + L) | ∀ u : Fin K → Fin d,
        tailRestrictₗ u ψ ∈ groundSpace A L} := by
  ext ψ
  constructor
  · rintro ⟨Y, rfl⟩ u
    rw [tailRestrictₗ_tailBoundaryMap A K L Y u]
    exact ⟨Y u, rfl⟩
  · intro hψ
    -- For each prefix u, pick a matrix Y_u representing the suffix slice
    have hY : ∀ u : Fin K → Fin d,
        tailRestrictₗ u ψ ∈ (groundSpaceMap A L).range := by
      intro u
      have hu := hψ u
      simpa [groundSpace] using hu
    -- Extract choice function Y
    choose Y hY' using (fun u => (LinearMap.mem_range).mp (hY u))
    -- hY' : ∀ u, groundSpaceMap A L (Y u) = tailRestrictₗ u ψ
    refine ⟨Y, ?_⟩
    ext σ
    rw [tailBoundaryMap_apply]
    set u := σ ∘ Fin.castAdd L
    set τ := σ ∘ Fin.natAdd K
    have hσ_eq : Fin.append u τ = σ := Fin.append_castAdd_natAdd
    have h_tail_eq : tailRestrictₗ u ψ τ = groundSpaceMap A L (Y u) τ := by
      rw [hY' u]
    rw [tailRestrictₗ_apply, hσ_eq, groundSpaceMap_apply] at h_tail_eq
    -- h_tail_eq : ψ σ = trace (evalWord A (List.ofFn τ) * Y u)
    simpa [groundSpaceMap_apply] using h_tail_eq.symm

/-! ### Left (suffix-spectator) boundary map -/

/-- Spectator-indexed left boundary map.

For a family \(Z : (Fin L → Fin d) → Matrix (Fin D) (Fin D) ℂ\) indexed by
\(L\)-site suffix configurations, the map produces a vector on \(K+L\) sites by
\[
  (\Gamma^{\mathrm{left}}_{K,L}(Z))(u,\tau)
  = \operatorname{tr}\bigl(A^{u}\;Z_{\tau}\bigr),
\]
where \(u\) is the prefix and \(τ\) is the suffix.
When \(Z_τ = A^τ·X\) the output equals the standard \(Γ_{K+L}(X)\). -/
noncomputable def leftBoundaryMap (A : MPSTensor d D) (K L : ℕ) :
    ((Fin L → Fin d) → Matrix (Fin D) (Fin D) ℂ) →ₗ[ℂ] NSiteSpace d (K + L) where
  toFun Z σ := Matrix.trace (evalWord A (List.ofFn (σ ∘ Fin.castAdd L)) *
    Z (σ ∘ Fin.natAdd K))
  map_add' Z₁ Z₂ := by ext σ; simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' c Z := by ext σ; simp [Matrix.trace_smul, smul_eq_mul]

@[simp] theorem leftBoundaryMap_apply (A : MPSTensor d D) (K L : ℕ)
    (Z : (Fin L → Fin d) → Matrix (Fin D) (Fin D) ℂ) (σ : Cfg d (K + L)) :
    leftBoundaryMap A K L Z σ =
      Matrix.trace (evalWord A (List.ofFn (σ ∘ Fin.castAdd L)) *
        Z (σ ∘ Fin.natAdd K)) :=
  rfl

/-- The left boundary map on a prefix–suffix pair reduces to the local
ground-space map on the prefix. -/
theorem leftBoundaryMap_append (A : MPSTensor d D) (K L : ℕ)
    (Z : (Fin L → Fin d) → Matrix (Fin D) (Fin D) ℂ)
    (u : Fin K → Fin d) (τ : Fin L → Fin d) :
    leftBoundaryMap A K L Z (Fin.append u τ) =
      groundSpaceMap A K (Z τ) u := by
  calc
    leftBoundaryMap A K L Z (Fin.append u τ)
        = Matrix.trace (evalWord A
            (List.ofFn ((Fin.append u τ) ∘ Fin.castAdd L)) *
          Z ((Fin.append u τ) ∘ Fin.natAdd K)) := rfl
    _ = Matrix.trace (evalWord A (List.ofFn u) * Z τ) := by
      have h_prefix : (Fin.append u τ) ∘ Fin.castAdd L = u := by
        ext i; simp [Fin.append_left]
      have h_suffix : (Fin.append u τ) ∘ Fin.natAdd K = τ := by
        ext i; simp [Fin.append_right]
      simp [h_prefix, h_suffix]
    _ = groundSpaceMap A K (Z τ) u := by simp [groundSpaceMap_apply]

/-- Restricting the left boundary map to the prefix for a fixed suffix \(τ\)
recovers \(Γ_K(Z_τ)\). -/
@[simp] theorem prefixRestrictₗ_leftBoundaryMap (A : MPSTensor d D) (K L : ℕ)
    (Z : (Fin L → Fin d) → Matrix (Fin D) (Fin D) ℂ) (τ : Fin L → Fin d) :
    prefixRestrictₗ τ (leftBoundaryMap A K L Z) = groundSpaceMap A K (Z τ) := by
  ext σ
  simp [leftBoundaryMap_append A K L Z σ τ]

/-- Word-factorization identity (left side): the standard length-\((K+L)\)
boundary map factors through the left boundary map by \(X ↦ (λ τ, A^τ·X)\).
\[
  \Gamma_{K+L}(X) = \Gamma^{\mathrm{left}}_{K,L}(\lambda \tau,\; A^\tau\,X).
\] -/
theorem leftBoundaryMap_factorization (A : MPSTensor d D) (K L : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    leftBoundaryMap A K L
      (fun τ : Fin L → Fin d => evalWord A (List.ofFn τ) * X) =
        groundSpaceMap A (K + L) X := by
  ext σ
  rw [leftBoundaryMap_apply, groundSpaceMap_apply]
  set u := σ ∘ Fin.castAdd L
  set τ := σ ∘ Fin.natAdd K
  have hσ : σ = Fin.append u τ := Fin.append_castAdd_natAdd.symm
  calc
    Matrix.trace (evalWord A (List.ofFn u) * (evalWord A (List.ofFn τ) * X))
        = Matrix.trace ((evalWord A (List.ofFn u) *
          evalWord A (List.ofFn τ)) * X) := by
      simp [Matrix.mul_assoc]
    _ = Matrix.trace (evalWord A (List.ofFn u ++ List.ofFn τ) * X) := by
      simp [evalWord_append A]
    _ = Matrix.trace (evalWord A (List.ofFn (Fin.append u τ)) * X) := by
      simp [List.ofFn_fin_append]
    _ = groundSpaceMap A (K + L) X σ := by simp [hσ, groundSpaceMap_apply]

/-- The range of the left boundary map equals the left ground space:
vectors whose prefix restriction lies in the local ground space for
every suffix configuration. -/
theorem leftBoundaryMap_range_eq (A : MPSTensor d D) (K L : ℕ) :
    (leftBoundaryMap A K L).range =
      {ψ : NSiteSpace d (K + L) | ∀ τ : Fin L → Fin d,
        prefixRestrictₗ τ ψ ∈ groundSpace A K} := by
  ext ψ
  constructor
  · rintro ⟨Z, rfl⟩ τ
    rw [prefixRestrictₗ_leftBoundaryMap A K L Z τ]
    exact ⟨Z τ, rfl⟩
  · intro hψ
    have hZ : ∀ τ : Fin L → Fin d,
        prefixRestrictₗ τ ψ ∈ (groundSpaceMap A K).range := by
      intro τ
      have hτ := hψ τ
      simpa [groundSpace] using hτ
    choose Z hZ' using (fun τ => (LinearMap.mem_range).mp (hZ τ))
    refine ⟨Z, ?_⟩
    ext σ
    rw [leftBoundaryMap_apply]
    set u := σ ∘ Fin.castAdd L
    set τ := σ ∘ Fin.natAdd K
    have hσ_eq : Fin.append u τ = σ := Fin.append_castAdd_natAdd
    have h_pre_eq : prefixRestrictₗ τ ψ u = groundSpaceMap A K (Z τ) u := by
      rw [hZ' τ]
    rw [prefixRestrictₗ_apply, hσ_eq, groundSpaceMap_apply] at h_pre_eq
    -- h_pre_eq : ψ σ = trace (evalWord A (List.ofFn u) * Z τ)
    simpa [groundSpaceMap_apply] using h_pre_eq.symm

/-! ### Euclidean-space transport to open-chain submodules

The following theorems identify the ranges of the spectator-indexed boundary
maps, after transport by the canonical `WithLp` isomorphism, with the
Hilbert-space ground submodules used in the open-chain martingale condition
(Chapter~13, Nachtergaele C3). -/

/-- For a one-site suffix \(\tau\), prefix restriction by \(\tau\) coincides
with last-site restriction at \(\tau(0)\).  This is used to connect the left boundary map range
(at \(L=1\)) to the open-chain left ground space defined by fixing the
last site. -/
lemma prefixRestrictₗ_one_eq_restrictLast {d K : ℕ} (τ : Fin 1 → Fin d)
    (ψ : NSiteSpace d (K + 1)) :
    prefixRestrictₗ τ ψ = restrictLast ψ (τ 0) := by
  ext σ
  simp [prefixRestrictₗ_apply, restrictLast_apply, Fin.append_right_eq_snoc]


/-- The Euclidean-space transport of the tail boundary map range identifies
with `openChainTailGroundSpaceES`.  This is the exact common-ambient
identification required for the open-chain martingale condition C3
(Nachtergaele, arXiv:cond-mat/9410110, eq. (2.4)). -/
theorem tailBoundaryMap_range_map_symm_eq_openChainTailGroundSpaceES
    (A : MPSTensor d D) (K L : ℕ) :
    Submodule.map ((WithLp.linearEquiv 2 ℂ (NSiteSpace d (K + L))).symm).toLinearMap
      (tailBoundaryMap A K L).range =
    openChainTailGroundSpaceES A K L :=
  calc
    Submodule.map ((WithLp.linearEquiv 2 ℂ (NSiteSpace d (K + L))).symm).toLinearMap
        (tailBoundaryMap A K L).range
      = Submodule.map ((WithLp.linearEquiv 2 ℂ (NSiteSpace d (K + L))).symm).toLinearMap
          (⨅ u : Fin K → Fin d, (groundSpace A L).comap (tailRestrictₗ u)) := by
        congr 1
        apply Submodule.ext
        intro ψ
        have h_set := tailBoundaryMap_range_eq A K L
        have h_mem := congrArg (fun (s : Set (NSiteSpace d (K + L))) => ψ ∈ s) h_set
        simpa [Submodule.mem_iInf, groundSpace, tailRestrictₗ] using h_mem
    _ = openChainTailGroundSpaceES A K L := by
      simp [openChainTailGroundSpaceES]

/-- At suffix length \(L=1\) (the C3 specialization), the Euclidean-space
transport of the left boundary map range identifies with
`openChainLeftGroundSpaceES`.  This complements the tail transport
theorem to place both overlapping ground spaces in the same ambient
Hilbert space. -/
theorem leftBoundaryMap_range_map_symm_eq_openChainLeftGroundSpaceES
    (A : MPSTensor d D) (K : ℕ) :
    Submodule.map ((WithLp.linearEquiv 2 ℂ (NSiteSpace d (K + 1))).symm).toLinearMap
      (leftBoundaryMap A K 1).range =
    openChainLeftGroundSpaceES A K :=
  calc
    Submodule.map ((WithLp.linearEquiv 2 ℂ (NSiteSpace d (K + 1))).symm).toLinearMap
        (leftBoundaryMap A K 1).range
      = Submodule.map ((WithLp.linearEquiv 2 ℂ (NSiteSpace d (K + 1))).symm).toLinearMap
          (⨅ j : Fin d, (groundSpace A K).comap (restrictLastₗ j)) := by
        congr 1
        apply Submodule.ext
        intro ψ
        have h_set := leftBoundaryMap_range_eq A K 1
        have h1 : ψ ∈ (leftBoundaryMap A K 1).range ↔
            ∀ τ : Fin 1 → Fin d, prefixRestrictₗ τ ψ ∈ groundSpace A K := by
          have := congrArg (fun (s : Set (NSiteSpace d (K + 1))) => ψ ∈ s) h_set
          simpa using this
        have h2 : (∀ τ : Fin 1 → Fin d, prefixRestrictₗ τ ψ ∈ groundSpace A K) ↔
            (∀ j : Fin d, (restrictLastₗ j) ψ ∈ groundSpace A K) := by
          constructor
          · intro h j
            have h_pre := h (fun _ => j)
            have eq_pre : prefixRestrictₗ (fun _ : Fin 1 => j) ψ = (restrictLastₗ j) ψ := by
              simpa [restrictLast] using prefixRestrictₗ_one_eq_restrictLast
                (fun _ : Fin 1 => j) ψ
            rwa [eq_pre] at h_pre
          · intro h τ
            have h_last := h (τ 0)
            have eq_last : prefixRestrictₗ τ ψ = (restrictLastₗ (τ 0)) ψ := by
              simpa [restrictLast] using prefixRestrictₗ_one_eq_restrictLast τ ψ
            rw [eq_last]
            exact h_last
        have h3 : (∀ j : Fin d, (restrictLastₗ j) ψ ∈ groundSpace A K) ↔
            ψ ∈ ⨅ j : Fin d, (groundSpace A K).comap (restrictLastₗ j) := by
          simp [Submodule.mem_iInf]
        exact (h1.trans h2).trans h3
    _ = openChainLeftGroundSpaceES A K := by
      simp [openChainLeftGroundSpaceES]

end MPSTensor
