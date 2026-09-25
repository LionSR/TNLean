/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Defs

/-!
# Basic parent-Hamiltonian properties

The parent interaction is the orthogonal projector onto \(G_L(A)^\perp\).
It therefore annihilates any vector in the ground space. The periodic MPS vector
`mpv A` lies in the ground space at every window, which gives
frustration-freeness.
-/

open scoped BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ### Parent interaction as a projector -/

/-- The parent interaction is idempotent.

This is the algebraic form of the fact that it is the orthogonal projector onto
\(G_L(A)^\perp\). -/
theorem parentInteraction_idempotent (A : MPSTensor d D) (L : ℕ) :
    parentInteraction A L * parentInteraction A L = parentInteraction A L := by
  let e := WithLp.linearEquiv 2 ℂ (NSiteSpace d L)
  let P : EuclideanSpace ℂ (Cfg d L) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d L) :=
    (groundSpaceES A L)ᗮ.starProjection.toLinearMap
  have hP : P * P = P := by
    simpa [P] using
      (Submodule.isSymmetricProjection_starProjection ((groundSpaceES A L)ᗮ)).isIdempotentElem.eq
  apply LinearMap.ext
  intro v
  change e (P (e.symm (e (P (e.symm v))))) = e (P (e.symm v))
  rw [LinearEquiv.symm_apply_apply]
  exact congr_arg e (LinearMap.congr_fun hP (e.symm v))

/-- Two tensors with the same local MPS space at length \(L\) have the same
canonical parent interaction at that length.

The parent interaction is the orthogonal projector onto \(G_L(A)^\perp\), so it
is a function of \(G_L(A)\) alone. -/
theorem parentInteraction_eq_of_groundSpace_eq {A B : MPSTensor d D} {L : ℕ}
    (h : groundSpace A L = groundSpace B L) :
    parentInteraction A L = parentInteraction B L := by
  simp [parentInteraction, groundSpaceES, h]

/-- Equal parent interactions give equal translated local terms. -/
theorem localTerm_eq_of_parentInteraction_eq {A B : MPSTensor d D} {L : ℕ}
    (h : parentInteraction A L = parentInteraction B L) (N : ℕ) (i : Fin N) :
    localTerm A L N i = localTerm B L N i := by
  unfold localTerm
  rw [h]

/-- Two tensors with the same local MPS space at length \(L\) have the same
finite-chain parent Hamiltonian on every periodic chain. -/
theorem parentHamiltonian_eq_of_groundSpace_eq {A B : MPSTensor d D} {L : ℕ}
    (h : groundSpace A L = groundSpace B L) (N : ℕ) :
    parentHamiltonian A L N = parentHamiltonian B L N := by
  unfold parentHamiltonian
  exact Finset.sum_congr rfl fun i _ =>
    localTerm_eq_of_parentInteraction_eq
      (parentInteraction_eq_of_groundSpace_eq h) N i

/-- A virtual gauge change leaves the canonical parent interaction unchanged.

The parent interaction depends only on the local MPS space, and gauge-equivalent
tensors have the same local MPS space at every length. -/
theorem GaugeEquiv.parentInteraction_eq {A B : MPSTensor d D}
    (h : GaugeEquiv A B) (L : ℕ) :
    parentInteraction A L = parentInteraction B L :=
  parentInteraction_eq_of_groundSpace_eq (h.groundSpace_eq L)

/-- A virtual gauge change leaves every translated parent interaction unchanged. -/
theorem GaugeEquiv.localTerm_eq {A B : MPSTensor d D}
    (h : GaugeEquiv A B) (L N : ℕ) (i : Fin N) :
    localTerm A L N i = localTerm B L N i :=
  localTerm_eq_of_parentInteraction_eq (h.parentInteraction_eq L) N i

/-- Pointwise formula for a translated local term when the window length is at
most the chain length. -/
@[simp] theorem localTerm_apply_of_le (A : MPSTensor d D) (L N : ℕ)
    (hLN : L ≤ N) (i : Fin N) (ψ : NSiteSpace d N) (σ : Cfg d N) :
    localTerm A L N i ψ σ =
      parentInteraction A L
        (fun τ => ψ (replaceWindow L hLN i σ τ)) (extractWindow L i σ) := by
  rw [localTerm, dite_eq_left hLN]
  rfl

/-- Every translated local parent interaction is idempotent.

This is the finite-chain form of the fact that the local parent interaction is an
orthogonal projector. -/
theorem localTerm_idempotent (A : MPSTensor d D) (L N : ℕ) (i : Fin N) :
    localTerm A L N i * localTerm A L N i = localTerm A L N i := by
  by_cases hLN : L ≤ N
  · apply LinearMap.ext
    intro ψ
    ext σ
    rw [Module.End.mul_apply]
    rw [localTerm_apply_of_le A L N hLN i (localTerm A L N i ψ) σ]
    rw [localTerm_apply_of_le A L N hLN i ψ σ]
    let f : NSiteSpace d L := fun τ => ψ (replaceWindow L hLN i σ τ)
    have hwindow :
        (fun τ => localTerm A L N i ψ (replaceWindow L hLN i σ τ)) =
          parentInteraction A L f := by
      funext τ
      rw [localTerm_apply_of_le A L N hLN i ψ (replaceWindow L hLN i σ τ)]
      simp [f]
    rw [hwindow]
    change parentInteraction A L (parentInteraction A L f) (extractWindow L i σ) =
      parentInteraction A L f (extractWindow L i σ)
    exact congr_fun (LinearMap.congr_fun (parentInteraction_idempotent A L) f)
      (extractWindow L i σ)
  · simp [localTerm, hLN]

/-! ### Parent interaction kills ground space elements -/

/-- The parent interaction annihilates any vector in the ground space.
This is the core property: `parentInteraction A L` is the orthogonal projector
onto \(G_L(A)^\perp\), so it kills everything in `groundSpace A L`. -/
lemma parentInteraction_apply_mem_groundSpace (A : MPSTensor d D) (L : ℕ)
    (v : NSiteSpace d L) (hv : v ∈ groundSpace A L) :
    parentInteraction A L v = 0 := by
  have hmem : (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm v ∈ groundSpaceES A L := by
    simp only [groundSpaceES, Submodule.mem_map]
    exact ⟨v, hv, rfl⟩
  have hkill : (groundSpaceES A L)ᗮ.starProjection
      ((WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm v) = 0 := by
    rw [Submodule.starProjection_orthogonal']
    simp only [sub_apply, one_apply_eq_self]
    rw [sub_eq_zero]
    exact (Submodule.starProjection_eq_self_iff.mpr hmem).symm
  -- Unfold `parentInteraction` to expose the equiv ∘ projection ∘ equiv⁻¹ structure.
  -- This `change` is definitional; update it if `parentInteraction` is restated.
  change (WithLp.linearEquiv 2 ℂ (NSiteSpace d L))
    ((groundSpaceES A L)ᗮ.starProjection
      ((WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm v)) = 0
  rw [hkill, map_zero]

/-! ### Periodic MPS vector window membership -/

/-- A boundary matrix that commutes with every letter up to a scalar \(c\) moves
past a word of length \(n\) at the cost of \(c^n\). -/
theorem mul_evalWord_of_mul_eq_smul (A : MPSTensor d D)
    (G : Matrix (Fin D) (Fin D) ℂ) (c : ℂ) (hG : ∀ i, G * A i = c • (A i * G)) :
    ∀ w : List (Fin d),
      G * Kraus.evalWord A w = c ^ w.length • (Kraus.evalWord A w * G)
  | [] => by simp
  | i :: w => by
      rw [Kraus.evalWord_cons, ← Matrix.mul_assoc, hG, Matrix.smul_mul, Matrix.mul_assoc,
        mul_evalWord_of_mul_eq_smul A G c hG w, Matrix.mul_smul, smul_smul,
        ← Matrix.mul_assoc, List.length_cons, pow_succ']

/-- The configuration with a window replaced, rotated to start at the window, is
the window followed by the outside sites in cyclic order starting from \(i+L\). -/
theorem rotate_ofFn_replaceWindow (L N : ℕ) (hLN : L ≤ N) (i : Fin N)
    (σ : Cfg d N) (τ : Fin L → Fin d) (hN : 0 < N) :
    (List.ofFn (replaceWindow L hLN i σ τ)).rotate i.val =
      List.ofFn τ ++ List.ofFn fun (j : Fin (N - L)) =>
        σ ⟨(i.val + L + j.val) % N, Nat.mod_lt _ hN⟩ := by
  apply List.ext_getElem
  · simp only [List.length_rotate, List.length_append, List.length_ofFn]
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
    · rw [dite_eq_left hkL, List.getElem_append_left (by simp only [List.length_ofFn]; exact hkL),
        List.getElem_ofFn]
    · rw [dite_eq_right hkL, List.getElem_append_right (by simp; omega), List.getElem_ofFn]
      simp only [List.length_ofFn]
      congr 1
      apply Fin.ext
      change (k + i.val) % N = (i.val + L + (k - L)) % N
      rw [show i.val + L + (k - L) = k + i.val by omega]

/-- If \(GA^i=c\,A^iG\) for every letter, the twisted periodic vector
\(\sigma\mapsto\operatorname{tr}(A^{\sigma_0}\cdots A^{\sigma_{N-1}}G)\) restricted
to any window of \(L\) sites lies in `groundSpace A L`.

The witness is \(c^i\) times the product of \(A\)-matrices on the sites outside the
window, cyclically ordered from \(i+L\), followed by \(G\). Trace cyclicity
rotates the full product so that the window comes first, and \(G\) is moved past
the \(i\) letters in front of the window. -/
theorem twistedMPV_window_mem_groundSpace (A : MPSTensor d D)
    (G : Matrix (Fin D) (Fin D) ℂ) (c : ℂ) (hG : ∀ i, G * A i = c • (A i * G))
    (L N : ℕ) (hLN : L ≤ N) (i : Fin N) (σ : Cfg d N) :
    (fun τ => Matrix.trace (Kraus.evalWord A (List.ofFn (replaceWindow L hLN i σ τ)) * G))
      ∈ groundSpace A L := by
  rw [groundSpace, LinearMap.mem_range]
  have hN : 0 < N := Nat.lt_of_lt_of_le (Fin.pos i) le_rfl
  refine ⟨c ^ i.val • (Kraus.evalWord A (List.ofFn fun (j : Fin (N - L)) =>
    σ ⟨(i.val + L + j.val) % N, Nat.mod_lt _ hN⟩) * G), ?_⟩
  ext τ
  rw [groundSpaceMap_apply]
  set l := List.ofFn (replaceWindow L hLN i σ τ)
  have hle : i.val ≤ l.length := by simp [l, List.length_ofFn]
  have hrot := rotate_ofFn_replaceWindow L N hLN i σ τ hN
  rw [List.rotate_eq_drop_append_take hle] at hrot
  have htake : (l.take i.val).length = i.val := by simp [l, List.length_take]
  calc Matrix.trace (Kraus.evalWord A (List.ofFn τ) *
          (c ^ i.val • (Kraus.evalWord A _ * G)))
        = c ^ i.val * Matrix.trace (Kraus.evalWord A (l.drop i.val ++ l.take i.val) * G) := by
          rw [hrot, Kraus.evalWord_append, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
            Matrix.mul_assoc]
      _ = Matrix.trace (Kraus.evalWord A l * G) := by
          conv_rhs => rw [← List.take_append_drop i.val l]
          rw [Kraus.evalWord_append, Kraus.evalWord_append,
            Matrix.mul_assoc (Kraus.evalWord A (l.take i.val)),
            Matrix.trace_mul_comm (Kraus.evalWord A (l.take i.val)), Matrix.mul_assoc,
            Matrix.mul_assoc, mul_evalWord_of_mul_eq_smul A G c hG, htake, Matrix.mul_smul,
            Matrix.trace_smul, smul_eq_mul]

/-- The periodic MPS vector restricted to any window of \(L\) sites lies in
`groundSpace A L`: the case \(G=1\), \(c=1\) of
`twistedMPV_window_mem_groundSpace`. -/
lemma mpv_window_mem_groundSpace (A : MPSTensor d D) (L N : ℕ) (hLN : L ≤ N)
    (i : Fin N) (σ : Cfg d N) :
    (fun τ => mpv A (replaceWindow L hLN i σ τ)) ∈ groundSpace A L := by
  simpa [mpv, coeff] using
    twistedMPV_window_mem_groundSpace A 1 1 (fun _ => by simp) L N hLN i σ

/-- Each local term annihilates the periodic MPS vector. -/
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

/-- The parent Hamiltonian annihilates the periodic MPS vector:
\(H_N V^{(N)}(A) = 0\). -/
lemma parentHamiltonian_annihilates (A : MPSTensor d D) (L N : ℕ) (hLN : L ≤ N) :
    parentHamiltonian A L N (mpv A) = 0 := by
  simp only [parentHamiltonian, LinearMap.sum_apply]
  exact Finset.sum_eq_zero fun i _ => localTerm_annihilates_mpv A L N hLN i

/-- The parent Hamiltonian model is frustration-free on the periodic MPS vector:
each local term individually annihilates `mpv A`. -/
lemma parentHamiltonian_frustrationFree (A : MPSTensor d D) (L N : ℕ) (hLN : L ≤ N) :
    IsFrustrationFree A L N (mpv A) :=
  fun i => localTerm_annihilates_mpv A L N hLN i

end MPSTensor
