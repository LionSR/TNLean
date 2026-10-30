/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.VaryingPhysicalKernelSupport
import TNLean.MPS.ParentHamiltonian.VaryingOBCParentUniqueness

/-!
# The common-alphabet specialization of the dependent parent

The dependent pair/outside coordinates and literal prefix/pair/suffix
coordinates describe the same fixed-outside sections. Their actual parent
Hamiltonians therefore have the same kernel on a common nonempty alphabet.
This comparison reuses the existing full-chain reconstruction rather than
repeating it for dependent physical spaces.

Source: PGVWC07, arXiv:quant-ph/0608197, equation unique-OBC,
source lines 1213–1220. Nonemptiness here is an auxiliary coordinate choice;
canonical normalization derives it in the final transport application.
-/

namespace Matrix

private def pairLeft (p q : ℕ) : Fin (p + 2 + q) :=
  Fin.castAdd q (Fin.natAdd p (0 : Fin 2))

private def pairRight (p q : ℕ) : Fin (p + 2 + q) :=
  Fin.castAdd q (Fin.natAdd p (1 : Fin 2))

private theorem pairRight_ne_left (p q : ℕ) : pairRight p q ≠ pairLeft p q :=
  fun h ↦ Nat.succ_ne_self p (congrArg Fin.val h)

private theorem append_pair_agree_outside {α : Type*} {p q : ℕ}
    (u : Fin p → α) (s t : Fin 2 → α) (v : Fin q → α)
    (k : Fin (p + 2 + q)) (h0 : k.val ≠ p) (h1 : k.val ≠ p + 1) :
    Fin.append (Fin.append u s) v k = Fin.append (Fin.append u t) v k := by
  revert h0 h1
  refine Fin.addCases (fun l ↦ ?_) (fun r ↦ ?_) k
  · intro h0 h1
    rw [Fin.append_left, Fin.append_left]
    revert h0 h1
    refine Fin.addCases (fun l ↦ ?_) (fun r ↦ ?_) l
    · intro _ _
      rw [Fin.append_left, Fin.append_left]
    · intro h0 h1
      change p + r.val ≠ p at h0
      change p + r.val ≠ p + 1 at h1
      have := r.isLt
      omega
  · intro _ _
    rw [Fin.append_right, Fin.append_right]

private theorem pair_coordinates_append {α : Type*} {p q : ℕ}
    (u : Fin p → α) (s t : Fin 2 → α) (v : Fin q → α) :
    pairConfigurationEquiv (fun _ : Fin (p + 2 + q) ↦ α)
        (pairLeft p q) (pairRight p q) (pairRight_ne_left p q)
        (Fin.append (Fin.append u s) v) =
      ((s 0, s 1),
        (pairConfigurationEquiv (fun _ : Fin (p + 2 + q) ↦ α)
          (pairLeft p q) (pairRight p q) (pairRight_ne_left p q)
          (Fin.append (Fin.append u t) v)).2) := by
  change ((Fin.append (Fin.append u s) v (pairLeft p q),
    Fin.append (Fin.append u s) v (pairRight p q)), _) = _
  apply Prod.ext
  · apply Prod.ext
    · exact (Fin.append_left _ _ _).trans (Fin.append_right _ _ _)
    · exact (Fin.append_left _ _ _).trans (Fin.append_right _ _ _)
  · funext k
    apply append_pair_agree_outside
    · intro h
      apply k.val.property
      exact Fin.ext h
    · intro h
      apply k.property
      apply Subtype.ext
      exact Fin.ext h

variable {d : ℕ} [Nonempty (Fin d)]

private theorem uniform_parent_list_sections_of_eq_zero
    (D : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (D k)) (Fin (D (k + 1))) ℂ) {N : ℕ}
    (ψ : EuclideanSpace ℂ (Fin N → Fin d)) (f : List (Fin d) → ℂ)
    (hf : ∀ w : Fin N → Fin d, f (List.ofFn w) = ψ w)
    (hzero : varyingPhysicalParentHamiltonian (fun _ : Fin N ↦ Fin d) D
      (fun k ↦ A k.val) ψ = 0) :
    ∀ u v : List (Fin d), u.length + 2 + v.length = N →
      ∃ X : Matrix (Fin (D (u.length + 2))) (Fin (D u.length)) ℂ,
        ∀ i j, f (u ++ i :: j :: v) = Matrix.trace (X * A u.length i * A (u.length + 1) j) := by
  classical
  intro u v hlength
  subst N
  let δ : Fin d := Classical.choice inferInstance
  let t : Fin 2 → Fin d := fun _ ↦ δ
  let Q := pairConfigurationEquiv (fun _ : Fin (u.length + 2 + v.length) ↦ Fin d)
    (pairLeft u.length v.length) (pairRight u.length v.length)
    (pairRight_ne_left u.length v.length)
  let w0 := Fin.append (Fin.append u.get t) v.get
  have hlocal := varyingPhysicalParentHamiltonian_pair_apply_eq_zero
    (fun _ : Fin (u.length + 2 + v.length) ↦ Fin d) D (fun k ↦ A k.val)
    ψ hzero u.length (by omega)
  obtain ⟨X, hX⟩ := physicalPairParentTerm_boundary_of_apply_eq_zero
    (fun _ : Fin (u.length + 2 + v.length) ↦ Fin d) _ _ _
    (A u.length) (A (u.length + 1)) ψ hlocal (Q w0).2
  refine ⟨X, fun i j ↦ ?_⟩
  let s : Fin 2 → Fin d := ![i, j]
  let w := Fin.append (Fin.append u.get s) v.get
  have hw : List.ofFn w = u ++ i :: j :: v := by
    simp only [w, List.ofFn_fin_append, List.ofFn_get]
    simp [s, List.ofFn_succ]
  have hcoord : w = Q.symm ((i, j), (Q w0).2) := by
    apply Q.injective
    rw [Q.apply_symm_apply]
    exact pair_coordinates_append u.get s t v.get
  rw [← hw, hf]
  exact (congrArg ψ hcoord).trans (hX i j)

private theorem uniform_pair_term_eq_zero_of_list_sections
    (D : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (D k)) (Fin (D (k + 1))) ℂ) {N : ℕ}
    (ψ : EuclideanSpace ℂ (Fin N → Fin d)) (f : List (Fin d) → ℂ)
    (hf : ∀ w : Fin N → Fin d, f (List.ofFn w) = ψ w)
    (p q : ℕ) (hlength : p + 2 + q = N)
    (hpair : ∀ u v : List (Fin d), u.length + 2 + v.length = N →
      ∃ X : Matrix (Fin (D (u.length + 2))) (Fin (D u.length)) ℂ,
        ∀ i j, f (u ++ i :: j :: v) = Matrix.trace (X * A u.length i * A (u.length + 1) j)) :
    physicalPairParentTerm (fun _ : Fin N ↦ Fin d) ⟨p, by omega⟩ ⟨p + 1, by omega⟩
      (fun h ↦ Nat.succ_ne_self p (congrArg Fin.val h)) (A p) (A (p + 1)) ψ = 0 := by
  classical
  subst N
  let Q := pairConfigurationEquiv (fun _ : Fin (p + 2 + q) ↦ Fin d)
    (pairLeft p q) (pairRight p q) (pairRight_ne_left p q)
  apply (physicalPairParentTerm_apply_eq_zero_iff_boundary _ _ _ _ _ _ ψ).mpr
  intro η
  let δ : Fin d := Classical.choice inferInstance
  let τ := Q.symm ((δ, δ), η)
  let pref : Fin (p + 2) → Fin d := fun k ↦ τ (Fin.castAdd q k)
  let u : Fin p → Fin d := fun k ↦ pref (Fin.castAdd 2 k)
  let t : Fin 2 → Fin d := fun k ↦ pref (Fin.natAdd p k)
  let v : Fin q → Fin d := fun k ↦ τ (Fin.natAdd (p + 2) k)
  have hprefix : Fin.append u t = pref := Fin.append_castAdd_natAdd
  have hτ : Fin.append (Fin.append u t) v = τ := by
    rw [hprefix]
    exact Fin.append_castAdd_natAdd
  have hη : (Q (Fin.append (Fin.append u t) v)).2 = η := by
    rw [hτ]
    change (Q (Q.symm ((δ, δ), η))).2 = η
    rw [Q.apply_symm_apply]
  have key : ∀ m : ℕ, m = (List.ofFn u).length →
      ∃ X : Matrix (Fin (D (m + 2))) (Fin (D m)) ℂ,
        ∀ i j, f (List.ofFn u ++ i :: j :: List.ofFn v) =
          Matrix.trace (X * A m i * A (m + 1) j) := by
    intro m hm
    subst hm
    exact hpair (List.ofFn u) (List.ofFn v) (by simp only [List.length_ofFn])
  obtain ⟨X, hX⟩ := key p List.length_ofFn.symm
  refine ⟨X, fun x y ↦ ?_⟩
  let s : Fin 2 → Fin d := ![x, y]
  let w := Fin.append (Fin.append u s) v
  have hw : w = Q.symm ((x, y), η) := by
    apply Q.injective
    rw [Q.apply_symm_apply]
    have hc := pair_coordinates_append u s t v
    rw [hη] at hc
    exact hc
  have hlist : List.ofFn w = List.ofFn u ++ x :: y :: List.ofFn v := by
    simp only [w, List.ofFn_fin_append]
    simp [s, List.ofFn_succ]
  change ψ (Q.symm ((x, y), η)) = _
  rw [← hw, ← hf, hlist]
  exact hX x y

/-- On a common nonempty physical alphabet, the actual dependent-coordinate
parent and the existing prefix/pair/suffix parent have precisely the same
kernel. This is a comparison of actual operators' kernel equations, not a
supplied representation condition.
Source: PGVWC07, equation unique-OBC, lines 1213–1220. -/
theorem varyingPhysicalParentHamiltonian_uniform_apply_eq_zero_iff
    (D : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (D k)) (Fin (D (k + 1))) ℂ)
    {N : ℕ} (ψ : EuclideanSpace ℂ (Fin N → Fin d)) :
    varyingPhysicalParentHamiltonian (fun _ : Fin N ↦ Fin d) D (fun k ↦ A k.val) ψ = 0 ↔
      obcParentHamiltonian D A N ψ = 0 := by
  classical
  let f : List (Fin d) → ℂ := Function.extend List.ofFn (fun w ↦ ψ w) 0
  have hf (w : Fin N → Fin d) : f (List.ofFn w) = ψ w :=
    List.ofFn_injective.extend_apply (fun w ↦ ψ w) 0 w
  constructor
  · intro hzero
    apply (obcParentHamiltonian_apply_eq_zero_iff_pair_sections D A ψ f hf).mpr
    exact uniform_parent_list_sections_of_eq_zero D A ψ f hf hzero
  · intro hzero
    have hpair := obcParentHamiltonian_pair_sections_of_apply_eq_zero D A ψ f hf hzero
    simp only [varyingPhysicalParentHamiltonian, LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro j _
    have hlength : j.val + 2 + (N - (j.val + 2)) = N := by
      have := j.isLt
      omega
    exact uniform_pair_term_eq_zero_of_list_sections D A ψ f hf
      j.val (N - (j.val + 2)) hlength hpair

end Matrix
