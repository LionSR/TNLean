/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.OpenBoundary.VaryingPhysicalParentHamiltonian
import QICLean.Spectral.Gap.WeightedPositiveKernel
import TNLean.MPS.ParentHamiltonian.OpenBoundary.VaryingOBCParentUniqueness

/-!
# Physical support forced by the actual open parent kernel

After physical extension by zero, each actual pair boundary range is supported
on the original two physical alphabets. Positivity derives the local equations
from the actual open Hamiltonian. Every site of a chain of length at least two
belongs to an adjacent pair, so every coefficient outside the original full
physical configuration image vanishes. The vector is therefore the extension
of its actual coefficient pullback, rather than an assumed embedded state.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 9 and equation unique-OBC,
source lines 1195–1220.

It also contains the following results.

* `Matrix.varyingPhysicalParentHamiltonian_uniform_apply_eq_zero_iff`: the common-alphabet
  specialization of the dependent parent.
-/

namespace Matrix

section VaryingPhysicalKernelSupport

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

/-- Each actual fixed-outside pair section has a rectangular trace boundary
when the actual extended local parent term vanishes.
Source: PGVWC07, equation unique-OBC, lines 1213–1220. -/
theorem physicalPairParentTerm_boundary_of_apply_eq_zero
    (β : ι → Type*) [∀ k, Fintype (β k)] (i j : ι) (hji : j ≠ i)
    (A : β i → Matrix a b ℂ) (B : β j → Matrix b c ℂ)
    (ψ : EuclideanSpace ℂ ((k : ι) → β k))
    (hzero : physicalPairParentTerm β i j hji A B ψ = 0)
    (η : (k : {k : {k : ι // k ≠ i} // k ≠ ⟨j, hji⟩}) → β k.val.val) :
    ∃ X : Matrix c a ℂ, ∀ x y,
      ψ ((pairConfigurationEquiv β i j hji).symm ((x, y), η)) =
        Matrix.trace (X * A x * B y) := by
  let U := pairConfigurationReindex β i j hji
  let G := LinearMap.range (rectangularPairBoundary A B)
  have hprod : ContinuousLinearMap.rightFiberwiseMap Gᗮ.starProjection (U ψ) = 0 := by
    rw [← physicalPairParentTerm_in_coordinates, hzero, map_zero]
  have hfiber := (ContinuousLinearMap.mem_ker_rightFiberwiseMap_iff
    Gᗮ.starProjection (U ψ)).mp hprod η
  have hmem : ContinuousLinearMap.rightFiber (U ψ) η ∈ G := by
    have horth := (Submodule.starProjection_apply_eq_zero_iff _).mp hfiber
    simpa only [Submodule.orthogonal_orthogonal] using horth
  obtain ⟨X, hX⟩ := LinearMap.mem_range.mp hmem
  refine ⟨X, fun x y ↦ ?_⟩
  have hc := congrArg (fun v ↦ v (x, y)) hX
  change Matrix.trace (X * (A x * B y)) =
    ψ ((pairConfigurationEquiv β i j hji).symm ((x, y), η)) at hc
  rw [← Matrix.mul_assoc] at hc
  exact hc.symm

/-- The actual local equation is equivalent to rectangular boundary
representations on every outside section. Source: PGVWC07,
equation unique-OBC, lines 1213–1220. -/
theorem physicalPairParentTerm_apply_eq_zero_iff_boundary
    (β : ι → Type*) [∀ k, Fintype (β k)] (i j : ι) (hji : j ≠ i)
    (A : β i → Matrix a b ℂ) (B : β j → Matrix b c ℂ)
    (ψ : EuclideanSpace ℂ ((k : ι) → β k)) :
    physicalPairParentTerm β i j hji A B ψ = 0 ↔
      ∀ η : (k : {k : {k : ι // k ≠ i} // k ≠ ⟨j, hji⟩}) → β k.val.val,
        ∃ X : Matrix c a ℂ, ∀ x y,
          ψ ((pairConfigurationEquiv β i j hji).symm ((x, y), η)) =
            Matrix.trace (X * A x * B y) := by
  constructor
  · exact physicalPairParentTerm_boundary_of_apply_eq_zero β i j hji A B ψ
  · intro hboundary
    let U := pairConfigurationReindex β i j hji
    let G := LinearMap.range (rectangularPairBoundary A B)
    apply U.injective
    rw [map_zero, physicalPairParentTerm_in_coordinates]
    apply (ContinuousLinearMap.mem_ker_rightFiberwiseMap_iff Gᗮ.starProjection (U ψ)).mpr
    intro η
    obtain ⟨X, hX⟩ := hboundary η
    have hmem : ContinuousLinearMap.rightFiber (U ψ) η ∈ G := by
      refine ⟨X, ?_⟩
      apply PiLp.ext
      rintro ⟨x, y⟩
      change Matrix.trace (X * (A x * B y)) =
        ψ ((pairConfigurationEquiv β i j hji).symm ((x, y), η))
      rw [← Matrix.mul_assoc]
      exact (hX x y).symm
    apply (Submodule.starProjection_apply_eq_zero_iff _).mpr
    simpa only [Submodule.orthogonal_orthogonal] using hmem

/-- An actual embedded pair term kills no coefficient at an added physical
letter: any vector in its kernel must vanish there.
Source: PGVWC07, actual pair range in Theorem 9, lines 1201–1220. -/
theorem physicalPairParentTerm_coeff_eq_zero_of_not_mem_range
    (β γ : ι → Type*) [∀ k, Fintype (γ k)]
    (e : ∀ k, β k ↪ γ k) (i j : ι) (hji : j ≠ i)
    (A : β i → Matrix a b ℂ) (B : β j → Matrix b c ℂ)
    (ψ : EuclideanSpace ℂ ((k : ι) → γ k))
    (hzero : physicalPairParentTerm γ i j hji (Function.extend (e i) A 0)
      (Function.extend (e j) B 0) ψ = 0)
    (σ : (k : ι) → γ k)
    (hσ : σ i ∉ Set.range (e i) ∨ σ j ∉ Set.range (e j)) : ψ σ = 0 := by
  classical
  let Q := pairConfigurationEquiv γ i j hji
  obtain ⟨X, hX⟩ := physicalPairParentTerm_boundary_of_apply_eq_zero γ i j hji
    (Function.extend (e i) A 0) (Function.extend (e j) B 0) ψ hzero (Q σ).2
  have hc := hX (σ i) (σ j)
  change ψ (Q.symm (Q σ)) = Matrix.trace
    (X * Function.extend (e i) A 0 (σ i) * Function.extend (e j) B 0 (σ j)) at hc
  rw [Q.symm_apply_apply] at hc
  rcases hσ with hi | hj
  · rw [Function.extend_apply' (f := ⇑(e i)) A 0 (σ i) hi, Pi.zero_apply, Matrix.mul_zero,
      Matrix.zero_mul, Matrix.trace_zero] at hc
    exact hc
  · rw [Function.extend_apply' (f := ⇑(e j)) B 0 (σ j) hj, Pi.zero_apply, Matrix.mul_zero,
      Matrix.trace_zero] at hc
    exact hc

/-- Positivity derives every actual adjacent local equation from the full
Hamiltonian equation. Source: PGVWC07, Theorem 9 proof, lines 1213–1217. -/
theorem varyingPhysicalParentHamiltonian_apply_eq_zero_iff_terms {n : ℕ}
    (β : Fin (n + 2) → Type*) [∀ k, Fintype (β k)] (D : ℕ → ℕ)
    (A : ∀ k : Fin (n + 2), β k → Matrix (Fin (D k.val)) (Fin (D (k.val + 1))) ℂ)
    (ψ : EuclideanSpace ℂ ((k : Fin (n + 2)) → β k)) :
    varyingPhysicalParentHamiltonian β D A ψ = 0 ↔
      ∀ j : Fin (n + 1), physicalPairParentTerm β j.castSucc j.succ
        (ne_of_gt j.castSucc_lt_succ) (A j.castSucc) (A j.succ) ψ = 0 := by
  change (∑ j : Fin (n + 1), physicalPairParentTerm β j.castSucc j.succ
    (ne_of_gt j.castSucc_lt_succ) (A j.castSucc) (A j.succ)) ψ = 0 ↔ _
  exact WeightedPositiveKernel.apply_sum_eq_zero_iff
    (fun j ↦ physicalPairParentTerm_isPositive β _ _ _ _ _) ψ

/-- Every nonwrapping adjacent pair satisfies its actual local equation when
the full parent Hamiltonian vanishes. Source: PGVWC07, Theorem 9 proof,
lines 1213–1217. -/
theorem varyingPhysicalParentHamiltonian_pair_apply_eq_zero {N : ℕ}
    (β : Fin N → Type*) [∀ k, Fintype (β k)] (D : ℕ → ℕ)
    (A : ∀ k : Fin N, β k → Matrix (Fin (D k.val)) (Fin (D (k.val + 1))) ℂ)
    (ψ : EuclideanSpace ℂ ((k : Fin N) → β k))
    (hzero : varyingPhysicalParentHamiltonian β D A ψ = 0)
    (p : ℕ) (hp : p + 1 < N) :
    physicalPairParentTerm β ⟨p, by omega⟩ ⟨p + 1, hp⟩
      (fun h ↦ Nat.succ_ne_self p (congrArg Fin.val h))
      (A ⟨p, by omega⟩) (A ⟨p + 1, hp⟩) ψ = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  exact (varyingPhysicalParentHamiltonian_apply_eq_zero_iff_terms β D A ψ).mp hzero
    ⟨p, by omega⟩

/-- Added physical letters have zero coefficients in the actual extended open
parent kernel. Adjacent local equations are derived from the Hamiltonian, and
every site is covered when the chain has at least two sites.
Source: PGVWC07, Theorem 9 and equation unique-OBC, lines 1195–1220. -/
theorem varyingPhysicalParentHamiltonian_coeff_eq_zero_of_not_mem_range {N : ℕ}
    (hN : 2 ≤ N) (β γ : Fin N → Type*) [∀ k, Fintype (γ k)]
    (e : ∀ k, β k ↪ γ k) (D : ℕ → ℕ)
    (A : ∀ k : Fin N, β k → Matrix (Fin (D k.val)) (Fin (D (k.val + 1))) ℂ)
    (ψ : EuclideanSpace ℂ ((k : Fin N) → γ k))
    (hzero : varyingPhysicalParentHamiltonian γ D
      (fun k ↦ Function.extend (e k) (A k) 0) ψ = 0)
    (σ : (k : Fin N) → γ k) (k : Fin N) (hk : σ k ∉ Set.range (e k)) : ψ σ = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  have hterms := (varyingPhysicalParentHamiltonian_apply_eq_zero_iff_terms γ D _ ψ).mp hzero
  by_cases hleft : k.val < n + 1
  · let j : Fin (n + 1) := ⟨k.val, hleft⟩
    have hkleft : j.castSucc = k := Fin.ext rfl
    exact physicalPairParentTerm_coeff_eq_zero_of_not_mem_range β γ e _ _ _ _ _ ψ
      (hterms j) σ (Or.inl (by rw [hkleft]; exact hk))
  · have hkright : (Fin.last n).succ = k := by
      apply Fin.ext
      have := k.isLt
      simp only [Fin.val_succ, Fin.val_last]
      omega
    exact physicalPairParentTerm_coeff_eq_zero_of_not_mem_range β γ e _ _ _ _ _ ψ
      (hterms (Fin.last n)) σ (Or.inr (by rw [hkright]; exact hk))

/-- Every actual kernel vector after physical extension is exactly the
extension of its literal coefficient pullback. Embedded-state membership is
derived, not supplied. Source: PGVWC07, Theorem 9, lines 1195–1220. -/
theorem varyingPhysicalParentHamiltonian_eq_extendByZero_pullback_of_eq_zero {N : ℕ}
    (hN : 2 ≤ N) (β γ : Fin N → Type*)
    [∀ k, Fintype (β k)] [∀ k, Fintype (γ k)]
    (e : ∀ k, β k ↪ γ k) (D : ℕ → ℕ)
    (A : ∀ k : Fin N, β k → Matrix (Fin (D k.val)) (Fin (D (k.val + 1))) ℂ)
    (ψ : EuclideanSpace ℂ ((k : Fin N) → γ k))
    (hzero : varyingPhysicalParentHamiltonian γ D
      (fun k ↦ Function.extend (e k) (A k) 0) ψ = 0) :
    ψ = (Function.Embedding.piCongrRight e).euclideanExtendByZero
      (WithLp.toLp 2 fun σ ↦ ψ (Function.Embedding.piCongrRight e σ)) := by
  classical
  let E := Function.Embedding.piCongrRight e
  apply PiLp.ext
  intro σ
  by_cases hσ : σ ∈ Set.range E
  · obtain ⟨τ, rfl⟩ := hσ
    exact (E.euclideanExtendByZero_apply_image (WithLp.toLp 2 fun σ ↦ ψ (E σ)) τ).symm
  · rw [E.euclideanExtendByZero_apply_not_mem_range _ _ hσ]
    have hinvalid : ∃ k, σ k ∉ Set.range (e k) := by
      by_contra hnone
      have hvalid : ∀ k, ∃ x, e k x = σ k := by
        intro k
        by_contra hk
        exact hnone ⟨k, hk⟩
      choose τ hτ using hvalid
      exact hσ ⟨τ, funext hτ⟩
    obtain ⟨k, hk⟩ := hinvalid
    exact varyingPhysicalParentHamiltonian_coeff_eq_zero_of_not_mem_range
      hN β γ e D A ψ hzero σ k hk

end VaryingPhysicalKernelSupport

section UniformPhysicalParentComparison

/-!
## The common-alphabet specialization of the dependent parent

The dependent pair/outside coordinates and literal prefix/pair/suffix
coordinates describe the same fixed-outside sections. Their actual parent
Hamiltonians therefore have the same kernel on a common nonempty alphabet.
This comparison reuses the existing full-chain reconstruction rather than
repeating it for dependent physical spaces.

Source: PGVWC07, arXiv:quant-ph/0608197, equation unique-OBC,
source lines 1213–1220. Nonemptiness here is an auxiliary coordinate choice;
canonical normalization derives it in the final transport application.
-/

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

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

private theorem uniform_parent_list_sections_of_eq_zero
    (D : ℕ → ℕ)
    (A : ∀ k, α → Matrix (Fin (D k)) (Fin (D (k + 1))) ℂ) {N : ℕ}
    (ψ : EuclideanSpace ℂ (Fin N → α)) (f : List α → ℂ)
    (hf : ∀ w : Fin N → α, f (List.ofFn w) = ψ w)
    (hzero : varyingPhysicalParentHamiltonian (fun _ : Fin N ↦ α) D
      (fun k ↦ A k.val) ψ = 0) :
    ∀ u v : List α, u.length + 2 + v.length = N →
      ∃ X : Matrix (Fin (D (u.length + 2))) (Fin (D u.length)) ℂ,
        ∀ i j, f (u ++ i :: j :: v) = Matrix.trace (X * A u.length i * A (u.length + 1) j) := by
  classical
  intro u v hlength
  subst N
  let δ : α := Classical.choice inferInstance
  let t : Fin 2 → α := fun _ ↦ δ
  let Q := pairConfigurationEquiv (fun _ : Fin (u.length + 2 + v.length) ↦ α)
    (pairLeft u.length v.length) (pairRight u.length v.length)
    (pairRight_ne_left u.length v.length)
  let w0 := Fin.append (Fin.append u.get t) v.get
  have hlocal := varyingPhysicalParentHamiltonian_pair_apply_eq_zero
    (fun _ : Fin (u.length + 2 + v.length) ↦ α) D (fun k ↦ A k.val)
    ψ hzero u.length (by omega)
  obtain ⟨X, hX⟩ := physicalPairParentTerm_boundary_of_apply_eq_zero
    (fun _ : Fin (u.length + 2 + v.length) ↦ α) _ _ _
    (A u.length) (A (u.length + 1)) ψ hlocal (Q w0).2
  refine ⟨X, fun i j ↦ ?_⟩
  let s : Fin 2 → α := ![i, j]
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
    (A : ∀ k, α → Matrix (Fin (D k)) (Fin (D (k + 1))) ℂ) {N : ℕ}
    (ψ : EuclideanSpace ℂ (Fin N → α)) (f : List α → ℂ)
    (hf : ∀ w : Fin N → α, f (List.ofFn w) = ψ w)
    (p q : ℕ) (hlength : p + 2 + q = N)
    (hpair : ∀ u v : List α, u.length + 2 + v.length = N →
      ∃ X : Matrix (Fin (D (u.length + 2))) (Fin (D u.length)) ℂ,
        ∀ i j, f (u ++ i :: j :: v) = Matrix.trace (X * A u.length i * A (u.length + 1) j)) :
    physicalPairParentTerm (fun _ : Fin N ↦ α) ⟨p, by omega⟩ ⟨p + 1, by omega⟩
      (fun h ↦ Nat.succ_ne_self p (congrArg Fin.val h)) (A p) (A (p + 1)) ψ = 0 := by
  classical
  subst N
  let Q := pairConfigurationEquiv (fun _ : Fin (p + 2 + q) ↦ α)
    (pairLeft p q) (pairRight p q) (pairRight_ne_left p q)
  apply (physicalPairParentTerm_apply_eq_zero_iff_boundary _ _ _ _ _ _ ψ).mpr
  intro η
  let δ : α := Classical.choice inferInstance
  let τ := Q.symm ((δ, δ), η)
  let pref : Fin (p + 2) → α := fun k ↦ τ (Fin.castAdd q k)
  let u : Fin p → α := fun k ↦ pref (Fin.castAdd 2 k)
  let t : Fin 2 → α := fun k ↦ pref (Fin.natAdd p k)
  let v : Fin q → α := fun k ↦ τ (Fin.natAdd (p + 2) k)
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
  let s : Fin 2 → α := ![x, y]
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
    (A : ∀ k, α → Matrix (Fin (D k)) (Fin (D (k + 1))) ℂ)
    {N : ℕ} (ψ : EuclideanSpace ℂ (Fin N → α)) :
    varyingPhysicalParentHamiltonian (fun _ : Fin N ↦ α) D (fun k ↦ A k.val) ψ = 0 ↔
      Matrix.toEuclideanLin (obcParentInteraction D A N).hamiltonian ψ = 0 := by
  classical
  let f : List α → ℂ := Function.extend List.ofFn (fun w ↦ ψ w) 0
  have hf (w : Fin N → α) : f (List.ofFn w) = ψ w :=
    List.ofFn_injective.extend_apply (fun w ↦ ψ w) 0 w
  constructor
  · intro hzero
    apply (hamiltonian_obcParentInteraction_apply_eq_zero_iff_pair_sections D A ψ f hf).mpr
    exact uniform_parent_list_sections_of_eq_zero D A ψ f hf hzero
  · intro hzero
    have hpair := pair_sections_of_hamiltonian_obcParentInteraction_apply_eq_zero D A ψ f hf hzero
    simp only [varyingPhysicalParentHamiltonian, LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro j _
    have hlength : j.val + 2 + (N - (j.val + 2)) = N := by
      have := j.isLt
      omega
    exact uniform_pair_term_eq_zero_of_list_sections D A ψ f hf
      j.val (N - (j.val + 2)) hlength hpair

end UniformPhysicalParentComparison

end Matrix
