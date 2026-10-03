/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.CanonicalNormalization
import TNLean.MPS.FundamentalTheorem.Reduction.ProjectorWeightedSum
import TNLean.MPS.FundamentalTheorem.Reduction.StationarySplitting

/-!
# Similarity from a normalized split compression

For a multi-block compression with zero remainder, the sum of the matched
inclusions followed by projections acts identically after every source letter.
Trace-preserving normalization excludes a common kernel, so this sum is the
identity. The assembled compression maps are consequently inverse coordinate
changes, with no unmatched zero factors.

This is the final step of the normalized asymmetric theorem in
`Notes/OpenProblemsTN/followup/2026_10_02_finite_asymmetric_tests/
stationary_semisimplicity.tex`, Corollary 2. Normalization and zero remainder
are explicit additional hypotheses, rather than conclusions of the
unrestricted asymmetric compression theorem (P5, Theorem 7.7).
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Matrix

namespace MPSTensor.MultiBlockCompression

variable {d DB : ℕ} {ι : Type*} [DecidableEq ι] {D : ι → ℕ}
  {B : MPSTensor d DB} {S : Finset ι} {C : ∀ s, MPSTensor d (D s)}
  (P : MultiBlockCompression B S C)

/-- In a split compression of a trace-preserving source, the matched factors
exhaust the bond space. This is the zero-factor exclusion in
`stationary_semisimplicity.tex`, Corollary 2. -/
theorem sum_right_mul_left_eq_one_of_leftCanonical
    (hB : IsLeftCanonical B) (hP : P.remainder = 0) :
    ∑ s : {s // s ∈ S}, P.right s * P.left s = 1 := by
  classical
  let E := ∑ s : {s // s ∈ S}, P.right s * P.left s
  have hBE (i : Fin d) : B i * E = B i := by
    calc
      B i * E = ∑ s : {s // s ∈ S}, (B i * P.right s) * P.left s := by
        simp only [E, Matrix.mul_sum, Matrix.mul_assoc]
      _ = ∑ s : {s // s ∈ S}, P.right s * C s.1 i * P.left s := by
        simp only [P.mul_right_eq_right_mul hP]
      _ = B i := (P.eq_sum_right_mul_mul_left hP i).symm
  have hBZ (i : Fin d) : B i * (1 - E) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hBE, sub_self]
  have hZ : (1 - E)ᴴ * (1 - E) = 0 := by
    calc
      (1 - E)ᴴ * (1 - E) =
          (1 - E)ᴴ * (∑ i : Fin d, (B i)ᴴ * B i) * (1 - E) := by
        rw [hB, Matrix.mul_one]
      _ = ∑ i : Fin d, (B i * (1 - E))ᴴ * (B i * (1 - E)) := by
        simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul,
          Matrix.mul_assoc]
      _ = 0 := by simp only [hBZ, Matrix.conjTranspose_zero, Matrix.zero_mul,
        Finset.sum_const_zero]
  exact (sub_eq_zero.mp (Matrix.conjTranspose_mul_self_eq_zero.mp hZ)).symm

/-- The matched left compression maps, assembled on the direct-sum coordinates
of P5, Theorem 7.7(iv). -/
noncomputable def assembledLeft :
    Matrix (Σ s : {s // s ∈ S}, Fin (D s.1)) (Fin DB) ℂ :=
  fun x j => P.left x.1 x.2 j

/-- The matched right compression maps, assembled on the direct-sum coordinates
of P5, Theorem 7.7(iv). -/
noncomputable def assembledRight :
    Matrix (Fin DB) (Σ s : {s // s ∈ S}, Fin (D s.1)) ℂ :=
  fun j x => P.right x.1 j x.2

/-- The assembled maps are inverse on the matched space, by the
biorthogonality of P5, Theorem 7.7(iv). -/
theorem assembledLeft_mul_assembledRight : P.assembledLeft * P.assembledRight = 1 := by
  classical
  ext ⟨s, a⟩ ⟨t, b⟩
  change (P.left s * P.right t) a b = _
  by_cases h : s = t
  · subst t
    rw [P.left_mul_right_self]
    simp only [Matrix.one_apply, Sigma.mk.inj_iff, heq_eq_eq, true_and]
  · rw [P.left_mul_right_of_ne h]
    simp only [Matrix.zero_apply, Matrix.one_apply,
      Sigma.mk.inj_iff, h, false_and, ite_false]

/-- Trace-preserving normalization and zero remainder make the assembled
maps inverse also on the source space (`stationary_semisimplicity.tex`,
Corollary 2). -/
theorem assembledRight_mul_assembledLeft_of_leftCanonical
    (hB : IsLeftCanonical B) (hP : P.remainder = 0) :
    P.assembledRight * P.assembledLeft = 1 := by
  classical
  rw [← P.sum_right_mul_left_eq_one_of_leftCanonical hB hP]
  ext i j
  simp only [Matrix.mul_apply, assembledRight, assembledLeft, Fintype.sum_sigma,
    Matrix.sum_apply]

/-- In a split compression, assembling the left and right maps turns every
letter into the prescribed direct-sum tensor (`stationary_semisimplicity.tex`,
Corollary 2). -/
theorem assembledLeft_mul_letter_mul_assembledRight
    (hP : P.remainder = 0) (i : Fin d) :
    P.assembledLeft * B i * P.assembledRight =
      Matrix.blockDiagonal' (fun s : {s // s ∈ S} => C s.1 i) := by
  classical
  ext ⟨s, a⟩ ⟨t, b⟩
  change ((P.left s * B i) * P.right t) a b = _
  rw [P.left_mul_eq_mul_left hP i s, Matrix.mul_assoc]
  by_cases h : s = t
  · subst t
    rw [P.left_mul_right_self, Matrix.mul_one, Matrix.blockDiagonal'_apply_eq]
  · rw [P.left_mul_right_of_ne h, Matrix.mul_zero,
      Matrix.blockDiagonal'_apply_ne _ _ _ h]
    rfl

/-- The assembled maps give a linear equivalence for a trace-preserving split
compression (`stationary_semisimplicity.tex`, Corollary 2). -/
noncomputable def assembledLinearEquiv_of_leftCanonical
    (hB : IsLeftCanonical B) (hP : P.remainder = 0) :
    (Fin DB → ℂ) ≃ₗ[ℂ] ((Σ s : {s // s ∈ S}, Fin (D s.1)) → ℂ) :=
  LinearEquiv.ofLinearMap (Matrix.toLin' P.assembledLeft) (Matrix.toLin' P.assembledRight)
    (by rw [← Matrix.toLin'_mul, P.assembledLeft_mul_assembledRight, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul,
      P.assembledRight_mul_assembledLeft_of_leftCanonical hB hP, Matrix.toLin'_one])

/-- A trace-preserving split compression has exactly the total bond dimension
of its matched factors (`stationary_semisimplicity.tex`, Corollary 2). -/
theorem dim_eq_sum_of_leftCanonical
    (hB : IsLeftCanonical B) (hP : P.remainder = 0) : DB = ∑ s ∈ S, D s := by
  have h := (P.assembledLinearEquiv_of_leftCanonical hB hP).finrank_eq
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Fintype.card_sigma] at h
  rw [Finset.sum_coe_sort] at h
  exact h

/-- A trace-preserving split compression has no unmatched zero slots
(`stationary_semisimplicity.tex`, Corollary 2). -/
theorem z_eq_zero_of_leftCanonical
    (hB : IsLeftCanonical B) (hP : P.remainder = 0) : P.z = 0 := by
  have h := P.dim_eq
  have hsum := P.dim_eq_sum_of_leftCanonical hB hP
  omega

/-- The explicit inverse coordinate matrices simultaneously conjugate all
letters of a normalized split compression to the prescribed normal blocks.
This is the similarity conclusion of `stationary_semisimplicity.tex`,
Corollary 2; no normalization of the target blocks is required. -/
theorem exists_simultaneous_similarity_of_leftCanonical
    (hB : IsLeftCanonical B) (hP : P.remainder = 0) :
    ∃ (L : Matrix (Σ s : {s // s ∈ S}, Fin (D s.1)) (Fin DB) ℂ)
      (R : Matrix (Fin DB) (Σ s : {s // s ∈ S}, Fin (D s.1)) ℂ),
      L * R = 1 ∧ R * L = 1 ∧
        ∀ i : Fin d, L * B i * R =
          Matrix.blockDiagonal' (fun s : {s // s ∈ S} => C s.1 i) :=
  ⟨P.assembledLeft, P.assembledRight, P.assembledLeft_mul_assembledRight,
    P.assembledRight_mul_assembledLeft_of_leftCanonical hB hP,
    P.assembledLeft_mul_letter_mul_assembledRight hP⟩

end MPSTensor.MultiBlockCompression

namespace MPSTensor

variable {d DB : ℕ} {ι : Type*} [DecidableEq ι] {D : ι → ℕ}

/-- The normalized asymmetric similarity theorem, with its additional faithful
stationarity hypothesis explicit (`stationary_semisimplicity.tex`, Corollary 2).
Positive-word character equality identifies the factors by P5, Theorem 7.7;
faithful stationarity splits the extensions, and normalization excludes zero
factors. -/
theorem exists_simultaneous_similarity_of_leftCanonical_of_posDef_fixedPoint
    (S : Finset ι) (C : ∀ s, MPSTensor d (D s))
    (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
    (B : MPSTensor d DB)
    (htr : ∀ w : List (Fin d), w ≠ [] →
      Matrix.trace (Kraus.evalWord B w) = ∑ s ∈ S, Matrix.trace (Kraus.evalWord (C s) w))
    (hB : IsLeftCanonical B) {ρ : Matrix (Fin DB) (Fin DB) ℂ} (hρ : ρ.PosDef)
    (hFix : Kraus.map B ρ = ρ) :
    DB = ∑ s ∈ S, D s ∧
      ∃ (L : Matrix (Σ s : {s // s ∈ S}, Fin (D s.1)) (Fin DB) ℂ)
        (R : Matrix (Fin DB) (Σ s : {s // s ∈ S}, Fin (D s.1)) ℂ),
        L * R = 1 ∧ R * L = 1 ∧
          ∀ i : Fin d, L * B i * R =
            Matrix.blockDiagonal' (fun s : {s // s ∈ S} => C s.1 i) := by
  obtain ⟨P, hP⟩ :=
    exists_multiBlockCompression_remainder_eq_zero_of_leftCanonical_of_posDef_fixedPoint
      S C hC hD B htr hB hρ hFix
  exact ⟨P.dim_eq_sum_of_leftCanonical hB hP,
    P.exists_simultaneous_similarity_of_leftCanonical hB hP⟩

end MPSTensor
