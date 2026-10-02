/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularBoundaryState
import TNLean.Algebra.FlatDensityEntropy
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.Algebra.Star.StarProjection

/-!
# Physical realization of a regular boundary state

For the invariant-boundary projector \(P\), the normalized virtual coefficient matrix is
\(C=P/\sqrt r\), where \(r=|G|^{b-1}\). Maps from the two virtual boundaries to the physical
systems are isometries on the invariant subspace when \(A^\dagger A=B^\dagger B=P\).
The physical coefficient matrix is \(ACB^{\mathsf T}\), and the reduced density operator
on the first physical system is \(APA^\dagger/r\). The operator \(APA^\dagger\) is again
an orthogonal projector of rank \(r\).

These are conditional statements about a specified realization of the finite boundary state.
They express the transport step in Schuch, Cirac, and Pérez-García, arXiv:1001.3807,
Theorem 6.9, proof (`Papers/1001.3807/paper_v3.tex`, lines 2043–2076). Identifying the
maps with contractions of a particular PEPS across a topologically trivial region is a
separate geometric statement.
-/

open scoped Matrix Kronecker ComplexOrder
open Matrix

namespace TNLean.PEPS

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The coefficient matrix after applying the two specified physical boundary maps. -/
noncomputable def physicalRegularBoundarySchmidtMatrix (n : ℕ)
    (A : Matrix α (Fin (n + 1) → G) ℂ) (B : Matrix β (Fin (n + 1) → G) ℂ) :
    Matrix α β ℂ :=
  A * regularBoundarySchmidtMatrix n * B.transpose

/-- The physical bipartite vector represented by the transported coefficient matrix. -/
noncomputable def physicalRegularBoundaryState (n : ℕ)
    (A : Matrix α (Fin (n + 1) → G) ℂ) (B : Matrix β (Fin (n + 1) → G) ℂ) :
    (α × β) → ℂ :=
  fun p => physicalRegularBoundarySchmidtMatrix n A B p.1 p.2

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
/-- The coefficient-matrix realization is exactly the action of the two physical maps
on the virtual bipartite vector. -/
theorem physicalRegularBoundaryState_eq_kronecker_mulVec (n : ℕ)
    (A : Matrix α (Fin (n + 1) → G) ℂ) (B : Matrix β (Fin (n + 1) → G) ℂ) :
    physicalRegularBoundaryState n A B = (A ⊗ₖ B) *ᵥ regularBoundaryState n := by
  change (A * regularBoundarySchmidtMatrix n * B.transpose).transpose.vec =
    (A ⊗ₖ B) *ᵥ (regularBoundarySchmidtMatrix n).transpose.vec
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  simpa only [Matrix.mul_assoc] using
    (Matrix.kronecker_mulVec_vec B (regularBoundarySchmidtMatrix n).transpose A).symm

/-- The image of the invariant-boundary projector under a specified physical boundary map. -/
noncomputable def physicalRegularBoundaryProjector (n : ℕ)
    (A : Matrix α (Fin (n + 1) → G) ℂ) : Matrix α α ℂ :=
  A * regularBoundaryProjector (n + 1) * A.conjTranspose

/-- The physical boundary density operator, before verifying normalization of the map. -/
noncomputable def physicalRegularBoundaryDensity (n : ℕ)
    (A : Matrix α (Fin (n + 1) → G) ℂ) : Matrix α α ℂ :=
  ((Fintype.card G : ℂ) ^ n)⁻¹ • physicalRegularBoundaryProjector n A

omit [Fintype α] [DecidableEq α] [DecidableEq β] in
/-- A boundary map isometric on the invariant subspace leaves the normalized virtual
reduced density unchanged on the traced side. Source: SCP10, proof of Theorem 6.9,
lines 2043–2076. Only the map on the traced side is needed for this identity. -/
theorem physicalRegularBoundarySchmidtMatrix_mul_conjTranspose (n : ℕ)
    (A : Matrix α (Fin (n + 1) → G) ℂ) (B : Matrix β (Fin (n + 1) → G) ℂ)
    (hB : B.conjTranspose * B = regularBoundaryProjector (n + 1)) :
    physicalRegularBoundarySchmidtMatrix n A B *
        (physicalRegularBoundarySchmidtMatrix n A B).conjTranspose =
      physicalRegularBoundaryDensity n A := by
  have hBt : B.transpose * B.transpose.conjTranspose = regularBoundaryProjector (n + 1) := by
    rw [conjTranspose_transpose_eq_transpose_conjTranspose, ← transpose_mul, hB,
      regularBoundaryProjector_transpose]
  calc
    _ = A * (regularBoundarySchmidtMatrix n * (B.transpose * B.transpose.conjTranspose)) *
        (regularBoundarySchmidtMatrix n).conjTranspose * A.conjTranspose := by
      simp only [physicalRegularBoundarySchmidtMatrix, conjTranspose_mul, Matrix.mul_assoc]
    _ = A * regularBoundarySchmidtMatrix n * (regularBoundarySchmidtMatrix n).conjTranspose *
        A.conjTranspose := by rw [hBt, regularBoundarySchmidtMatrix_mul_projector]
    _ = A * regularBoundaryDensity n * A.conjTranspose := by
      rw [Matrix.mul_assoc A, regularBoundarySchmidtMatrix_mul_conjTranspose]
    _ = physicalRegularBoundaryDensity n A := by
      simp only [regularBoundaryDensity, physicalRegularBoundaryDensity,
        physicalRegularBoundaryProjector, Matrix.mul_smul, Matrix.smul_mul]

omit [Fintype α] [DecidableEq α] [DecidableEq β] in
/-- The reduced physical state is the image of the normalized invariant-boundary projector.
Source: SCP10, proof of Theorem 6.9, lines 2043–2076, conditional on the specified cut maps. -/
theorem partialTrace_physicalRegularBoundaryState (n : ℕ)
    (A : Matrix α (Fin (n + 1) → G) ℂ) (B : Matrix β (Fin (n + 1) → G) ℂ)
    (hB : B.conjTranspose * B = regularBoundaryProjector (n + 1)) :
    partialTraceRight (vecMulVec (physicalRegularBoundaryState n A B)
        (star (physicalRegularBoundaryState n A B))) =
      physicalRegularBoundaryDensity n A := by
  rw [partialTraceRight_vecMulVec_eq]
  change physicalRegularBoundarySchmidtMatrix n A B *
    (physicalRegularBoundarySchmidtMatrix n A B).conjTranspose = _
  exact physicalRegularBoundarySchmidtMatrix_mul_conjTranspose n A B hB

omit [Fintype α] [DecidableEq α] in
/-- The transported invariant-boundary projector is Hermitian. -/
theorem physicalRegularBoundaryProjector_conjTranspose (n : ℕ)
    (A : Matrix α (Fin (n + 1) → G) ℂ) :
    (physicalRegularBoundaryProjector n A).conjTranspose =
      physicalRegularBoundaryProjector n A := by
  simp only [physicalRegularBoundaryProjector, conjTranspose_mul,
    conjTranspose_conjTranspose, regularBoundaryProjector_conjTranspose, Matrix.mul_assoc]

omit [DecidableEq α] in
/-- An isometry on the invariant boundary sends its projector to a physical projector. -/
theorem physicalRegularBoundaryProjector_mul_self (n : ℕ)
    (A : Matrix α (Fin (n + 1) → G) ℂ)
    (hA : A.conjTranspose * A = regularBoundaryProjector (n + 1)) :
    physicalRegularBoundaryProjector n A * physicalRegularBoundaryProjector n A =
      physicalRegularBoundaryProjector n A := by
  calc
    _ = A * (regularBoundaryProjector (n + 1) * (A.conjTranspose * A) *
        regularBoundaryProjector (n + 1)) * A.conjTranspose := by
      simp only [physicalRegularBoundaryProjector, Matrix.mul_assoc]
    _ = physicalRegularBoundaryProjector n A := by
      simp only [hA, regularBoundaryProjector_mul_self, physicalRegularBoundaryProjector]

omit [DecidableEq α] in
/-- The transported boundary support is an orthogonal projector in the matrix star algebra. -/
theorem physicalRegularBoundaryProjector_isStarProjection (n : ℕ)
    (A : Matrix α (Fin (n + 1) → G) ℂ)
    (hA : A.conjTranspose * A = regularBoundaryProjector (n + 1)) :
    IsStarProjection (physicalRegularBoundaryProjector n A) := by
  rw [isStarProjection_iff']
  exact ⟨physicalRegularBoundaryProjector_mul_self n A hA,
    by simpa only [Matrix.star_eq_conjTranspose] using
      physicalRegularBoundaryProjector_conjTranspose n A⟩

omit [DecidableEq α] in
/-- The physical boundary projector retains the virtual boundary rank
(|G|^n), for a cut with (n+1) regular bonds. -/
theorem rank_physicalRegularBoundaryProjector (n : ℕ)
    (A : Matrix α (Fin (n + 1) → G) ℂ)
    (hA : A.conjTranspose * A = regularBoundaryProjector (n + 1)) :
    (physicalRegularBoundaryProjector n A).rank = Fintype.card G ^ n := by
  have hrecover : A.conjTranspose * physicalRegularBoundaryProjector n A * A =
      regularBoundaryProjector (n + 1) := by
    calc
      _ = (A.conjTranspose * A) * regularBoundaryProjector (n + 1) *
          (A.conjTranspose * A) := by
        simp only [physicalRegularBoundaryProjector, Matrix.mul_assoc]
      _ = regularBoundaryProjector (n + 1) := by
        simp only [hA, regularBoundaryProjector_mul_self]
  have hrank : (physicalRegularBoundaryProjector n A).rank =
      (regularBoundaryProjector (G := G) (n + 1)).rank := by
    apply le_antisymm
    · exact (rank_mul_le_left (A * regularBoundaryProjector (n + 1)) A.conjTranspose).trans
        (rank_mul_le_right A (regularBoundaryProjector (n + 1)))
    · rw [← hrecover]
      exact (rank_mul_le_left (A.conjTranspose * physicalRegularBoundaryProjector n A) A).trans
        (rank_mul_le_right A.conjTranspose (physicalRegularBoundaryProjector n A))
  simpa using hrank.trans (rank_regularBoundaryProjector (G := G) (n + 1) (Nat.zero_lt_succ n))

omit [DecidableEq α] in
/-- The trace of the physical boundary projector is its virtual boundary dimension. -/
theorem trace_physicalRegularBoundaryProjector (n : ℕ)
    (A : Matrix α (Fin (n + 1) → G) ℂ)
    (hA : A.conjTranspose * A = regularBoundaryProjector (n + 1)) :
    (physicalRegularBoundaryProjector n A).trace = (Fintype.card G : ℂ) ^ n := by
  rw [physicalRegularBoundaryProjector, trace_mul_cycle, hA,
    regularBoundaryProjector_mul_self, trace_regularBoundaryProjector]

omit [Fintype α] [DecidableEq α] in
/-- The transported boundary density is positive semidefinite. -/
theorem physicalRegularBoundaryDensity_posSemidef (n : ℕ) [Finite α]
    (A : Matrix α (Fin (n + 1) → G) ℂ) : (physicalRegularBoundaryDensity n A).PosSemidef := by
  have h := PosSemidef.mul_mul_conjTranspose_same
    (posSemidef_self_mul_conjTranspose (regularBoundarySchmidtMatrix (G := G) n)) A
  simpa only [regularBoundarySchmidtMatrix_mul_conjTranspose, regularBoundaryDensity,
    physicalRegularBoundaryDensity, physicalRegularBoundaryProjector,
    Matrix.mul_smul, Matrix.smul_mul] using h

omit [DecidableEq α] in
/-- A map isometric on the invariant boundary gives a normalized physical density operator. -/
theorem trace_physicalRegularBoundaryDensity (n : ℕ)
    (A : Matrix α (Fin (n + 1) → G) ℂ)
    (hA : A.conjTranspose * A = regularBoundaryProjector (n + 1)) :
    (physicalRegularBoundaryDensity n A).trace = 1 := by
  rw [physicalRegularBoundaryDensity, trace_smul, trace_physicalRegularBoundaryProjector n A hA]
  exact inv_mul_cancel₀ (pow_ne_zero n (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))

omit [DecidableEq α] in
/-- The normalized physical boundary density retains the rank (|G|^n). -/
theorem rank_physicalRegularBoundaryDensity (n : ℕ)
    (A : Matrix α (Fin (n + 1) → G) ℂ)
    (hA : A.conjTranspose * A = regularBoundaryProjector (n + 1)) :
    (physicalRegularBoundaryDensity n A).rank = Fintype.card G ^ n := by
  rw [physicalRegularBoundaryDensity, rank_smul_of_mem_nonZeroDivisors _
    (mem_nonZeroDivisors_of_ne_zero (inv_ne_zero (pow_ne_zero n
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))))]
  exact rank_physicalRegularBoundaryProjector n A hA

omit [DecidableEq α] in
/-- The normalized physical boundary density is a scalar multiple of an orthogonal projector;
this identity expresses its flat nonzero spectrum. -/
theorem physicalRegularBoundaryDensity_mul_self (n : ℕ)
    (A : Matrix α (Fin (n + 1) → G) ℂ)
    (hA : A.conjTranspose * A = regularBoundaryProjector (n + 1)) :
    physicalRegularBoundaryDensity n A * physicalRegularBoundaryDensity n A =
      ((Fintype.card G : ℂ) ^ n)⁻¹ • physicalRegularBoundaryDensity n A := by
  simp only [physicalRegularBoundaryDensity, Matrix.smul_mul, Matrix.mul_smul,
    physicalRegularBoundaryProjector_mul_self n A hA, smul_smul]

/-- Every nonzero spectral value of the physical boundary density is (|G|^{-n}).
Together with the rank and normalization identities, this is the flat-spectrum conclusion
for the specified boundary realization in SCP10, Theorem 6.9. -/
theorem spectrum_physicalRegularBoundaryDensity_subset (n : ℕ)
    (A : Matrix α (Fin (n + 1) → G) ℂ)
    (hA : A.conjTranspose * A = regularBoundaryProjector (n + 1)) :
    spectrum ℂ (physicalRegularBoundaryDensity n A) ⊆
      {0, ((Fintype.card G : ℂ) ^ n)⁻¹} := by
  let c : ℂˣ := Units.mk0 ((Fintype.card G : ℂ) ^ n)⁻¹
    (inv_ne_zero (pow_ne_zero n (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)))
  change spectrum ℂ (c • physicalRegularBoundaryProjector n A) ⊆ {0, (c : ℂ)}
  rw [spectrum.unit_smul_eq_smul]
  rintro z ⟨w, hw, rfl⟩
  have hP : IsIdempotentElem (physicalRegularBoundaryProjector n A) :=
    physicalRegularBoundaryProjector_mul_self n A hA
  have hw01 := hP.spectrum_subset ℂ hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw01
  rcases hw01 with rfl | rfl <;> simp

/-- The physical realization of a cut with (n+1) regular bonds has entropy (nlog|G|).
This is the entropy transport step in SCP10, Theorem 6.9, conditional on the specified
boundary map being isometric on the invariant subspace. -/
theorem vonNeumannEntropy_physicalRegularBoundaryDensity (n : ℕ)
    (A : Matrix α (Fin (n + 1) → G) ℂ)
    (hA : A.conjTranspose * A = regularBoundaryProjector (n + 1)) :
    vonNeumannEntropy (physicalRegularBoundaryDensity n A)
        (physicalRegularBoundaryDensity_posSemidef n A).isHermitian =
      (n : ℝ) * Real.log (Fintype.card G : ℝ) := by
  have hflat : physicalRegularBoundaryDensity n A * physicalRegularBoundaryDensity n A =
      (((Fintype.card G : ℝ) ^ n : ℝ) : ℂ)⁻¹ • physicalRegularBoundaryDensity n A := by
    simpa only [Complex.ofReal_pow, Complex.ofReal_natCast] using
      physicalRegularBoundaryDensity_mul_self n A hA
  calc
    _ = Real.log ((Fintype.card G : ℝ) ^ n) :=
      vonNeumannEntropy_of_mul_self_eq_inv_smul (physicalRegularBoundaryDensity_posSemidef n A)
        (trace_physicalRegularBoundaryDensity n A hA) hflat
    _ = (n : ℝ) * Real.log (Fintype.card G : ℝ) := Real.log_pow _ _

end TNLean.PEPS
