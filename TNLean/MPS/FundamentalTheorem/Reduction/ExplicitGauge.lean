/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Algebra.ComplexOfInt
import TNLean.MPS.FundamentalTheorem.Reduction.RingEmbedding
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlock

/-!
# Explicit gauges for multi-block compression data

**Source.** None: this is infrastructure of this development for the worked examples of the
multi-block asymmetric compression theorem, and no paper states it.

**Formalized here.** The multi-block asymmetric compression data of
`MPSTensor.MultiBlockCompression` carries its change of bond coordinates as a linear
equivalence onto a graded coordinate space. For a worked example the change of coordinates is
a concrete invertible matrix together with a concrete labelling of the coordinates by blocks.
This file packages that presentation: a bijection of the graded coordinate space with the bond
index set, and a pair of mutually inverse square matrices, assemble into a gauge whose
conjugation is the matrix conjugation followed by the relabelling.

The worked examples have entries in a ring `R` with decidable equality embedded in the complex
numbers (`ℤ`, `ℤ√2`, `ℤ[σ]`, `ℤ[ω]`). Entrywise transport along the embedding reduces the
three clauses of the compression data to decidable identities over `R`; the constructor
`MPSTensor.MultiBlockCompression.ofRing` assembles the datum from them once for every example.

## Main definitions

* `MPSTensor.mulIntTensor`: the bond-space product of two integer matrix product operator
  tensors.
* `MPSTensor.gaugeOfMatrix`, `MPSTensor.gaugeOfRingMatrix`: the gauge attached to a bijective
  labelling and an invertible complex matrix, or an invertible matrix over `R`.
* `MPSTensor.MultiBlockCompression.ofRing`: the compression datum from decided entrywise
  clauses over `R`; `MPSTensor.MultiBlockCompression.ofRingBlockDiagonal` from one
  block-diagonal letter identity over `R`.
* `MPSTensor.oneSlot`, `MPSTensor.unitOrd`, `MPSTensor.unitCoord`: the slot set, block ordering
  and bond coordinates of a compression with one target.

## Main results

* `MPSTensor.conjMatrix_gaugeOfMatrix`, `MPSTensor.conjMatrix_gaugeOfRingMatrix`: conjugation by
  such a gauge is matrix conjugation followed by the relabelling.
* `MPSTensor.MultiBlockCompression.left_gaugeOfMatrix`,
  `MPSTensor.MultiBlockCompression.right_gaugeOfMatrix`: the compression pair of a slot reads
  off the rows of the matrix and the columns of its inverse at the coordinates of that slot.
* `MPSTensor.MultiBlockCompression.remainder_eq_zero_of_offDiag`,
  `MPSTensor.MultiBlockCompression.remainder_ofRing`,
  `MPSTensor.MultiBlockCompression.remainder_ofRingBlockDiagonal`: the remainder vanishes when
  the letters are block diagonal in the block coordinates.
* `MPSTensor.MultiBlockCompression.remainder_oneSlot`: the remainder of a datum with one target
  slot.

## Provenance

The compression theorem these gauges instantiate is Theorem 7.7
(`thm:p5-asymmetric-compression`) of
`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, lines 495–569.
-/

open scoped Matrix Kronecker

namespace MPSTensor

/-! ### The bond-space product of integer tensors -/

variable {d D₁ D₂ : ℕ}

/-- The bond-space product of two integer tensors,
`(M · N)^{ik} = ∑_j M^{ij} ⊗ N^{jk}`, in the bond order of `finProdFinEquiv`. -/
abbrev mulIntTensor (M : Fin d → Fin d → Matrix (Fin D₁) (Fin D₁) ℤ)
    (N : Fin d → Fin d → Matrix (Fin D₂) (Fin D₂) ℤ) (i k : Fin d) :
    Matrix (Fin (D₁ * D₂)) (Fin (D₁ * D₂)) ℤ :=
  mulTensorR M N i k

/-! ### The gauge attached to an invertible matrix -/

variable {d DB : ℕ} {ι : Type*} [DecidableEq ι] {D : ι → ℕ} {S : Finset ι} {z : ℕ}

variable (τ : BlockSpace D S z ≃ Fin DB) (G Ginv : Matrix (Fin DB) (Fin DB) ℂ)

/-- The change of bond coordinates given by an invertible matrix `G` with inverse `Ginv`,
followed by the labelling of the bond coordinates by the graded coordinate space along the
bijection `τ`. -/
noncomputable def gaugeOfMatrix (hG : G * Ginv = 1) (hG' : Ginv * G = 1) :
    (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D S z → ℂ) where
  toFun v b := (G *ᵥ v) (τ b)
  map_add' u v := by funext b; simp [Matrix.mulVec_add]
  map_smul' c v := by funext b; simp [Matrix.mulVec_smul]
  invFun u := Ginv *ᵥ fun x => u (τ.symm x)
  left_inv v := by
    have hcomp : (fun x => (G *ᵥ v) (τ (τ.symm x))) = G *ᵥ v := by
      funext x
      exact congrArg (G *ᵥ v) (τ.apply_symm_apply x)
    simp only [hcomp, Matrix.mulVec_mulVec, hG', Matrix.one_mulVec]
  right_inv u := by
    funext b
    change (G *ᵥ (Ginv *ᵥ fun x => u (τ.symm x))) (τ b) = u b
    rw [Matrix.mulVec_mulVec, hG, Matrix.one_mulVec]
    exact congrArg u (τ.symm_apply_apply b)

variable (hG : G * Ginv = 1) (hG' : Ginv * G = 1)

omit [DecidableEq ι] in
theorem gaugeMatrix_gaugeOfMatrix :
    gaugeMatrix (gaugeOfMatrix τ G Ginv hG hG') = G.submatrix τ id := by
  ext b x
  simp [gaugeMatrix, LinearMap.toMatrix'_apply, gaugeOfMatrix, Matrix.mulVec_single]

theorem gaugeMatrixInv_gaugeOfMatrix :
    gaugeMatrixInv (gaugeOfMatrix τ G Ginv hG hG') = Ginv.submatrix id τ := by
  ext x b
  have hsingle : (fun y => (Pi.single b (1 : ℂ) : BlockSpace D S z → ℂ) (τ.symm y)) =
      Pi.single (τ b) (1 : ℂ) := by
    funext y
    simp only [Pi.single_apply, Equiv.symm_apply_eq]
  simp [gaugeMatrixInv, LinearMap.toMatrix'_apply, gaugeOfMatrix, hsingle,
    Matrix.mulVec_single]

/-- Conjugation by an explicit gauge is matrix conjugation followed by the relabelling. -/
theorem conjMatrix_gaugeOfMatrix (A : Matrix (Fin DB) (Fin DB) ℂ) :
    conjMatrix (gaugeOfMatrix τ G Ginv hG hG') A = (G * A * Ginv).submatrix τ τ := by
  rw [conjMatrix_eq_gaugeMatrix_mul, gaugeMatrix_gaugeOfMatrix, gaugeMatrixInv_gaugeOfMatrix]
  ext x y
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id_eq, Finset.mul_sum, Finset.sum_mul,
    mul_assoc]
  exact Finset.sum_comm

namespace MultiBlockCompression

variable {B : MPSTensor d DB} {C : ∀ s, MPSTensor d (D s)}

/-- The compression out of the bond space onto a slot reads off the rows of the gauge matrix at
the coordinates of that slot. -/
theorem left_gaugeOfMatrix (P : MultiBlockCompression B S C)
    {τ : BlockSpace D S P.z ≃ Fin DB} {G Ginv : Matrix (Fin DB) (Fin DB) ℂ}
    {hG : G * Ginv = 1} {hG' : Ginv * G = 1}
    (hgauge : P.gauge = gaugeOfMatrix τ G Ginv hG hG') (s : {s // s ∈ S}) :
    P.left s = G.submatrix (fun i => τ ⟨Sum.inl s, i⟩) id := by
  ext i y
  rw [left, hgauge, gaugeMatrix_gaugeOfMatrix, Matrix.mul_apply,
    Finset.sum_eq_single (⟨Sum.inl s, i⟩ : BlockSpace D S P.z)]
  · simp [Matrix.blockProj, Matrix.blockEmbed]
  · intro x _ hx
    rw [Matrix.blockProj, Matrix.transpose_apply, Matrix.blockEmbed_apply_of_ne hx, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ (⟨Sum.inl s, i⟩ : BlockSpace D S P.z)) h

/-- The compression into the bond space from a slot reads off the columns of the inverse gauge
matrix at the coordinates of that slot. -/
theorem right_gaugeOfMatrix (P : MultiBlockCompression B S C)
    {τ : BlockSpace D S P.z ≃ Fin DB} {G Ginv : Matrix (Fin DB) (Fin DB) ℂ}
    {hG : G * Ginv = 1} {hG' : Ginv * G = 1}
    (hgauge : P.gauge = gaugeOfMatrix τ G Ginv hG hG') (s : {s // s ∈ S}) :
    P.right s = Ginv.submatrix id fun j => τ ⟨Sum.inl s, j⟩ := by
  ext x j
  rw [right, hgauge, gaugeMatrixInv_gaugeOfMatrix, Matrix.mul_apply,
    Finset.sum_eq_single (⟨Sum.inl s, j⟩ : BlockSpace D S P.z)]
  · simp [Matrix.blockEmbed]
  · intro y _ hy
    rw [Matrix.blockEmbed_apply_of_ne hy, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ (⟨Sum.inl s, j⟩ : BlockSpace D S P.z)) h

omit [DecidableEq ι] in
/-- A relation between block coordinates that holds off the diagonal blocks holds strictly below
them, for every ordering of the blocks. -/
theorem triangular_of_offDiag {n : ℕ} {ord : BlockIndex S z ≃ Fin n}
    {P : BlockSpace D S z → BlockSpace D S z → Prop} (h : ∀ x y, x.1 ≠ y.1 → P x y)
    (x y : BlockSpace D S z) (hxy : ord y.1 < ord x.1) : P x y :=
  h x y fun e => by
    rw [e] at hxy
    exact lt_irrefl _ hxy

/-- **The remainder vanishes when the letter is block diagonal**: if the matrix of `B^i` in the
block coordinates vanishes off the diagonal blocks, the remainder `R^i` vanishes. -/
theorem remainder_eq_zero_of_offDiag (P : MultiBlockCompression B S C) (i : Fin d)
    (h : ∀ x y : BlockSpace D S P.z, x.1 ≠ y.1 → conjMatrix P.gauge (B i) x y = 0) :
    P.remainder i = 0 := by
  refine conjMatrix_injective P.gauge ?_
  rw [P.conjMatrix_remainder, conjMatrix_zero, sub_eq_zero]
  ext x y
  rcases eq_or_ne x.1 y.1 with hxy | hxy
  · obtain ⟨k, a⟩ := x
    obtain ⟨l, b⟩ := y
    subst hxy
    rw [Matrix.blockDiagonal'_apply_eq, Matrix.blockDiag'_apply]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hxy, h x y hxy]

/-- The remainder of a compression with a single target slot `s₀` is `B^i - V C^i W` for that
slot. -/
theorem remainder_oneSlot [Subsingleton {s // s ∈ S}] (P : MultiBlockCompression B S C)
    (s₀ : {s // s ∈ S}) (i : Fin d) :
    P.remainder i = B i - P.right s₀ * C s₀.1 i * P.left s₀ := by
  rw [remainder, Finset.sum_eq_single_of_mem s₀ (Finset.mem_univ s₀)
    fun b _ hb => absurd (Subsingleton.elim b s₀) hb]

end MultiBlockCompression

/-! ### Compression data from decided identities over a ring

The worked examples record the letters of the source, the targets and the conjugated letters as
matrices over a commutative ring `R` with decidable equality, embedded in the complex numbers by
a ring homomorphism `f`. The clauses (i)–(iii) of Theorem 7.7 then reduce to entrywise identities
over `R`, decided in exact arithmetic. -/

section Ring

variable {R : Type*} [CommRing R] (f : R →+* ℂ)

/-- The gauge attached to a pair of mutually inverse matrices over `R` and a labelling of the
bond coordinates by the graded block space. -/
noncomputable def gaugeOfRingMatrix (τ : BlockSpace D S z ≃ Fin DB)
    (G Ginv : Matrix (Fin DB) (Fin DB) R) (hG : G * Ginv = 1) (hG' : Ginv * G = 1) :
    (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D S z → ℂ) :=
  gaugeOfMatrix τ (complexOfRing f G) (complexOfRing f Ginv) (complexOfRing_mul_eq_one f hG)
    (complexOfRing_mul_eq_one f hG')

/-- Conjugating the image of a matrix over `R` by the gauge of a matrix over `R` is the image of
the conjugated matrix, relabelled along the bond coordinates. -/
theorem conjMatrix_gaugeOfRingMatrix (τ : BlockSpace D S z ≃ Fin DB)
    {G Ginv : Matrix (Fin DB) (Fin DB) R} (hG : G * Ginv = 1) (hG' : Ginv * G = 1)
    {A : Matrix (Fin DB) (Fin DB) ℂ} {AR : Matrix (Fin DB) (Fin DB) R}
    (hA : A = complexOfRing f AR) :
    conjMatrix (gaugeOfRingMatrix f τ G Ginv hG hG') A =
      (complexOfRing f (G * AR * Ginv)).submatrix τ τ := by
  rw [gaugeOfRingMatrix, conjMatrix_gaugeOfMatrix, hA, ← complexOfRing_mul, ← complexOfRing_mul]

namespace MultiBlockCompression

variable {B : MPSTensor d DB} {C : ∀ s, MPSTensor d (D s)}

/-- **A multi-block compression datum from decided identities over a ring** (P5 note,
Theorem 7.7(i)–(iii)). The gauge is any change of bond coordinates in which every letter `B^i`
is the image of a matrix `K i` over `R`, relabelled along the bond coordinates `τ`; the targets
are the images of matrices `Cg s` over `R`. The three clauses are then entrywise identities for
`K i` over `R`: block upper triangularity for the ordering `ord`, the target `Cg s` on the
diagonal block of each slot `s`, and zero on each zero slot. -/
noncomputable def ofRing (ord : BlockIndex S z ≃ Fin (S.card + z))
    (τ : BlockSpace D S z ≃ Fin DB) (gauge : (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D S z → ℂ))
    (K : Fin d → Matrix (Fin DB) (Fin DB) R)
    (hK : ∀ i, conjMatrix gauge (B i) = (complexOfRing f (K i)).submatrix τ τ)
    (Cg : ∀ s, Fin d → Matrix (Fin (D s)) (Fin (D s)) R)
    (hC : ∀ s i, C s i = complexOfRing f (Cg s i))
    (htri : ∀ (i : Fin d) (x y : BlockSpace D S z), ord y.1 < ord x.1 → K i (τ x) (τ y) = 0)
    (hmatched : ∀ (i : Fin d) (s : {s // s ∈ S}) (p q : Fin (D s.1)),
      K i (τ ⟨Sum.inl s, p⟩) (τ ⟨Sum.inl s, q⟩) = Cg s.1 i p q)
    (hunmatched : ∀ (i : Fin d) (t : Fin z) (p q : Fin 1),
      K i (τ ⟨Sum.inr t, p⟩) (τ ⟨Sum.inr t, q⟩) = 0) :
    MultiBlockCompression B S C where
  z := z
  ord := ord
  gauge := gauge
  triangular i x y h := by
    rw [hK, Matrix.submatrix_apply, complexOfRing_apply, htri i x y h, map_zero]
  matched i s := by
    ext p q
    rw [Matrix.blockDiag'_apply, hK, Matrix.submatrix_apply, complexOfRing_apply,
      hmatched i s p q, hC, complexOfRing_apply]
  unmatched i t := by
    ext p q
    rw [Matrix.blockDiag'_apply, hK, Matrix.submatrix_apply, complexOfRing_apply,
      hunmatched i t p q, map_zero, Matrix.zero_apply]

variable {f} in
/-- **The remainder of a ring-certified datum vanishes when the recorded letters are block
diagonal**: if every `K i` vanishes off the diagonal blocks, the extension splits. -/
theorem remainder_ofRing {ord : BlockIndex S z ≃ Fin (S.card + z)}
    {τ : BlockSpace D S z ≃ Fin DB} {gauge : (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D S z → ℂ)}
    {K : Fin d → Matrix (Fin DB) (Fin DB) R}
    {hK : ∀ i, conjMatrix gauge (B i) = (complexOfRing f (K i)).submatrix τ τ}
    {Cg : ∀ s, Fin d → Matrix (Fin (D s)) (Fin (D s)) R}
    {hC : ∀ s i, C s i = complexOfRing f (Cg s i)}
    {htri : ∀ (i : Fin d) (x y : BlockSpace D S z), ord y.1 < ord x.1 → K i (τ x) (τ y) = 0}
    {hmatched : ∀ (i : Fin d) (s : {s // s ∈ S}) (p q : Fin (D s.1)),
      K i (τ ⟨Sum.inl s, p⟩) (τ ⟨Sum.inl s, q⟩) = Cg s.1 i p q}
    {hunmatched : ∀ (i : Fin d) (t : Fin z) (p q : Fin 1),
      K i (τ ⟨Sum.inr t, p⟩) (τ ⟨Sum.inr t, q⟩) = 0}
    (hoff : ∀ (i : Fin d) (x y : BlockSpace D S z), x.1 ≠ y.1 → K i (τ x) (τ y) = 0)
    (i : Fin d) :
    (ofRing f ord τ gauge K hK Cg hC htri hmatched hunmatched).remainder i = 0 :=
  remainder_eq_zero_of_offDiag _ i fun x y hxy => by
    change conjMatrix gauge (B i) x y = 0
    rw [hK]
    exact (congrArg f (hoff i x y hxy)).trans (map_zero f)

/-- **A multi-block compression datum from a block-diagonal letter identity over a ring.**
When the matrix of every letter in the block coordinates is the image of a block-diagonal matrix
over `R` with the targets on the slots and zero on the zero slots, the clauses of
`MultiBlockCompression.ofRing` hold for the letters read back along any labelling `τ` of the
bond coordinates. -/
noncomputable def ofRingBlockDiagonal (ord : BlockIndex S z ≃ Fin (S.card + z))
    (τ : BlockSpace D S z ≃ Fin DB) (gauge : (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D S z → ℂ))
    (blk : Fin d → ∀ b : BlockIndex S z, Matrix (Fin (slotSize D b)) (Fin (slotSize D b)) R)
    (hblk : ∀ i, conjMatrix gauge (B i) = complexOfRing f (Matrix.blockDiagonal' (blk i)))
    (Cg : ∀ s, Fin d → Matrix (Fin (D s)) (Fin (D s)) R)
    (hC : ∀ s i, C s i = complexOfRing f (Cg s i))
    (hmatched : ∀ (i : Fin d) (s : {s // s ∈ S}), blk i (Sum.inl s) = Cg s.1 i)
    (hunmatched : ∀ (i : Fin d) (t : Fin z), blk i (Sum.inr t) = 0) :
    MultiBlockCompression B S C :=
  ofRing f ord τ gauge (fun i => (Matrix.blockDiagonal' (blk i)).submatrix τ.symm τ.symm)
    (fun i => by rw [hblk, complexOfRing_submatrix, Matrix.submatrix_submatrix]; simp) Cg hC
    (fun i => triangular_of_offDiag fun x y hxy => by
      simp [Matrix.blockDiagonal'_apply_ne _ _ _ hxy])
    (fun i s p q => by simp [hmatched]) fun i t p q => by simp [hunmatched]

variable {f} in
/-- The remainder of a datum with a block-diagonal letter identity vanishes. -/
theorem remainder_ofRingBlockDiagonal {ord : BlockIndex S z ≃ Fin (S.card + z)}
    {τ : BlockSpace D S z ≃ Fin DB} {gauge : (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D S z → ℂ)}
    {blk : Fin d → ∀ b : BlockIndex S z, Matrix (Fin (slotSize D b)) (Fin (slotSize D b)) R}
    {hblk : ∀ i, conjMatrix gauge (B i) = complexOfRing f (Matrix.blockDiagonal' (blk i))}
    {Cg : ∀ s, Fin d → Matrix (Fin (D s)) (Fin (D s)) R}
    {hC : ∀ s i, C s i = complexOfRing f (Cg s i)}
    {hmatched : ∀ (i : Fin d) (s : {s // s ∈ S}), blk i (Sum.inl s) = Cg s.1 i}
    {hunmatched : ∀ (i : Fin d) (t : Fin z), blk i (Sum.inr t) = 0} (i : Fin d) :
    (ofRingBlockDiagonal f ord τ gauge blk hblk Cg hC hmatched hunmatched).remainder i = 0 :=
  remainder_ofRing (fun i x y hxy => by simp [Matrix.blockDiagonal'_apply_ne _ _ _ hxy]) i

end MultiBlockCompression

end Ring

/-! ### One target slot -/

/-- The slot set of a compression with one target. -/
abbrev oneSlot : Finset Unit := {()}

/-- The single slot as an element of the slot subtype. -/
abbrev oneSlotMem : {s // s ∈ oneSlot} := ⟨(), Finset.mem_singleton_self ()⟩

theorem eq_oneSlotMem (s : {s // s ∈ oneSlot}) : s = oneSlotMem :=
  Subtype.ext (Subsingleton.elim _ _)

/-- The single target slot counts one. -/
theorem oneSlot_card : oneSlot.card = 1 := rfl

/-- The block ordering of a compression with one target: the target first, then the `z` zero
slots in order. -/
def unitOrd (z : ℕ) : BlockIndex oneSlot z ≃ Fin (oneSlot.card + z) where
  toFun := Sum.elim (fun _ => Fin.castAdd z ⟨0, by rw [oneSlot_card]; exact Nat.one_pos⟩)
    fun t => Fin.natAdd oneSlot.card t
  invFun := Fin.addCases (fun _ => Sum.inl oneSlotMem) fun t => Sum.inr t
  left_inv b := by
    rcases b with s | t
    · obtain rfl : s = oneSlotMem := eq_oneSlotMem s
      simp only [Sum.elim_inl, Fin.addCases_left]
    · simp only [Sum.elim_inr, Fin.addCases_right]
  right_inv k := by
    refine Fin.addCases (fun i => ?_) (fun t => ?_) k
    · simp only [Fin.addCases_left, Sum.elim_inl]
      exact congrArg (Fin.castAdd z) (Fin.ext (by have hi : (i : ℕ) < 1 := i.2; simp; omega))
    · simp only [Fin.addCases_right, Sum.elim_inr]

/-- The bond coordinates of a compression with one target of bond dimension `n`: the `n`
coordinates of the target first, then the `z` zero slots in order. -/
def unitCoord (n z : ℕ) : BlockSpace (fun _ : Unit => n) oneSlot z ≃ Fin (n + z) where
  toFun x := Sum.rec (motive := fun b => Fin (slotSize (fun _ : Unit => n) b) → Fin (n + z))
    (fun _ p => Fin.castAdd z p) (fun t _ => Fin.natAdd n t) x.1 x.2
  invFun := Fin.addCases (fun p => ⟨Sum.inl oneSlotMem, p⟩) fun t => ⟨Sum.inr t, 0⟩
  left_inv x := by
    rcases x with ⟨s | t, p⟩
    · obtain rfl : s = oneSlotMem := eq_oneSlotMem s
      exact Fin.addCases_left p
    · obtain rfl : p = 0 := Subsingleton.elim _ _
      exact Fin.addCases_right t
  right_inv k := by
    refine Fin.addCases (fun p => ?_) (fun t => ?_) k
    · dsimp only
      rw [Fin.addCases_left]
    · dsimp only
      rw [Fin.addCases_right]

end MPSTensor
