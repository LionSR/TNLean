/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Algebra.MatrixSingleSpan
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.GoldenRing
import TNLean.MPS.MPDO.ActionTensor

/-!
# Compression data with golden-integer gauges

The worked examples over the ring `ℤ[σ]` of `GoldenRing.lean` all follow one pattern: the
letters of the source tensor, of the target blocks, of the change of bond coordinates and of its
inverse are explicit matrices over `ℤ[σ]`, the conjugated letters `G B^i G⁻¹` are explicit
block-triangular matrices, and every identity between them is decided in exact arithmetic. This
file packages that pattern once, so that each example only supplies its matrices and the decided
identities.

## Main definitions

* `MPSTensor.actGoldenTensor`: the action of an operator tensor on a state tensor over `ℤ[σ]`.
* `MPSTensor.goldenGauge`, `MPSTensor.MultiBlockCompression.ofGolden`: the gauge attached to a
  pair of mutually inverse matrices over `ℤ[σ]`, and the multi-block compression datum assembled
  from it and the decided block structure of the conjugated letters.
* `MPSTensor.unitOrd`, `MPSTensor.unitCoord`: the block ordering and the bond coordinates of a
  compression with one target slot placed before the zero slots.

## Main results

* `MPSTensor.actTensor_complexOfGolden`: the action tensor commutes with the entrywise embedding
  of `ℤ[σ]`.
* `MPSTensor.isNormal_of_golden_single`: normality of a tensor over `ℤ[σ]` from a decided table
  expressing every matrix unit as a combination of words of one positive length.
* `MPSTensor.MultiBlockCompression.remainder_eq_zero_of_goldenGauge`: the remainder of a datum
  with a golden gauge vanishes when the conjugated letters are block diagonal.
-/

open scoped Matrix Kronecker

namespace MPSTensor

variable {d D D₁ D₂ : ℕ}

/-! ### Action tensors over the golden integers -/

/-- The bond-space action of an operator tensor on a state tensor over the golden integers,
`(M · A)^i = ∑_j M^{ij} ⊗ A^j`, in the bond order of `finProdFinEquiv`, matching
`MPOTensor.actTensor`. -/
def actGoldenTensor (M : Fin d → Fin d → Matrix (Fin D₁) (Fin D₁) GoldenInt)
    (A : Fin d → Matrix (Fin D₂) (Fin D₂) GoldenInt) (i : Fin d) :
    Matrix (Fin (D₁ * D₂)) (Fin (D₁ * D₂)) GoldenInt :=
  (∑ j : Fin d, (M i j) ⊗ₖ (A j)).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

/-- The action tensor commutes with the entrywise embedding of the golden integers. -/
theorem actTensor_complexOfGolden (M : Fin d → Fin d → Matrix (Fin D₁) (Fin D₁) GoldenInt)
    (A : Fin d → Matrix (Fin D₂) (Fin D₂) GoldenInt) (i : Fin d) :
    MPOTensor.actTensor (fun i j => complexOfGolden (M i j)) (fun j => complexOfGolden (A j)) i =
      complexOfGolden (actGoldenTensor M A i) := by
  ext x y
  simp only [MPOTensor.actTensor_apply, actGoldenTensor, Matrix.submatrix_apply, Matrix.sum_apply,
    Matrix.kroneckerMap_apply, complexOfGolden_apply, map_sum, map_mul]

/-! ### Normality from a decided table of matrix units -/

/-- **Normality from a table of matrix units over `ℤ[σ]`.** If every matrix unit `E_{ij}` is a
combination, with coefficients in `ℤ[σ]`, of finitely many words of one positive length `ℓ` of
a tensor over `ℤ[σ]`, then the complex tensor is normal, its length-`ℓ` words spanning the full
matrix algebra. -/
theorem isNormal_of_golden_single {A : MPSTensor d D}
    (Ag : Fin d → Matrix (Fin D) (Fin D) GoldenInt) (hA : ∀ a, A a = complexOfGolden (Ag a))
    {ℓ : ℕ} (hℓ : 0 < ℓ) {κ : Type*} [Fintype κ]
    (word : Fin D → Fin D → κ → Fin ℓ → Fin d) (coef : Fin D → Fin D → κ → GoldenInt)
    (h : ∀ i j, ∑ k, coef i j k • evalWordGolden Ag (List.ofFn (word i j k)) =
      Matrix.single i j 1) :
    Kraus.IsNormal A := by
  refine ⟨ℓ, hℓ, ?_⟩
  rw [Kraus.IsNBlkInjective, Kraus.wordSpan]
  set T := Submodule.span ℂ
    (Set.range fun w : Fin ℓ → Fin d => Kraus.evalWord A (List.ofFn w)) with hT
  have hA' : A = fun a => complexOfGolden (Ag a) := funext hA
  have hunit : ∀ i j : Fin D, Matrix.single i j (1 : ℂ) ∈ T := by
    intro i j
    have h' := congrArg complexOfGolden (h i j)
    rw [complexOfGolden_single, complexOfGolden_sum] at h'
    rw [← h']
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [complexOfGolden_smul, ← evalWord_complexOfGolden, ← hA']
    exact T.smul_mem _ (Submodule.subset_span ⟨word i j k, rfl⟩)
  exact Submodule.eq_top_of_forall_single_mem T hunit

/-! ### Compression data from a golden gauge -/

variable {DB : ℕ} {ι : Type*} [DecidableEq ι] {Dι : ι → ℕ} {S : Finset ι} {z : ℕ}

/-- The gauge attached to a pair of mutually inverse matrices over `ℤ[σ]` and a labelling of
the bond coordinates by the graded block space. -/
noncomputable def goldenGauge (τ : BlockSpace Dι S z ≃ Fin DB)
    (G Ginv : Matrix (Fin DB) (Fin DB) GoldenInt) (hG : G * Ginv = 1) (hG' : Ginv * G = 1) :
    (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace Dι S z → ℂ) :=
  gaugeOfMatrix τ (complexOfGolden G) (complexOfGolden Ginv)
    (by rw [← complexOfGolden_mul, hG, complexOfGolden_one])
    (by rw [← complexOfGolden_mul, hG', complexOfGolden_one])

/-- Conjugating a letter by a golden gauge reads off the recorded conjugated letter: if
`Bg^i Ginv = Ginv K^i` over `ℤ[σ]`, the matrix of `B^i` in the block coordinates is `K^i`
relabelled along `τ`. -/
theorem conjMatrix_goldenGauge (τ : BlockSpace Dι S z ≃ Fin DB)
    {G Ginv : Matrix (Fin DB) (Fin DB) GoldenInt} (hG : G * Ginv = 1) (hG' : Ginv * G = 1)
    {B : Matrix (Fin DB) (Fin DB) ℂ} {Bg K : Matrix (Fin DB) (Fin DB) GoldenInt}
    (hB : B = complexOfGolden Bg) (hK : Bg * Ginv = Ginv * K) :
    conjMatrix (goldenGauge τ G Ginv hG hG') B = (complexOfGolden K).submatrix τ τ := by
  rw [goldenGauge, conjMatrix_gaugeOfMatrix, hB, ← complexOfGolden_mul, ← complexOfGolden_mul,
    Matrix.mul_assoc, hK, ← Matrix.mul_assoc, hG, Matrix.one_mul]

/-- **A multi-block compression datum from a gauge over `ℤ[σ]`.** The letters of the source
`B` and of the targets `C s` are the entrywise embeddings of the matrices `Bg` and `Cg` over
`ℤ[σ]`; the matrices `G` and `Ginv` over `ℤ[σ]` are mutually inverse; the conjugated letters
`G Bg^i Ginv` are the matrices `K i`, recorded through the identity `Bg^i Ginv = Ginv K^i`; and,
read along the bond coordinates `τ`, each `K i` is block upper triangular for the ordering `ord`
with the target `Cg s` on the diagonal block of the slot `s` and zero on every zero slot. -/
noncomputable def MultiBlockCompression.ofGolden {B : MPSTensor d DB}
    {C : ∀ s, MPSTensor d (Dι s)} (z : ℕ) (ord : BlockIndex S z ≃ Fin (S.card + z))
    (τ : BlockSpace Dι S z ≃ Fin DB) (Bg : Fin d → Matrix (Fin DB) (Fin DB) GoldenInt)
    (hB : ∀ i, B i = complexOfGolden (Bg i))
    (Cg : ∀ s, Fin d → Matrix (Fin (Dι s)) (Fin (Dι s)) GoldenInt)
    (hC : ∀ s i, C s i = complexOfGolden (Cg s i))
    (G Ginv : Matrix (Fin DB) (Fin DB) GoldenInt) (hG : G * Ginv = 1) (hG' : Ginv * G = 1)
    (K : Fin d → Matrix (Fin DB) (Fin DB) GoldenInt) (hK : ∀ i, Bg i * Ginv = Ginv * K i)
    (htri : ∀ (i : Fin d) (x y : BlockSpace Dι S z), ord y.1 < ord x.1 → K i (τ x) (τ y) = 0)
    (hmatched : ∀ (i : Fin d) (s : ι) (hs : s ∈ S) (p q : Fin (Dι s)),
      K i (τ ⟨Sum.inl ⟨s, hs⟩, p⟩) (τ ⟨Sum.inl ⟨s, hs⟩, q⟩) = Cg s i p q)
    (hunmatched : ∀ (i : Fin d) (t : Fin z) (p q : Fin 1),
      K i (τ ⟨Sum.inr t, p⟩) (τ ⟨Sum.inr t, q⟩) = 0) :
    MultiBlockCompression B S C where
  z := z
  ord := ord
  gauge := goldenGauge τ G Ginv hG hG'
  triangular i x y h := by
    rw [conjMatrix_goldenGauge τ hG hG' (hB i) (hK i), Matrix.submatrix_apply,
      complexOfGolden_apply, htri i x y h, map_zero]
  matched i s := by
    obtain ⟨s, hs⟩ := s
    ext p q
    rw [Matrix.blockDiag'_apply, conjMatrix_goldenGauge τ hG hG' (hB i) (hK i),
      Matrix.submatrix_apply, complexOfGolden_apply, hmatched i s hs p q, hC,
      complexOfGolden_apply]
  unmatched i t := by
    ext p q
    rw [Matrix.blockDiag'_apply, conjMatrix_goldenGauge τ hG hG' (hB i) (hK i),
      Matrix.submatrix_apply, complexOfGolden_apply, hunmatched i t p q, map_zero,
      Matrix.zero_apply]

/-- **The remainder of a compression with a golden gauge vanishes when the conjugated letters are
block diagonal**: if every recorded conjugated letter `K i` vanishes off the diagonal blocks, the
extension splits. -/
theorem MultiBlockCompression.remainder_eq_zero_of_goldenGauge {B : MPSTensor d DB}
    {C : ∀ s, MPSTensor d (Dι s)} (P : MultiBlockCompression B S C)
    {τ : BlockSpace Dι S P.z ≃ Fin DB} {G Ginv : Matrix (Fin DB) (Fin DB) GoldenInt}
    {hG : G * Ginv = 1} {hG' : Ginv * G = 1} (hgauge : P.gauge = goldenGauge τ G Ginv hG hG')
    {Bg K : Fin d → Matrix (Fin DB) (Fin DB) GoldenInt} (hB : ∀ i, B i = complexOfGolden (Bg i))
    (hK : ∀ i, Bg i * Ginv = Ginv * K i)
    (hoff : ∀ (i : Fin d) (x y : BlockSpace Dι S P.z), x.1 ≠ y.1 → K i (τ x) (τ y) = 0)
    (i : Fin d) : P.remainder i = 0 := by
  refine conjMatrix_injective P.gauge ?_
  rw [P.conjMatrix_remainder, conjMatrix_zero, sub_eq_zero]
  ext x y
  rcases eq_or_ne x.1 y.1 with hxy | hxy
  · obtain ⟨k, a⟩ := x
    obtain ⟨l, b⟩ := y
    subst hxy
    rw [Matrix.blockDiagonal'_apply_eq, Matrix.blockDiag'_apply]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hxy, hgauge,
      conjMatrix_goldenGauge τ hG hG' (hB i) (hK i), Matrix.submatrix_apply,
      complexOfGolden_apply, hoff i x y hxy, map_zero]

/-! ### One target slot before the zero slots -/

/-- The slot set of a compression with one target. -/
abbrev unitSlots : Finset Unit := Finset.univ

/-- The single slot of a compression with one target. -/
def unitSlot : {s // s ∈ unitSlots} := ⟨(), Finset.mem_univ ()⟩

instance : Subsingleton {s // s ∈ unitSlots} :=
  ⟨fun ⟨(), _⟩ ⟨(), _⟩ => rfl⟩

/-- The single target slot counts one. -/
theorem unitSlots_card : unitSlots.card = 1 := rfl

/-- The block ordering of a compression with one target: the target first, then the `z` zero
slots in order. -/
def unitOrd (z : ℕ) : BlockIndex unitSlots z ≃ Fin (unitSlots.card + z) where
  toFun := Sum.elim (fun _ => Fin.castAdd z ⟨0, by rw [unitSlots_card]; exact Nat.one_pos⟩)
    fun t => Fin.natAdd unitSlots.card t
  invFun := Fin.addCases (fun _ => Sum.inl unitSlot) fun t => Sum.inr t
  left_inv b := by
    rcases b with s | t
    · simp only [Sum.elim_inl, Fin.addCases_left]
      exact congrArg Sum.inl (Subsingleton.elim _ _)
    · simp only [Sum.elim_inr, Fin.addCases_right]
  right_inv k := by
    refine Fin.addCases (fun i => ?_) (fun t => ?_) k
    · simp only [Fin.addCases_left, Sum.elim_inl]
      exact congrArg (Fin.castAdd z) (Fin.ext (by have hi : (i : ℕ) < 1 := i.2; simp; omega))
    · simp only [Fin.addCases_right, Sum.elim_inr]

/-- The bond coordinates of a compression with one target of bond dimension `n`: the `n`
coordinates of the target first, then the `z` zero slots in order. -/
def unitCoord (n z : ℕ) : BlockSpace (fun _ : Unit => n) unitSlots z ≃ Fin (n + z) where
  toFun x := Sum.rec (motive := fun b => Fin (slotSize (fun _ : Unit => n) b) → Fin (n + z))
    (fun _ p => Fin.castAdd z p) (fun t _ => Fin.natAdd n t) x.1 x.2
  invFun := Fin.addCases (fun p => ⟨Sum.inl unitSlot, p⟩) fun t => ⟨Sum.inr t, 0⟩
  left_inv x := by
    rcases x with ⟨s | t, p⟩
    · obtain rfl : s = unitSlot := Subsingleton.elim _ _
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
