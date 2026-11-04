/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalCoordinates

/-!
# Rational matrix entries and height bounds

This is part of the finite-precision analysis of the boundary optimization in
Landau, Vazirani and Vidick, arXiv:1307.5143v1, equation `eq:conv`.
-/

open Matrix
open scoped Kronecker ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw
/-- Every entry of a matrix has rational real and imaginary parts. -/
def Matrix.HasRationalEntries {m n : Type*} (A : Matrix m n ℂ) : Prop :=
  ∀ i j, HasRationalComplexCoordinates (A i j)

/-- Every matrix entry has rational coordinates of height at most `H`. -/
def Matrix.HasRationalEntriesOfHeight {m n : Type*} (H : ℕ)
    (A : Matrix m n ℂ) : Prop :=
  ∀ i j, HasRationalComplexCoordinatesOfHeight H (A i j)

/-- Height bound obtained after taking the Hermitian part of a matrix whose entries
have coordinate height at most `H`. -/
def hermitianPartHeight (H : ℕ) : ℕ :=
  2 * (2 * (2 * H * H)) * (2 * (2 * H * H))

namespace Matrix.HasRationalEntriesOfHeight

theorem forget {m n : Type*} {H : ℕ} {A : Matrix m n ℂ}
    (hA : Matrix.HasRationalEntriesOfHeight H A) : Matrix.HasRationalEntries A :=
  fun i j ↦ (hA i j).forget

theorem entry_exists_bitLength_le {m n : Type*} {H : ℕ} {A : Matrix m n ℂ}
    (hA : Matrix.HasRationalEntriesOfHeight H A) (i : m) (j : n) :
    ∃ x y : ℚ, A i j = ⟨(x : ℝ), (y : ℝ)⟩ ∧
      rationalBitLength x ≤ Nat.log2 H + 1 ∧
      rationalBitLength y ≤ Nat.log2 H + 1 :=
  (hA i j).exists_bitLength_le

theorem mono {m n : Type*} {H K : ℕ} {A : Matrix m n ℂ} (hHK : H ≤ K)
    (hA : Matrix.HasRationalEntriesOfHeight H A) :
    Matrix.HasRationalEntriesOfHeight K A :=
  fun i j ↦ (hA i j).mono hHK

theorem one {n : Type*} [DecidableEq n] :
    Matrix.HasRationalEntriesOfHeight 1 (1 : Matrix n n ℂ) := by
  intro i j
  by_cases hij : i = j
  · subst j
    simpa using HasRationalComplexCoordinatesOfHeight.one
  · simp only [Matrix.one_apply_ne hij]
    exact HasRationalComplexCoordinatesOfHeight.zero

theorem smul {m n : Type*} {H K : ℕ} {c : ℂ} {A : Matrix m n ℂ}
    (hc : HasRationalComplexCoordinatesOfHeight H c)
    (hA : Matrix.HasRationalEntriesOfHeight K A) :
    Matrix.HasRationalEntriesOfHeight (2 * (H * K) * (H * K)) (c • A) :=
  fun i j ↦ hc.mul (hA i j)

theorem conjTranspose {m n : Type*} {H : ℕ} {A : Matrix m n ℂ}
    (hA : Matrix.HasRationalEntriesOfHeight H A) :
    Matrix.HasRationalEntriesOfHeight H Aᴴ :=
  fun i j ↦ (hA j i).star

theorem add {m n : Type*} {H K : ℕ} {A B : Matrix m n ℂ}
    (hA : Matrix.HasRationalEntriesOfHeight H A)
    (hB : Matrix.HasRationalEntriesOfHeight K B) :
    Matrix.HasRationalEntriesOfHeight (2 * H * K) (A + B) :=
  fun i j ↦ (hA i j).add (hB i j)

theorem hermitianPart {n : Type*} [Fintype n] {H : ℕ} {A : Matrix n n ℂ}
    (hA : Matrix.HasRationalEntriesOfHeight H A) :
    Matrix.HasRationalEntriesOfHeight (hermitianPartHeight H)
      (matrixHermitianPart A) := by
  rw [matrixHermitianPart]
  have hhalf : HasRationalComplexCoordinatesOfHeight 2 (1 / 2 : ℂ) := by
    simpa [one_div] using HasRationalComplexCoordinatesOfHeight.half
  exact smul hhalf (add hA hA.conjTranspose)

theorem sub {m n : Type*} {H K : ℕ} {A B : Matrix m n ℂ}
    (hA : Matrix.HasRationalEntriesOfHeight H A)
    (hB : Matrix.HasRationalEntriesOfHeight K B) :
    Matrix.HasRationalEntriesOfHeight (2 * H * K) (A - B) :=
  fun i j ↦ (hA i j).sub (hB i j)

/-- Matrix multiplication has an explicit coordinate-height bound.  Its binary
length is linear in the contracted dimension. -/
theorem mul {m n p : Type*} [Fintype n] {H K : ℕ}
    {A : Matrix m n ℂ} {B : Matrix n p ℂ}
    (hA : Matrix.HasRationalEntriesOfHeight H A)
    (hB : Matrix.HasRationalEntriesOfHeight K B) :
    Matrix.HasRationalEntriesOfHeight
      ((2 * (2 * (H * K) * (H * K))) ^ Fintype.card n) (A * B) := by
  intro i j
  rw [Matrix.mul_apply]
  exact HasRationalComplexCoordinatesOfHeight.finset_sum fun k _hk ↦
    (hA i k).mul (hB k j)

/-- The trace has an explicit coordinate-height bound linear in the matrix order
after taking binary logarithms. -/
theorem trace {n : Type*} [Fintype n] {H : ℕ} {A : Matrix n n ℂ}
    (hA : Matrix.HasRationalEntriesOfHeight H A) :
    HasRationalComplexCoordinatesOfHeight ((2 * H) ^ Fintype.card n) A.trace := by
  rw [Matrix.trace]
  exact HasRationalComplexCoordinatesOfHeight.finset_sum fun i _hi ↦ hA i i

/-- The Gram matrix of a height-bounded rational matrix has an explicit
coordinate-height bound. -/
theorem gram {n : Type*} [Fintype n] {H : ℕ} {Q : Matrix n n ℂ}
    (hQ : Matrix.HasRationalEntriesOfHeight H Q) :
    Matrix.HasRationalEntriesOfHeight
      ((2 * (2 * (H * H) * (H * H))) ^ Fintype.card n) (Q * Qᴴ) :=
  mul hQ hQ.conjTranspose

/-- The shifted Gram residual occurring in each approximate semidefinite
certificate has an explicit coordinate-height bound. -/
theorem shiftedGramResidual {n : Type*} [Fintype n] [DecidableEq n]
    {HA Hε HQ : ℕ} {A Q : Matrix n n ℂ} {ε : ℂ}
    (hA : Matrix.HasRationalEntriesOfHeight HA A)
    (hε : HasRationalComplexCoordinatesOfHeight Hε ε)
    (hQ : Matrix.HasRationalEntriesOfHeight HQ Q) :
    let Hshift := 2 * (Hε * 1) * (Hε * 1)
    let Hleft := 2 * HA * Hshift
    let Hgram := (2 * (2 * (HQ * HQ) * (HQ * HQ))) ^ Fintype.card n
    Matrix.HasRationalEntriesOfHeight (2 * Hleft * Hgram)
      ((A + ε • (1 : Matrix n n ℂ)) - Q * Qᴴ) := by
  dsimp only
  exact sub (add hA (smul hε one)) (gram hQ)

theorem reindex {m n m' n' : Type*} (em : m ≃ m') (en : n ≃ n')
    {H : ℕ} {A : Matrix m n ℂ} (hA : Matrix.HasRationalEntriesOfHeight H A) :
    Matrix.HasRationalEntriesOfHeight H (Matrix.reindex em en A) := by
  intro i j
  exact hA (em.symm i) (en.symm j)

theorem partialTraceLeft {α β : Type*} [Fintype α] {H : ℕ}
    {A : Matrix (α × β) (α × β) ℂ}
    (hA : Matrix.HasRationalEntriesOfHeight H A) :
    Matrix.HasRationalEntriesOfHeight ((2 * H) ^ Fintype.card α)
      (Matrix.partialTraceLeft A) := by
  intro i j
  rw [Matrix.partialTraceLeft_apply]
  exact HasRationalComplexCoordinatesOfHeight.finset_sum fun k _hk ↦ hA (k, i) (k, j)

/-- The trace of a matrix product has an explicit coordinate-height bound. -/
theorem trace_mul {n : Type*} [Fintype n] {H K : ℕ}
    {A B : Matrix n n ℂ}
    (hA : Matrix.HasRationalEntriesOfHeight H A)
    (hB : Matrix.HasRationalEntriesOfHeight K B) :
    let Hmul := (2 * (2 * (H * K) * (H * K))) ^ Fintype.card n
    HasRationalComplexCoordinatesOfHeight ((2 * Hmul) ^ Fintype.card n)
      (A * B).trace := by
  dsimp only
  exact trace (mul hA hB)

end Matrix.HasRationalEntriesOfHeight

namespace Matrix.HasRationalEntries

theorem one {n : Type*} [DecidableEq n] :
    Matrix.HasRationalEntries (1 : Matrix n n ℂ) := by
  intro i j
  by_cases hij : i = j
  · subst j
    simpa using HasRationalComplexCoordinates.one
  · simp only [Matrix.one_apply_ne hij]
    exact HasRationalComplexCoordinates.zero

theorem smul {m n : Type*} {c : ℂ} {A : Matrix m n ℂ}
    (hc : HasRationalComplexCoordinates c) (hA : Matrix.HasRationalEntries A) :
    Matrix.HasRationalEntries (c • A) := fun i j ↦ hc.mul (hA i j)

theorem add {m n : Type*} {A B : Matrix m n ℂ}
    (hA : Matrix.HasRationalEntries A) (hB : Matrix.HasRationalEntries B) :
    Matrix.HasRationalEntries (A + B) := fun i j ↦ (hA i j).add (hB i j)

theorem neg {m n : Type*} {A : Matrix m n ℂ} (hA : Matrix.HasRationalEntries A) :
    Matrix.HasRationalEntries (-A) := fun i j ↦ (hA i j).neg

theorem sub {m n : Type*} {A B : Matrix m n ℂ}
    (hA : Matrix.HasRationalEntries A) (hB : Matrix.HasRationalEntries B) :
    Matrix.HasRationalEntries (A - B) := fun i j ↦ (hA i j).sub (hB i j)

theorem conjTranspose {m n : Type*} {A : Matrix m n ℂ}
    (hA : Matrix.HasRationalEntries A) :
    Matrix.HasRationalEntries Aᴴ := fun i j ↦ (hA j i).star

theorem mul {m n p : Type*} [Fintype n] {A : Matrix m n ℂ} {B : Matrix n p ℂ}
    (hA : Matrix.HasRationalEntries A) (hB : Matrix.HasRationalEntries B) :
    Matrix.HasRationalEntries (A * B) := by
  intro i k
  rw [Matrix.mul_apply]
  exact HasRationalComplexCoordinates.finset_sum fun j _ ↦ (hA i j).mul (hB j k)

theorem trace {n : Type*} [Fintype n] {A : Matrix n n ℂ}
    (hA : Matrix.HasRationalEntries A) :
    HasRationalComplexCoordinates A.trace := by
  rw [Matrix.trace]
  exact HasRationalComplexCoordinates.finset_sum fun i _ ↦ hA i i

theorem reindex {m n m' n' : Type*} (em : m ≃ m') (en : n ≃ n')
    {A : Matrix m n ℂ} (hA : Matrix.HasRationalEntries A) :
    Matrix.HasRationalEntries (Matrix.reindex em en A) := by
  intro i j
  exact hA (em.symm i) (en.symm j)

theorem partialTraceLeft {α β : Type*} [Fintype α]
    {A : Matrix (α × β) (α × β) ℂ} (hA : Matrix.HasRationalEntries A) :
    Matrix.HasRationalEntries (Matrix.partialTraceLeft A) := by
  intro i j
  rw [Matrix.partialTraceLeft_apply]
  exact HasRationalComplexCoordinates.finset_sum fun k _ ↦ hA (k, i) (k, j)

end Matrix.HasRationalEntries

/-- Rational coordinates are preserved by the compressed boundary marginal whenever
the coordinate isometry itself has rational entries. -/
theorem compressedBoundaryLM_hasRationalEntries
    {a s b : Type*} [Fintype a]
    {n : ℕ} {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hZ : Matrix.HasRationalEntries Z) (hA : Matrix.HasRationalEntries A) :
    Matrix.HasRationalEntries (compressedBoundaryLM Z A) := by
  rw [compressedBoundaryLM_apply]
  unfold Matrix.partialTraceFirst
  exact ((hZ.mul hA).mul hZ.conjTranspose).reindex
    (Equiv.prodAssoc a s b) (Equiv.prodAssoc a s b) |>.partialTraceLeft

/-- The compressed boundary marginal has an explicit coordinate-height bound in
terms of the input heights and the two contracted dimensions. -/
theorem compressedBoundaryLM_hasRationalEntriesOfHeight
    {a s b : Type*} [Fintype a]
    {n : ℕ} {HZ HA : ℕ} {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hZ : Matrix.HasRationalEntriesOfHeight HZ Z)
    (hA : Matrix.HasRationalEntriesOfHeight HA A) :
    let HZA := (2 * (2 * (HZ * HA) * (HZ * HA))) ^ n
    let HZAZ := (2 * (2 * (HZA * HZ) * (HZA * HZ))) ^ n
    Matrix.HasRationalEntriesOfHeight ((2 * HZAZ) ^ Fintype.card a)
      (compressedBoundaryLM Z A) := by
  dsimp only
  rw [compressedBoundaryLM_apply]
  unfold Matrix.partialTraceFirst
  have hprod := Matrix.HasRationalEntriesOfHeight.mul
    (Matrix.HasRationalEntriesOfHeight.mul hZ hA) hZ.conjTranspose
  simp only [Fintype.card_fin] at hprod
  exact Matrix.HasRationalEntriesOfHeight.partialTraceLeft
    (Matrix.HasRationalEntriesOfHeight.reindex
      (Equiv.prodAssoc a s b) (Equiv.prodAssoc a s b)
      hprod)

/-- The complete boundary equality residual in the approximate SDP certificate has
an explicit coordinate-height bound. -/
theorem compressedBoundaryResidual_hasRationalEntriesOfHeight
    {a s b : Type*} [Fintype a]
    {n : ℕ} {HZ HA HX HP HN : ℕ}
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    {X P N : Matrix (s × b) (s × b) ℂ}
    (hZ : Matrix.HasRationalEntriesOfHeight HZ Z)
    (hA : Matrix.HasRationalEntriesOfHeight HA A)
    (hX : Matrix.HasRationalEntriesOfHeight HX X)
    (hP : Matrix.HasRationalEntriesOfHeight HP P)
    (hN : Matrix.HasRationalEntriesOfHeight HN N) :
    let HZA := (2 * (2 * (HZ * HA) * (HZ * HA))) ^ n
    let HZAZ := (2 * (2 * (HZA * HZ) * (HZA * HZ))) ^ n
    let Hboundary := (2 * HZAZ) ^ Fintype.card a
    let Hleft := 2 * Hboundary * HX
    let Hright := 2 * HP * HN
    Matrix.HasRationalEntriesOfHeight (2 * Hleft * Hright)
      ((compressedBoundaryLM Z A - X) - (P - N)) := by
  dsimp only
  exact Matrix.HasRationalEntriesOfHeight.sub
    (Matrix.HasRationalEntriesOfHeight.sub
      (compressedBoundaryLM_hasRationalEntriesOfHeight hZ hA) hX)
    (Matrix.HasRationalEntriesOfHeight.sub hP hN)

/-- Coordinate-height bound for a dense matrix product across dimension `d`. -/
def matrixProductHeight (d H K : ℕ) : ℕ :=
  (2 * (2 * (H * K) * (H * K))) ^ d

/-- Coordinate-height bound for the trace of a height-`H` square matrix of order `d`. -/
def matrixTraceHeight (d H : ℕ) : ℕ :=
  (2 * H) ^ d

/-- Coordinate-height bound for a trace of a product of two order-`d` matrices. -/
def matrixTraceProductHeight (d H K : ℕ) : ℕ :=
  matrixTraceHeight d (matrixProductHeight d H K)

/-- Coordinate-height bound for a shifted Gram residual. -/
def shiftedGramResidualHeight (d HA Hε HQ : ℕ) : ℕ :=
  let Hshift := 2 * (Hε * 1) * (Hε * 1)
  let Hleft := 2 * HA * Hshift
  let Hgram := matrixProductHeight d HQ HQ
  2 * Hleft * Hgram

/-- Coordinate-height bound for the compressed boundary marginal. -/
def compressedBoundaryHeight (a n HZ HA : ℕ) : ℕ :=
  let HZA := matrixProductHeight n HZ HA
  let HZAZ := matrixProductHeight n HZA HZ
  matrixTraceHeight a HZAZ

/-- Coordinate-height bound for the full compressed-boundary equality residual. -/
def compressedBoundaryResidualHeight (a n HZ HA HX HP HN : ℕ) : ℕ :=
  let Hboundary := compressedBoundaryHeight a n HZ HA
  let Hleft := 2 * Hboundary * HX
  let Hright := 2 * HP * HN
  2 * Hleft * Hright

end TNLean.MPS.AreaLaw
