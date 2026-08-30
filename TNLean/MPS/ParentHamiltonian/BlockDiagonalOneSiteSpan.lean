/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BNTBlockDiagonalBoundaryClosing

/-!
# Parent Hamiltonians from a simultaneous one-site span

This file proves that a simultaneous one-letter span of a finite tensor family
splits the periodic chain space of its weighted direct sum. Combining this
splitting with injectivity of the individual tensors gives the nearest-neighbor
parent-Hamiltonian ground-space equation.

The argument follows the restriction and cyclic-cut comparison in
Perez-Garcia--Verstraete--Wolf--Cirac, arXiv:quant-ph/0608197, Theorem 12,
proof lines 1430--1456.

**Scope restriction (common identity coefficients):** The source uses
right-canonical normalization, \(\sum_i A_iA_i^\dagger=1\), and an
adjoint-corrected boundary matrix. The three identity-coefficient lemmas below
instead assume one coefficient family \(c_i\), common to every block, with
\(\sum_i c_iA_i=1\). The subsequent one-site-span results derive such
coefficients from their simultaneous product-algebra span. This replacement
and its boundary-matrix construction are documented in
`docs/paper-gaps/pgvwc07_common_identity_coefficients.tex`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

/-- A full simultaneous one-site span propagates to every positive word
length by concatenation. -/
theorem WordTupleSpanTop.of_one_of_pos
    {A : (j : Fin r) → MPSTensor d (dim j)}
    (hOne : WordTupleSpanTop A 1) {n : ℕ} (hn : 0 < n) :
    WordTupleSpanTop A n := by
  have h := wordTupleSpanTop_add_mul_of_wordTupleSpanTop A hOne hOne (n - 1)
  convert h using 1
  all_goals omega

/-- A full simultaneous one-site span gives a common linear expression for
the identity matrix in every block. -/
theorem WordTupleSpanTop.exists_one_letter_identity_coefficients
    {A : (j : Fin r) → MPSTensor d (dim j)}
    (hOne : WordTupleSpanTop A 1) :
    ∃ c : (Fin 1 → Fin d) → ℂ, ∀ j : Fin r,
      ∑ w, c w • A j (w 0) = 1 := by
  classical
  let I : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ := fun _ ↦ 1
  have hI : I ∈ Submodule.span ℂ (Set.range (wordTuple A 1)) := by
    rw [hOne]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hI
  refine ⟨c, ?_⟩
  intro j
  have hj := congrArg (fun M ↦ M j) hc
  simpa [I, wordTuple, Fintype.linearCombination_apply, List.ofFn_succ] using hj

/-- A common one-letter expression for the block identities replaces the
right-canonical normalization in the restriction argument of
arXiv:quant-ph/0608197, Theorem 12, proof lines 1442--1452. -/
theorem pgvwc07_mem_iSup_groundSpace_of_trace_decomposition_of_identity_coefficients
    (A : (j : Fin r) → MPSTensor d (dim j))
    {n : ℕ} (hSpan : WordTupleSpanTop A n)
    (c : (Fin 1 → Fin d) → ℂ)
    (hId : ∀ j : Fin r, ∑ w, c w • A j (w 0) = 1)
    (C Dmat : (j : Fin r) → Fin d → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hCoeff : ∀ a b : Fin d, ∀ w : Fin n → Fin d,
      (∑ j : Fin r,
        Matrix.trace ((A j b * C j a) * Kraus.evalWord (A j) (List.ofFn w))) =
      (∑ j : Fin r,
        Matrix.trace ((Dmat j b * A j a) * Kraus.evalWord (A j) (List.ofFn w))))
    (ψ : NSiteSpace d (n + 2))
    (hψ : ψ = ∑ j : Fin r, pgvwc07LeftBoundaryComponent (A j) (C j) n) :
    ψ ∈ ⨆ j : Fin r, groundSpace (A j) (n + 2) := by
  classical
  rw [hψ]
  let E : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ :=
    fun j ↦ ∑ w, c w • C j (w 0)
  have hCompat : ∀ j : Fin r, ∀ a b : Fin d,
      A j b * C j a = Dmat j b * A j a :=
    pgvwc07_blockwise_compatibility_of_trace_decomposition A hSpan C Dmat hCoeff
  have hDE : ∀ j : Fin r, ∀ b : Fin d, A j b * E j = Dmat j b := by
    intro j b
    calc
      A j b * E j = ∑ w, c w • (A j b * C j (w 0)) := by
        simp [E, Matrix.mul_sum]
      _ = ∑ w, c w • (Dmat j b * A j (w 0)) := by
        apply Finset.sum_congr rfl
        intro w _
        rw [hCompat j (w 0) b]
      _ = Dmat j b * (∑ w, c w • A j (w 0)) := by
        simp [Matrix.mul_sum]
      _ = Dmat j b := by rw [hId j, Matrix.mul_one]
  have hACE : ∀ j : Fin r, ∀ a b : Fin d,
      A j b * C j a = A j b * E j * A j a := by
    intro j a b
    rw [hCompat j a b, hDE j b]
  exact pgvwc07_sum_leftBoundaryComponents_mem_iSup_groundSpace A C E n hACE

/-- The two one-boundary restrictions imply membership in the next block
ground-space sum when the identity tuple has a common one-letter expansion.
This is the common-identity-coefficient variant of the local step in
arXiv:quant-ph/0608197, Theorem 12, proof lines 1442--1452. -/
theorem pgvwc07_mem_iSup_groundSpace_of_iSup_restrictions_of_identity_coefficients
    (A : (j : Fin r) → MPSTensor d (dim j))
    {n : ℕ} (hSpan : WordTupleSpanTop A n)
    (c : (Fin 1 → Fin d) → ℂ)
    (hId : ∀ j : Fin r, ∑ w, c w • A j (w 0) = 1)
    (ψ : NSiteSpace d (n + 2))
    (hLeft : ∀ b : Fin d,
      restrictLast ψ b ∈ ⨆ j : Fin r, groundSpace (A j) (n + 1))
    (hRight : ∀ a : Fin d,
      restrictFirst ψ a ∈ ⨆ j : Fin r, groundSpace (A j) (n + 1)) :
    ψ ∈ ⨆ j : Fin r, groundSpace (A j) (n + 2) := by
  rcases pgvwc07_trace_decompositions_of_iSup_restrictions A ψ hLeft hRight with
    ⟨C, Dmat, hψ, hCoeff⟩
  exact pgvwc07_mem_iSup_groundSpace_of_trace_decomposition_of_identity_coefficients
    A hSpan c hId C Dmat hCoeff ψ hψ

/-- The PGVWC one-step restriction intersection needs only a common
one-letter expansion of the block identities, rather than right-canonical
normalization. This is a local variant of the intersection step in
arXiv:quant-ph/0608197, Theorem 12, proof lines 1442--1452. -/
theorem pgvwc07_iSup_groundSpace_eq_restriction_intersection_of_identity_coefficients
    (A : (j : Fin r) → MPSTensor d (dim j))
    {n : ℕ} (hSpan : WordTupleSpanTop A n)
    (c : (Fin 1 → Fin d) → ℂ)
    (hId : ∀ j : Fin r, ∑ w, c w • A j (w 0) = 1) :
    ((⨅ b : Fin d,
        (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictLastₗ b)) ⊓
      (⨅ a : Fin d,
        (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictFirstₗ a))) =
      ⨆ j : Fin r, groundSpace (A j) (n + 2) := by
  classical
  ext ψ
  simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
  constructor
  · intro hRestrict
    exact
      pgvwc07_mem_iSup_groundSpace_of_iSup_restrictions_of_identity_coefficients
        A hSpan c hId ψ
          (by simpa [restrictLast] using hRestrict.1)
          (by simpa [restrictFirst] using hRestrict.2)
  · intro hψ
    constructor
    · intro b
      refine Submodule.iSup_induction
        (p := fun j : Fin r ↦ groundSpace (A j) (n + 2))
        (motive := fun φ ↦ restrictLast φ b ∈
          ⨆ j : Fin r, groundSpace (A j) (n + 1))
        (x := ψ) hψ ?_ ?_ ?_
      · intro j φ hφ
        exact Submodule.mem_iSup_of_mem j
          (groundSpace_inLeftGround (A j) (n + 1) hφ b)
      · exact Submodule.zero_mem _
      · intro φ ξ hφ hξ
        exact Submodule.add_mem _ hφ hξ
    · intro a
      refine Submodule.iSup_induction
        (p := fun j : Fin r ↦ groundSpace (A j) (n + 2))
        (motive := fun φ ↦ restrictFirst φ a ∈
          ⨆ j : Fin r, groundSpace (A j) (n + 1))
        (x := ψ) hψ ?_ ?_ ?_
      · intro j φ hφ
        exact Submodule.mem_iSup_of_mem j
          (groundSpace_inRightGround (A j) (n + 1) hφ a)
      · exact Submodule.zero_mem _
      · intro φ ξ hφ hξ
        exact Submodule.add_mem _ hφ hξ

/-- A simultaneous one-site span propagates nearest-neighbor periodic
constraints into the sum of the open-boundary block spaces. This is the
restriction-intersection propagation in arXiv:quant-ph/0608197, Theorem 12,
proof lines 1430--1452. -/
theorem chainGroundSpace_toTensorFromBlocks_le_iSup_groundSpace_of_wordTupleSpanTop_one
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j : Fin r, μ j ≠ 0)
    (hOne : WordTupleSpanTop A 1) [NeZero d]
    {N : ℕ} (hN : 2 < N) :
    chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) 2 N ≤
      ⨆ j : Fin r, groundSpace (A j) N := by
  classical
  obtain ⟨c, hId⟩ := hOne.exists_one_letter_identity_coefficients
  apply chainGroundSpace_toTensorFromBlocks_le_iSup_groundSpace
    μ A hμ (by omega) (by omega) (by omega)
  intro M hM
  obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le hM
  have hMq : M = q + 2 := by omega
  clear hq
  subst M
  have hSpan : WordTupleSpanTop A (q + 1) :=
    hOne.of_one_of_pos (by omega)
  have hstep :=
    pgvwc07_iSup_groundSpace_eq_restriction_intersection_of_identity_coefficients
      A hSpan c hId
  simpa [Nat.add_assoc] using hstep

/-- A nearest-neighbor chain vector has block-diagonal open-boundary matrices
when the simultaneous one-site word tuples span the product algebra. This is
the block-boundary decomposition in arXiv:quant-ph/0608197, Theorem 12, proof
lines 1430--1452. -/
theorem exists_blockDiagonal_boundary_of_chainGroundSpace_of_wordTupleSpanTop_one
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j : Fin r, μ j ≠ 0)
    (hOne : WordTupleSpanTop A 1) [NeZero d]
    {N : ℕ} (hN : 2 < N) {ψ : NSiteSpace d N}
    (hψ : ψ ∈ chainGroundSpace
      (toTensorFromBlocks (d := d) (μ := μ) A) 2 N) :
    ∃ X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
      ψ = groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
        ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv)
          (Matrix.blockDiagonal' X)) := by
  have hOpen : ψ ∈ ⨆ j : Fin r, groundSpace (A j) N :=
    chainGroundSpace_toTensorFromBlocks_le_iSup_groundSpace_of_wordTupleSpanTop_one
      μ A hμ hOne hN hψ
  obtain ⟨X, hX, _⟩ :=
    BlockSumGroundSpace.exists_blockDiagonal_boundary_of_mem_iSup_groundSpace
      μ A hμ hOpen
  exact ⟨X, hX⟩

/-- A global one-site change of cut closes the block-diagonal boundary
matrices of a nearest-neighbor chain vector. This is the boundary-closing step
in arXiv:quant-ph/0608197, Theorem 12, proof lines 1454--1456. -/
theorem exists_blockDiagonal_boundary_chainGroundSpace_of_wordTupleSpanTop_one
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j : Fin r, μ j ≠ 0)
    (hOne : WordTupleSpanTop A 1) [NeZero d]
    {N : ℕ} (hN : 2 < N) {ψ : NSiteSpace d N}
    (hψ : ψ ∈ chainGroundSpace
      (toTensorFromBlocks (d := d) (μ := μ) A) 2 N) :
    ∃ X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
      ψ = groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
        ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv)
          (Matrix.blockDiagonal' X)) ∧
      ∀ j : Fin r,
        groundSpaceMap (A j) N ((μ j) ^ N • X j) ∈
          chainGroundSpace (A j) 2 N := by
  classical
  obtain ⟨X, hψX⟩ :=
    exists_blockDiagonal_boundary_of_chainGroundSpace_of_wordTupleSpanTop_one
      μ A hμ hOne hN hψ
  let s : Fin N := ⟨N - 1, by omega⟩
  have hTranslate :
      cyclicTranslateState s ψ ∈
        chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) 2 N :=
    cyclicTranslateState_mem_chainGroundSpace
      (toTensorFromBlocks (d := d) (μ := μ) A) (by omega) (by omega) s hψ
  obtain ⟨Y, hψY⟩ :=
    exists_blockDiagonal_boundary_of_chainGroundSpace_of_wordTupleSpanTop_one
      μ A hμ hOne hN hTranslate
  have hXsum :
      ψ = ∑ j : Fin r, groundSpaceMap (A j) N ((μ j) ^ N • X j) := by
    calc
      ψ = groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
          ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv)
            (Matrix.blockDiagonal' X)) := hψX
      _ = ∑ j : Fin r, groundSpaceMap (A j) N ((μ j) ^ N • X j) := by
        rw [BlockSumGroundSpace.groundSpaceMap_toTensorFromBlocks_eq_sum_blockDiagonal]
  have hYsum :
      cyclicTranslateState s ψ =
        ∑ j : Fin r, groundSpaceMap (A j) N ((μ j) ^ N • Y j) := by
    calc
      cyclicTranslateState s ψ =
          groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) N
            ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv)
              (Matrix.blockDiagonal' Y)) := hψY
      _ = ∑ j : Fin r, groundSpaceMap (A j) N ((μ j) ^ N • Y j) := by
        rw [BlockSumGroundSpace.groundSpaceMap_toTensorFromBlocks_eq_sum_blockDiagonal]
  have hSplit : N - 1 + 1 = N := by omega
  have hSumTranslate :
      cyclicTranslateState s
          (∑ j : Fin r, groundSpaceMap (A j) N ((μ j) ^ N • X j)) =
        ∑ j : Fin r, groundSpaceMap (A j) N ((μ j) ^ N • Y j) := by
    rw [← hXsum]
    exact hYsum
  have hLongSpan : WordTupleSpanTop A (N - 1) :=
    hOne.of_one_of_pos (by omega)
  have hIntertwine :
      ∀ (α : Fin 1 → Fin d) (j : Fin r),
        ((μ j) ^ N • X j) * Kraus.evalWord (A j) (List.ofFn α) =
          Kraus.evalWord (A j) (List.ofFn α) * ((μ j) ^ N • Y j) := by
    apply block_boundary_intertwines_of_cyclicTranslate_sum_groundSpaceMap_eq_of_add_eq
      A hSplit (by omega) hLongSpan
        (fun j ↦ (μ j) ^ N • X j) (fun j ↦ (μ j) ^ N • Y j)
    simpa only [s] using hSumTranslate
  have hBlk : ∀ j : Fin r, Kraus.IsNBlkInjective (A j) 1 := fun j ↦
    Kraus.isNBlkInjective_one_of_isInjective (hOne.isInjective_one j)
  have hComm : ∀ j : Fin r, ∀ a : Fin d,
      ((μ j) ^ N • X j) * A j a = A j a * ((μ j) ^ N • X j) := by
    intro j
    exact (boundary_eq_and_commutes_of_isNBlkInjective_of_intertwines
      (hBlk j) (by omega) ((μ j) ^ N • X j) ((μ j) ^ N • Y j)
      (fun α ↦ hIntertwine α j)).2
  have hCommWord : ∀ j : Fin r, ∀ w : List (Fin d),
      ((μ j) ^ N • X j) * Kraus.evalWord (A j) w =
        Kraus.evalWord (A j) w * ((μ j) ^ N • X j) := by
    intro j w
    induction w with
    | nil => simp [Kraus.evalWord_nil]
    | cons a w ih =>
        rw [Kraus.evalWord_cons, ← Matrix.mul_assoc, hComm j a, Matrix.mul_assoc, ih,
          ← Matrix.mul_assoc]
  refine ⟨X, hψX, ?_⟩
  apply blockDiagonal_boundary_component_chainGroundSpace_of_boundary_identities
    μ A (by omega) (by omega) X
  intro j i _τ _hi
  refine ⟨(μ j) ^ N • X j, ?_⟩
  intro β
  exact hCommWord j (List.ofFn β)

/-- A simultaneous one-site product span splits the nearest-neighbor periodic
chain space into the periodic chain spaces of the blocks. This is the
multiplicity-one distinct-block specialization of arXiv:quant-ph/0608197,
Theorem 12, proof lines 1430--1456. -/
theorem chainGroundSpace_toTensorFromBlocks_eq_iSup_of_wordTupleSpanTop_one
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j : Fin r, μ j ≠ 0)
    (hOne : WordTupleSpanTop A 1) [NeZero d]
    {N : ℕ} (hN : 2 < N) :
    chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) 2 N =
      ⨆ j : Fin r, chainGroundSpace (A j) 2 N := by
  have hClose :
      chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) 2 N ≤
        ⨆ j : Fin r, chainGroundSpace (A j) 2 N :=
    chainGroundSpace_toTensorFromBlocks_le_iSup_of_blockDiagonal_boundary_groundSpaceMap
      μ A (fun ψ hψ ↦
        exists_blockDiagonal_boundary_chainGroundSpace_of_wordTupleSpanTop_one
          μ A hμ hOne hN hψ)
  exact chainGroundSpace_toTensorFromBlocks_eq_iSup_chainGroundSpace_of_boundary_closing
    μ A hμ (by omega) (by omega) hClose

/-- A simultaneous one-letter span gives the nearest-neighbor
parent-Hamiltonian ground-space equation for a weighted direct sum of the
component tensors.

The periodic-chain splitting follows from the cyclic-cut comparison above,
while the one-letter span makes each component injective. This is the
parent-Hamiltonian consequence of the block-injective argument in
arXiv:quant-ph/0608197, Theorem 12, proof lines 1430--1456. -/
theorem hasParentHamiltonianGroundSpaceSpanning_toTensorFromBlocks_of_wordTupleSpanTop_one
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j : Fin r, μ j ≠ 0)
    (hOne : WordTupleSpanTop A 1) [NeZero d] [∀ j, NeZero (dim j)] :
    HasParentHamiltonianGroundSpaceSpanning
      (toTensorFromBlocks (d := d) (μ := μ) A) 2 A := by
  apply hasParentHamiltonianGroundSpaceSpanning_toTensorFromBlocks_of_chain_eq_iSup_chain
    μ A hμ
  · intro N hN
    exact chainGroundSpace_toTensorFromBlocks_eq_iSup_of_wordTupleSpanTop_one
      μ A hμ hOne hN
  · intro N _ j
    exact chainGroundSpace_eq_mpvSubmodule
      (hOne.isInjective_one j) (by omega) (by omega) (by omega)

end MPSTensor
