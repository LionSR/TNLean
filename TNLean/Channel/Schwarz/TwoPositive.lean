/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Basic
import TNLean.Channel.Schwarz.KadisonSchwarz
import TNLean.Channel.Schwarz.PositiveMapProperties
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Matrix.Composition

/-!
# 2-Positive maps and the generalized Kadison–Schwarz inequality

This file defines **n-positive** and **2-positive** maps and proves that the
Kadison–Schwarz inequality holds for **unital 2-positive maps**, generalizing
the existing result which is restricted to completely positive maps.

## Main definitions

* `IsNPositiveMap` — a linear map `E` is n-positive if `E ⊗ id_n` is positive
* `Is2PositiveMap` — 2-positive maps (the case n = 2)

## Main results

* `IsCPMap.isNPositiveMap` — CP maps are n-positive for all n
* `IsCPMap.is2PositiveMap` — CP maps are 2-positive
* `kadison_schwarz_2positive` — Kadison–Schwarz for unital 2-positive maps

## Mathematical content

The hierarchy of positivity conditions is:

  positive ⊇ 2-positive ⊇ 3-positive ⊇ ⋯ ⊇ completely positive

The Kadison–Schwarz inequality `E(X†X) ≥ E(X)†E(X)` for **unital** maps
requires only **2-positivity**, not complete positivity. This was established
by Kadison (1952) and Choi (1974). The proof in `KadisonSchwarz.lean` already
uses only 2-positivity implicitly — it applies `E ⊗ id₂` to a 2×2 block
matrix — but the theorem is stated for CP maps via Kraus operators.

This file makes the 2-positivity hypothesis explicit.

## Strengthening relative to the literature

The existing `kadison_schwarz` in `KadisonSchwarz.lean` requires a Kraus
representation (complete positivity). The generalized version here applies
to the broader class of 2-positive maps, which includes some positive maps
that are not CP. For example, the transpose map on 2×2 matrices is positive
but not 2-positive, so it correctly fails the Kadison–Schwarz inequality.
More generally, there exist 2-positive maps that are not completely positive,
so the theorem here applies strictly beyond the CP case.

## References

* [Kadison, *A generalized Schwarz inequality and algebraic invariants for
  operator algebras*, Ann. Math. 56 (1952)]
* [Choi, *A Schwarz inequality for positive linear maps on C*-algebras*,
  Illinois J. Math. 18 (1974)]
* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, §5.1]
* [Størmer, *Positive linear maps of operator algebras*, Springer (2013)]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

private lemma posSemidef_fromBlocks_diag {m o : Type*}
    [Fintype m] [Fintype o] [DecidableEq m] [DecidableEq o]
    {A : Matrix m m ℂ} {D : Matrix o o ℂ}
    (hA : A.PosSemidef) (hD : D.PosSemidef) :
    (Matrix.fromBlocks A 0 0 D : Matrix (m ⊕ o) (m ⊕ o) ℂ).PosSemidef := by
  letI : CStarAlgebra (Matrix m m ℂ) :=
    { toNormedRing := Matrix.instL2OpNormedRing
      toStarRing := inferInstance
      toCompleteSpace := inferInstance
      toCStarRing := Matrix.instCStarRing
      toNormedAlgebra := Matrix.instL2OpNormedAlgebra
      toStarModule := inferInstance }
  letI : CStarAlgebra (Matrix o o ℂ) :=
    { toNormedRing := Matrix.instL2OpNormedRing
      toStarRing := inferInstance
      toCompleteSpace := inferInstance
      toCStarRing := Matrix.instCStarRing
      toNormedAlgebra := Matrix.instL2OpNormedAlgebra
      toStarModule := inferInstance }
  obtain ⟨CA, hCA⟩ := CStarAlgebra.nonneg_iff_eq_mul_star_self.mp
    ((Matrix.nonneg_iff_posSemidef).mpr hA)
  obtain ⟨CD, hCD⟩ := CStarAlgebra.nonneg_iff_eq_mul_star_self.mp
    ((Matrix.nonneg_iff_posSemidef).mpr hD)
  have hCA' : A = CA * CAᴴ := by
    simpa [Matrix.star_eq_conjTranspose] using hCA
  have hCD' : D = CD * CDᴴ := by
    simpa [Matrix.star_eq_conjTranspose] using hCD
  let C : Matrix (m ⊕ o) (m ⊕ o) ℂ := Matrix.fromBlocks CA 0 0 CD
  have hC : Matrix.fromBlocks A 0 0 D = C * Cᴴ := by
    simp [C, hCA', hCD', Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose]
  rw [hC]
  exact Matrix.posSemidef_self_mul_conjTranspose C

private lemma posSemidef_reindex {m o : Type*}
    [Fintype m] [Fintype o] {M : Matrix m m ℂ}
    (hM : M.PosSemidef) (e : m ≃ o) :
    (Matrix.reindex e e M).PosSemidef := by
  simpa [Matrix.reindex_apply] using hM.submatrix e.symm

private noncomputable def finSuccBlockEquiv (α : Type*) (k : ℕ) :
    α × Fin (k + 1) ≃ (α × Fin k) ⊕ α :=
  (((Equiv.prodCongr (Equiv.refl α)
      ((finSumFinEquiv : Fin k ⊕ Fin 1 ≃ Fin (k + 1)).symm)).trans
    (Equiv.prodSumDistrib α (Fin k) (Fin 1))).trans
    (Equiv.sumCongr (Equiv.refl _) (Equiv.prodUnique α (Fin 1))))

@[simp] private theorem finSuccBlockEquiv_apply_castSucc {α : Type*} (k : ℕ)
    (a : α) (i : Fin k) :
    finSuccBlockEquiv α k (a, Fin.castSucc i) = Sum.inl (a, i) := by
  change Sum.map id Prod.fst
      ((Equiv.prodSumDistrib α (Fin k) (Fin 1))
        (a, ((finSumFinEquiv : Fin k ⊕ Fin 1 ≃ Fin (k + 1)).symm (Fin.castSucc i)))) =
      Sum.inl (a, i)
  rw [finSumFinEquiv_symm_apply_castSucc]
  simp

@[simp] private theorem finSuccBlockEquiv_apply_last {α : Type*} (k : ℕ) (a : α) :
    finSuccBlockEquiv α k (a, Fin.last k) = Sum.inr a := by
  change Sum.map id Prod.fst
      ((Equiv.prodSumDistrib α (Fin k) (Fin 1))
        (a, ((finSumFinEquiv : Fin k ⊕ Fin 1 ≃ Fin (k + 1)).symm (Fin.last k)))) =
      Sum.inr a
  rw [finSumFinEquiv_symm_last]
  simp

private noncomputable def finTwoBlockEquiv (α : Type*) : α × Fin 2 ≃ α ⊕ α :=
  (finSuccBlockEquiv α 1).trans
    (Equiv.sumCongr (Equiv.prodUnique α (Fin 1)) (Equiv.refl α))

@[simp] private theorem finTwoBlockEquiv_apply_zero {α : Type*} (a : α) :
    finTwoBlockEquiv α (a, 0) = Sum.inl a := by
  change Sum.map Prod.fst id ((finSuccBlockEquiv α 1) (a, 0)) = Sum.inl a
  rw [show (0 : Fin 2) = Fin.castSucc (0 : Fin 1) by rfl]
  rw [finSuccBlockEquiv_apply_castSucc (α := α) 1 a (0 : Fin 1)]
  simp

@[simp] private theorem finTwoBlockEquiv_apply_one {α : Type*} (a : α) :
    finTwoBlockEquiv α (a, Fin.last 1) = Sum.inr a := by
  change Sum.map Prod.fst id ((finSuccBlockEquiv α 1) (a, Fin.last 1)) = Sum.inr a
  rw [finSuccBlockEquiv_apply_last (α := α) 1 a]
  simp

@[simp] private theorem finTwoBlockEquiv_apply_one' {α : Type*} (a : α) :
    finTwoBlockEquiv α (a, 1) = Sum.inr a := by
  simpa using finTwoBlockEquiv_apply_one (α := α) a

@[simp] private theorem finTwoBlockEquiv_symm_apply_left {α : Type*} (a : α) :
    (finTwoBlockEquiv α).symm (Sum.inl a) = (a, 0) := by
  apply (finTwoBlockEquiv α).injective
  simp

@[simp] private theorem finTwoBlockEquiv_symm_apply_right {α : Type*} (a : α) :
    (finTwoBlockEquiv α).symm (Sum.inr a) = (a, 1) := by
  apply (finTwoBlockEquiv α).injective
  simp

private theorem IsPositiveMap.map_conjTranspose'
    {m : Type*} [Fintype m] [DecidableEq m]
    {T : Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ} (hT : IsPositiveMap T) (A : Matrix m m ℂ) :
    T Aᴴ = (T A)ᴴ := by
  let B : Matrix m m ℂ := (1 / 2 : ℝ) • (A + Aᴴ)
  let C : Matrix m m ℂ := (1 / 2 : ℝ) • (Complex.I • (Aᴴ - A))
  have hB : B.IsHermitian := by
    ext i j
    simp [B, add_comm]
  have hC : C.IsHermitian := by
    ext i j
    simp [C, sub_eq_add_neg, add_comm]
  have hmulI (z : ℂ) : Complex.I * ((2 : ℂ)⁻¹ * (Complex.I * z)) = -((2 : ℂ)⁻¹ * z) := by
    calc
      Complex.I * ((2 : ℂ)⁻¹ * (Complex.I * z)) = (Complex.I * Complex.I) * ((2 : ℂ)⁻¹ * z) := by
        ring
      _ = -((2 : ℂ)⁻¹ * z) := by norm_num [Complex.I_sq]
  have hIC : Complex.I • C = (1 / 2 : ℝ) • (A - Aᴴ) := by
    ext i j
    simp [C, sub_eq_add_neg, mul_add, hmulI, add_comm]
  have hNegIC : -(Complex.I • C) = (1 / 2 : ℝ) • (Aᴴ - A) := by
    ext i j
    simp [C, sub_eq_add_neg, hmulI, add_comm]
  have hA_decomp : A = B + Complex.I • C := by
    rw [hIC]
    ext i j
    simp [B, sub_eq_add_neg]
    ring
  have hAstar_decomp : Aᴴ = B - Complex.I • C := by
    rw [sub_eq_add_neg, hNegIC]
    ext i j
    simp [B, sub_eq_add_neg]
    ring
  have hTB : (T B).IsHermitian := hT.map_isHermitian hB
  have hTC : (T C).IsHermitian := hT.map_isHermitian hC
  have hTA_decomp : T A = T B + Complex.I • T C := by
    rw [hA_decomp]
    simp
  rw [hAstar_decomp, hTA_decomp]
  simp [sub_eq_add_neg, hTB.eq, hTC.eq, Matrix.conjTranspose_add, Matrix.conjTranspose_smul]

/-! ## Definitions of n-positivity -/

/-- A linear map `E : M_n(ℂ) → M_n(ℂ)` is **k-positive** if the ampliation
`E ⊗ id_k : M_n(ℂ) ⊗ M_k(ℂ) → M_n(ℂ) ⊗ M_k(ℂ)` is a positive map.

We represent `M_n(ℂ) ⊗ M_k(ℂ)` as `M_{n×k}(ℂ)` via the Kronecker product
identification, and the ampliation acts blockwise:
`(E ⊗ id_k)(X)_{ij} = E(X_{ij})` for block indices `i, j ∈ Fin k`.

**Encoding choice**: We use a blockwise `Matrix.of` encoding rather than
`TensorProduct` because it avoids the overhead of tensor product API and
matches the block-matrix arguments used in `KadisonSchwarz.lean`. A
`TensorProduct`-based definition would be closer to the mathematical
definition but would require additional infrastructure to connect with the
existing Kraus-based proofs.

**Index convention**: We use `(n × Fin k)` indexing where `n` is the inner
(algebra) index and `Fin k` is the outer (ampliation) index. This is the
transpose of the standard Kronecker convention `(Fin k × n)`, but is
mathematically equivalent (PSD-ness is invariant under simultaneous row/column
permutation). -/
def IsNPositiveMap (k : ℕ) (E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) : Prop :=
  ∀ X : Matrix (n × Fin k) (n × Fin k) ℂ,
    X.PosSemidef →
    (Matrix.of fun (ip : n × Fin k) (jq : n × Fin k) =>
      (E (Matrix.of fun i j => X (i, ip.2) (j, jq.2))) ip.1 jq.1).PosSemidef

/-- A linear map is **2-positive** if `E ⊗ id₂` is positive. -/
def Is2PositiveMap (E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) : Prop :=
  IsNPositiveMap 2 E

/-- A completely positive map is n-positive for every `n`.

This follows immediately from the definition: CP maps have Kraus representations,
and `E ⊗ id_k` applied to a PSD matrix yields a PSD matrix (by the same
Kraus-based argument as `IsCPMap.isPositiveMap`). -/
theorem IsCPMap.isNPositiveMap {E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
    (hCP : IsCPMap E) (k : ℕ) : IsNPositiveMap k E := by
  classical
  intro X hX
  obtain ⟨r, K, hK⟩ := hCP
  let e : n × Fin k ≃ Fin k × n := Equiv.prodComm n (Fin k)
  let Xswap : Matrix (Fin k × n) (Fin k × n) ℂ := Matrix.reindex e e X
  have hXswap : Xswap.PosSemidef := posSemidef_reindex hX e
  let Xblk : Matrix (Fin k) (Fin k) (Matrix n n ℂ) :=
    (Matrix.compRingEquiv (Fin k) n ℂ).symm Xswap
  let D : Fin r → Matrix (Fin k) (Fin k) (Matrix n n ℂ) :=
    fun a => Matrix.diagonal fun _ => K a
  let Yblk : Matrix (Fin k) (Fin k) (Matrix n n ℂ) :=
    ∑ a, D a * Xblk * (D a)ᴴ
  let F := Matrix.compRingEquiv (Fin k) n ℂ
  have hcomp_conjTranspose (M : Matrix (Fin k) (Fin k) (Matrix n n ℂ)) :
      F Mᴴ = (F M)ᴴ := by
    ext ip jq
    rcases ip with ⟨p, i⟩
    rcases jq with ⟨q, j⟩
    rfl
  have hYswap :
      (F Yblk).PosSemidef := by
    rw [show F Yblk = ∑ a, F (D a * Xblk * (D a)ᴴ) by
      simp [Yblk]]
    refine Matrix.posSemidef_sum (s := Finset.univ)
      (x := fun a => F (D a * Xblk * (D a)ᴴ)) ?_
    intro a _
    let L : Matrix (Fin k × n) (Fin k × n) ℂ := F (D a)
    have hL :
        F (D a * Xblk * (D a)ᴴ) = L * Xswap * Lᴴ := by
      calc
        F (D a * Xblk * (D a)ᴴ) = F (D a * Xblk) * F ((D a)ᴴ) := by
          rw [F.map_mul]
        _ = (F (D a) * F Xblk) * (F (D a))ᴴ := by
          rw [F.map_mul, hcomp_conjTranspose]
        _ = L * (Xswap * Lᴴ) := by simp [F, L, Xblk, Matrix.mul_assoc]
        _ = L * Xswap * Lᴴ := by simp [Matrix.mul_assoc]
    change (F (D a * Xblk * (D a)ᴴ)).PosSemidef
    simpa [hL] using hXswap.mul_mul_conjTranspose_same (B := L)
  have hDterm (a : Fin r) :
      D a * Xblk * (D a)ᴴ = Matrix.of fun p q => K a * Xblk p q * (K a)ᴴ := by
    ext p q i j
    simp [D, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.mul_assoc, Matrix.star_eq_conjTranspose]
  have hYblk :
      Yblk = Matrix.of fun p q => E (Xblk p q) := by
    ext p q i j
    change Yblk p q i j = E (Xblk p q) i j
    rw [hK (Xblk p q)]
    simp [Yblk, hDterm, Matrix.sum_apply]
  have hXblk_apply (p q : Fin k) :
      Xblk p q = Matrix.of fun i j => X (i, p) (j, q) := by
    ext i j
    simp [Xblk, Xswap, e, Matrix.reindex_apply]
  convert posSemidef_reindex hYswap e.symm using 1
  ext ip jq
  rw [hYblk]
  simp [Matrix.reindex_apply, e]
  change E (Matrix.of fun i j => X (i, ip.2) (j, jq.2)) ip.1 jq.1 =
      E (Xblk ip.2 jq.2) ip.1 jq.1
  rw [hXblk_apply ip.2 jq.2]

/-- **Monotonicity sanity check**: `(k+1)`-positive implies `k`-positive.

This is a basic structural property of the n-positivity hierarchy. If this
were not provable, the definition of `IsNPositiveMap` would be wrong.
The proof embeds `M_n ⊗ M_k ↪ M_n ⊗ M_{k+1}` via padding with zeros. -/
theorem IsNPositiveMap.mono {E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} {k : ℕ}
    (h : IsNPositiveMap (k + 1) E) : IsNPositiveMap k E := by
  intro X hX
  -- Embed X into the larger space (n × Fin (k+1)) by padding with zeros
  let X' : Matrix (n × Fin (k + 1)) (n × Fin (k + 1)) ℂ :=
    Matrix.of fun ip jq =>
      if h₁ : ip.2.val < k then
        if h₂ : jq.2.val < k then
          X (ip.1, ⟨ip.2.val, h₁⟩) (jq.1, ⟨jq.2.val, h₂⟩)
        else 0
      else 0
  -- X' is PSD: for any v, v†X'v = w†Xw where w is the restriction of v
  have hX' : X'.PosSemidef := by
    let e := finSuccBlockEquiv n k
    have hEq :
        X' = Matrix.reindex e.symm e.symm
          (Matrix.fromBlocks X 0 0 (0 : Matrix n n ℂ)) := by
      ext ip jq
      rcases ip with ⟨i, a⟩
      rcases jq with ⟨j, b⟩
      by_cases ha : a.val < k
      · have ha' : a = Fin.castSucc ⟨a.val, ha⟩ := by
          apply Fin.ext
          simp
        by_cases hb : b.val < k
        · have hb' : b = Fin.castSucc ⟨b.val, hb⟩ := by
            apply Fin.ext
            simp
          have hea : e (i, a) = Sum.inl (i, ⟨a.val, ha⟩) := by
            cases ha'
            exact finSuccBlockEquiv_apply_castSucc (α := n) k i ⟨a.val, ha⟩
          have heb : e (j, b) = Sum.inl (j, ⟨b.val, hb⟩) := by
            cases hb'
            exact finSuccBlockEquiv_apply_castSucc (α := n) k j ⟨b.val, hb⟩
          simp [Matrix.reindex_apply, X', hea, heb, ha, hb]
        · have hb' : b = Fin.last k := by
            apply Fin.ext
            exact le_antisymm (Nat.le_of_lt_succ b.isLt) (not_lt.mp hb)
          have hea : e (i, a) = Sum.inl (i, ⟨a.val, ha⟩) := by
            cases ha'
            exact finSuccBlockEquiv_apply_castSucc (α := n) k i ⟨a.val, ha⟩
          have heb : e (j, b) = Sum.inr j := by
            cases hb'
            exact finSuccBlockEquiv_apply_last (α := n) k j
          simp [Matrix.reindex_apply, X', hea, heb, ha, hb]
      · have ha' : a = Fin.last k := by
          apply Fin.ext
          exact le_antisymm (Nat.le_of_lt_succ a.isLt) (not_lt.mp ha)
        by_cases hb : b.val < k
        · have hb' : b = Fin.castSucc ⟨b.val, hb⟩ := by
            apply Fin.ext
            simp
          have hea : e (i, a) = Sum.inr i := by
            cases ha'
            exact finSuccBlockEquiv_apply_last (α := n) k i
          have heb : e (j, b) = Sum.inl (j, ⟨b.val, hb⟩) := by
            cases hb'
            exact finSuccBlockEquiv_apply_castSucc (α := n) k j ⟨b.val, hb⟩
          simp [Matrix.reindex_apply, X', hea, heb, ha]
        · have hb' : b = Fin.last k := by
            apply Fin.ext
            exact le_antisymm (Nat.le_of_lt_succ b.isLt) (not_lt.mp hb)
          have hea : e (i, a) = Sum.inr i := by
            cases ha'
            exact finSuccBlockEquiv_apply_last (α := n) k i
          have heb : e (j, b) = Sum.inr j := by
            cases hb'
            exact finSuccBlockEquiv_apply_last (α := n) k j
          simp [Matrix.reindex_apply, X', hea, heb, ha]
    rw [hEq]
    exact posSemidef_reindex
      (posSemidef_fromBlocks_diag hX (Matrix.PosSemidef.zero (n := n) (R := ℂ))) e.symm
  -- Apply (k+1)-positivity
  have hY' := h X' hX'
  -- Extract the k-block from the result
  let emb : n × Fin k → n × Fin (k + 1) := fun ip => (ip.1, Fin.castSucc ip.2)
  convert hY'.submatrix emb using 1
  ext ip jq
  simp [emb, X']

/-- CP maps are 2-positive. -/
theorem IsCPMap.is2PositiveMap {E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
    (hCP : IsCPMap E) : Is2PositiveMap E :=
  hCP.isNPositiveMap 2

/-- 2-positive maps are positive.

Apply the definition with `k = 1` embedded into `k = 2`: given PSD `X`,
embed it as `diag(X, 0)` in `M_n ⊗ M_2`, apply 2-positivity to get PSD
output, then extract the (0,0)-block which equals `E(X)`. -/
theorem Is2PositiveMap.isPositiveMap {E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
    (h : Is2PositiveMap E) : IsPositiveMap E := by
  intro X hX
  -- Embed X as the (0,0) block of a (n × Fin 2) × (n × Fin 2) PSD matrix
  let X' : Matrix (n × Fin 2) (n × Fin 2) ℂ :=
    Matrix.of fun ip jq =>
      if ip.2 = 0 ∧ jq.2 = 0 then X ip.1 jq.1 else 0
  have hX' : X'.PosSemidef := by
    let e := finTwoBlockEquiv n
    have hEq :
        X' = Matrix.reindex e.symm e.symm
          (Matrix.fromBlocks X 0 0 (0 : Matrix n n ℂ)) := by
      ext ip jq
      rcases ip with ⟨i, a⟩
      rcases jq with ⟨j, b⟩
      fin_cases a <;> fin_cases b <;> simp [Matrix.reindex_apply, X', e]
    rw [hEq]
    exact posSemidef_reindex
      (posSemidef_fromBlocks_diag hX (Matrix.PosSemidef.zero (n := n) (R := ℂ))) e.symm
  -- Apply 2-positivity to X'
  have hY' := h X' hX'
  -- The (0,0)-block of the result is E(X), which is PSD as a principal submatrix
  let emb : n → n × Fin 2 := fun i => (i, 0)
  simpa [emb, X'] using hY'.submatrix emb

/-! ## Kadison–Schwarz for 2-positive maps -/

/-- A linear map is **unital** if `E(I) = I`.

This is intentionally separate from `KadisonSchwarz.IsUnitalKraus` (which
requires `∑ Kᵢ Kᵢ† = I` for a Kraus family): `IsUnitalMap` applies to any
linear map without requiring a Kraus decomposition, which is the right
generality for 2-positive maps that may not be CP.

Note: placed in the `KadisonSchwarz` namespace to avoid clashes with other
unitality notions in the codebase. -/
def KadisonSchwarz.IsUnitalMap (E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) : Prop :=
  E 1 = 1

/-- **Kadison–Schwarz inequality for unital 2-positive maps.**

For any **unital 2-positive** map `E`, we have
`E(X† X) - E(X)† E(X) ≥ 0` (positive semidefinite).

This generalizes the existing `kadison_schwarz` (which requires a Kraus
representation, i.e., complete positivity) to the natural level of
generality: 2-positivity suffices.

**Proof sketch** (following Choi 1974): Apply `E ⊗ id₂` to the PSD block
matrix `P = [[X†X, X†], [X, I]]`, which is PSD as `P = v v†` with
`v = [X†, I]ᵀ`. Since `E ⊗ id₂` preserves PSD-ness (by 2-positivity), the
result `[[E(X†X), E(X†)], [E(X), E(I)]] = [[E(X†X), E(X)†], [E(X), I]]`
is PSD. The Schur complement of the (2,2)-block `I` gives the result.

This is exactly the same argument as in `KadisonSchwarz.lean`, but the
hypothesis is weakened from "Kraus representation exists" to "2-positive". -/
theorem kadison_schwarz_2positive
    (E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (h2pos : Is2PositiveMap E)
    (h_unital : KadisonSchwarz.IsUnitalMap E)
    (X : Matrix n n ℂ) :
    (E (Xᴴ * X) - (E X)ᴴ * E X).PosSemidef := by
  let e := finTwoBlockEquiv n
  let P : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
    Matrix.fromBlocks (Xᴴ * X) Xᴴ X 1
  have hP : P.PosSemidef := by
    let A : Matrix (n ⊕ n) (n ⊕ Fin 0) ℂ :=
      Matrix.fromBlocks Xᴴ 0 1 0
    simpa [A, P, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose]
      using Matrix.posSemidef_self_mul_conjTranspose A
  let P' : Matrix (n × Fin 2) (n × Fin 2) ℂ := Matrix.reindex e.symm e.symm P
  have hP' : P'.PosSemidef := posSemidef_reindex hP e.symm
  have hY' := h2pos P' hP'
  have hPos : IsPositiveMap E := h2pos.isPositiveMap
  have hBlock :
      Matrix.reindex e e
        (Matrix.of fun (ip : n × Fin 2) (jq : n × Fin 2) =>
          (E (Matrix.of fun i j => P' (i, ip.2) (j, jq.2))) ip.1 jq.1) =
        Matrix.fromBlocks (E (Xᴴ * X)) ((E X)ᴴ)
          (((E X)ᴴ)ᴴ) (1 : Matrix n n ℂ) := by
    ext ip jq
    rcases ip with i | i <;> rcases jq with j | j
    · change E (Matrix.of fun i' j' => (Xᴴ * X) i' j') i j = E (Xᴴ * X) i j
      rfl
    · change E (Matrix.of fun i' j' => (starRingEnd ℂ) (X j' i')) i j = (starRingEnd ℂ) (E X j i)
      rw [show (Matrix.of fun i' j' => (starRingEnd ℂ) (X j' i')) = Xᴴ by
        ext a b
        rfl]
      simpa [Matrix.conjTranspose_apply] using
        congr_fun (congr_fun (IsPositiveMap.map_conjTranspose' hPos X) i) j
    · have hId : (Matrix.of fun i' j' => X i' j') = X := by
        ext a b
        rfl
      simp [Matrix.reindex_apply, P', P, e, hId]
    · change E (Matrix.of fun i' j' => (1 : Matrix n n ℂ) i' j') i j = (1 : Matrix n n ℂ) i j
      simpa [KadisonSchwarz.IsUnitalMap] using congr_fun (congr_fun h_unital i) j
  have hBlockPsD :
      (Matrix.fromBlocks (E (Xᴴ * X)) ((E X)ᴴ)
        (((E X)ᴴ)ᴴ) (1 : Matrix n n ℂ)).PosSemidef := by
    simpa [hBlock] using posSemidef_reindex hY' e
  haveI : Invertible (1 : Matrix n n ℂ) := invertibleOne
  simpa [inv_one, Matrix.mul_assoc, conjTranspose_conjTranspose] using
    (Matrix.PosDef.fromBlocks₂₂ (A := E (Xᴴ * X)) (B := (E X)ᴴ)
      (D := (1 : Matrix n n ℂ)) Matrix.PosDef.one).1 hBlockPsD

/-- **Placeholder**: once `kadison_schwarz_2positive` is proved, the existing
Kraus-based KS inequality becomes a corollary via:
  `IsCPMap → Is2PositiveMap → kadison_schwarz_2positive`

Currently this just delegates to the existing direct proof. When the sorry in
`kadison_schwarz_2positive` is filled, this should be rerouted through the
2-positive path to demonstrate the logical subsumption. -/
theorem kadison_schwarz_from_2positive
    {d D : ℕ}
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (h_unital : KadisonSchwarz.IsUnitalKraus K)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    (KadisonSchwarz.krausMap K (Xᴴ * X) -
      (KadisonSchwarz.krausMap K X)ᴴ * KadisonSchwarz.krausMap K X).PosSemidef :=
  -- TODO (#22): reroute through kadison_schwarz_2positive once it's proved.
  -- For now, use the existing direct Kraus-based proof.
  KadisonSchwarz.kadison_schwarz K h_unital X
