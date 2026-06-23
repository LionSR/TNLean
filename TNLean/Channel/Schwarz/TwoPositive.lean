/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Algebra.MatrixAux
import TNLean.Algebra.TracePairing
import TNLean.Channel.Basic
import TNLean.Channel.ChoiJamiolkowski
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
* `nPositiveAmpliation` — the explicit blockwise ampliation `E ⊗ id_k`

## Main results

* `IsCPMap.isNPositiveMap` — CP maps are n-positive for all n
* `isNPositiveMap_one_iff_isPositiveMap` — 1-positive maps are exactly positive maps
* `isCPMap_iff_isNPositiveMap_card` — on `M_D`, `D`-positive maps are exactly CP maps
* `IsPositiveMap.traceAdjointMap` — the trace-pairing adjoint of a positive map is positive
* `IsNPositiveMap.traceAdjointMap` — the trace-pairing adjoint of a `k`-positive
  map is `k`-positive
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
* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 5.1]
* [Størmer, *Positive linear maps of operator algebras*, Springer (2013)]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

private noncomputable def finTwoSumEquiv (α : Type*) : α × Fin 2 ≃ α ⊕ α :=
  ((Equiv.prodCongr (Equiv.refl α) finTwoEquiv).trans (Equiv.prodComm α Bool)).trans
    (Equiv.boolProdEquivSum α)

@[simp] private theorem finTwoSumEquiv_apply_zero {α : Type*} (a : α) :
    finTwoSumEquiv α (a, 0) = Sum.inl a := by
  simp [finTwoSumEquiv, finTwoEquiv]

@[simp] private theorem finTwoSumEquiv_apply_one {α : Type*} (a : α) :
    finTwoSumEquiv α (a, 1) = Sum.inr a := by
  simp [finTwoSumEquiv, finTwoEquiv]

@[simp] private theorem finTwoSumEquiv_symm_inl {α : Type*} (a : α) :
    (finTwoSumEquiv α).symm (Sum.inl a) = (a, 0) := by
  rw [Equiv.symm_apply_eq]
  exact finTwoSumEquiv_apply_zero a

@[simp] private theorem finTwoSumEquiv_symm_inr {α : Type*} (a : α) :
    (finTwoSumEquiv α).symm (Sum.inr a) = (a, 1) := by
  rw [Equiv.symm_apply_eq]
  exact finTwoSumEquiv_apply_one a

/-! ## Definitions of n-positivity -/

/-- A linear map `E : M_n(ℂ) → M_n(ℂ)` is **k-positive** if the ampliation
`E ⊗ id_k : M_n(ℂ) ⊗ M_k(ℂ) → M_n(ℂ) ⊗ M_k(ℂ)` is a positive map.

We represent `M_n(ℂ) ⊗ M_k(ℂ)` as `M_{n×k}(ℂ)` via the Kronecker product
identification, and the ampliation acts blockwise:
`(E ⊗ id_k)(X)_{ij} = E(X_{ij})` for block indices `i, j ∈ Fin k`.

**Encoding choice**: We use a blockwise `Matrix.of` encoding rather than
`TensorProduct` because it avoids the overhead of tensor product interface and
matches the block-matrix arguments used in `KadisonSchwarz.lean`. A
`TensorProduct`-based definition would be closer to the mathematical
definition but would require additional formalization to connect with the
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

/-- The explicit blockwise ampliation `E ⊗ id_k` used in the definition of
`k`-positivity. -/
def nPositiveAmpliation (k : ℕ) (E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) :
    Matrix (n × Fin k) (n × Fin k) ℂ →ₗ[ℂ]
      Matrix (n × Fin k) (n × Fin k) ℂ where
  toFun X := Matrix.of fun (ip : n × Fin k) (jq : n × Fin k) =>
    (E (Matrix.of fun i j => X (i, ip.2) (j, jq.2))) ip.1 jq.1
  map_add' X Y := by
    ext ip jq
    change E ((Matrix.of fun i j => X (i, ip.2) (j, jq.2)) +
        (Matrix.of fun i j => Y (i, ip.2) (j, jq.2))) ip.1 jq.1 =
      (E (Matrix.of fun i j => X (i, ip.2) (j, jq.2)) +
        E (Matrix.of fun i j => Y (i, ip.2) (j, jq.2))) ip.1 jq.1
    rw [map_add]
  map_smul' c X := by
    ext ip jq
    change E (c • (Matrix.of fun i j => X (i, ip.2) (j, jq.2))) ip.1 jq.1 =
      (c • E (Matrix.of fun i j => X (i, ip.2) (j, jq.2))) ip.1 jq.1
    rw [map_smul]

omit [Fintype n] [DecidableEq n] in
/-- The definition of `k`-positivity is positivity of the blockwise ampliation. -/
theorem isNPositiveMap_iff_isPositiveMap_nPositiveAmpliation
    (k : ℕ) (E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) :
    IsNPositiveMap k E ↔ IsPositiveMap (nPositiveAmpliation k E) := by
  rfl

omit [Fintype n] [DecidableEq n] in
/-- One-positive maps are exactly positive maps. -/
theorem isNPositiveMap_one_iff_isPositiveMap
    {E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} :
    IsNPositiveMap 1 E ↔ IsPositiveMap E := by
  constructor
  · intro hE X hX
    let X' : Matrix (n × Fin 1) (n × Fin 1) ℂ :=
      Matrix.of fun ip jq => X ip.1 jq.1
    have hX' : X'.PosSemidef := by
      convert hX.submatrix (fun ip : n × Fin 1 => ip.1) using 1
      ext ip jq
      rfl
    have hY := hE X' hX'
    let emb : n → n × Fin 1 := fun i => (i, 0)
    convert hY.submatrix emb using 1
    ext i j
    simp only [emb, X', Matrix.submatrix_apply, Matrix.of_apply]
    rw [show (Matrix.of fun i j => X i j) = X by ext i j; rfl]
  · intro hE
    rw [isNPositiveMap_iff_isPositiveMap_nPositiveAmpliation]
    intro X hX
    let e : n × Fin 1 ≃ n := Equiv.prodUnique n (Fin 1)
    have hY : (Matrix.of fun (ip : n × Fin 1) (jq : n × Fin 1) =>
        E (Matrix.of fun i j => X (i, 0) (j, 0)) ip.1 jq.1).PosSemidef := by
      have hblock : (Matrix.of fun i j => X (i, 0) (j, 0)).PosSemidef := by
        convert hX.submatrix e.symm using 1
        ext i j
        simp [e]
      have hEblock := hE _ hblock
      convert hEblock.submatrix e using 1
      ext ip jq
      simp [e]
    convert hY using 1
    ext ip jq
    have hip : ip.2 = 0 := Subsingleton.elim ip.2 0
    have hjq : jq.2 = 0 := Subsingleton.elim jq.2 0
    simp [nPositiveAmpliation, hip, hjq]

omit [DecidableEq n] in
private theorem traceAdjointMap_map_isHermitian_of_isPositiveMap
    {E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
    (hE : IsPositiveMap E) {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    (Matrix.traceAdjointMap E X).IsHermitian := by
  classical
  rw [Matrix.IsHermitian]
  ext i j
  simp only [Matrix.conjTranspose_apply, RCLike.star_def]
  calc
    (starRingEnd ℂ) (Matrix.trace (X * E (Matrix.single i j 1)))
        = Matrix.trace ((X * E (Matrix.single i j 1))ᴴ) := by
          simpa using (Matrix.trace_conjTranspose (X * E (Matrix.single i j 1))).symm
    _ = Matrix.trace ((E (Matrix.single i j 1))ᴴ * Xᴴ) := by
          rw [Matrix.conjTranspose_mul]
    _ = Matrix.trace (E (Matrix.single j i 1) * X) := by
          rw [hX.eq, ← hE.map_conjTranspose]
          simp
    _ = Matrix.trace (X * E (Matrix.single j i 1)) := by
          rw [Matrix.trace_mul_comm]

omit [DecidableEq n] in
/-- The trace-pairing adjoint of a positive map is positive. -/
theorem IsPositiveMap.traceAdjointMap
    {E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
    (hE : IsPositiveMap E) : IsPositiveMap (Matrix.traceAdjointMap E) := by
  intro X hX
  refine Matrix.PosSemidef.of_forall_trace_mul_nonneg
    (traceAdjointMap_map_isHermitian_of_isPositiveMap hE hX.1) ?_
  intro B hB
  rw [Matrix.trace_traceAdjointMap_mul]
  exact Matrix.PosSemidef.trace_mul_nonneg hX (hE B hB)

omit [DecidableEq n] in
/-- Positivity is invariant under the trace-pairing adjoint. -/
theorem isPositiveMap_traceAdjointMap_iff
    {E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} :
    IsPositiveMap (Matrix.traceAdjointMap E) ↔ IsPositiveMap E := by
  constructor
  · intro h
    have h' := h.traceAdjointMap
    simpa [Matrix.traceAdjointMap_traceAdjointMap] using h'
  · intro h
    exact h.traceAdjointMap

omit [DecidableEq n] in
private theorem trace_mul_eq_sum_trace_blocks
    (k : ℕ) (A B : Matrix (n × Fin k) (n × Fin k) ℂ) :
    Matrix.trace (A * B) =
      ∑ p : Fin k, ∑ q : Fin k,
        Matrix.trace
          ((Matrix.of fun i j => A (i, p) (j, q)) *
            (Matrix.of fun i j => B (i, q) (j, p))) := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  congr 1
  ext p
  conv_lhs =>
    enter [2, i]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

omit [DecidableEq n] in
/-- The trace-pairing adjoint commutes with the blockwise ampliation:
`(E^{(k)})^* = (E^*)^{(k)}`. -/
theorem nPositiveAmpliation_traceAdjointMap
    (k : ℕ) (E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) :
    nPositiveAmpliation k (Matrix.traceAdjointMap E) =
      Matrix.traceAdjointMap (nPositiveAmpliation k E) := by
  classical
  apply LinearMap.ext
  intro ρ
  refine (Matrix.ext_iff_trace_mul_right
    (A := nPositiveAmpliation k (Matrix.traceAdjointMap E) ρ)
    (B := Matrix.traceAdjointMap (nPositiveAmpliation k E) ρ)).2 ?_
  intro X
  rw [Matrix.trace_traceAdjointMap_mul]
  rw [trace_mul_eq_sum_trace_blocks, trace_mul_eq_sum_trace_blocks]
  congr 1
  ext p
  congr 1
  ext q
  simp only [nPositiveAmpliation, Matrix.of_apply, LinearMap.coe_mk, AddHom.coe_mk]
  change Matrix.trace
      (Matrix.traceAdjointMap E (Matrix.of fun i j => ρ (i, p) (j, q)) *
        (Matrix.of fun i j => X (i, q) (j, p))) =
    Matrix.trace
      ((Matrix.of fun i j => ρ (i, p) (j, q)) *
        E (Matrix.of fun i j => X (i, q) (j, p)))
  rw [Matrix.trace_traceAdjointMap_mul]

omit [DecidableEq n] in
/-- The trace-pairing adjoint of a `k`-positive map is `k`-positive. -/
theorem IsNPositiveMap.traceAdjointMap
    {k : ℕ} {E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
    (hE : IsNPositiveMap k E) : IsNPositiveMap k (Matrix.traceAdjointMap E) := by
  rw [isNPositiveMap_iff_isPositiveMap_nPositiveAmpliation] at hE ⊢
  rw [nPositiveAmpliation_traceAdjointMap]
  exact hE.traceAdjointMap

omit [DecidableEq n] in
/-- `k`-positivity is invariant under the trace-pairing adjoint. -/
theorem isNPositiveMap_traceAdjointMap_iff
    {k : ℕ} {E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} :
    IsNPositiveMap k (Matrix.traceAdjointMap E) ↔ IsNPositiveMap k E := by
  constructor
  · intro h
    have h' := h.traceAdjointMap
    simpa [Matrix.traceAdjointMap_traceAdjointMap] using h'
  · intro h
    exact h.traceAdjointMap

private theorem posSemidef_fromBlocks_zero_zero
    {m o : Type*} {A : Matrix m m ℂ} (hA : A.PosSemidef) :
    (Matrix.fromBlocks A 0 0 (0 : Matrix o o ℂ)).PosSemidef := by
  refine ⟨Matrix.IsHermitian.fromBlocks hA.1 (by simp) isHermitian_zero, ?_⟩
  intro x
  let fg := Finsupp.sumFinsuppEquivProdFinsupp x
  let xL : m →₀ ℂ := fg.1
  let xR : o →₀ ℂ := fg.2
  have hx : x = Finsupp.sumElim xL xR :=
    (Finsupp.sumFinsuppEquivProdFinsupp.symm_apply_apply x).symm
  rw [hx, Finsupp.sumElim_eq_add, Finsupp.sum_add_index']
  · have hRight :
        (Finsupp.mapDomain Sum.inr xR).sum (fun i xi =>
            (Finsupp.mapDomain Sum.inl xL + Finsupp.mapDomain Sum.inr xR).sum fun j xj =>
              star xi * (Matrix.fromBlocks A 0 0 (0 : Matrix o o ℂ)) i j * xj) = 0 := by
      rw [Finsupp.sum_mapDomain_index]
      · have hInner (a : o) (x₁ : ℂ) :
          (Finsupp.mapDomain Sum.inl xL + Finsupp.mapDomain Sum.inr xR).sum (fun j xj =>
              star x₁ * (Matrix.fromBlocks A 0 0 (0 : Matrix o o ℂ)) (Sum.inr a) j * xj) = 0 := by
          rw [Finsupp.sum_add_index']
          · rw [Finsupp.sum_mapDomain_index, Finsupp.sum_mapDomain_index]
            · simp
            · intro i
              simp
            · intro i u v
              simp [mul_assoc, mul_add]
            · intro i
              simp
            · intro i u v
              simp [mul_assoc, mul_add]
          · intro i
            simp
          · intro i u v
            simp [mul_assoc, mul_add]
        rw [Finsupp.sum]
        refine Finset.sum_eq_zero ?_
        intro a ha
        exact hInner a (xR a)
      · intro i
        simp
      · intro i u v
        simp [add_mul, mul_assoc]
    have hLeft :
        (Finsupp.mapDomain Sum.inl xL).sum (fun i xi =>
            (Finsupp.mapDomain Sum.inl xL + Finsupp.mapDomain Sum.inr xR).sum fun j xj =>
              star xi * (Matrix.fromBlocks A 0 0 (0 : Matrix o o ℂ)) i j * xj) =
          xL.sum (fun i xi => xL.sum fun j xj => star xi * A i j * xj) := by
      rw [Finsupp.sum_mapDomain_index]
      · apply Finsupp.sum_congr
        intro a x₁
        rw [Finsupp.sum_add_index']
        · rw [Finsupp.sum_mapDomain_index, Finsupp.sum_mapDomain_index]
          · simp [mul_assoc]
          · intro i
            simp
          · intro i u v
            simp [mul_assoc, mul_add]
          · intro i
            simp
          · intro i u v
            simp [mul_assoc, mul_add]
        · intro i
          simp
        · intro i u v
          simp [mul_assoc, mul_add]
      · intro i
        simp
      · intro i u v
        simp [add_mul, mul_assoc]
    rw [hLeft, hRight]
    simpa using hA.2 xL
  · intro i
    simp
  · intro i u v
    simp [add_mul, mul_assoc]

omit [DecidableEq n] in
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
  have hXswap : Xswap.PosSemidef := by
    simpa [Xswap, Matrix.reindex_apply] using hX.submatrix e.symm
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
    rw [show F Yblk = ∑ a, F (D a * Xblk * (D a)ᴴ) by simp [Yblk]]
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
    simp [D, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.mul_assoc, Matrix.star_eq_conjTranspose]
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
  have hY : (Matrix.reindex e.symm e.symm (F Yblk)).PosSemidef := by
    simpa [Matrix.reindex_apply] using hYswap.submatrix e
  convert hY using 1
  ext ip jq
  rw [hYblk]
  simp only [of_apply, Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_apply]
  change E (Matrix.of fun i j => X (i, ip.2) (j, jq.2)) ip.1 jq.1 =
      E (Xblk ip.2 jq.2) ip.1 jq.1
  rw [hXblk_apply ip.2 jq.2]

omit [DecidableEq n] [Fintype n] in
/-- On `M_D(ℂ)`, a `D`-positive map is completely positive. -/
theorem IsNPositiveMap.isCPMap_of_card {D : ℕ} [NeZero D]
    {E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hE : IsNPositiveMap D E) : IsCPMap E := by
  rw [ChoiJamiolkowski.cp_iff_choi_posSemidef]
  have hΩ : (Matrix.omegaProj D).PosSemidef := by
    simpa [Matrix.omegaProj, Matrix.star_omegaVec] using
      Matrix.posSemidef_vecMulVec_self_star (Matrix.omegaVec D)
  convert hE (Matrix.omegaProj D) hΩ using 1
  ext ip jq
  rfl

omit [DecidableEq n] [Fintype n] in
/-- On `M_D(ℂ)`, complete positivity is equivalent to `D`-positivity. -/
theorem isCPMap_iff_isNPositiveMap_card {D : ℕ} [NeZero D]
    {E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ} :
    IsCPMap E ↔ IsNPositiveMap D E := by
  constructor
  · intro hE
    exact hE.isNPositiveMap D
  · intro hE
    exact hE.isCPMap_of_card

omit [DecidableEq n] [Fintype n] in
/-- **Monotonicity sanity check**: `(k+1)`-positive implies `k`-positive.

This is a basic structural property of the n-positivity hierarchy. If this
were not provable, the definition of `IsNPositiveMap` would be wrong.
The proof embeds `M_n ⊗ M_k ↪ M_n ⊗ M_{k+1}` via padding with zeros. -/
theorem IsNPositiveMap.mono {E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} {k : ℕ}
    (h : IsNPositiveMap (k + 1) E) : IsNPositiveMap k E := by
  intro X hX
  let e : n × Fin (k + 1) ≃ (n × Fin k) ⊕ n :=
    (((Equiv.prodCongr (Equiv.refl n)
        ((finSumFinEquiv : Fin k ⊕ Fin 1 ≃ Fin (k + 1)).symm)).trans
      (Equiv.prodSumDistrib n (Fin k) (Fin 1))).trans
      (Equiv.sumCongr (Equiv.refl _) (Equiv.prodUnique n (Fin 1))))
  let X' : Matrix (n × Fin (k + 1)) (n × Fin (k + 1)) ℂ :=
    Matrix.reindex e.symm e.symm (Matrix.fromBlocks X 0 0 (0 : Matrix n n ℂ))
  have he_castSucc (i : n) (a : Fin k) : e (i, Fin.castSucc a) = Sum.inl (i, a) := by
    change Sum.map id Prod.fst
        ((Equiv.prodSumDistrib n (Fin k) (Fin 1))
          (i, ((finSumFinEquiv : Fin k ⊕ Fin 1 ≃ Fin (k + 1)).symm (Fin.castSucc a)))) =
        Sum.inl (i, a)
    rw [finSumFinEquiv_symm_apply_castSucc]
    simp
  have hX' : X'.PosSemidef := by
    have hdiag : (Matrix.fromBlocks X 0 0 (0 : Matrix n n ℂ)).PosSemidef :=
      posSemidef_fromBlocks_zero_zero hX
    simpa [X', Matrix.reindex_apply] using hdiag.submatrix e
  have hY' := h X' hX'
  let emb : n × Fin k → n × Fin (k + 1) := fun ip => (ip.1, Fin.castSucc ip.2)
  convert hY'.submatrix emb using 1
  ext ip jq
  simp [emb, X', Matrix.reindex_apply, he_castSucc]

omit [DecidableEq n] [Fintype n] in
/-- If `m ≤ k`, then `k`-positivity implies `m`-positivity.

This is the inclusion direction in Wolf Chapter 3, Equation (3.3):
the cones of positive maps become larger as the amplification dimension
decreases. -/
theorem IsNPositiveMap.mono_of_le {E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} {m k : ℕ}
    (hmk : m ≤ k) (h : IsNPositiveMap k E) : IsNPositiveMap m E := by
  exact Nat.le_induction (P := fun k _ => IsNPositiveMap k E → IsNPositiveMap m E)
    (fun h => h)
    (fun _ _ ih hk => ih (IsNPositiveMap.mono hk)) k hmk h

omit [DecidableEq n] [Fintype n] in
/-- The zero map is `k`-positive. -/
theorem IsNPositiveMap.zero (k : ℕ) :
    IsNPositiveMap k (0 : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) := by
  intro X hX
  convert (Matrix.PosSemidef.zero : (0 : Matrix (n × Fin k) (n × Fin k) ℂ).PosSemidef)
    using 1
  ext ip jq
  simp

omit [DecidableEq n] [Fintype n] in
/-- The sum of two `k`-positive maps is `k`-positive. -/
theorem IsNPositiveMap.add {E F : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} {k : ℕ}
    (hE : IsNPositiveMap k E) (hF : IsNPositiveMap k F) : IsNPositiveMap k (E + F) := by
  intro X hX
  convert Matrix.PosSemidef.add (hE X hX) (hF X hX) using 1
  ext ip jq
  simp

omit [DecidableEq n] [Fintype n] in
/-- A nonnegative real multiple of a `k`-positive map is `k`-positive. -/
theorem IsNPositiveMap.smul_nonneg {E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} {k : ℕ}
    {c : ℝ} (hc : 0 ≤ c) (hE : IsNPositiveMap k E) : IsNPositiveMap k ((c : ℂ) • E) := by
  intro X hX
  have hcC : 0 ≤ (c : ℂ) := by
    exact_mod_cast hc
  convert (hE X hX).smul hcC using 1
  ext ip jq
  simp

omit [DecidableEq n] [Fintype n] in
/-- The set of `k`-positive maps is closed.

Wolf Chapter 3, §3.1, lines 75--79 of
`Notes/WolfNoteTexSource/ch03_positive_not_completely.tex`, treats the
`k`-positive maps as closed convex cones.  This proves the closedness part for
the topology inherited from the finite-dimensional space of linear maps. -/
theorem isClosed_setOf_isNPositiveMap [Finite n] (k : ℕ) :
    IsClosed {E : Matrix n n ℂ →L[ℂ] Matrix n n ℂ |
      IsNPositiveMap k E.toLinearMap} := by
  classical
  let ampEval (X : Matrix (n × Fin k) (n × Fin k) ℂ) :
      (Matrix n n ℂ →L[ℂ] Matrix n n ℂ) →ₗ[ℂ]
        Matrix (n × Fin k) (n × Fin k) ℂ :=
    { toFun := fun E => Matrix.of fun (ip : n × Fin k) (jq : n × Fin k) =>
        (E (Matrix.of fun i j => X (i, ip.2) (j, jq.2))) ip.1 jq.1
      map_add' := by
        intro E F
        ext ip jq
        simp
      map_smul' := by
        intro c E
        ext ip jq
        simp }
  have hset :
      {E : Matrix n n ℂ →L[ℂ] Matrix n n ℂ |
        IsNPositiveMap k E.toLinearMap}
        = ⋂ (X : Matrix (n × Fin k) (n × Fin k) ℂ),
          ⋂ (_hX : X.PosSemidef), {E | (ampEval X E).PosSemidef} := by
    ext E
    simp [IsNPositiveMap, ampEval]
  rw [hset]
  exact isClosed_iInter fun X => isClosed_iInter fun _hX =>
    matrix_isClosed_posSemidef.preimage ((ampEval X).continuous_of_finiteDimensional)

omit [DecidableEq n] in
/-- CP maps are 2-positive. -/
theorem IsCPMap.is2PositiveMap {E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
    (hCP : IsCPMap E) : Is2PositiveMap E := by
  classical
  exact hCP.isNPositiveMap 2

omit [DecidableEq n] [Fintype n] in
/-- 2-positive maps are positive.

Apply the definition with `k = 1` embedded into `k = 2`: given PSD `X`,
embed it as `diag(X, 0)` in `M_n ⊗ M_2`, apply 2-positivity to get PSD
output, then extract the (0,0)-block which equals `E(X)`. -/
theorem Is2PositiveMap.isPositiveMap {E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
    (h : Is2PositiveMap E) : IsPositiveMap E := by
  intro X hX
  let e : n × Fin 2 ≃ n ⊕ n := finTwoSumEquiv n
  let X' : Matrix (n × Fin 2) (n × Fin 2) ℂ :=
    Matrix.reindex e.symm e.symm (Matrix.fromBlocks X 0 0 (0 : Matrix n n ℂ))
  have hX' : X'.PosSemidef := by
    have hdiag : (Matrix.fromBlocks X 0 0 (0 : Matrix n n ℂ)).PosSemidef :=
      posSemidef_fromBlocks_zero_zero hX
    simpa [X', Matrix.reindex_apply] using hdiag.submatrix e
  have hY' := h X' hX'
  let emb : n → n × Fin 2 := fun i => (i, 0)
  convert hY'.submatrix emb using 1
  ext i j
  simp [emb, X', Matrix.reindex_apply, e]
  rfl

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
  let e : n × Fin 2 ≃ n ⊕ n := finTwoSumEquiv n
  let P : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
    Matrix.fromBlocks (Xᴴ * X) Xᴴ X 1
  have hP : P.PosSemidef := by
    let A : Matrix (n ⊕ n) (n ⊕ Fin 0) ℂ :=
      Matrix.fromBlocks Xᴴ 0 1 0
    simpa [A, P, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose]
      using Matrix.posSemidef_self_mul_conjTranspose A
  let P' : Matrix (n × Fin 2) (n × Fin 2) ℂ := Matrix.reindex e.symm e.symm P
  have hP' : P'.PosSemidef := by
    simpa [P', Matrix.reindex_apply] using hP.submatrix e
  have hY' := h2pos P' hP'
  have hPos : IsPositiveMap E := h2pos.isPositiveMap
  have hP'Block (p q : Fin 2) :
      Matrix.of (fun i j => P' (i, p) (j, q)) =
        match p, q with
        | 0, 0 => Xᴴ * X
        | 0, 1 => Xᴴ
        | 1, 0 => X
        | 1, 1 => (1 : Matrix n n ℂ) := by
    fin_cases p <;> fin_cases q <;>
      ext a b <;> simp [P', Matrix.reindex_apply, P, e]
  have hEBlock (p q : Fin 2) :
      E (Matrix.of fun i j => P' (i, p) (j, q)) =
        match p, q with
        | 0, 0 => E (Xᴴ * X)
        | 0, 1 => (E X)ᴴ
        | 1, 0 => ((E X)ᴴ)ᴴ
        | 1, 1 => (1 : Matrix n n ℂ) := by
    fin_cases p <;> fin_cases q
    · simpa using congrArg E (hP'Block 0 0)
    · exact (congrArg E (hP'Block 0 1)).trans (IsPositiveMap.map_conjTranspose hPos X)
    · exact (congrArg E (hP'Block 1 0)).trans (by simp)
    · exact (congrArg E (hP'Block 1 1)).trans (by simpa [KadisonSchwarz.IsUnitalMap] using h_unital)
  have hBlock :
      Matrix.reindex e e
        (Matrix.of fun (ip : n × Fin 2) (jq : n × Fin 2) =>
          (E (Matrix.of fun i j => P' (i, ip.2) (j, jq.2))) ip.1 jq.1) =
        Matrix.fromBlocks (E (Xᴴ * X)) ((E X)ᴴ)
          (((E X)ᴴ)ᴴ) (1 : Matrix n n ℂ) := by
    ext ip jq
    rcases ip with i | i <;> rcases jq with j | j
    · convert congr_fun (congr_fun (hEBlock 0 0) i) j using 1 <;>
        simp [Matrix.reindex_apply, e]
    · convert congr_fun (congr_fun (hEBlock 0 1) i) j using 1 <;>
        simp [Matrix.reindex_apply, e]
    · convert congr_fun (congr_fun (hEBlock 1 0) i) j using 1 <;>
        simp [Matrix.reindex_apply, e]
    · convert congr_fun (congr_fun (hEBlock 1 1) i) j using 1 <;>
        simp [Matrix.reindex_apply, e]
  have hBlockPsD :
      (Matrix.fromBlocks (E (Xᴴ * X)) ((E X)ᴴ)
        (((E X)ᴴ)ᴴ) (1 : Matrix n n ℂ)).PosSemidef := by
    have hYsum : (Matrix.reindex e e
        (Matrix.of fun (ip : n × Fin 2) (jq : n × Fin 2) =>
          (E (Matrix.of fun i j => P' (i, ip.2) (j, jq.2))) ip.1 jq.1)).PosSemidef := by
      simpa [Matrix.reindex_apply] using hY'.submatrix e.symm
    simpa [hBlock] using hYsum
  haveI : Invertible (1 : Matrix n n ℂ) := invertibleOne
  simpa [inv_one, Matrix.mul_assoc, conjTranspose_conjTranspose] using
    (Matrix.PosDef.fromBlocks₂₂ (A := E (Xᴴ * X)) (B := (E X)ᴴ)
      (D := (1 : Matrix n n ℂ)) Matrix.PosDef.one).1 hBlockPsD

/-- The Kraus-based Kadison-Schwarz inequality as a consequence of 2-positivity.

The Kraus map is completely positive, hence 2-positive, and the unital Kraus
condition is exactly unitality of the associated linear map. -/
theorem kadison_schwarz_from_2positive
    {d D : ℕ}
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (h_unital : KadisonSchwarz.IsUnitalKraus K)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    (KadisonSchwarz.krausMap K (Xᴴ * X) -
      (KadisonSchwarz.krausMap K X)ᴴ * KadisonSchwarz.krausMap K X).PosSemidef := by
  let E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ := Kraus.mapLM K
  have hCP : IsCPMap E := ⟨d, K, fun _ => rfl⟩
  have hUnital : KadisonSchwarz.IsUnitalMap E := by
    simpa [E, KadisonSchwarz.IsUnitalMap, Kraus.map, KadisonSchwarz.IsUnitalKraus,
      Matrix.mul_one] using h_unital
  simpa [E, Kraus.map, KadisonSchwarz.krausMap] using
    kadison_schwarz_2positive E hCP.is2PositiveMap hUnital X
