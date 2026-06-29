/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Defs
import TNLean.MPS.Core.Transfer
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# MPO, MPDO, and LPDO — basic definitions

This file introduces the core tensor types and predicates for mixed-state
tensor networks, following arXiv:1606.00608 Section 4 (Cirac–Pérez-García–Schuch–
Verstraete):

* **MPO** (Matrix Product Operator): a 4-index tensor `MPOTensor d D` with
  physical ket/bra indices and virtual left/right indices.
* **MPDO** (Matrix Product Density Operator): an MPO whose operator family
  `mpo M N` is positive semidefinite for every system size `N`.
* **LPDO** (Locally Purifiable Density Operator): an MPO that admits a
  local purification tensor with Kronecker structure,
  `M^{ij} = (∑_k A^{(i,k)} ⊗ₖ conj(A^{(j,k)})).submatrix ↑e ↑e`,
  for an identification `e : Fin D ≃ Fin D' × Fin D'` of the bond index.

## Main definitions

* `MPOTensor d D`: the type of 4-index tensors (ket, bra, left-virtual,
  right-virtual).
* `MPOTensor.evalWord`: word evaluation for MPO tensors (product of 4-index
  matrices along a pair of ket/bra words).
* `MPOTensor.mpo`: the MPO operator family for system size `N`.
* `MPOTensor.transferMap`: the MPO transfer map
  `E_M(X) = ∑_{i,j} M^{ij} X (M^{ij})†`.
* `MPOTensor.IsHermitian`: local hermiticity predicate on the tensor.
* `MPOTensor.IsMPDO`: global positivity predicate.
* `MPOTensor.IsLPDO`: local purification predicate.
* `MPOTensor.IsRFP`: renormalization fixed-point predicate.
* `MPOTensor.toMPSTensor`: view an MPO tensor as an MPS tensor with doubled
  physical index `Fin (d * d)`.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608, Section 4.1–4.3
* [VGRC04] Verstraete, Garcia-Ripoll, Cirac, PRL 93, 207204 (2004)
* [ZV04] Zwolak, Vidal, PRL 93, 207205 (2004)
-/

open scoped Matrix ComplexOrder BigOperators Kronecker
open Matrix Finset

/-- A **Matrix Product Operator** tensor:
a family of `D × D` matrices `M^{ij}` indexed by a ket index `i` and a bra
index `j`, both in `Fin d`.

This is equivalent to an MPS tensor with doubled physical index `Fin d × Fin d`;
we keep both indices explicit following the notation of
arXiv:1606.00608, Section 4. -/
abbrev MPOTensor (d D : ℕ) := Fin d → Fin d → Matrix (Fin D) (Fin D) ℂ

namespace MPOTensor

variable {d D : ℕ}

/-! ### Conversion to MPS tensor with doubled physical index -/

/-- The doubled-index MPS view: `(toMPSTensor M)_{(i,j)} = M^{ij}`,
identifying `Fin d × Fin d` with `Fin (d * d)` via the standard product encoding
(`Fin.divNat` = ket, `Fin.modNat` = bra). -/
def toMPSTensor (M : MPOTensor d D) : MPSTensor (d * d) D :=
  fun ij => M (ij.divNat) (ij.modNat)

/-! ### Word evaluation -/

/-- Evaluate a pair of ket/bra words by multiplying the corresponding
4-index matrices: `M^{i₁ j₁} * M^{i₂ j₂} * ⋯ * M^{iₙ jₙ}`.
Returns `1` for the empty word pair, and `0` for mismatched lengths. -/
noncomputable def evalWord (M : MPOTensor d D) :
    List (Fin d) → List (Fin d) → Matrix (Fin D) (Fin D) ℂ
  | [], [] => 1
  | i :: is, j :: js => M i j * evalWord M is js
  | _, _ => 0

@[simp] lemma evalWord_nil (M : MPOTensor d D) : evalWord M [] [] = 1 := rfl

@[simp] lemma evalWord_cons (M : MPOTensor d D)
    (i j : Fin d) (is js : List (Fin d)) :
    evalWord M (i :: is) (j :: js) = M i j * evalWord M is js := rfl

/-- Word evaluation on `List.ofFn` equals a non-commutative product:
`evalWord M (ofFn σ) (ofFn τ) = (ofFn (fun i => M (σ i) (τ i))).prod`. -/
lemma evalWord_ofFn (M : MPOTensor d D) {N : ℕ} (σ τ : Fin N → Fin d) :
    evalWord M (List.ofFn σ) (List.ofFn τ) =
      (List.ofFn fun i : Fin N => M (σ i) (τ i)).prod := by
  induction N with
  | zero =>
      simp only [List.ofFn_zero, evalWord_nil, List.prod_nil]
  | succ n ih =>
      simp only [List.ofFn_succ, evalWord_cons, List.prod_cons]
      congr 1
      exact ih (σ ∘ Fin.succ) (τ ∘ Fin.succ)

/-- `evalWord` is multiplicative under concatenation of equal-length bra/ket
prefixes: splitting both words at the same position factors the matrix product.
-/
theorem evalWord_append (M : MPOTensor d D) :
    ∀ (l₁ k₁ l₂ k₂ : List (Fin d)), l₁.length = k₁.length →
      evalWord M (l₁ ++ l₂) (k₁ ++ k₂) = evalWord M l₁ k₁ * evalWord M l₂ k₂ := by
  intro l₁
  induction l₁ with
  | nil =>
      intro k₁ l₂ k₂ h
      rw [List.length_nil, eq_comm, List.length_eq_zero_iff] at h
      subst h
      simp [evalWord]
  | cons i is ih =>
      intro k₁ l₂ k₂ h
      cases k₁ with
      | nil => simp at h
      | cons j js =>
          simp only [List.cons_append, evalWord_cons]
          rw [ih js l₂ k₂ (by simpa using h), Matrix.mul_assoc]

/-- **Cyclicity of the closed MPO word trace.** Moving the first bra/ket letter
to the end of both words leaves the trace of the matrix product unchanged, since
`tr(M^{ab} \, P) = tr(P \, M^{ab})`. This is the translation invariance of the
periodic MPDO at the level of a single shift. -/
theorem trace_evalWord_cons_eq_append (M : MPOTensor d D)
    (a b : Fin d) (l k : List (Fin d)) (h : l.length = k.length) :
    Matrix.trace (evalWord M (a :: l) (b :: k))
      = Matrix.trace (evalWord M (l ++ [a]) (k ++ [b])) := by
  rw [evalWord_cons, evalWord_append M l k [a] [b] h, evalWord_cons, evalWord_nil,
    mul_one, Matrix.trace_mul_comm]

/-! ### The MPO operator family -/

/-- The `(σ, τ)` matrix entry of the MPO density operator for system size `N`:
`tr(M^{σ₀ τ₀} * M^{σ₁ τ₁} * ⋯ * M^{σ_{N-1} τ_{N-1}})`. -/
noncomputable def mpoMatrixEntry (M : MPOTensor d D) {N : ℕ}
    (σ τ : Fin N → Fin d) : ℂ :=
  Matrix.trace (evalWord M (List.ofFn σ) (List.ofFn τ))

/-- The **MPO operator family** for system size `N`: the operator
`ρ^{(N)}(M)` on `(ℂ^d)^{⊗N}` with matrix elements
`⟨σ|ρ^{(N)}|τ⟩ = tr(M^{σ₀ τ₀} ⋯ M^{σ_{N-1} τ_{N-1}})`.

This is the `d^N × d^N` matrix indexed by `Fin N → Fin d`. -/
noncomputable def mpo (M : MPOTensor d D) (N : ℕ) :
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
  Matrix.of fun σ τ => mpoMatrixEntry M σ τ

@[simp] lemma mpo_apply (M : MPOTensor d D) (N : ℕ)
    (σ τ : Fin N → Fin d) :
    mpo M N σ τ = mpoMatrixEntry M σ τ := rfl

/-! ### Hermiticity -/

/-- An MPO tensor is **Hermitian** if `M^{ij} = (M^{ji})†` for all `i, j`. -/
def IsHermitian (M : MPOTensor d D) : Prop :=
  ∀ i j : Fin d, M i j = (M j i)ᴴ

/-! ### Transfer map -/

/-- The **MPO transfer map** associated to an MPO tensor `M`:
$$E_M(X) = \sum_{i,j} M^{ij} \, X \, (M^{ij})^\dagger.$$ -/
noncomputable def transferMap (M : MPOTensor d D) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  ∑ i : Fin d, ∑ j : Fin d,
    (LinearMap.mulLeft ℂ (M i j)).comp (LinearMap.mulRight ℂ (M i j)ᴴ)

lemma transferMap_apply (M : MPOTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) :
    transferMap M X = ∑ i : Fin d, ∑ j : Fin d, M i j * X * (M i j)ᴴ := by
  simp only [transferMap, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, LinearMap.mulRight_apply, Matrix.mul_assoc]

/-- The MPO transfer map equals the MPS transfer map of the doubled-index tensor. -/
@[simp] lemma transferMap_eq_toMPSTensor (M : MPOTensor d D) :
    transferMap M = MPSTensor.transferMap (toMPSTensor M) := by
  refine LinearMap.ext fun X => ?_
  simp only [transferMap_apply, MPSTensor.transferMap_apply, toMPSTensor]
  rw [← Fintype.sum_prod_type']
  exact (finProdFinEquiv.symm.sum_comp _).symm

/-- The transfer map of an MPO preserves positive semidefiniteness. -/
theorem transferMap_pos (M : MPOTensor d D)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X.PosSemidef) :
    (transferMap M X).PosSemidef := by
  simpa [transferMap_eq_toMPSTensor] using
    MPSTensor.transferMap_pos (toMPSTensor M) hX

/-! ### MPDO: global positivity -/

/-- An MPO tensor `M` is an **MPDO** (Matrix Product Density Operator) if
it generates positive semidefinite operators for all system sizes:
`ρ^{(N)}(M) ≥ 0` for all `N`.

See arXiv:1606.00608, Section 4. -/
def IsMPDO (M : MPOTensor d D) : Prop :=
  ∀ N : ℕ, (mpo M N).PosSemidef

/-! ### LPDO: local purification -/

/-- An MPO tensor `M` is an **LPDO** (Locally Purifiable Density Operator) if
there exist a Kraus dimension `dK`, an inner bond dimension `D'`, a purifying
family `A^{(i,k)} ∈ M_{D'}(ℂ)` for `i ∈ Fin d`, `k ∈ Fin dK`, and a bond-space
identification `e : Fin D ≃ Fin D' × Fin D'` such that

  `M^{ij} = (∑_{k} A^{(i,k)} ⊗ₖ (A^{(j,k)})^*).submatrix ↑e ↑e`

for all `i, j`, where `(·)^*` is entrywise complex conjugation and `⊗ₖ` is the
Kronecker product. See arXiv:1606.00608, Section 4.3. -/
def IsLPDO (M : MPOTensor d D) : Prop :=
  ∃ (dK D' : ℕ) (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ)
    (e : Fin D ≃ Fin D' × Fin D'),
    ∀ i j : Fin d, M i j = (∑ k : Fin dK,
      (A i k) ⊗ₖ ((A j k).map (starRingEnd ℂ))).submatrix ↑e ↑e

/-- The list product of LPDO tensor entries decomposes via Kronecker products
of the purifying tensor. This is the key technical lemma for `IsLPDO.isMPDO` and
for the purification identity `mpo_eq_purificationDensity`: the product of
Kronecker sums expands as a Kronecker sum of products, using the mixed-product
property `(A ⊗ B)(C ⊗ D) = (AC) ⊗ (BD)`. -/
lemma lpdo_prod_decomp {dK D' : ℕ}
    (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ)
    (e : Fin D ≃ Fin D' × Fin D')
    {M : MPOTensor d D}
    (hM : ∀ i j : Fin d, M i j = (∑ k : Fin dK,
      (A i k) ⊗ₖ ((A j k).map (starRingEnd ℂ))).submatrix ↑e ↑e)
    {N : ℕ} (σ τ : Fin N → Fin d) :
    (List.ofFn fun l => M (σ l) (τ l)).prod =
      (∑ κ : Fin N → Fin dK,
        (List.ofFn fun l => A (σ l) (κ l)).prod ⊗ₖ
        ((List.ofFn fun l => A (τ l) (κ l)).prod).map
          (starRingEnd ℂ)).submatrix ↑e ↑e := by
  induction N with
  | zero =>
    simp only [List.ofFn_zero, List.prod_nil, Fintype.sum_unique]
    have h1 : (1 : Matrix (Fin D') (Fin D') ℂ).map ⇑(starRingEnd ℂ) = 1 :=
      (starRingEnd ℂ).mapMatrix.map_one
    rw [h1, Matrix.kroneckerMap_one_one (· * ·) (fun _ => zero_mul _)
      (fun _ => mul_zero _) (one_mul 1), Matrix.submatrix_one_equiv]
  | succ n ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    rw [hM (σ 0) (τ 0)]
    have ih_step := ih (σ ∘ Fin.succ) (τ ∘ Fin.succ)
    simp only [Function.comp_def] at ih_step
    rw [ih_step, Matrix.submatrix_mul_equiv _ _ (↑e) e (↑e)]
    -- Strip the submatrix to work at the (Fin D' × Fin D') level
    congr 1
    -- Expand LHS product of sums
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    -- Apply mixed product property
    simp_rw [← Matrix.mul_kronecker_mul]
    -- Combine the conjugated matrices: map star (A) * map star (B) = map star (A * B)
    have map_star_mul : ∀ (P Q : Matrix (Fin D') (Fin D') ℂ),
        P.map ⇑(starRingEnd ℂ) * Q.map ⇑(starRingEnd ℂ) =
        (P * Q).map ⇑(starRingEnd ℂ) :=
      fun P Q => ((starRingEnd ℂ).mapMatrix.map_mul P Q).symm
    simp_rw [map_star_mul]
    -- Reindex RHS: ∑ κ : Fin(n+1) → Fin dK = ∑ k, ∑ κ'
    have reindex : ∀ (F : (Fin (n + 1) → Fin dK) →
        Matrix (Fin D' × Fin D') (Fin D' × Fin D') ℂ),
      ∑ κ, F κ = ∑ k : Fin dK, ∑ κ' : Fin n → Fin dK,
        F (Fin.cons k κ') := fun F => by
          rw [← Fintype.sum_prod_type']
          exact ((Fin.consEquiv (fun _ : Fin (n + 1) => Fin dK)).sum_comp F).symm
    symm
    rw [reindex]
    simp only [Fin.cons_zero, Fin.cons_succ]

/-- **LPDO implies MPDO**: every LPDO tensor generates positive semidefinite
density operators for all system sizes.

The proof uses the Kronecker product structure: the N-site density matrix
decomposes as `ρ^{(N)} = ∑_κ |ψ_κ⟩⟨ψ_κ|` where each `ψ_κ` is an MPS
vector built from the purifying tensor, giving a manifestly PSD sum of
rank-1 positive semidefinite matrices.

See arXiv:1606.00608, Section 4.3. -/
theorem IsLPDO.isMPDO {M : MPOTensor d D} (h : IsLPDO M) : IsMPDO M := by
  obtain ⟨dK, D', A, e, hM⟩ := h
  intro N
  -- Define the MPS coefficient vectors from the purifying tensor
  set ψ : (Fin N → Fin dK) → (Fin N → Fin d) → ℂ :=
    fun κ σ => Matrix.trace ((List.ofFn fun l => A (σ l) (κ l)).prod) with hψ
  -- Show mpo M N = ∑ κ, |ψ_κ⟩⟨ψ_κ|, then conclude PSD
  suffices hmpo : mpo M N = ∑ κ : Fin N → Fin dK,
      Matrix.vecMulVec (ψ κ) (star (ψ κ)) by
    rw [hmpo]
    exact Matrix.posSemidef_sum _ fun κ _ => Matrix.posSemidef_vecMulVec_self_star _
  -- Prove the matrix equality entry-by-entry
  ext σ τ
  simp only [mpo_apply, mpoMatrixEntry, hψ, evalWord_ofFn]
  -- Apply the Kronecker product decomposition
  rw [lpdo_prod_decomp A e hM σ τ]
  -- trace of submatrix = trace (via equiv reindexing)
  have trace_sub : ∀ (X : Matrix (Fin D' × Fin D') (Fin D' × Fin D') ℂ),
      Matrix.trace (X.submatrix (↑e) (↑e)) = Matrix.trace X := by
    intro X; simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
    exact e.sum_comp (fun p => X p p)
  rw [trace_sub, Matrix.trace_sum]
  simp_rw [Matrix.trace_kronecker]
  -- trace of entrywise conjugate = conjugate of trace: trace(A.map star) = star(trace A)
  simp_rw [← AddMonoidHom.map_trace (starRingEnd ℂ)]
  -- Evaluate the entries of the finite sum of rank-one matrices.
  simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply, starRingEnd_apply]

/-! ### MPDO renormalization fixed points -/

/-- `IsRFP M` is the MPO transfer-map **idempotence** condition `E_M ∘ E_M = E_M`
(definitionally `IsZCL M`, the zero-correlation-length characterization).

This is *not* the paper's MPDO renormalization-fixed-point Definition 4.1
(paper label RFPMixedTS, arXiv:1606.00608 line 657: existence of two
trace-preserving CP maps T and S on the physical indices). Idempotence coincides
with Definition 4.1 only in the pure (MPS) case. For general MPDO, Definition 4.1
is strictly stronger:
it implies idempotence/ZCL (Theorem 4.9, i ⟹ ii, gives ZCL and SAL), but ZCL alone
does not imply it (line 786). Definition 4.1 is stated as `MPOTensor.IsRFPViaTS`;
the theorem deriving idempotence from it is future work (#826, #237). -/
def IsRFP (M : MPOTensor d D) : Prop :=
  transferMap M ∘ₗ transferMap M = transferMap M

end MPOTensor
