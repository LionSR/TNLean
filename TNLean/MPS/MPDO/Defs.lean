/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Word
import TNLean.MPS.Defs
import QICLean.Kraus.Transfer
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# MPO and MPDO — basic definitions

This file introduces the core tensor types and predicates for mixed-state
tensor networks, following arXiv:1606.00608 Sections 4.1–4.2 (Cirac–Pérez-García–Schuch–
Verstraete):

* **MPO** (Matrix Product Operator): a 4-index tensor `MPOTensor d D` with
  physical ket/bra indices and virtual left/right indices.
* **MPDO** (Matrix Product Density Operator): an MPO whose operator family
  `mpo M N` is positive semidefinite for every nonempty chain.
## Main definitions

* `MPOTensor d D`: the type of 4-index tensors (ket, bra, left-virtual,
  right-virtual).
* `MPOTensor.evalWord`: word evaluation for MPO tensors (product of 4-index
  matrices along a pair of ket/bra words).
* `MPOTensor.mpo`: the MPO operator family for system size `N`.
* `MPOTensor.reindexPhysical`: relabel both physical indices by an equivalence.
* `MPOTensor.reindexPhysicalConfigEquiv`: the induced sitewise equivalence on
  physical configurations.
* `MPOTensor.normalizedMPO`: the operator family divided by its trace.
* `MPOTensor.transferMap`: the MPO transfer map
  `E_M(X) = ∑_{i,j} M^{ij} X (M^{ij})†`.
* `MPOTensor.IsHermitian`: local hermiticity predicate on the tensor.
* `MPOTensor.adjointTensor`: the adjoint tensor `(M†)^{ij} = (M^{ji})†`, which
  generates the adjoint operator family up to spatial reflection.
* `MPOTensor.IsMPDO`: global positivity predicate.
* `MPOTensor.toMPSTensor`: view an MPO tensor as an MPS tensor with doubled
  physical index `Fin (d * d)`.
* `MPOTensor.physicalSlice`: the physical matrix at fixed virtual indices.

## Main results

* `MPOTensor.evalWord_reindexPhysical`: word evaluation commutes with physical
  reindexing.
* `MPOTensor.mpo_reindexPhysical`: finite-size MPOs are related by simultaneous
  row and column reindexing.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608, Sections 4.1–4.2
* [VGRC04] Verstraete, Garcia-Ripoll, Cirac, PRL 93, 207204 (2004)
* [ZV04] Zwolak, Vidal, PRL 93, 207205 (2004)
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix Finset

/-- A **Matrix Product Operator** tensor:
a family of `D × D` matrices `M^{ij}` indexed by a ket index `i` and a bra
index `j`, both in `Fin d`.

This is equivalent to an MPS tensor with doubled physical index `Fin d × Fin d`;
we keep both indices explicit following the notation of
arXiv:1606.00608, Section 4. -/
abbrev MPOTensor (d D : ℕ) := Fin d → Fin d → Matrix (Fin D) (Fin D) ℂ

namespace MPSTensor

/-- The first factor of a product index encoded by `finProdFinEquiv`. -/
@[simp] theorem finProdFinEquiv_divNat {m n : ℕ} (i : Fin m) (j : Fin n) :
    (finProdFinEquiv (i, j) : Fin (m * n)).divNat = i :=
  congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (i, j))

/-- The second factor of a product index encoded by `finProdFinEquiv`. -/
@[simp] theorem finProdFinEquiv_modNat {m n : ℕ} (i : Fin m) (j : Fin n) :
    (finProdFinEquiv (i, j) : Fin (m * n)).modNat = j :=
  congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (i, j))

end MPSTensor

namespace MPOTensor

variable {d D : ℕ}

/-! ### Conversion to MPS tensor with doubled physical index -/

/-- The doubled-index MPS view: `(toMPSTensor M)_{(i,j)} = M^{ij}`,
identifying `Fin d × Fin d` with `Fin (d * d)` via the standard product encoding
(`Fin.divNat` = ket, `Fin.modNat` = bra). -/
def toMPSTensor (M : MPOTensor d D) : MPSTensor (d * d) D :=
  fun ij => M (ij.divNat) (ij.modNat)

/-- Reindex both physical legs of an MPO tensor by the same equivalence. -/
def reindexPhysical {d' : ℕ} (e : Fin d' ≃ Fin d)
    (U : MPOTensor d D) : MPOTensor d' D :=
  fun i j ↦ U (e i) (e j)

/-- Apply a physical-index equivalence sitewise to a finite configuration.

Source: arXiv:1703.09188, proof of Theorem `IndexTh` (ii), lines 824--847. -/
def reindexPhysicalConfigEquiv {d' : ℕ} (N : ℕ) (e : Fin d' ≃ Fin d) :
    (Fin N → Fin d') ≃ (Fin N → Fin d) :=
  Equiv.arrowCongr (Equiv.refl (Fin N)) e

/-- The physical matrix obtained from a fixed pair of virtual indices of an
MPO tensor.

Source: arXiv:1606.00608, Appendix C.2, lines 1424--1438 and equation `formK`. -/
def physicalSlice (K : MPOTensor d D) (β α : Fin D) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun i j ↦ K i j β α

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

/-- Word evaluation after physical reindexing is word evaluation on the two
mapped words.

Source: arXiv:1703.09188, proof of Theorem `IndexTh` (ii), lines 824--847. -/
theorem evalWord_reindexPhysical {d' : ℕ} (e : Fin d' ≃ Fin d)
    (U : MPOTensor d D) (is js : List (Fin d')) :
    evalWord (reindexPhysical e U) is js =
      evalWord U (is.map e) (js.map e) := by
  induction is generalizing js with
  | nil => cases js <;> simp [evalWord]
  | cons i is ih =>
      cases js with
      | nil => simp [evalWord]
      | cons j js => simp [evalWord, reindexPhysical, ih]

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

/-- Evaluating the doubled-index MPS view on paired physical letters is the
same as evaluating the ket and bra words separately. -/
theorem evalWord_toMPSTensor_ofFn (M : MPOTensor d D) (N : ℕ)
    (w : Fin N → Fin (d * d)) :
    Kraus.evalWord M.toMPSTensor (List.ofFn w) =
      evalWord M (List.ofFn fun k ↦ (w k).divNat)
        (List.ofFn fun k ↦ (w k).modNat) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
      change M (w 0).divNat (w 0).modNat *
          Kraus.evalWord M.toMPSTensor (List.ofFn (w ∘ Fin.succ)) =
        M (w 0).divNat (w 0).modNat *
          evalWord M (List.ofFn fun k ↦ (w (Fin.succ k)).divNat)
            (List.ofFn fun k ↦ (w (Fin.succ k)).modNat)
      rw [ih (w ∘ Fin.succ)]
      rfl

/-- Paired physical configurations give the same word evaluation in the MPO
and doubled-index MPS descriptions. -/
@[simp]
theorem evalWord_toMPSTensor_pairConfig (M : MPOTensor d D) {N : ℕ}
    (σ τ : Fin N → Fin d) :
    Kraus.evalWord M.toMPSTensor
        (List.ofFn fun k ↦ finProdFinEquiv (σ k, τ k)) =
      evalWord M (List.ofFn σ) (List.ofFn τ) := by
  simpa using evalWord_toMPSTensor_ofFn M N
    (fun k ↦ finProdFinEquiv (σ k, τ k))

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

/-- Physical reindexing of a tensor simultaneously reindexes the row and column
configurations of every finite-size MPO.

Source: arXiv:1703.09188, proof of Theorem `IndexTh` (ii), lines 824--847. -/
theorem mpo_reindexPhysical {d' : ℕ} (e : Fin d' ≃ Fin d)
    (U : MPOTensor d D) (N : ℕ) :
    mpo (reindexPhysical e U) N =
      Matrix.reindex (reindexPhysicalConfigEquiv N e).symm
        (reindexPhysicalConfigEquiv N e).symm (mpo U N) := by
  ext σ τ
  simp [mpoMatrixEntry, evalWord_reindexPhysical, reindexPhysicalConfigEquiv,
    Equiv.arrowCongr, List.map_ofFn, Function.comp_def]

/-- The **normalized density operator** of the MPO for system size `N`:

  `σ^{(N)}(M) = ρ^{(N)}(M) / tr[ρ^{(N)}(M)]`.

This is the convention of arXiv:1606.00608, line 792. -/
noncomputable def normalizedMPO (M : MPOTensor d D) (N : ℕ) :
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
  (Matrix.trace (mpo M N))⁻¹ • mpo M N

/-! ### Hermiticity -/

/-- An MPO tensor is **Hermitian** if `M^{ij} = (M^{ji})†` for all `i, j`. -/
def IsHermitian (M : MPOTensor d D) : Prop :=
  ∀ i j : Fin d, M i j = (M j i)ᴴ

/-! ### The adjoint tensor -/

/-- The **adjoint tensor** $M^\dagger$: exchange the ket and bra physical
indices and take the conjugate transpose of each virtual matrix,
$(M^\dagger)^{ij} = (M^{ji})^\dagger$.  Site by site this is the dagger of
the generated operator family; the $\dagger$-marked tensors in the first
displayed diagram of the proof of Proposition 4.13 of arXiv:1606.00608,
lines 1909--1913, are of this form. -/
def adjointTensor (M : MPOTensor d D) : MPOTensor d D :=
  fun i j => (M j i)ᴴ

@[simp] lemma adjointTensor_apply (M : MPOTensor d D) (i j : Fin d) :
    adjointTensor M i j = (M j i)ᴴ := rfl

/-- A tensor equals its adjoint tensor precisely when it is Hermitian. -/
lemma adjointTensor_eq_iff_isHermitian (M : MPOTensor d D) :
    adjointTensor M = M ↔ IsHermitian M := by
  constructor
  · intro h i j
    exact (congrFun (congrFun h i) j).symm
  · intro h
    funext i j
    exact (h i j).symm

/-- Word evaluation of the adjoint tensor: for equal-length words it is the
conjugate transpose of the original word evaluation on the reversed words
with ket and bra exchanged. -/
theorem evalWord_adjointTensor (M : MPOTensor d D) :
    ∀ σs τs : List (Fin d), σs.length = τs.length →
      evalWord (adjointTensor M) σs τs = (evalWord M τs.reverse σs.reverse)ᴴ := by
  intro σs
  induction σs with
  | nil =>
      intro τs h
      rw [List.length_nil, eq_comm, List.length_eq_zero_iff] at h
      subst h
      simp only [List.reverse_nil, evalWord_nil, Matrix.conjTranspose_one]
  | cons i is ih =>
      intro τs h
      cases τs with
      | nil => simp at h
      | cons j js =>
          have hlen : is.length = js.length := by simpa using h
          simp only [evalWord_cons, adjointTensor_apply, List.reverse_cons]
          rw [ih js hlen,
            evalWord_append M js.reverse is.reverse [j] [i]
              (by simp only [List.length_reverse]; exact hlen.symm),
            evalWord_cons, evalWord_nil, Matrix.mul_one, Matrix.conjTranspose_mul]

/-- The adjoint tensor generates the adjoint operator family up to spatial
reflection: entrywise,
$H^{(N)}(M^\dagger)_{\sigma\tau}
= \overline{H^{(N)}(M)_{\tau\circ\mathrm{rev},\,\sigma\circ\mathrm{rev}}}$,
where $\mathrm{rev}$ reverses the site order.  This identifies the
$\dagger$-marked chain in the first displayed diagram of the proof of
Proposition 4.13 of arXiv:1606.00608, lines 1909--1913. -/
theorem mpo_adjointTensor (M : MPOTensor d D) {N : ℕ} (σ τ : Fin N → Fin d) :
    mpo (adjointTensor M) N σ τ =
      star (mpo M N (fun k => τ (Fin.rev k)) (fun k => σ (Fin.rev k))) := by
  simp only [mpo_apply, mpoMatrixEntry]
  rw [evalWord_adjointTensor M _ _ (by simp), ← Matrix.trace_conjTranspose,
    List.ofFn_reverse τ, List.ofFn_reverse σ]
  rfl

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
    transferMap M = Kraus.transferMap (toMPSTensor M) := by
  refine LinearMap.ext fun X => ?_
  simp only [transferMap_apply, Kraus.transferMap_apply, toMPSTensor]
  rw [← Fintype.sum_prod_type']
  exact (finProdFinEquiv.symm.sum_comp _).symm

/-- The transfer map of an MPO preserves positive semidefiniteness. -/
theorem transferMap_pos (M : MPOTensor d D)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X.PosSemidef) :
    (transferMap M X).PosSemidef := by
  simpa [transferMap_eq_toMPSTensor] using
    Kraus.transferMap_pos (toMPSTensor M) hX

/-! ### MPDO: global positivity -/

/-- An MPO tensor `M` is an **MPDO** (Matrix Product Density Operator) if
it generates a positive semidefinite operator on every nonempty chain:
`ρ^{(N)}(M) ≥ 0` for all `N > 0`.

Source: arXiv:1606.00608, Section 4, equation `eq:III_MPDOform`, lines 623--630. -/
def IsMPDO (M : MPOTensor d D) : Prop :=
  ∀ N : ℕ, 0 < N → (mpo M N).PosSemidef

/-- For an MPDO, Hermiticity of the density operators removes the conjugation:
the adjoint tensor generates the spatially reflected density operators. -/
theorem IsMPDO.mpo_adjointTensor_eq {M : MPOTensor d D} (hM : IsMPDO M)
    {N : ℕ} (hN : 0 < N) (σ τ : Fin N → Fin d) :
    mpo (adjointTensor M) N σ τ =
      mpo M N (fun k => σ (Fin.rev k)) (fun k => τ (Fin.rev k)) := by
  rw [mpo_adjointTensor]
  exact (hM N hN).isHermitian.apply _ _

/-- The adjoint tensor of an MPDO is again an MPDO: its density operators are
spatial reflections of positive semidefinite operators. -/
theorem IsMPDO.adjointTensor {M : MPOTensor d D} (hM : IsMPDO M) :
    IsMPDO (MPOTensor.adjointTensor M) := by
  intro N hN
  have href : mpo (MPOTensor.adjointTensor M) N =
      (mpo M N).submatrix (fun σ k => σ (Fin.rev k)) (fun τ k => τ (Fin.rev k)) := by
    ext σ τ
    rw [hM.mpo_adjointTensor_eq hN]
    rfl
  rw [href]
  exact (hM N hN).submatrix _

end MPOTensor
