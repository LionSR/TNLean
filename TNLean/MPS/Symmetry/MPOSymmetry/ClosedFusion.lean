/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.Associator
import TNLean.MPS.MPDO.BondOneOperator

/-!
# Closed fusion forces an on-site group representation

**Source.** Garre-Rubio, Lootens, Molnár (arXiv:2203.12563), Section "Periodic
boundary condition case", Lemma, `Papers/2203.12563/REsubmission.tex` lines 1211--1216:
an injective matrix product operator representation of a group with `U_g U_h = U_{gh}` and
`U_e = 1` whose fusion tensors reduce the stacked tensor exactly,
$(T_gT_h)^{ij} = W_{g,h}\,T_{gh}^{ij}\,V_{g,h}$ (equation `fusiontensorG`, lines 641--656),
is on-site, and its three-cocycle is trivial.

**Formalized here.** Both claims, for injective doubled-index tensors, with the source's
on-site notion `U_g = u_g^{⊗ n}` (lines 658 and 842).

The argument follows the proof at line 1213. The identity element is represented by a bond
dimension one tensor with letters `δ_{ij}`: its one- and two-site operators force
`tr(XY) = tr X tr Y` on the span of its letters, which is the whole matrix algebra.
Decomposing the triple product `T_g T_{g⁻¹} T_g` in the two ways allowed by closed fusion gives
`P ⊗ T_g^{ij} = T_g^{ij} ⊗ Q` with `tr P ≠ 0`; injectivity of `T_g` then forces bond dimension
one. With every bond dimension one, the fusion tensors are nonzero scalars `v(g,h)` and the
three-cocycle is the coboundary of `v⁻¹`.

## Main definitions

* `MPOTensor.GroupFamily.IsOnSite`: every periodic operator is a tensor power `u_g^{⊗ N}`.
* `MPOTensor.GroupFamily.FusionData.IsClosed`: closed fusion, equation `fusiontensorG`.

## Main results

* `MPOTensor.GroupFamily.bondDim_eq_one_of_closed_fusion`: every bond dimension is one.
* `MPOTensor.GroupFamily.isOnSite_of_closed_fusion`: the representation is on-site.
* `MPOTensor.GroupFamily.FusionData.isTrivialGaugeClass_omega_of_closed_fusion`: the
  three-cocycle has trivial class.

## References

- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- J. Garre-Rubio, L. Lootens,
  A. Molnár, *Classifying phases protected by matrix product operator symmetries using matrix
  product states*
-/

open scoped Matrix Kronecker
open TNLean.Algebra

namespace MPOTensor

variable {d : ℕ}

/-! ### The tensor of the identity element -/

/-- The trace is multiplicative on the span of the letters of an injective tensor whose one-
and two-site operators are the identity. -/
private theorem trace_mul_eq_of_mpo_eq_one {D : ℕ} {M : MPOTensor d D}
    (hM : Kraus.IsInjective M.toMPSTensor) (h1 : mpo M 1 = 1) (h2 : mpo M 2 = 1)
    (X Y : Matrix (Fin D) (Fin D) ℂ) : (X * Y).trace = X.trace * Y.trace := by
  have hlet : ∀ a b, (M.toMPSTensor a * M.toMPSTensor b).trace =
      (M.toMPSTensor a).trace * (M.toMPSTensor b).trace := by
    intro a b
    have e1 : ∀ i j, (M i j).trace = if i = j then 1 else 0 := fun i j ↦ by
      have := congrFun (congrFun h1 (fun _ ↦ i)) (fun _ ↦ j)
      simpa [mpoMatrixEntry, Matrix.one_apply, funext_iff] using this
    have e2 := congrFun (congrFun h2 ![a.divNat, b.divNat]) ![a.modNat, b.modNat]
    simp only [mpo_apply, mpoMatrixEntry, List.ofFn_succ, List.ofFn_zero, evalWord_cons,
      evalWord_nil, Matrix.mul_one, Matrix.one_apply, funext_iff, Fin.forall_fin_two] at e2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.succ_zero_eq_one] at e2
    change (M a.divNat a.modNat * M b.divNat b.modNat).trace =
      (M a.divNat a.modNat).trace * (M b.divNat b.modNat).trace
    rw [e2, e1, e1]
    by_cases hA : a.divNat = a.modNat <;> by_cases hB : b.divNat = b.modNat <;> simp [hA, hB]
  have hspan : ∀ Z : Matrix (Fin D) (Fin D) ℂ,
      Z ∈ Submodule.span ℂ (Set.range M.toMPSTensor) := fun Z ↦ by
    rw [hM.span_eq_top]; exact Submodule.mem_top
  induction hspan Y using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      induction hspan X using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨a, rfl⟩ := hx
          exact hlet a b
      | zero => simp
      | add x x' _ _ hx hx' =>
          rw [Matrix.add_mul, Matrix.trace_add, Matrix.trace_add, hx, hx', add_mul]
      | smul c x _ hx =>
          rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_smul, hx, smul_eq_mul,
            smul_eq_mul, mul_assoc]
  | zero => simp
  | add y y' _ _ hy hy' =>
      rw [Matrix.mul_add, Matrix.trace_add, Matrix.trace_add, hy, hy', mul_add]
  | smul c y _ hy =>
      rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, hy, smul_eq_mul,
        smul_eq_mul, mul_left_comm]

/-- **The tensor of the identity has bond dimension one.** An injective tensor whose one- and
two-site operators are the identity has bond dimension at most one.

Source: arXiv:2203.12563, line 1213 ("`T_e` has to be the identity matrix"). The source cites
the fundamental theorem of injective matrix product states; the argument here uses only the
trace identity `tr(XY) = tr X tr Y` on the full matrix algebra. -/
theorem bondDim_le_one_of_mpo_eq_one {D : ℕ} {M : MPOTensor d D}
    (hM : Kraus.IsInjective M.toMPSTensor) (h1 : mpo M 1 = 1) (h2 : mpo M 2 = 1) :
    D ≤ 1 := by
  by_contra hD
  push Not at hD
  have h := trace_mul_eq_of_mpo_eq_one hM h1 h2
    (Matrix.single ⟨0, by omega⟩ ⟨1, hD⟩ 1) (Matrix.single ⟨1, hD⟩ ⟨0, by omega⟩ 1)
  rw [Matrix.single_mul_single_same, Matrix.trace_single_eq_same,
    Matrix.trace_single_eq_of_ne _ _ _ (by simp)] at h
  simp at h

/-- The letters of an injective tensor whose one- and two-site operators are the identity are
`M^{ij} = δ_{ij}`.

Source: arXiv:2203.12563, line 1213. -/
theorem eq_ite_one_of_mpo_eq_one {D : ℕ} {M : MPOTensor d D}
    (hM : Kraus.IsInjective M.toMPSTensor) (h1 : mpo M 1 = 1) (h2 : mpo M 2 = 1)
    (i j : Fin d) : M i j = if i = j then 1 else 0 := by
  have hsub : Subsingleton (Fin D) :=
    Fin.subsingleton_iff_le_one.2 (bondDim_le_one_of_mpo_eq_one hM h1 h2)
  have e1 := congrFun (congrFun h1 (fun _ ↦ i)) (fun _ ↦ j)
  simp only [mpo_apply, mpoMatrixEntry, List.ofFn_succ, List.ofFn_zero, evalWord_cons,
    evalWord_nil, Matrix.mul_one, Matrix.one_apply, funext_iff] at e1
  ext a b
  obtain rfl := Subsingleton.elim a b
  rw [Matrix.trace, Fintype.sum_subsingleton _ a] at e1
  simp only [Matrix.diag_apply] at e1
  rw [e1]
  split_ifs <;> simp_all

/-! ### The triple product -/

/-- **The triple-product step.** If the stacked products `A B` and `B A` of two tensors are
`δ_{ik} P` and `δ_{ik} Q` letterwise, with `tr P ≠ 0`, and `A` is injective, then `A` has bond
dimension at most one.

Decomposing `A B A` in the two ways gives `P ⊗ A^{ik} = A^{ik} ⊗ Q`, hence `P ⊗ X = X ⊗ Q` for
every matrix `X`; testing on `X = E_{cc}` kills every diagonal entry of `P` once the bond
dimension is at least two.

Source: arXiv:2203.12563, line 1213 ("we decompose the product of the three MPO tensors
`T_g T_{g⁻¹} T_g` in two equivalent ways ... we close the two upper virtual indices"). -/
theorem bondDim_le_one_of_mulTensor_eq_ite {D₁ D₂ : ℕ} {A : MPOTensor d D₁}
    {B : MPOTensor d D₂} (hA : Kraus.IsInjective A.toMPSTensor)
    {P : Matrix (Fin (D₁ * D₂)) (Fin (D₁ * D₂)) ℂ} {Q : Matrix (Fin (D₂ * D₁)) (Fin (D₂ * D₁)) ℂ}
    (hP : ∀ i k, mulTensor A B i k = if i = k then P else 0)
    (hQ : ∀ i k, mulTensor B A i k = if i = k then Q else 0) (htr : P.trace ≠ 0) :
    D₁ ≤ 1 := by
  -- the entry identity on letters
  have hlet : ∀ (i k : Fin d) (a c : Fin D₁) (b : Fin D₂),
      P (finProdFinEquiv (a, b)) (finProdFinEquiv (a, b)) * A i k c c =
        A i k a a * Q (finProdFinEquiv (b, c)) (finProdFinEquiv (b, c)) := by
    intro i k a c b
    have h := congrFun (congrFun (mulTensor_assoc A B A i k)
      (finProdFinEquiv (finProdFinEquiv (a, b), c)))
      (finProdFinEquiv (finProdFinEquiv (a, b), c))
    simp only [mulTensor_apply, Matrix.submatrix_apply, Matrix.sum_apply,
      Matrix.kroneckerMap_apply, Equiv.symm_apply_apply, mulTensorAssocEquiv,
      Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply,
      Equiv.prodAssoc_apply] at h
    have hPe : ∀ i' j : Fin d, ∑ c', A i' c' a a * B c' j b b =
        if i' = j then P (finProdFinEquiv (a, b)) (finProdFinEquiv (a, b)) else 0 := by
      intro i' j
      have := congrFun (congrFun (hP i' j) (finProdFinEquiv (a, b))) (finProdFinEquiv (a, b))
      simp only [mulTensor_apply, Matrix.submatrix_apply, Matrix.sum_apply,
        Matrix.kroneckerMap_apply, Equiv.symm_apply_apply] at this
      rw [this]
      split_ifs <;> rfl
    have hQe : ∀ i' j : Fin d, ∑ c', B i' c' b b * A c' j c c =
        if i' = j then Q (finProdFinEquiv (b, c)) (finProdFinEquiv (b, c)) else 0 := by
      intro i' j
      have := congrFun (congrFun (hQ i' j) (finProdFinEquiv (b, c))) (finProdFinEquiv (b, c))
      simp only [mulTensor_apply, Matrix.submatrix_apply, Matrix.sum_apply,
        Matrix.kroneckerMap_apply, Equiv.symm_apply_apply] at this
      rw [this]
      split_ifs <;> rfl
    simp only [hPe, hQe, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
    exact h
  -- extension to the full matrix algebra
  have hall : ∀ (X : Matrix (Fin D₁) (Fin D₁) ℂ) (a c : Fin D₁) (b : Fin D₂),
      P (finProdFinEquiv (a, b)) (finProdFinEquiv (a, b)) * X c c =
        X a a * Q (finProdFinEquiv (b, c)) (finProdFinEquiv (b, c)) := by
    intro X a c b
    have hX : X ∈ Submodule.span ℂ (Set.range A.toMPSTensor) := by
      rw [hA.span_eq_top]; exact Submodule.mem_top
    induction hX using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨ik, rfl⟩ := hx
        exact hlet ik.divNat ik.modNat a c b
    | zero => simp
    | add x y _ _ hx hy => simp only [Matrix.add_apply, mul_add, add_mul, hx, hy]
    | smul z x _ hx =>
        simp only [Matrix.smul_apply, smul_eq_mul]
        rw [mul_left_comm, hx, mul_assoc]
  by_contra hD
  push Not at hD
  apply htr
  rw [Matrix.trace, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun b _ ↦ ?_
  obtain ⟨c, hc⟩ : ∃ c : Fin D₁, c ≠ a := by
    by_cases ha : a = ⟨0, by omega⟩
    · exact ⟨⟨1, hD⟩, by rw [ha]; simp⟩
    · exact ⟨⟨0, by omega⟩, Ne.symm ha⟩
  have := hall (Matrix.single c c 1) a c b
  simpa [Matrix.single_apply, hc, Ne.symm hc] using this


/-! ### Matrices on one-point index types -/

section EntrySum

variable {m n p m' n' : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype m'] [Fintype n']

/-- The sum of the entries of a matrix; on one-point index types it is the single entry. -/
private noncomputable def entrySum (X : Matrix m n ℂ) : ℂ := ∑ i, ∑ j, X i j

private theorem apply_eq_entrySum [Subsingleton m] [Subsingleton n] (X : Matrix m n ℂ)
    (i : m) (j : n) : X i j = entrySum X := by
  rw [entrySum, Fintype.sum_subsingleton _ i, Fintype.sum_subsingleton _ j]

private theorem entrySum_mul [Subsingleton n] (X : Matrix m n ℂ) (Y : Matrix n p ℂ) :
    entrySum (X * Y) = entrySum X * entrySum Y := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨j⟩⟩
  · simp [entrySum, Matrix.mul_apply]
  · simp only [entrySum, Matrix.mul_apply, Fintype.sum_subsingleton _ j, Finset.sum_mul_sum]

private theorem entrySum_submatrix (X : Matrix m n ℂ) (e : m' ≃ m) (f : n' ≃ n) :
    entrySum (X.submatrix e f) = entrySum X := by
  simp only [entrySum, Matrix.submatrix_apply]
  exact (e.sum_comp fun i ↦ ∑ j, X i (f j)).trans
    (Finset.sum_congr rfl fun i _ ↦ f.sum_comp (X i))

private theorem entrySum_kronecker (X : Matrix m n ℂ) (Y : Matrix m' n' ℂ) :
    entrySum (X ⊗ₖ Y) = entrySum X * entrySum Y := by
  simp only [entrySum, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Finset.sum_mul_sum]

private theorem entrySum_one (D : ℕ) : entrySum (1 : Matrix (Fin D) (Fin D) ℂ) = D := by
  simp [entrySum, Matrix.one_apply]

private theorem entrySum_toMatrix [DecidableEq n] (e : m ≃ n) :
    entrySum e.toPEquiv.toMatrix = Fintype.card m := by
  simp [entrySum, PEquiv.toMatrix_apply]

end EntrySum

namespace GroupFamily

universe u

variable {G : Type u} [Group G] {F : GroupFamily G d}

/-- A group family is **on-site** when every periodic operator is a tensor power of a one-site
matrix, `U_g = u_g^{⊗ N}` on every nonempty chain.

Source: arXiv:2203.12563, `Papers/2203.12563/REsubmission.tex` line 658 ("the symmetry is
on-site, `O_g = (u_g)^{⊗ n}`") and line 842 ("`U_g = u_g^{⊗ n}`"). -/
def IsOnSite (F : GroupFamily G d) : Prop :=
  ∃ u : G → Matrix (Fin d) (Fin d) ℂ, ∀ g N, 0 < N → ∀ σ τ : Fin N → Fin d,
    mpo (F.tensor g) N σ τ = ∏ n, u g (σ n) (τ n)

/-- A choice of fusion tensors is **closed** when it decomposes every stacked tensor exactly,
letter by letter: `(T_g T_h)^{ij} = W_{g,h} T_{gh}^{ij} V_{g,h}`.

Source: arXiv:2203.12563, equation `fusiontensorG`, `Papers/2203.12563/REsubmission.tex`
lines 641--656, with the fusion tensors of `fusiontensorG2` (lines 1002--1026). -/
def FusionData.IsClosed (fd : FusionData F) : Prop :=
  ∀ g h i, (mulTensor (F.tensor g) (F.tensor h)).toMPSTensor i =
    fd.W g h * (F.tensor (g * h)).toMPSTensor i * fd.V g h

/-- Closed fusion in terms of the two physical indices. -/
theorem FusionData.IsClosed.mulTensor_apply {fd : FusionData F} (hfd : fd.IsClosed)
    (g h : G) (i k : Fin d) :
    mulTensor (F.tensor g) (F.tensor h) i k = fd.W g h * F.tensor (g * h) i k * fd.V g h := by
  simpa only [toMPSTensor_finProdFinEquiv] using hfd g h (finProdFinEquiv (i, k))

/-- **Every bond dimension is one.** For an injective representation with `U_e = 1` and closed
fusion, every tensor has bond dimension one.

Source: arXiv:2203.12563, Lemma, `Papers/2203.12563/REsubmission.tex` lines 1211--1213. -/
theorem bondDim_eq_one_of_closed_fusion
    (hinj : ∀ g, Kraus.IsInjective (F.tensor g).toMPSTensor)
    (hone : ∀ N, 0 < N → mpo (F.tensor 1) N = 1) {fd : FusionData F} (hfd : fd.IsClosed)
    (g : G) : F.bondDim g = 1 := by
  refine le_antisymm ?_ (F.bondDim_pos g)
  have hδ : ∀ {a : G}, a = 1 → ∀ i k : Fin d,
      F.tensor a i k = if i = k then 1 else 0 := by
    rintro a rfl i k
    exact eq_ite_one_of_mpo_eq_one (hinj 1) (hone 1 one_pos) (hone 2 two_pos) i k
  have hclosed : ∀ a b : G, a * b = 1 → ∀ i k : Fin d,
      mulTensor (F.tensor a) (F.tensor b) i k = if i = k then fd.W a b * fd.V a b else 0 := by
    intro a b hab i k
    rw [hfd.mulTensor_apply, hδ hab]
    split_ifs <;> simp
  refine bondDim_le_one_of_mulTensor_eq_ite (hinj g) (hclosed g g⁻¹ (mul_inv_cancel g))
    (hclosed g⁻¹ g (inv_mul_cancel g)) ?_
  rw [Matrix.trace_mul_comm, (fd.isReduction g g⁻¹).mul_eq_one, Matrix.trace_one]
  simpa using (F.bondDim_pos _).ne'

/-- **Closed fusion forces an on-site representation.** An injective matrix product operator
representation of a group with `U_g U_h = U_{gh}` and `U_e = 1`, whose fusion tensors
decompose every stacked tensor exactly, is on-site: `U_g = u_g^{⊗ N}` with
`u_g = (T_g^{ij})_{ij}` the one-site matrix of the bond dimension one tensor.

The product law is not needed for the on-site conclusion.

Source: arXiv:2203.12563, Lemma, `Papers/2203.12563/REsubmission.tex` lines 1211--1213. -/
theorem isOnSite_of_closed_fusion
    (hinj : ∀ g, Kraus.IsInjective (F.tensor g).toMPSTensor)
    (hone : ∀ N, 0 < N → mpo (F.tensor 1) N = 1) {fd : FusionData F} (hfd : fd.IsClosed) :
    F.IsOnSite := by
  refine ⟨fun g i j ↦ (F.tensor g i j).trace, fun g N hN σ τ ↦ ?_⟩
  have key : ∀ (D : ℕ) (M : MPOTensor d D), D = 1 →
      mpo M N σ τ = ∏ n, (M (σ n) (τ n)).trace := by
    rintro D M rfl
    have : NeZero N := ⟨hN.ne'⟩
    rw [mpo_apply_of_bondOne]
    simp [Matrix.trace_fin_one]
  exact key _ _ (bondDim_eq_one_of_closed_fusion hinj hone hfd g)

/-- **Closed fusion forces a trivial three-cocycle.** For an injective matrix product operator
representation of a group with `U_g U_h = U_{gh}`, `U_e = 1`, and closed fusion, the anomaly
three-cocycle `ω` of the fusion tensors has trivial class: with every bond dimension one, the
fusion tensors are nonzero scalars `v(g,h)` and `ω` is the coboundary of `v⁻¹`.

Source: arXiv:2203.12563, Lemma, `Papers/2203.12563/REsubmission.tex` lines 1211--1213 ("In
particular, the MPO representation is characterized by a trivial `3`-cocycle"), with the
three-cocycle of the fusion tensors of arXiv:2502.20257, `main.tex` lines 1506--1545. -/
theorem FusionData.isTrivialGaugeClass_omega_of_closed_fusion
    (hinj : ∀ g, Kraus.IsInjective (F.tensor g).toMPSTensor)
    (hone : ∀ N, 0 < N → mpo (F.tensor 1) N = 1)
    (hmul : ∀ g h N, 0 < N →
      mpo (F.tensor g) N * mpo (F.tensor h) N = mpo (F.tensor (g * h)) N)
    {fd : FusionData F} (hfd : fd.IsClosed) :
    ScalarThreeCochain.IsTrivialGaugeClass fd.omega := by
  have hχ := bondDim_eq_one_of_closed_fusion hinj hone hfd
  have hF : F.IsNormalRepresentation := ⟨fun g ↦ (hinj g).isNormal, hmul⟩
  have hc : ∀ g, (F.bondDim g : ℂ) = 1 := fun g ↦ by rw [hχ]; norm_num
  have sub : ∀ n : ℕ, n = 1 → Subsingleton (Fin n) := by rintro n rfl; infer_instance
  let v : G → G → ℂ := fun g h ↦ entrySum (fd.V g h)
  have hv : ∀ g h, v g h ≠ 0 := by
    intro g h h0
    have := sub (F.bondDim g * F.bondDim h) (by rw [hχ, hχ])
    have key := entrySum_mul (fd.V g h) (fd.W g h)
    rw [(fd.isReduction g h).mul_eq_one, entrySum_one, hc] at key
    have : entrySum (fd.V g h) = 0 := h0
    rw [this, zero_mul] at key
    exact one_ne_zero key
  have hω : ∀ g h k, (fd.omega g h k : ℂ) = v (g * h) k * v g h / (v g (h * k) * v h k) := by
    intro g h k
    have := sub (F.bondDim (g * h * k)) (hχ _)
    have := sub (F.bondDim g * F.bondDim h * F.bondDim k) (by rw [hχ, hχ, hχ])
    have := sub (F.bondDim (g * h) * F.bondDim k) (by rw [hχ, hχ])
    have := sub (F.bondDim (g * (h * k))) (hχ _)
    have := sub (F.bondDim g * F.bondDim (h * k)) (by rw [hχ, hχ])
    have := sub (F.bondDim g * (F.bondDim h * F.bondDim k)) (by rw [hχ, hχ, hχ])
    have hL : entrySum (fd.leftV g h k) = v (g * h) k * v g h := by
      rw [FusionData.leftV, entrySum_mul, kronId, entrySum_submatrix, entrySum_kronecker,
        entrySum_one, hc]
      simp [v]
    have hR : entrySum (fd.rightV g h k) = v g (h * k) * v h k := by
      rw [FusionData.rightV, entrySum_mul, entrySum_mul, entrySum_mul, castMat,
        entrySum_toMatrix, idKron, entrySum_submatrix, entrySum_kronecker, entrySum_one,
        mulTensorAssocInvMatrix, entrySum_toMatrix]
      simp [v, hc]
    refine (eq_omega_of_isAssociator hF (fd := fd) ⟨0, fun w _ ↦ ?_⟩).symm
    have hLR : fd.leftV g h k =
        (v (g * h) k * v g h / (v g (h * k) * v h k)) • fd.rightV g h k := by
      ext a x
      rw [Matrix.smul_apply, apply_eq_entrySum (fd.leftV g h k),
        apply_eq_entrySum (fd.rightV g h k), hL, hR, smul_eq_mul,
        div_mul_cancel₀ _ (mul_ne_zero (hv _ _) (hv _ _))]
    rw [hLR, Matrix.smul_mul]
  refine ⟨fun g h ↦ (Units.mk0 (v g h) (hv g h))⁻¹, funext fun g ↦ funext fun h ↦
    funext fun k ↦ Units.ext ?_⟩
  simp only [ScalarThreeCochain.fusionGauge, ScalarThreeCochain.coboundary, Units.val_mul,
    Units.val_div_eq_div_val, Units.val_inv_eq_inv_val, Units.val_mk0, mul_one,
    hω]
  have := hv g h; have := hv (g * h) k; have := hv g (h * k); have := hv h k
  field_simp

end GroupFamily

end MPOTensor
