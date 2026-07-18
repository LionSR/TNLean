/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CommutingBondEtaCyclicTransport
import TNLean.MPS.MPDO.SitewisePhysicalMatrix

/-!
# Finite-chain neighboring-operator decomposition

This file combines the local neighboring-operator decomposition of a positive commuting
bond with its cyclic finite-chain transport.  The one-site unitary, sector decomposition,
and positive neighboring operators are independent of the chain length.  The positive
scalar relating the matrix-product operator to the commuting-bond product may depend on
the chain length.

No zero-correlation-length hypothesis, trace factorization, Markov decomposition, or
saturation of the area law is used.

## Main statement

* `MPOTensor.EtaLocalStructureData.exists_finite_chain_eta_decomposition`

## References

* arXiv:1606.00608, Appendix C.2, equation sigmaNK2, lines 1581--1605.
-/

open scoped BigOperators ComplexOrder Kronecker Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- On two sites, the configuration-indexed tensor power is the Kronecker square after
the standard identification of a two-site configuration with an ordered pair. -/
theorem reindex_sitewisePhysicalMatrix_two
    (V : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.reindex (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d))
        (sitewisePhysicalMatrix V 2) =
      V ⊗ₖ V := by
  ext ⟨i, j⟩ ⟨a, b⟩
  simp [Matrix.reindex_apply, sitewisePhysicalMatrix,
    Matrix.kroneckerMap_apply, finTwoArrowEquiv]

/-- Taking the conjugate transpose commutes with the sitewise tensor power. -/
theorem sitewisePhysicalMatrix_conjTranspose
    (V : Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    (sitewisePhysicalMatrix V N)ᴴ =
      sitewisePhysicalMatrix (star V) N := by
  ext s t
  simp [sitewisePhysicalMatrix, Matrix.conjTranspose_apply, star_prod]

/-- Multiplication of sitewise tensor powers is computed one site at a time. -/
theorem sitewisePhysicalMatrix_mul
    (V W : Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    sitewisePhysicalMatrix V N * sitewisePhysicalMatrix W N =
      sitewisePhysicalMatrix (V * W) N := by
  classical
  ext x y
  simp only [Matrix.mul_apply, sitewisePhysicalMatrix]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.piFinset_univ]
  rw [← Finset.prod_univ_sum
    (fun _ : Fin N ↦ (Finset.univ : Finset (Fin d)))
    (fun n z ↦ V (x n) z * W z (y n))]

/-- The sitewise tensor power of the identity matrix is the identity matrix. -/
@[simp] theorem sitewisePhysicalMatrix_one (N : ℕ) :
    sitewisePhysicalMatrix (1 : Matrix (Fin d) (Fin d) ℂ) N = 1 := by
  ext x y
  simp only [sitewisePhysicalMatrix, Matrix.one_apply]
  rw [Fintype.prod_boole]
  congr 1
  exact propext funext_iff.symm

/-- The sitewise tensor power of a unitary matrix is unitary. -/
theorem sitewisePhysicalMatrix_mem_unitaryGroup
    (V : Matrix (Fin d) (Fin d) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (N : ℕ) :
    sitewisePhysicalMatrix V N ∈
      Matrix.unitaryGroup (Fin N → Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  rw [Matrix.star_eq_conjTranspose, sitewisePhysicalMatrix_conjTranspose,
    sitewisePhysicalMatrix_mul,
    Matrix.mem_unitaryGroup_iff'.mp hV, sitewisePhysicalMatrix_one]

private def etaCyclicShiftEquiv (N : ℕ) (i : Fin N) : Fin N ≃ Fin N where
  toFun k := ⟨(i.val + k.val) % N, Nat.mod_lt _ (Fin.pos i)⟩
  invFun k := ⟨(k.val + N - i.val) % N, Nat.mod_lt _ (Fin.pos i)⟩
  left_inv k := by
    apply Fin.ext
    exact MPSTensor.offset_mod_eq i.isLt k.isLt
  right_inv k := by
    apply Fin.ext
    change (i.val + ((k.val + N - i.val) % N)) % N = k.val
    let offset := (k.val + N - i.val) % N
    have hsite : (i.val + offset) % N = k.val := by
      rcases lt_or_ge k.val i.val with hki | hik
      · have hmod : offset = k.val + N - i.val := by
          simp only [offset]
          rw [Nat.mod_eq_of_lt (by omega)]
        rw [hmod, show i.val + (k.val + N - i.val) = k.val + N by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt k.isLt]
      · have hmod : offset = k.val - i.val := by
          simp only [offset]
          have heq : k.val + N - i.val = N + (k.val - i.val) := by omega
          rw [heq, Nat.add_mod_left,
            Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) k.isLt)]
        rw [hmod, Nat.add_sub_of_le hik, Nat.mod_eq_of_lt k.isLt]
    exact hsite

private def etaCyclicWindowIndexEquiv
    (L N : ℕ) (hLN : L ≤ N) (i : Fin N) :
    Fin L ⊕ Fin (N - L) ≃ Fin N :=
  finSumFinEquiv |>.trans (finCongr (Nat.add_sub_of_le hLN)) |>.trans
    (etaCyclicShiftEquiv N i)

@[simp] private theorem etaCyclicWindowIndexEquiv_inl
    (L N : ℕ) (hLN : L ≤ N) (i : Fin N) (r : Fin L) :
    etaCyclicWindowIndexEquiv L N hLN i (Sum.inl r) =
      ⟨(i.val + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩ := rfl

@[simp] private theorem etaCyclicWindowIndexEquiv_inr
    (L N : ℕ) (hLN : L ≤ N) (i : Fin N) (r : Fin (N - L)) :
    etaCyclicWindowIndexEquiv L N hLN i (Sum.inr r) =
      ⟨(i.val + L + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩ := by
  apply Fin.ext
  change (i.val + (L + r.val)) % N = (i.val + L + r.val) % N
  congr 1
  omega

private theorem prod_etaCyclicWindow_complement
    (L N : ℕ) (hLN : L ≤ N) (i : Fin N) (f : Fin N → ℂ) :
    (∏ n : Fin N, f n) =
      (∏ r : Fin L,
        f ⟨(i.val + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩) *
        (∏ r : Fin (N - L),
          f ⟨(i.val + L + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩) := by
  rw [Fintype.prod_equiv
    (etaCyclicWindowIndexEquiv L N hLN i).symm f
    (fun x ↦ f (etaCyclicWindowIndexEquiv L N hLN i x))
    (fun n ↦ by simp)]
  rw [Fintype.prod_sum_type]
  simp only [etaCyclicWindowIndexEquiv_inl,
    etaCyclicWindowIndexEquiv_inr]

private theorem reindex_sitewisePhysicalMatrix_etaWindowComplement
    (V : Matrix (Fin d) (Fin d) ℂ) {N : ℕ} (hN : 2 ≤ N) (i : Fin N) :
    Matrix.reindex (windowComplementEquiv (d := d) 2 N hN i)
        (windowComplementEquiv (d := d) 2 N hN i)
        (sitewisePhysicalMatrix V N) =
      sitewisePhysicalMatrix V 2 ⊗ₖ
        sitewisePhysicalMatrix V (N - 2) := by
  ext ⟨x, u⟩ ⟨y, v⟩
  let e := windowComplementEquiv (d := d) 2 N hN i
  let s := e.symm (x, u)
  let t := e.symm (y, v)
  have hx : MPSTensor.extractWindow 2 i s = x :=
    congrArg Prod.fst (e.apply_symm_apply (x, u))
  have hy : MPSTensor.extractWindow 2 i t = y :=
    congrArg Prod.fst (e.apply_symm_apply (y, v))
  have hu : (fun r ↦ s ⟨(i.val + 2 + r.val) % N,
      Nat.mod_lt _ (Fin.pos i)⟩) = u :=
    congrArg Prod.snd (e.apply_symm_apply (x, u))
  have hv : (fun r ↦ t ⟨(i.val + 2 + r.val) % N,
      Nat.mod_lt _ (Fin.pos i)⟩) = v :=
    congrArg Prod.snd (e.apply_symm_apply (y, v))
  change (∏ n : Fin N, V (s n) (t n)) = _
  rw [prod_etaCyclicWindow_complement 2 N hN i]
  simp only [MPSTensor.extractWindow] at hx hy
  simp only [sitewisePhysicalMatrix, Matrix.kroneckerMap_apply]
  apply congrArg₂ (fun a b : ℂ ↦ a * b)
  · apply Finset.prod_congr rfl
    intro r _
    rw [congrFun hx r, congrFun hy r]
  · apply Finset.prod_congr rfl
    intro r _
    rw [congrFun hu r, congrFun hv r]

/-- Conjugating a translated two-site operator by a sitewise unitary is the
translation of its two-site conjugate. -/
theorem singleKrausMap_sitewisePhysicalMatrix_embedLocalOperator
    (V : Matrix (Fin d) (Fin d) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ)
    {N : ℕ} (hN : 2 ≤ N) (i : Fin N)
    (B : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) :
    singleKrausMap (sitewisePhysicalMatrix V N)
        (embedLocalOperator (d := d) 2 N hN i B) =
      embedLocalOperator (d := d) 2 N hN i
        (singleKrausMap (sitewisePhysicalMatrix V 2) B) := by
  let e := windowComplementEquiv (d := d) 2 N hN i
  apply (Matrix.reindex e e).injective
  simp only [singleKrausMap_apply]
  change Matrix.reindexLinearEquiv ℂ ℂ e e
      (sitewisePhysicalMatrix V N *
        embedLocalOperator (d := d) 2 N hN i B *
          (sitewisePhysicalMatrix V N)ᴴ) = _
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ e e e,
    ← Matrix.reindexLinearEquiv_mul ℂ ℂ e e e]
  simp only [Matrix.coe_reindexLinearEquiv]
  rw [reindex_sitewisePhysicalMatrix_etaWindowComplement,
    reindex_embedLocalOperator_windowComplement,
    reindex_embedLocalOperator_windowComplement]
  have hVH : Matrix.reindex e e (sitewisePhysicalMatrix V N)ᴴ =
      (sitewisePhysicalMatrix V 2)ᴴ ⊗ₖ
        (sitewisePhysicalMatrix V (N - 2))ᴴ := by
    simpa only [Matrix.conjTranspose_reindex,
      Matrix.conjTranspose_kronecker] using congrArg Matrix.conjTranspose
        (reindex_sitewisePhysicalMatrix_etaWindowComplement V hN i)
  rw [hVH, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  have hcoiso : sitewisePhysicalMatrix V (N - 2) *
      (sitewisePhysicalMatrix V (N - 2))ᴴ = 1 := by
    exact Matrix.mem_unitaryGroup_iff.mp
      (sitewisePhysicalMatrix_mem_unitaryGroup V hV (N - 2))
  rw [Matrix.mul_one, hcoiso]

private theorem singleKrausMap_mul_of_isometry
    {a b : Type*} [Fintype a] [Fintype b] [DecidableEq b]
    (V : Matrix a b ℂ) (hV : Vᴴ * V = 1)
    (X Y : Matrix b b ℂ) :
    singleKrausMap V (X * Y) =
      singleKrausMap V X * singleKrausMap V Y := by
  simp only [singleKrausMap_apply, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul]

private theorem singleKrausMap_list_prod_of_unitary
    {a : Type*} [Fintype a] [DecidableEq a]
    (V : Matrix a a ℂ) (hV : V ∈ Matrix.unitaryGroup a ℂ)
    (l : List (Matrix a a ℂ)) :
    singleKrausMap V l.prod =
      (l.map (singleKrausMap V)).prod := by
  induction l with
  | nil =>
      simp only [List.prod_nil, List.map_nil, singleKrausMap_apply,
        Matrix.mul_one]
      exact Matrix.mem_unitaryGroup_iff.mp hV
  | cons X l ih =>
      simp only [List.prod_cons, List.map_cons]
      rw [singleKrausMap_mul_of_isometry V
        (by simpa only [Matrix.star_eq_conjTranspose] using
          Matrix.mem_unitaryGroup_iff'.mp hV), ih]

/-- Under the ordered-pair coordinates, two-site sitewise conjugation is
conjugation by the Kronecker square. -/
theorem reindex_singleKrausMap_sitewisePhysicalMatrix_two
    (V : Matrix (Fin d) (Fin d) ℂ)
    (B : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) :
    Matrix.reindex (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d))
        (singleKrausMap (sitewisePhysicalMatrix V 2) B) =
      singleKrausMap (V ⊗ₖ V) (pairBondMatrix B) := by
  simp only [singleKrausMap_apply]
  change Matrix.reindexLinearEquiv ℂ ℂ
      (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d))
      (sitewisePhysicalMatrix V 2 * B *
        (sitewisePhysicalMatrix V 2)ᴴ) = _
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ
      (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d))
      (finTwoArrowEquiv (Fin d)),
    ← Matrix.reindexLinearEquiv_mul ℂ ℂ
      (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d))
      (finTwoArrowEquiv (Fin d))]
  simp only [Matrix.coe_reindexLinearEquiv]
  rw [reindex_sitewisePhysicalMatrix_two]
  have hVH : Matrix.reindex (finTwoArrowEquiv (Fin d))
      (finTwoArrowEquiv (Fin d)) (sitewisePhysicalMatrix V 2)ᴴ =
        (V ⊗ₖ V)ᴴ := by
    simpa only [Matrix.conjTranspose_reindex] using congrArg Matrix.conjTranspose
      (reindex_sitewisePhysicalMatrix_two V)
  rw [hVH]
  rfl

/-- Conjugating the ordered product of translated bonds by the sitewise
tensor power of (U^*) gives the ordered product of the locally conjugated
bonds. -/
theorem singleKrausMap_product_embedLocalOperator_star
    (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    {N : ℕ} (hN : 2 ≤ N)
    (B : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) :
    singleKrausMap (sitewisePhysicalMatrix (star U) N)
        (List.ofFn fun i : Fin N ↦
          embedLocalOperator (d := d) 2 N hN i B).prod =
      (List.ofFn fun i : Fin N ↦
        embedLocalOperator (d := d) 2 N hN i
          (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
            (finTwoArrowEquiv (Fin d)).symm
            (star (U ⊗ₖ U) * pairBondMatrix B * (U ⊗ₖ U)))).prod := by
  have hstarU : star U ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    simpa only [star_star] using Matrix.mem_unitaryGroup_iff.mp hU
  have hUN : sitewisePhysicalMatrix (star U) N ∈
      Matrix.unitaryGroup (Fin N → Fin d) ℂ :=
    sitewisePhysicalMatrix_mem_unitaryGroup (star U) hstarU N
  rw [singleKrausMap_list_prod_of_unitary _ hUN]
  rw [List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  change singleKrausMap (sitewisePhysicalMatrix (star U) N)
      (embedLocalOperator (d := d) 2 N hN i B) = _
  rw [singleKrausMap_sitewisePhysicalMatrix_embedLocalOperator
    (star U) hstarU hN i B]
  congr 1
  apply (Matrix.reindex (finTwoArrowEquiv (Fin d))
    (finTwoArrowEquiv (Fin d))).injective
  rw [reindex_singleKrausMap_sitewisePhysicalMatrix_two]
  simp only [pairBondMatrix, Matrix.reindex_apply]
  simp only [singleKrausMap_apply, Matrix.conjTranspose_kronecker,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  ext x y
  rfl

namespace EtaLocalStructureData

variable {M : MPOTensor d D}

/-- A positive translation-invariant commuting bond has one chain-independent
unitary decomposition for which every finite-chain matrix-product operator is
a positive scalar multiple of the cyclic direct sum of neighboring operators:
\[
  \mathcal R_{E_N}\!\left(
    (U^{*\otimes N})\,\sigma^{(N)}(M)\,U^{\otimes N}\right)
  = c_N \bigoplus_{k_0,\ldots,k_{N-1}}
      \bigotimes_{n=0}^{N-1}\eta_{k_n,k_{n+1}},
  \qquad c_N>0.
\]
Here \(E_N\) is the bijection from site configurations to sector-labelled
cyclic edge configurations, and
\(\mathcal R_{E_N}(A)_{s,t}=A_{E_N^{-1}(s),E_N^{-1}(t)}\).
The unitary, sector dimensions, and positive neighboring operators are the
same for every \(N\ge 2\); only the scalar may depend on \(N\).

No zero-correlation-length hypothesis, trace factorization, Markov
decomposition, or saturation of the area law is used.

Source: arXiv:1606.00608, Appendix C.2, equation sigmaNK2, lines
1581--1605. -/
theorem exists_finite_chain_eta_decomposition
    (data : EtaLocalStructureData M) :
    ∃ (K : ℕ) (dl dr : Fin K → ℕ)
      (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d)
      (U : Matrix (Fin d) (Fin d) ℂ)
      (η : (q h : Fin K) →
        Matrix (Matrix.EtaEdgeIndex dl dr q h)
          (Matrix.EtaEdgeIndex dl dr q h) ℂ),
      U ∈ Matrix.unitaryGroup (Fin d) ℂ ∧
        (∀ q, 0 < dl q) ∧ (∀ q, 0 < dr q) ∧
        (∀ q h, (η q h).PosSemidef) ∧
        ∀ (N : ℕ) (hN : 2 ≤ N),
          let _ : NeZero N := ⟨by omega⟩
          ∃ c : ℝ, 0 < c ∧
            Matrix.reindex (Matrix.etaCyclicEdgeEquiv dl dr e)
                (Matrix.etaCyclicEdgeEquiv dl dr e)
                (star (sitewisePhysicalMatrix U N) * mpo M N *
                  sitewisePhysicalMatrix U N) =
              (c : ℂ) • Matrix.blockDiagonal' fun k : Fin N → Fin K ↦
                fun x y ↦ ∏ n : Fin N,
                  η (k n) (k (n + 1)) (x n) (y n) := by
  classical
  obtain ⟨K, dl, dr, e, U, η, hU, hdl, hdr, hη, hB⟩ :=
    data.exists_positive_eta_pairBond_decomposition
  refine ⟨K, dl, dr, e, U, η, hU, hdl, hdr, hη, ?_⟩
  intro N hN
  dsimp only
  letI : NeZero N := ⟨by omega⟩
  obtain ⟨c, hc, hreal⟩ := data.exists_positive_scalar_mpo_eq_product N hN
  refine ⟨c, hc, ?_⟩
  have hproduct := singleKrausMap_product_embedLocalOperator_star
    U hU hN data.bondData.bond
  have hcyclic := reindex_product_embedLocalOperator_of_etaPair_decomposition
    hN dl dr e η
      (star (U ⊗ₖ U) * data.pairBond * (U ⊗ₖ U)) hB
  dsimp only [pairBond] at hcyclic
  rw [Matrix.star_eq_conjTranspose,
    sitewisePhysicalMatrix_conjTranspose]
  have hsandwich :
      singleKrausMap (sitewisePhysicalMatrix (star U) N) (mpo M N) =
        sitewisePhysicalMatrix (star U) N * mpo M N *
          sitewisePhysicalMatrix U N := by
    simp [singleKrausMap_apply, sitewisePhysicalMatrix_conjTranspose]
  rw [← hsandwich]
  rw [hreal]
  rw [(singleKrausMap (sitewisePhysicalMatrix (star U) N)).map_smul]
  rw [show Matrix.reindex (Matrix.etaCyclicEdgeEquiv dl dr e)
      (Matrix.etaCyclicEdgeEquiv dl dr e)
      ((c : ℂ) • singleKrausMap (sitewisePhysicalMatrix (star U) N)
        (data.formAt N hN).product) =
      (c : ℂ) • Matrix.reindex (Matrix.etaCyclicEdgeEquiv dl dr e)
        (Matrix.etaCyclicEdgeEquiv dl dr e)
        (singleKrausMap (sitewisePhysicalMatrix (star U) N)
          (data.formAt N hN).product) by rfl]
  change (c : ℂ) • Matrix.reindex (Matrix.etaCyclicEdgeEquiv dl dr e)
      (Matrix.etaCyclicEdgeEquiv dl dr e)
      (singleKrausMap (sitewisePhysicalMatrix (star U) N)
        (List.ofFn fun i : Fin N ↦
          embedLocalOperator (d := d) 2 N hN i data.bondData.bond).prod) = _
  rw [hproduct, hcyclic]

end EtaLocalStructureData

end MPOTensor
