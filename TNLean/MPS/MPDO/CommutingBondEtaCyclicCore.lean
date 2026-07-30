/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.PiSigmaEquiv
import TNLean.MPS.MPDO.CommutingBondEtaDecomposition
import TNLean.MPS.MPDO.SitewisePhysicalMatrix

/-!
# Cyclic transport of neighboring operators

This file transports a two-site neighboring-operator decomposition around a periodic
finite chain.  The argument is purely algebraic: it uses neither zero correlation length,
trace factorization, a Markov decomposition, nor saturation of the area law.

## References

* arXiv:1606.00608, Appendix C.2, equation expression, lines 1571--1576,
  and equation sigmaNK2, lines 1581--1605.
-/

open scoped BigOperators ComplexOrder Kronecker Matrix

namespace Matrix

/-- A one-site sector index in the coordinate order
\(H_{q,r}\otimes H_{q,l}\). -/
abbrev EtaSiteIndex (K : ℕ) (dl dr : Fin K → ℕ) :=
  Σ q : Fin K, Fin (dr q) × Fin (dl q)

/-- The neighboring index carried by the cyclic edge from sector \(q\) to sector \(h\). -/
abbrev EtaEdgeIndex {K : ℕ} (dl dr : Fin K → ℕ) (q h : Fin K) :=
  Fin (dr q) × Fin (dl h)

/-- For a fixed cyclic sector configuration, regroup the site factors
\((R_n,L_n)\) into the edge factors \((R_n,L_{n+1})\). -/
def etaFixedSectorCyclicEdgeEquiv {K N : ℕ} [NeZero N]
    (dl dr : Fin K → ℕ) (k : Fin N → Fin K) :
    ((n : Fin N) → Fin (dr (k n)) × Fin (dl (k n))) ≃
      ((n : Fin N) → EtaEdgeIndex dl dr (k n) (k (n + 1))) :=
  (Equiv.arrowProdEquivProdArrow _ _ _).trans <|
    (Equiv.prodCongr (Equiv.refl _)
      (Equiv.piCongrLeft
        (fun n : Fin N ↦ Fin (dl (k n))) (finRotate N)).symm).trans <|
      (Equiv.arrowProdEquivProdArrow _ _ _).symm |>.trans <|
        Equiv.piCongrRight fun n ↦
          Equiv.prodCongr (Equiv.refl _)
            (finCongr (congrArg dl (congrArg k (finRotate_apply n))))

@[simp] theorem etaFixedSectorCyclicEdgeEquiv_apply {K N : ℕ} [NeZero N]
    (dl dr : Fin K → ℕ) (k : Fin N → Fin K)
    (x : (n : Fin N) → Fin (dr (k n)) × Fin (dl (k n))) (n : Fin N) :
    etaFixedSectorCyclicEdgeEquiv dl dr k x n = ((x n).1, (x (n + 1)).2) := by
  apply Prod.ext
  · rfl
  · apply Fin.ext
    change ((x (finRotate N n)).2 : ℕ) = ((x (n + 1)).2 : ℕ)
    rw [finRotate_apply]

@[simp] theorem etaFixedSectorCyclicEdgeEquiv_symm_edge {K N : ℕ} [NeZero N]
    (dl dr : Fin K → ℕ) (k : Fin N → Fin K)
    (x : (n : Fin N) → EtaEdgeIndex dl dr (k n) (k (n + 1)))
    (n : Fin N) :
    (((etaFixedSectorCyclicEdgeEquiv dl dr k).symm x n).1,
        ((etaFixedSectorCyclicEdgeEquiv dl dr k).symm x (n + 1)).2) = x n := by
  have h := congrFun ((etaFixedSectorCyclicEdgeEquiv dl dr k).apply_symm_apply x) n
  simpa only [etaFixedSectorCyclicEdgeEquiv_apply] using h

/-- Apply the one-site sector decomposition at every site and regroup the site factors into
cyclic neighboring factors. -/
def etaCyclicEdgeEquiv {K N d : ℕ} [NeZero N] (dl dr : Fin K → ℕ)
    (e : EtaSiteIndex K dl dr ≃ Fin d) :
    (Fin N → Fin d) ≃
      Σ k : Fin N → Fin K,
        (n : Fin N) → EtaEdgeIndex dl dr (k n) (k (n + 1)) :=
  ((Equiv.piCongrRight fun _ : Fin N ↦ e.symm).trans Equiv.piSigmaEquiv).trans <|
    Equiv.sigmaCongrRight fun k ↦ etaFixedSectorCyclicEdgeEquiv dl dr k

@[simp] theorem etaCyclicEdgeEquiv_symm_apply {K N d : ℕ} [NeZero N]
    (dl dr : Fin K → ℕ) (e : EtaSiteIndex K dl dr ≃ Fin d)
    (k : Fin N → Fin K)
    (x : (n : Fin N) → EtaEdgeIndex dl dr (k n) (k (n + 1)))
    (n : Fin N) :
    (etaCyclicEdgeEquiv dl dr e).symm ⟨k, x⟩ n =
      e ⟨k n, (etaFixedSectorCyclicEdgeEquiv dl dr k).symm x n⟩ := by
  apply e.symm.injective
  simp [etaCyclicEdgeEquiv, Equiv.piCongrRight, Equiv.sigmaCongrRight]

end Matrix

namespace MPOTensor

variable {d : ℕ}

/-- In pair coordinates, conjugating a two-site operator by the tensor square
of a conjugate-transposed one-site matrix is the corresponding Kronecker
conjugation. -/
theorem singleKrausMap_sitewise_conjTranspose_two_eq
    (U : Matrix (Fin d) (Fin d) ℂ)
    (B : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) :
    singleKrausMap (sitewisePhysicalMatrix Uᴴ 2) B =
      Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
        (finTwoArrowEquiv (Fin d)).symm
        (star (U ⊗ₖ U) * pairBondMatrix B * (U ⊗ₖ U)) := by
  apply (Matrix.reindex (finTwoArrowEquiv (Fin d))
    (finTwoArrowEquiv (Fin d))).injective
  rw [Matrix.reindex_singleKrausMap
      (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d)),
    reindex_sitewisePhysicalMatrix_two]
  rw [show Matrix.reindex (finTwoArrowEquiv (Fin d))
      (finTwoArrowEquiv (Fin d))
      (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
        (finTwoArrowEquiv (Fin d)).symm
        (star (U ⊗ₖ U) * pairBondMatrix B * (U ⊗ₖ U))) =
      star (U ⊗ₖ U) * pairBondMatrix B * (U ⊗ₖ U) by
    exact (Matrix.reindex (finTwoArrowEquiv (Fin d))
      (finTwoArrowEquiv (Fin d))).apply_symm_apply _]
  simp only [singleKrausMap_apply, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_conjTranspose]
  change (Uᴴ ⊗ₖ Uᴴ) * pairBondMatrix B * (U ⊗ₖ U) =
    star (U ⊗ₖ U) * pairBondMatrix B * (U ⊗ₖ U)
  simp [Matrix.conjTranspose_kronecker, Matrix.star_eq_conjTranspose]

/-- The product on a chosen set of cyclic edges.  Edges outside the set carry the
identity matrix. -/
private noncomputable def etaEdgePartialProduct {K N : ℕ} [NeZero N]
    (dl dr : Fin K → ℕ)
    (η : (q h : Fin K) →
      Matrix (Matrix.EtaEdgeIndex dl dr q h) (Matrix.EtaEdgeIndex dl dr q h) ℂ)
    (k : Fin N → Fin K) (s : Finset (Fin N)) :
    Matrix ((n : Fin N) → Matrix.EtaEdgeIndex dl dr (k n) (k (n + 1)))
      ((n : Fin N) → Matrix.EtaEdgeIndex dl dr (k n) (k (n + 1))) ℂ :=
  fun x y ↦ ∏ n : Fin N,
    if n ∈ s then η (k n) (k (n + 1)) (x n) (y n)
    else if x n = y n then 1 else 0

@[simp] private theorem etaEdgePartialProduct_empty {K N : ℕ} [NeZero N]
    (dl dr : Fin K → ℕ)
    (η : (q h : Fin K) →
      Matrix (Matrix.EtaEdgeIndex dl dr q h) (Matrix.EtaEdgeIndex dl dr q h) ℂ)
    (k : Fin N → Fin K) :
    etaEdgePartialProduct dl dr η k ∅ = 1 := by
  ext x y
  simp only [etaEdgePartialProduct, Finset.notMem_empty, ↓reduceIte,
    Matrix.one_apply]
  rw [Fintype.prod_boole]
  congr 1
  exact propext funext_iff.symm

@[simp] private theorem etaEdgePartialProduct_univ {K N : ℕ} [NeZero N]
    (dl dr : Fin K → ℕ)
    (η : (q h : Fin K) →
      Matrix (Matrix.EtaEdgeIndex dl dr q h) (Matrix.EtaEdgeIndex dl dr q h) ℂ)
    (k : Fin N → Fin K) :
    etaEdgePartialProduct dl dr η k Finset.univ =
      fun x y ↦ ∏ n : Fin N, η (k n) (k (n + 1)) (x n) (y n) := by
  ext x y
  simp [etaEdgePartialProduct]

/-- Multiplication by a new one-edge factor adjoins that edge to a partial product. -/
private theorem etaEdgePartialProduct_singleton_mul {K N : ℕ} [NeZero N]
    (dl dr : Fin K → ℕ)
    (η : (q h : Fin K) →
      Matrix (Matrix.EtaEdgeIndex dl dr q h) (Matrix.EtaEdgeIndex dl dr q h) ℂ)
    (k : Fin N → Fin K) (s : Finset (Fin N)) (i : Fin N) (hi : i ∉ s) :
    etaEdgePartialProduct dl dr η k {i} * etaEdgePartialProduct dl dr η k s =
      etaEdgePartialProduct dl dr η k (insert i s) := by
  classical
  ext x y
  simp only [Matrix.mul_apply, etaEdgePartialProduct]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.piFinset_univ]
  rw [← Finset.prod_univ_sum
    (fun n : Fin N ↦
      (Finset.univ : Finset (Matrix.EtaEdgeIndex dl dr (k n) (k (n + 1)))))
    (fun n z ↦
      (if n ∈ ({i} : Finset (Fin N)) then
        η (k n) (k (n + 1)) (x n) z
      else if x n = z then 1 else 0) *
      (if n ∈ s then η (k n) (k (n + 1)) z (y n)
      else if z = y n then 1 else 0))]
  apply Finset.prod_congr rfl
  intro n _
  by_cases hni : n = i
  · subst n
    simp [hi]
  · by_cases hns : n ∈ s
    · simp [hni, hns]
    · by_cases hxy : x n = y n
      · simp [hni, hns, hxy]
      · simp [hni, hns, hxy]

private theorem prod_etaEdgePartialProduct_singletons {K N : ℕ} [NeZero N]
    (dl dr : Fin K → ℕ)
    (η : (q h : Fin K) →
      Matrix (Matrix.EtaEdgeIndex dl dr q h) (Matrix.EtaEdgeIndex dl dr q h) ℂ)
    (k : Fin N → Fin K) (l : List (Fin N)) (hl : l.Nodup) :
    (l.map fun i ↦ etaEdgePartialProduct dl dr η k {i}).prod =
      etaEdgePartialProduct dl dr η k l.toFinset := by
  induction l with
  | nil => simp
  | cons i l ih =>
      rw [List.nodup_cons] at hl
      simp only [List.map_cons, List.prod_cons, List.toFinset_cons]
      rw [ih hl.2]
      exact etaEdgePartialProduct_singleton_mul dl dr η k l.toFinset i (by
        simpa only [List.mem_toFinset] using hl.1)

private theorem prod_etaEdgePartialProduct_singletons_univ {K N : ℕ} [NeZero N]
    (dl dr : Fin K → ℕ)
    (η : (q h : Fin K) →
      Matrix (Matrix.EtaEdgeIndex dl dr q h) (Matrix.EtaEdgeIndex dl dr q h) ℂ)
    (k : Fin N → Fin K) :
    (List.ofFn fun i : Fin N ↦ etaEdgePartialProduct dl dr η k {i}).prod =
      fun x y ↦ ∏ n : Fin N, η (k n) (k (n + 1)) (x n) (y n) := by
  have hlist : List.ofFn (fun i : Fin N ↦ etaEdgePartialProduct dl dr η k {i}) =
      (List.ofFn id).map fun i ↦ etaEdgePartialProduct dl dr η k {i} := by
    simp
  rw [hlist]
  rw [prod_etaEdgePartialProduct_singletons dl dr η k (List.ofFn id)
    (List.nodup_ofFn.mpr Function.injective_id)]
  have hfin : (List.ofFn id : List (Fin N)).toFinset = Finset.univ := by
    ext i
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  rw [hfin]
  exact etaEdgePartialProduct_univ dl dr η k

private theorem etaEdgePartialProduct_singletons_comm {K N : ℕ} [NeZero N]
    (dl dr : Fin K → ℕ)
    (η : (q h : Fin K) →
      Matrix (Matrix.EtaEdgeIndex dl dr q h) (Matrix.EtaEdgeIndex dl dr q h) ℂ)
    (k : Fin N → Fin K) (i j : Fin N) :
    etaEdgePartialProduct dl dr η k {i} * etaEdgePartialProduct dl dr η k {j} =
      etaEdgePartialProduct dl dr η k {j} * etaEdgePartialProduct dl dr η k {i} := by
  by_cases hij : i = j
  · subst j
    rfl
  · calc
      etaEdgePartialProduct dl dr η k {i} * etaEdgePartialProduct dl dr η k {j} =
          etaEdgePartialProduct dl dr η k (insert i {j}) :=
        etaEdgePartialProduct_singleton_mul dl dr η k {j} i (by simp [hij])
      _ = etaEdgePartialProduct dl dr η k (insert j {i}) := by
        congr 1
        apply Finset.ext
        intro q
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact or_comm
      _ = etaEdgePartialProduct dl dr η k {j} *
          etaEdgePartialProduct dl dr η k {i} :=
        (etaEdgePartialProduct_singleton_mul dl dr η k {i} j
          (by
            simp only [Finset.mem_singleton]
            exact fun hji ↦ hij hji.symm)).symm

private theorem add_one_ne_self_of_two_le {N : ℕ} [NeZero N]
    (hN : 2 ≤ N) (i : Fin N) :
    i + 1 ≠ i := by
  have h1 : ((1 : Fin N) : ℕ) = 1 := by
    change 1 % N = 1
    rw [Nat.mod_eq_of_lt (by omega)]
  intro h
  have hval := congrArg Fin.val h
  rw [Fin.val_add_eq_ite, h1] at hval
  have := i.isLt
  split_ifs at hval <;> omega

private theorem mem_cyclicWindowSupport_two {N : ℕ} (i q : Fin N) :
    q ∈ MPSTensor.cyclicWindowSupport N 2 i ↔
      q = i ∨ q = MPSTensor.cyclicForwardSite i 1 := by
  rw [MPSTensor.cyclicWindowSupport]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨r, hr, rfl⟩
    interval_cases r
    · simp
    · simp
  · rintro (rfl | rfl)
    · exact ⟨0, by simp, by simp⟩
    · exact ⟨1, by simp, rfl⟩

/-- In cyclic edge coordinates, one translated pair bond is block diagonal in the sector
configuration and acts only on the edge beginning at the translation site. -/
theorem reindex_embedLocalOperator_etaPairBond {K N : ℕ} [NeZero N]
    (hN : 2 ≤ N) (dl dr : Fin K → ℕ)
    (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d)
    (η : (q h : Fin K) →
      Matrix (Matrix.EtaEdgeIndex dl dr q h) (Matrix.EtaEdgeIndex dl dr q h) ℂ)
    (B : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hB : Matrix.reindex (Matrix.etaPairSpatialBlockEquiv e).symm
        (Matrix.etaPairSpatialBlockEquiv e).symm B =
      Matrix.blockDiagonal' fun qh : Fin K × Fin K ↦
        ((1 : Matrix (Fin (dl qh.1)) (Fin (dl qh.1)) ℂ) ⊗ₖ
          η qh.1 qh.2) ⊗ₖ
            (1 : Matrix (Fin (dr qh.2)) (Fin (dr qh.2)) ℂ))
    (i : Fin N) :
    Matrix.reindex (Matrix.etaCyclicEdgeEquiv dl dr e)
        (Matrix.etaCyclicEdgeEquiv dl dr e)
        (embedLocalOperator (d := d) 2 N hN i
          (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
            (finTwoArrowEquiv (Fin d)).symm B)) =
      Matrix.blockDiagonal' fun k ↦ etaEdgePartialProduct dl dr η k {i} := by
  classical
  ext ⟨k, x⟩ ⟨h, y⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    embedLocalOperator_apply]
  by_cases hkh : k = h
  · subst h
    rw [Matrix.blockDiagonal'_apply_eq]
    let sx := (Matrix.etaFixedSectorCyclicEdgeEquiv dl dr k).symm x
    let sy := (Matrix.etaFixedSectorCyclicEdgeEquiv dl dr k).symm y
    have hxchain : (Matrix.etaCyclicEdgeEquiv dl dr e).symm ⟨k, x⟩ =
        fun n ↦ e ⟨k n, sx n⟩ := by
      funext n
      exact Matrix.etaCyclicEdgeEquiv_symm_apply dl dr e k x n
    have hychain : (Matrix.etaCyclicEdgeEquiv dl dr e).symm ⟨k, y⟩ =
        fun n ↦ e ⟨k n, sy n⟩ := by
      funext n
      exact Matrix.etaCyclicEdgeEquiv_symm_apply dl dr e k y n
    rw [hxchain, hychain]
    simp only [Equiv.symm_symm, MPSTensor.extractWindow, finTwoArrowEquiv_apply,
      Equiv.toFun_as_coe,
      piFinTwoEquiv_apply, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
      Nat.add_zero, Nat.reduceMod, etaEdgePartialProduct, Finset.mem_singleton]
    have hi0 : (⟨i.val % N, Nat.mod_lt _ (Fin.pos i)⟩ : Fin N) = i := by
      ext
      exact Nat.mod_eq_of_lt i.isLt
    have hi1 : (⟨(i.val + 1) % N, Nat.mod_lt _ (Fin.pos i)⟩ : Fin N) = i + 1 := by
      ext
      simp [Fin.add_def]
    rw [hi0, hi1]
    have hlocal :
        B (e ⟨k i, sx i⟩, e ⟨k (i + 1), sx (i + 1)⟩)
            (e ⟨k i, sy i⟩, e ⟨k (i + 1), sy (i + 1)⟩) =
          (1 : Matrix (Fin (dl (k i))) (Fin (dl (k i))) ℂ)
              (sx i).2 (sy i).2 *
            η (k i) (k (i + 1)) ((sx i).1, (sx (i + 1)).2)
              ((sy i).1, (sy (i + 1)).2) *
            (1 : Matrix (Fin (dr (k (i + 1)))) (Fin (dr (k (i + 1)))) ℂ)
              (sx (i + 1)).1 (sy (i + 1)).1 := by
      have hentry := congrFun (congrFun hB
        ⟨(k i, k (i + 1)),
          (((sx i).2, ((sx i).1, (sx (i + 1)).2)), (sx (i + 1)).1)⟩)
        ⟨(k i, k (i + 1)),
          (((sy i).2, ((sy i).1, (sy (i + 1)).2)), (sy (i + 1)).1)⟩
      simpa [Matrix.reindex_apply, Matrix.etaPairSpatialBlockEquiv,
        Matrix.blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply] using hentry
    rw [hlocal]
    simp only [Matrix.one_apply]
    have hxedge : ∀ n : Fin N,
        x n = ((sx n).1, (sx (n + 1)).2) := by
      intro n
      simpa only [sx, Matrix.etaFixedSectorCyclicEdgeEquiv_apply] using
        (congrFun
          ((Matrix.etaFixedSectorCyclicEdgeEquiv dl dr k).apply_symm_apply x)
          n).symm
    have hyedge : ∀ n : Fin N,
        y n = ((sy n).1, (sy (n + 1)).2) := by
      intro n
      simpa only [sy, Matrix.etaFixedSectorCyclicEdgeEquiv_apply] using
        (congrFun
          ((Matrix.etaFixedSectorCyclicEdgeEquiv dl dr k).apply_symm_apply y)
          n).symm
    have hj : MPSTensor.cyclicForwardSite i 1 = i + 1 := by
      ext
      simp [MPSTensor.cyclicForwardSite, Fin.add_def]
    have hij : i + 1 ≠ i := add_one_ne_self_of_two_le hN i
    have hcondition :
        (AgreesOutsideWindow 2 hN i (fun n ↦ e ⟨k n, sx n⟩)
            (fun n ↦ e ⟨k n, sy n⟩) ∧
          ((sx i).2, (sx (i + 1)).1) = ((sy i).2, (sy (i + 1)).1)) ↔
          ∀ n : Fin N, n ≠ i → x n = y n := by
      constructor
      · rintro ⟨ha, hb⟩ n hni
        rw [hxedge, hyedge]
        apply Prod.ext
        · by_cases hnj : n = i + 1
          · subst n
            exact congrArg (fun z ↦ z.2) hb
          · have hs := (agreesOutsideWindow_iff 2 hN i _ _).mp ha n (by
                rw [← MPSTensor.mem_cyclicWindowSupport_iff hN,
                  mem_cyclicWindowSupport_two, hj]
                simp [hni, hnj])
            have hs' := congrArg e.symm hs
            simp only [Equiv.symm_apply_apply, Sigma.mk.injEq, true_and] at hs'
            exact congrArg
              (fun z : Fin (dr (k n)) × Fin (dl (k n)) ↦ z.1)
              (eq_of_heq hs').symm
        · by_cases hn1i : n + 1 = i
          · rw [hn1i]
            exact congrArg (fun z ↦ z.1) hb
          · have hn1j : n + 1 ≠ i + 1 := by
              intro hn
              exact hni (add_right_cancel hn)
            have hs := (agreesOutsideWindow_iff 2 hN i _ _).mp ha (n + 1) (by
                rw [← MPSTensor.mem_cyclicWindowSupport_iff hN,
                  mem_cyclicWindowSupport_two, hj]
                simp [hn1i, hn1j])
            have hs' := congrArg e.symm hs
            simp only [Equiv.symm_apply_apply, Sigma.mk.injEq, true_and] at hs'
            exact congrArg
              (fun z : Fin (dr (k (n + 1))) × Fin (dl (k (n + 1))) ↦ z.2)
              (eq_of_heq hs').symm
      · intro he
        constructor
        · rw [agreesOutsideWindow_iff]
          intro q hq
          have hqi : q ≠ i := by
            intro h
            subst q
            exact hq (by simp)
          have hqj : q ≠ i + 1 := by
            intro h
            subst q
            apply hq
            rw [← MPSTensor.mem_cyclicWindowSupport_iff hN,
              mem_cyclicWindowSupport_two, hj]
            simp
          congr 1
          refine Sigma.ext rfl (heq_of_eq ?_)
          apply Prod.ext
          · have hqedge := congrArg Prod.fst (he q hqi).symm
            rw [hxedge q, hyedge q] at hqedge
            exact hqedge
          · let p : Fin N := q - 1
            have hpnext : p + 1 = q := by simp [p]
            have hpne : p ≠ i := by
              intro hp
              have : q = i + 1 := by rw [← hpnext, hp]
              exact hqj this
            have hpedge := congrArg Prod.snd (he p hpne).symm
            rw [hxedge p, hyedge p, hpnext] at hpedge
            exact hpedge
        · apply Prod.ext
          · let p : Fin N := i - 1
            have hpnext : p + 1 = i := by simp [p]
            have hpne : p ≠ i := by
              intro hp
              have hpnext' := hpnext
              rw [hp] at hpnext'
              exact hij hpnext'
            have hpedge := he p hpne
            rw [hxedge p, hyedge p, hpnext] at hpedge
            exact congrArg
              (fun z : Matrix.EtaEdgeIndex dl dr (k p) (k i) ↦ z.2) hpedge
          · have hedge := he (i + 1) hij
            rw [hxedge (i + 1), hyedge (i + 1)] at hedge
            exact (Prod.ext_iff.mp hedge).1
    by_cases he : ∀ n : Fin N, n ≠ i → x n = y n
    · obtain ⟨ha, hb⟩ := hcondition.mpr he
      rw [if_pos ha]
      simp only [Prod.ext_iff] at hb
      rw [if_pos hb.1, if_pos hb.2, one_mul, mul_one]
      rw [Finset.prod_eq_single i]
      · rw [if_pos rfl, hxedge i, hyedge i]
      · intro n _ hni
        rw [if_neg hni, if_pos (he n hni)]
      · simp
    · have hnot : ¬ (AgreesOutsideWindow 2 hN i
            (fun n ↦ e ⟨k n, sx n⟩) (fun n ↦ e ⟨k n, sy n⟩) ∧
          ((sx i).2, (sx (i + 1)).1) = ((sy i).2, (sy (i + 1)).1)) :=
        fun hc ↦ he (hcondition.mp hc)
      push Not at he
      obtain ⟨n, hni, hnxy⟩ := he
      have hprod : (∏ q : Fin N,
          if q = i then η (k q) (k (q + 1)) (x q) (y q)
          else if x q = y q then 1 else 0) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ n)
        simp [hni, hnxy]
      rw [hprod]
      by_cases ha : AgreesOutsideWindow 2 hN i
          (fun n ↦ e ⟨k n, sx n⟩) (fun n ↦ e ⟨k n, sy n⟩)
      · rw [if_pos ha]
        have hb : ((sx i).2, (sx (i + 1)).1) ≠
            ((sy i).2, (sy (i + 1)).1) := fun hb ↦ hnot ⟨ha, hb⟩
        by_cases hbL : (sx i).2 = (sy i).2
        · have hbR : (sx (i + 1)).1 ≠ (sy (i + 1)).1 :=
            fun hbR ↦ hb (Prod.ext hbL hbR)
          rw [if_pos hbL, if_neg hbR, mul_zero]
        · rw [if_neg hbL, zero_mul, zero_mul]
      · rw [if_neg ha]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hkh]
    let sx := (Matrix.etaFixedSectorCyclicEdgeEquiv dl dr k).symm x
    let ty := (Matrix.etaFixedSectorCyclicEdgeEquiv dl dr h).symm y
    have hxchain : (Matrix.etaCyclicEdgeEquiv dl dr e).symm ⟨k, x⟩ =
        fun n ↦ e ⟨k n, sx n⟩ := by
      funext n
      exact Matrix.etaCyclicEdgeEquiv_symm_apply dl dr e k x n
    have hychain : (Matrix.etaCyclicEdgeEquiv dl dr e).symm ⟨h, y⟩ =
        fun n ↦ e ⟨h n, ty n⟩ := by
      funext n
      exact Matrix.etaCyclicEdgeEquiv_symm_apply dl dr e h y n
    rw [hxchain, hychain]
    simp only [Equiv.symm_symm, MPSTensor.extractWindow, finTwoArrowEquiv_apply,
      Equiv.toFun_as_coe,
      piFinTwoEquiv_apply, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
      Nat.add_zero, Nat.reduceMod]
    have hi0 : (⟨i.val % N, Nat.mod_lt _ (Fin.pos i)⟩ : Fin N) = i := by
      ext
      exact Nat.mod_eq_of_lt i.isLt
    have hi1 : (⟨(i.val + 1) % N, Nat.mod_lt _ (Fin.pos i)⟩ : Fin N) = i + 1 := by
      ext
      simp [Fin.add_def]
    rw [hi0, hi1]
    by_cases ha : AgreesOutsideWindow 2 hN i
        (fun n ↦ e ⟨k n, sx n⟩) (fun n ↦ e ⟨h n, ty n⟩)
    · rw [if_pos ha]
      have hpairs : (k i, k (i + 1)) ≠ (h i, h (i + 1)) := by
        intro hp
        apply hkh
        funext q
        by_cases hq : ((q.val + N - i.val) % N < 2)
        · rw [← MPSTensor.mem_cyclicWindowSupport_iff hN,
            mem_cyclicWindowSupport_two] at hq
          rcases hq with rfl | hq
          · exact congrArg Prod.fst hp
          · have hj : MPSTensor.cyclicForwardSite i 1 = i + 1 := by
              ext
              simp [MPSTensor.cyclicForwardSite, Fin.add_def]
            rw [hj] at hq
            subst q
            exact congrArg Prod.snd hp
        · have hs := (agreesOutsideWindow_iff 2 hN i _ _).mp ha q hq
          have hs' := congrArg e.symm hs
          simpa only [Equiv.symm_apply_apply] using (congrArg Sigma.fst hs').symm
      have hentry := congrFun (congrFun hB
        ⟨(k i, k (i + 1)),
          (((sx i).2, ((sx i).1, (sx (i + 1)).2)), (sx (i + 1)).1)⟩)
        ⟨(h i, h (i + 1)),
          (((ty i).2, ((ty i).1, (ty (i + 1)).2)), (ty (i + 1)).1)⟩
      simpa [Matrix.reindex_apply, Matrix.etaPairSpatialBlockEquiv,
        Matrix.blockDiagonal'_apply_ne _ _ _ hpairs] using hentry
    · rw [if_neg ha]

/-- Two translated bonds commute whenever their common two-site matrix has a
neighboring-operator decomposition.  This is the local-to-global commutation
consequence of the same cyclic edge coordinates used in Beigi's finite-chain
decomposition.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section III, equations (2)--(3), pages 3--4. -/
theorem embedLocalOperator_commute_of_etaPair_decomposition
    {K N : ℕ} [NeZero N] (hN : 2 ≤ N) (dl dr : Fin K → ℕ)
    (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d)
    (η : (q h : Fin K) →
      Matrix (Matrix.EtaEdgeIndex dl dr q h) (Matrix.EtaEdgeIndex dl dr q h) ℂ)
    (B : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hB : Matrix.reindex (Matrix.etaPairSpatialBlockEquiv e).symm
        (Matrix.etaPairSpatialBlockEquiv e).symm B =
      Matrix.blockDiagonal' fun qh : Fin K × Fin K ↦
        ((1 : Matrix (Fin (dl qh.1)) (Fin (dl qh.1)) ℂ) ⊗ₖ
          η qh.1 qh.2) ⊗ₖ
            (1 : Matrix (Fin (dr qh.2)) (Fin (dr qh.2)) ℂ))
    (i j : Fin N) :
    embedLocalOperator (d := d) 2 N hN i
          (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
            (finTwoArrowEquiv (Fin d)).symm B) *
        embedLocalOperator (d := d) 2 N hN j
          (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
            (finTwoArrowEquiv (Fin d)).symm B) =
      embedLocalOperator (d := d) 2 N hN j
          (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
            (finTwoArrowEquiv (Fin d)).symm B) *
        embedLocalOperator (d := d) 2 N hN i
          (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
            (finTwoArrowEquiv (Fin d)).symm B) := by
  classical
  apply (Matrix.reindex (Matrix.etaCyclicEdgeEquiv dl dr e)
    (Matrix.etaCyclicEdgeEquiv dl dr e)).injective
  change (Matrix.reindexLinearEquiv ℂ ℂ (Matrix.etaCyclicEdgeEquiv dl dr e)
      (Matrix.etaCyclicEdgeEquiv dl dr e))
        (embedLocalOperator (d := d) 2 N hN i
            (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
              (finTwoArrowEquiv (Fin d)).symm B) *
          embedLocalOperator (d := d) 2 N hN j
            (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
              (finTwoArrowEquiv (Fin d)).symm B)) =
    (Matrix.reindexLinearEquiv ℂ ℂ (Matrix.etaCyclicEdgeEquiv dl dr e)
      (Matrix.etaCyclicEdgeEquiv dl dr e))
        (embedLocalOperator (d := d) 2 N hN j
            (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
              (finTwoArrowEquiv (Fin d)).symm B) *
          embedLocalOperator (d := d) 2 N hN i
            (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
              (finTwoArrowEquiv (Fin d)).symm B))
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ (Matrix.etaCyclicEdgeEquiv dl dr e)
      (Matrix.etaCyclicEdgeEquiv dl dr e) (Matrix.etaCyclicEdgeEquiv dl dr e),
    ← Matrix.reindexLinearEquiv_mul ℂ ℂ (Matrix.etaCyclicEdgeEquiv dl dr e)
      (Matrix.etaCyclicEdgeEquiv dl dr e) (Matrix.etaCyclicEdgeEquiv dl dr e),
    Matrix.coe_reindexLinearEquiv,
    reindex_embedLocalOperator_etaPairBond hN dl dr e η B hB i,
    reindex_embedLocalOperator_etaPairBond hN dl dr e η B hB j,
    ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  congr 1
  funext k
  exact etaEdgePartialProduct_singletons_comm dl dr η k i j

private theorem reindex_list_prod {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (l : List (Matrix α α ℂ)) :
    Matrix.reindex e e l.prod = (l.map fun A ↦ Matrix.reindex e e A).prod := by
  induction l with
  | nil =>
      ext x y
      simp [Matrix.reindex_apply, Matrix.one_apply]
  | cons A l ih =>
      simp only [List.prod_cons, List.map_cons]
      change Matrix.reindexLinearEquiv ℂ ℂ e e (A * l.prod) = _
      rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ e e e]
      simp only [Matrix.coe_reindexLinearEquiv, ih]

private theorem blockDiagonal'_list_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (l : List ((i : ι) → Matrix (α i) (α i) ℂ)) :
    (l.map Matrix.blockDiagonal').prod =
      Matrix.blockDiagonal' fun i ↦ (l.map fun A ↦ A i).prod := by
  induction l with
  | nil =>
      ext ⟨i, x⟩ ⟨j, y⟩
      by_cases hij : i = j
      · subst j
        simp [Matrix.one_apply, Matrix.blockDiagonal'_apply]
      · simp [Matrix.blockDiagonal'_apply_ne _ _ _ hij, hij]
  | cons A l ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [ih, ← Matrix.blockDiagonal'_mul]

/-- A local neighboring-operator decomposition propagates to the ordered product of all
translated bonds on every periodic chain of length at least two.  At length two the two
translated windows have the opposite orders \((0,1)\) and \((1,0)\); the cyclic edge
equivalence records both orientations explicitly.

Source: arXiv:1606.00608, Appendix C.2, equation sigmaNK2, lines 1581--1605.
Documented in `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem reindex_product_embedLocalOperator_of_etaPair_decomposition
    {K N : ℕ} [NeZero N] (hN : 2 ≤ N) (dl dr : Fin K → ℕ)
    (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d)
    (η : (q h : Fin K) →
      Matrix (Matrix.EtaEdgeIndex dl dr q h) (Matrix.EtaEdgeIndex dl dr q h) ℂ)
    (B : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hB : Matrix.reindex (Matrix.etaPairSpatialBlockEquiv e).symm
        (Matrix.etaPairSpatialBlockEquiv e).symm B =
      Matrix.blockDiagonal' fun qh : Fin K × Fin K ↦
        ((1 : Matrix (Fin (dl qh.1)) (Fin (dl qh.1)) ℂ) ⊗ₖ
          η qh.1 qh.2) ⊗ₖ
            (1 : Matrix (Fin (dr qh.2)) (Fin (dr qh.2)) ℂ)) :
    Matrix.reindex (Matrix.etaCyclicEdgeEquiv dl dr e)
        (Matrix.etaCyclicEdgeEquiv dl dr e)
        (List.ofFn fun i : Fin N ↦
          embedLocalOperator (d := d) 2 N hN i
            (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
              (finTwoArrowEquiv (Fin d)).symm B)).prod =
      Matrix.blockDiagonal' fun k : Fin N → Fin K ↦
        fun x y ↦ ∏ n : Fin N, η (k n) (k (n + 1)) (x n) (y n) := by
  classical
  rw [reindex_list_prod]
  rw [show (List.ofFn fun i : Fin N ↦
      embedLocalOperator (d := d) 2 N hN i
        (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
          (finTwoArrowEquiv (Fin d)).symm B)).map
        (fun A ↦ Matrix.reindex (Matrix.etaCyclicEdgeEquiv dl dr e)
          (Matrix.etaCyclicEdgeEquiv dl dr e) A) =
      List.ofFn (fun i : Fin N ↦
        Matrix.reindex (Matrix.etaCyclicEdgeEquiv dl dr e)
          (Matrix.etaCyclicEdgeEquiv dl dr e)
          (embedLocalOperator (d := d) 2 N hN i
            (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
              (finTwoArrowEquiv (Fin d)).symm B))) by
    simp
    rfl]
  have hmap :
      (List.ofFn fun i : Fin N ↦
        Matrix.reindex (Matrix.etaCyclicEdgeEquiv dl dr e)
          (Matrix.etaCyclicEdgeEquiv dl dr e)
          (embedLocalOperator (d := d) 2 N hN i
            (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
              (finTwoArrowEquiv (Fin d)).symm B))) =
      List.ofFn (fun i : Fin N ↦
        Matrix.blockDiagonal' fun k ↦ etaEdgePartialProduct dl dr η k {i}) := by
    exact congrArg List.ofFn (funext fun i ↦
      reindex_embedLocalOperator_etaPairBond hN dl dr e η B hB i)
  rw [hmap]
  rw [show List.ofFn (fun i : Fin N ↦
      Matrix.blockDiagonal' fun k ↦ etaEdgePartialProduct dl dr η k {i}) =
      (List.ofFn fun i : Fin N ↦
        fun k ↦ etaEdgePartialProduct dl dr η k {i}).map Matrix.blockDiagonal' by
    simp
    rfl]
  rw [blockDiagonal'_list_prod]
  congr
  funext k
  symm
  have hl : (List.ofFn fun i : Fin N ↦
      fun q ↦ etaEdgePartialProduct dl dr η q {i}).map (fun A ↦ A k) =
      List.ofFn (fun i : Fin N ↦ etaEdgePartialProduct dl dr η k {i}) := by
    simp
    rfl
  rw [hl]
  exact (prod_etaEdgePartialProduct_singletons_univ dl dr η k).symm

/-- The length-two specialization of cyclic transport.  The two translated windows are
\((0,1)\) and \((1,0)\), and hence contribute the two oriented edge factors
\(\eta_{k_0,k_1}\) and \(\eta_{k_1,k_0}\).

Source: arXiv:1606.00608, Appendix C.2, equation sigmaNK2, lines 1581--1605.
Documented in `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem reindex_product_embedLocalOperator_two_of_etaPair_decomposition
    {K : ℕ} (dl dr : Fin K → ℕ)
    (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d)
    (η : (q h : Fin K) →
      Matrix (Matrix.EtaEdgeIndex dl dr q h) (Matrix.EtaEdgeIndex dl dr q h) ℂ)
    (B : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hB : Matrix.reindex (Matrix.etaPairSpatialBlockEquiv e).symm
        (Matrix.etaPairSpatialBlockEquiv e).symm B =
      Matrix.blockDiagonal' fun qh : Fin K × Fin K ↦
        ((1 : Matrix (Fin (dl qh.1)) (Fin (dl qh.1)) ℂ) ⊗ₖ
          η qh.1 qh.2) ⊗ₖ
            (1 : Matrix (Fin (dr qh.2)) (Fin (dr qh.2)) ℂ)) :
    Matrix.reindex (Matrix.etaCyclicEdgeEquiv (N := 2) dl dr e)
        (Matrix.etaCyclicEdgeEquiv (N := 2) dl dr e)
        (List.ofFn fun i : Fin 2 ↦
          embedLocalOperator (d := d) 2 2 (by omega) i
            (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
              (finTwoArrowEquiv (Fin d)).symm B)).prod =
      Matrix.blockDiagonal' fun k : Fin 2 → Fin K ↦
        fun x y ↦ ∏ n : Fin 2, η (k n) (k (n + 1)) (x n) (y n) := by
  exact reindex_product_embedLocalOperator_of_etaPair_decomposition
    (N := 2) (by omega) dl dr e η B hB

end MPOTensor
