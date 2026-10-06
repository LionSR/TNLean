/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SiteEmbedding
import TNLean.MPS.ParentHamiltonian.Martingale.PeriodicInteraction

/-!
# Local matrices on cyclic windows

Extension of a local Euclidean operator to a cyclic window agrees with the
matrix obtained by placing the same operator on those sites. Consequently
extension preserves products and orthogonal projections. A one-site matrix
commutes with an extended interaction whenever its site is outside the window.

These are the local operator identities used for the open endpoint sectors in
GLM23, arXiv:2203.12563v3, Section 5, lines 1690–1692 and 1695–1777.
-/

open scoped BigOperators ComplexOrder Matrix

namespace MPSTensor

variable {d R N : ℕ}

/-- A cyclic window of length at most the chain length visits distinct sites. -/
theorem cyclicForwardSite_injective (hRN : R ≤ N) (i : Fin N) :
    Function.Injective (fun r : Fin R => cyclicForwardSite i r.val) := by
  intro r s hrs
  have h : (Sum.inl r : Fin R ⊕ Fin (N - R)) = Sum.inl s :=
    (cyclicWindowIndexEquiv R N hRN i).injective hrs
  exact Sum.inl_injective h

private theorem cyclicActiveBlockConfigEquiv_fst (hRN : R ≤ N) (i : Fin N)
    (σ : Cfg d N) :
    (cyclicActiveBlockConfigEquiv d R hRN i σ).1 =
      σ ∘ (fun r : Fin R => cyclicForwardSite i r.val) := by
  funext r
  have h := cyclicActiveBlockConfigEquiv_symm_apply_window hRN i
    (cyclicActiveBlockConfigEquiv d R hRN i σ).1
    (cyclicActiveBlockConfigEquiv d R hRN i σ).2 r
  simpa only [Prod.mk.eta, Equiv.symm_apply_apply, Function.comp_apply] using h.symm

private theorem cyclicActiveBlockConfigEquiv_symm_eq_extend
    (hRN : R ≤ N) (i : Fin N) (ω : Cfg d R) (σ : Cfg d N) :
    (cyclicActiveBlockConfigEquiv d R hRN i).symm
        (ω, (cyclicActiveBlockConfigEquiv d R hRN i σ).2) =
      Function.extend (fun r : Fin R => cyclicForwardSite i r.val) ω σ := by
  funext k
  obtain ⟨r | r, rfl⟩ := (cyclicWindowIndexEquiv R N hRN i).surjective k
  · change (cyclicActiveBlockConfigEquiv d R hRN i).symm
        (ω, (cyclicActiveBlockConfigEquiv d R hRN i σ).2)
          (cyclicForwardSite i r.val) = _
    rw [cyclicActiveBlockConfigEquiv_symm_apply_window,
      (cyclicForwardSite_injective hRN i).extend_apply]
  · have hoff : ¬∃ a : Fin R, cyclicForwardSite i a.val =
        cyclicWindowIndexEquiv R N hRN i (Sum.inr r) := by
      rintro ⟨a, ha⟩
      have h : (Sum.inl a : Fin R ⊕ Fin (N - R)) = Sum.inr r :=
        (cyclicWindowIndexEquiv R N hRN i).injective ha
      cases h
    rw [Function.extend_apply' _ _ _ hoff]
    have hsite : cyclicWindowIndexEquiv R N hRN i (Sum.inr r) =
        cyclicForwardSite i (R + r.val) := by
      simp only [cyclicWindowIndexEquiv_inr, cyclicForwardSite, Nat.add_assoc]
    rw [hsite, cyclicActiveBlockConfigEquiv_symm_apply_spectator]
    have h := cyclicActiveBlockConfigEquiv_symm_apply_spectator hRN i
      (cyclicActiveBlockConfigEquiv d R hRN i σ).1
      (cyclicActiveBlockConfigEquiv d R hRN i σ).2 r
    simpa only [Prod.mk.eta, Equiv.symm_apply_apply] using h.symm

/-- The cyclic extension of a local matrix is its placement on the actual
window sites, with the identity on every other site. -/
theorem periodicLocalInteractionES_eq_embedOp
    (M : Matrix (Cfg d R) (Cfg d R) ℂ) (hRN : R ≤ N) (i : Fin N) :
    periodicLocalInteractionES (Matrix.toEuclideanLin M) i =
      Matrix.toEuclideanLin
        (QuantumCircuit.embedOp (fun r : Fin R => cyclicForwardSite i r.val) M) := by
  classical
  apply LinearMap.ext
  intro v
  apply PiLp.ext
  intro σ
  let e := fun r : Fin R => cyclicForwardSite i r.val
  let U := cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i
  let c := cyclicActiveBlockConfigEquiv d R hRN i
  have he : Function.Injective e := cyclicForwardSite_injective hRN i
  unfold periodicLocalInteractionES
  rw [dite_eq_left hRN]
  change (U.symm (ContinuousLinearMap.rightFiberwiseMap
    (S := Cfg d (N - R))
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)) (U v))) σ = _
  rw [cyclicActiveBlockConfigLinearIsometryEquiv_symm_apply_apply]
  change (M.mulVec (fun ω => U v (ω, (c σ).2))) (c σ).1 =
    ((QuantumCircuit.embedOp e M).mulVec (fun τ => v τ)) σ
  simp only [Matrix.mulVec, dotProduct, U,
    cyclicActiveBlockConfigLinearIsometryEquiv_apply_apply]
  simp only [c, cyclicActiveBlockConfigEquiv_fst,
    cyclicActiveBlockConfigEquiv_symm_eq_extend]
  change (∑ ω, M (σ ∘ e) ω * v (Function.extend e ω σ)) =
    ∑ τ, QuantumCircuit.embedOp e M σ τ * v τ
  rw [← QuantumCircuit.sum_agreeOff he σ
    (fun ω => M (σ ∘ e) ω * v (Function.extend e ω σ))]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [QuantumCircuit.embedOp_apply]
  by_cases h : QuantumCircuit.AgreeOff e σ τ
  · rw [if_pos h, if_pos h, ← QuantumCircuit.eq_extend_of_agreeOff he h]
  · simp only [if_neg h, zero_mul]

private theorem toEuclideanLin_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M K : Matrix ι ι ℂ) :
    Matrix.toEuclideanLin (M * K) = Matrix.toEuclideanLin M * Matrix.toEuclideanLin K :=
  Matrix.toLpLin_mul_same 2 M K

/-- Cyclic extension preserves composition, including the convention that an
interaction longer than the chain extends to zero. -/
theorem periodicLocalInteractionES_mul
    (h k : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (i : Fin N) :
    periodicLocalInteractionES (h * k) i =
      periodicLocalInteractionES h i * periodicLocalInteractionES k i := by
  classical
  by_cases hRN : R ≤ N
  · obtain ⟨M, rfl⟩ := Matrix.toEuclideanLin.surjective h
    obtain ⟨K, rfl⟩ := Matrix.toEuclideanLin.surjective k
    rw [← toEuclideanLin_mul, periodicLocalInteractionES_eq_embedOp _ hRN,
      periodicLocalInteractionES_eq_embedOp _ hRN,
      periodicLocalInteractionES_eq_embedOp _ hRN,
      ← toEuclideanLin_mul, QuantumCircuit.embedOp_mul (cyclicForwardSite_injective hRN i)]
  · simp [periodicLocalInteractionES, hRN]

/-- Every cyclic extension of an orthogonal projection is an orthogonal
projection, without a nonzero physical-dimension assumption. -/
theorem periodicLocalInteractionES_isSymmetricProjection
    {P : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)}
    (hP : P.IsSymmetricProjection) (i : Fin N) :
    (periodicLocalInteractionES P i).IsSymmetricProjection := by
  constructor
  · rw [isIdempotentElem_iff, ← periodicLocalInteractionES_mul,
      hP.isIdempotentElem.eq]
  · have hpos : (periodicLocalInteractionES P i).IsPositive := by
      apply LinearMap.nonneg_iff_isPositive.mp
      have h := periodicLocalInteractionES_mono
        (LinearMap.nonneg_iff_isPositive.mpr hP.isPositive) i
      simpa only [show periodicLocalInteractionES
        (0 : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)) i = 0 by
          simp [periodicLocalInteractionES]] using h
    exact hpos.isSymmetric

/-- A cyclic extension of a product of one-site matrices is the product of
those matrices placed on the window, with identity matrices elsewhere. -/
theorem periodicLocalInteractionES_finKronecker (hRN : R ≤ N) (i : Fin N)
    (A : Fin R → Matrix (Fin d) (Fin d) ℂ) :
    periodicLocalInteractionES (Matrix.toEuclideanLin (Matrix.finKronecker A)) i =
      Matrix.toEuclideanLin (Matrix.finKronecker
        (Function.extend (fun r : Fin R => cyclicForwardSite i r.val) A 1)) := by
  rw [periodicLocalInteractionES_eq_embedOp _ hRN,
    QuantumCircuit.embedOp_finKronecker (cyclicForwardSite_injective hRN i)]

/-- A product of one-site orthogonal projections is an orthogonal projection. -/
theorem finKronecker_toEuclideanLin_isSymmetricProjection
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ k, (Matrix.toEuclideanLin (A k)).IsSymmetricProjection) :
    (Matrix.toEuclideanLin (Matrix.finKronecker A)).IsSymmetricProjection := by
  classical
  constructor
  · rw [isIdempotentElem_iff, ← toEuclideanLin_mul, Matrix.finKronecker_mul]
    apply congrArg Matrix.toEuclideanLin
    apply congrArg Matrix.finKronecker
    funext k
    apply Matrix.toEuclideanLin.injective
    rw [toEuclideanLin_mul]
    exact (hA k).isIdempotentElem.eq
  · rw [Matrix.isSymmetric_toEuclideanLin_iff]
    change (Matrix.finKronecker A)ᴴ = Matrix.finKronecker A
    rw [Matrix.finKronecker_conjTranspose]
    congr 1
    funext k
    exact (Matrix.isSymmetric_toEuclideanLin_iff.mp (hA k).isSymmetric).eq

/-- A one-site matrix acting at the chosen chain site, with the identity at
every other site. -/
noncomputable def siteMatrixES (M : Matrix (Fin d) (Fin d) ℂ) (k : Fin N) :
    EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  Matrix.toEuclideanLin (Matrix.finKronecker (Pi.mulSingle k M))

/-- A diagonal one-site matrix evaluates its coefficient at that chain site. -/
theorem siteMatrixES_diagonal (f : Fin d → ℂ) (k : Fin N) :
    siteMatrixES (Matrix.diagonal f) k =
      Matrix.toEuclideanLin (Matrix.diagonal fun σ : Cfg d N => f (σ k)) := by
  classical
  unfold siteMatrixES
  apply congrArg Matrix.toEuclideanLin
  ext σ τ
  rw [Matrix.finKronecker_apply]
  by_cases hστ : σ = τ
  · subst τ
    rw [Matrix.diagonal_apply_eq, Finset.prod_eq_single k]
    · simp only [Pi.mulSingle_eq_same, Matrix.diagonal_apply_eq]
    · intro j _ hj
      simp only [Pi.mulSingle_eq_of_ne hj, Matrix.one_apply_eq]
    · simp
  · rw [Matrix.diagonal_apply_ne _ hστ]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hστ
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    by_cases hjk : j = k
    · subst j
      rw [Pi.mulSingle_eq_same, Matrix.diagonal_apply_ne _ hj]
    · rw [Pi.mulSingle_eq_of_ne hjk, Matrix.one_apply_ne hj]

/-- Placing two matrices at the same site preserves their product. -/
theorem siteMatrixES_mul_same (M K : Matrix (Fin d) (Fin d) ℂ) (k : Fin N) :
    siteMatrixES M k * siteMatrixES K k = siteMatrixES (M * K) k := by
  classical
  simp only [siteMatrixES, ← toEuclideanLin_mul, Matrix.finKronecker_mul]
  apply congrArg Matrix.toEuclideanLin
  apply congrArg Matrix.finKronecker
  funext j
  by_cases hj : j = k
  · subst j
    simp only [Pi.mulSingle_eq_same]
  · simp only [Pi.mulSingle_eq_of_ne hj, mul_one]

/-- Matrices placed at distinct chain sites commute. -/
theorem commute_siteMatrixES_of_ne (M K : Matrix (Fin d) (Fin d) ℂ)
    {i j : Fin N} (hij : i ≠ j) : Commute (siteMatrixES M i) (siteMatrixES K j) := by
  classical
  apply (commute_iff_eq _ _).mpr
  simp only [siteMatrixES, ← toEuclideanLin_mul, Matrix.finKronecker_mul]
  apply congrArg Matrix.toEuclideanLin
  apply congrArg Matrix.finKronecker
  funext k
  by_cases hki : k = i
  · subst k
    simp only [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij, mul_one, one_mul]
  · simp only [Pi.mulSingle_eq_of_ne hki, mul_one, one_mul]

/-- Placing one orthogonal projection at a chain site preserves its projection
property, even when the local physical space is zero dimensional. -/
theorem siteMatrixES_isSymmetricProjection (k : Fin N)
    {P : Matrix (Fin d) (Fin d) ℂ}
    (hP : (Matrix.toEuclideanLin P).IsSymmetricProjection) :
    (siteMatrixES P k).IsSymmetricProjection := by
  apply finKronecker_toEuclideanLin_isSymmetricProjection
  intro j
  by_cases hj : j = k
  · subst j
    simpa only [Pi.mulSingle_eq_same] using hP
  · rw [Pi.mulSingle_eq_of_ne hj]
    rw [Matrix.toEuclideanLin, Matrix.toLpLin_one]
    exact ⟨IsIdempotentElem.one, LinearMap.IsSymmetric.id⟩

/-- A matrix on a site outside a cyclic interaction window commutes with that
interaction. The local matrix and the interaction need not be diagonal. -/
theorem commute_siteMatrixES_periodicLocalInteractionES_of_notMem
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hRN : R ≤ N) (i k : Fin N) (M : Matrix (Fin d) (Fin d) ℂ)
    (hk : ∀ r : Fin R, cyclicForwardSite i r.val ≠ k) :
    Commute (siteMatrixES M k)
      (periodicLocalInteractionES h i) := by
  classical
  obtain ⟨H, rfl⟩ := Matrix.toEuclideanLin.surjective h
  rw [siteMatrixES, periodicLocalInteractionES_eq_embedOp _ hRN]
  have hs : Matrix.finKronecker (Pi.mulSingle k M) ∈
      QuantumCircuit.supportedOperators d ({k} : Set (Fin N)) := by
    apply QuantumCircuit.finKronecker_mem_supportedOperators
    intro j hj
    exact Pi.mulSingle_eq_of_ne (by simpa only [Set.mem_singleton_iff] using hj) M
  have hd : Disjoint ({k} : Set (Fin N))
      (Set.range (fun r : Fin R => cyclicForwardSite i r.val)) := by
    rw [Set.disjoint_left]
    rintro j hj ⟨r, hr⟩
    exact hk r (hr.trans (Set.mem_singleton_iff.mp hj))
  have hc := QuantumCircuit.commute_of_mem_supportedOperators hd hs
    (QuantumCircuit.embedOp_mem_supportedOperators (cyclicForwardSite_injective hRN i) H)
  apply (commute_iff_eq _ _).mpr
  rw [← toEuclideanLin_mul, ← toEuclideanLin_mul, hc.eq]

/-- Extending a two-site product places its first factor at the window start
and its second factor at the next cyclic site. -/
theorem periodicLocalInteractionES_twoSite_product (hN : 2 ≤ N) (i : Fin N)
    (M K : Matrix (Fin d) (Fin d) ℂ) :
    periodicLocalInteractionES
        (Matrix.toEuclideanLin (Matrix.finKronecker ![M, K])) i =
      siteMatrixES M i * siteMatrixES K (cyclicForwardSite i 1) := by
  classical
  let e := fun r : Fin 2 => cyclicForwardSite i r.val
  have he : Function.Injective e := cyclicForwardSite_injective hN i
  have h01 : i ≠ cyclicForwardSite i 1 := by
    intro h
    have h' : e 0 = e 1 := by simpa only [e, Fin.val_zero, Fin.val_one,
      cyclicForwardSite_zero] using h
    exact (by decide : (0 : Fin 2) ≠ 1) (he h')
  rw [periodicLocalInteractionES_finKronecker hN]
  simp only [siteMatrixES, ← toEuclideanLin_mul, Matrix.finKronecker_mul]
  apply congrArg Matrix.toEuclideanLin
  apply congrArg Matrix.finKronecker
  funext j
  change Function.extend e ![M, K] 1 j =
    Pi.mulSingle i M j * Pi.mulSingle (cyclicForwardSite i 1) K j
  by_cases hj : ∃ r : Fin 2, e r = j
  · obtain ⟨r, rfl⟩ := hj
    rw [he.extend_apply]
    fin_cases r
    · simp only [e, Fin.val_zero, cyclicForwardSite_zero, Matrix.cons_val_zero,
        Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne h01, mul_one]
    · simp only [e, Fin.val_one, Matrix.cons_val_one, Matrix.cons_val_zero,
        Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne h01.symm, one_mul]
  · rw [Function.extend_apply' _ _ _ hj, Pi.one_apply]
    have hji : j ≠ i := by
      intro h
      apply hj
      exact ⟨0, by simpa only [e, Fin.val_zero, cyclicForwardSite_zero] using h.symm⟩
    have hjnext : j ≠ cyclicForwardSite i 1 := by
      intro h
      apply hj
      exact ⟨1, by simpa only [e, Fin.val_one] using h.symm⟩
    simp only [Pi.mulSingle_eq_of_ne hji, Pi.mulSingle_eq_of_ne hjnext, mul_one]

end MPSTensor
