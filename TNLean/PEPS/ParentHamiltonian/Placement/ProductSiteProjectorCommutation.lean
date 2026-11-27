/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.Injective.VertexVirtualParentTransport
import QICLean.ManyBody.Sites.Placement.DependentRegionCoordinates
import QICLean.ManyBody.Sites.Placement.RegionPlacement

/-!
# Regional projector commutation through product site maps

Regional orthogonal projections supported on product site images inherit
commutation from intertwiners on the virtual coordinates. The argument
cancels only the nonzero complementary product of site projections; it does
not require the full product site map to be surjective.
-/

open ManyBody (exists_place_commutator_union)

open scoped BigOperators Matrix Kronecker

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {In Out : V → Type*}

/-- The local image projection on selected sites and the identity elsewhere. -/
def productSiteMask [∀ v, DecidableEq (Out v)]
    (J : (v : V) → Matrix (Out v) (Out v) ℂ) (T : Finset V) (v : V) :
    Matrix (Out v) (Out v) ℂ :=
  if v ∈ T then J v else 1

/-- The product of the site image projections on a selected region. -/
def globalProductSiteMask [∀ v, DecidableEq (Out v)]
    (J : (v : V) → Matrix (Out v) (Out v) ℂ) (T : Finset V) :
    Matrix ((v : V) → Out v) ((v : V) → Out v) ℂ :=
  Matrix.piKronecker (productSiteMask J T)

omit [Fintype V] [LinearOrder V] in
/-- A product of nonzero site matrices is nonzero, also for an empty region. -/
theorem regionPhysicalProductMatrix_ne_zero (R : Finset V)
    (F : (v : V) → Matrix (Out v) (In v) ℂ) (hF : ∀ v, F v ≠ 0) :
    regionPhysicalProductMatrix R F ≠ 0 := by
  classical
  have hentry (v : V) : ∃ α β, F v α β ≠ 0 := by
    by_contra! h
    exact hF v (by ext α β; exact h α β)
  choose α β hαβ using hentry
  intro hzero
  have h := congrFun (congrFun hzero (fun w => α w.1)) (fun w => β w.1)
  change (∏ w : {w : V // w ∈ R}, F w.1 (α w.1) (β w.1)) = 0 at h
  exact (Finset.prod_ne_zero_iff.mpr (fun w _ => hαβ w.1)) h

/-- A site mask is the placement of the regional product matrix. -/
theorem globalProductSiteMask_eq_place [∀ v, DecidableEq (Out v)]
    (J : (v : V) → Matrix (Out v) (Out v) ℂ) (R : Finset V) :
    globalProductSiteMask J R =
      ManyBody.place R (regionPhysicalProductMatrix R J) := by
  classical
  rw [globalProductSiteMask,
    ManyBody.piKronecker_eq_place (D := R) _ fun v hv ↦ by simp [productSiteMask, hv]]
  congr 1
  ext α β
  exact Finset.prod_congr rfl fun w _ ↦ by simp [productSiteMask, w.2]

/-- The product of two site masks is the mask on the union. -/
theorem globalProductSiteMask_mul [∀ v, Fintype (Out v)] [∀ v, DecidableEq (Out v)]
    (J : (v : V) → Matrix (Out v) (Out v) ℂ)
    (hJ : ∀ v, IsStarProjection (J v)) (R S : Finset V) :
    globalProductSiteMask J R * globalProductSiteMask J S =
      globalProductSiteMask J (R ∪ S) := by
  rw [globalProductSiteMask, globalProductSiteMask, Matrix.piKronecker_mul]
  congr 1
  funext v
  by_cases hR : v ∈ R <;> by_cases hS : v ∈ S <;>
    simp [productSiteMask, hR, hS, (hJ v).isIdempotentElem.eq]

section FiniteSites

variable [∀ v, Fintype (Out v)] [∀ v, DecidableEq (Out v)]

omit [Fintype V] in
/-- A selected site mask is an orthogonal projection. -/
theorem productSiteMask_isStarProjection
    (J : (v : V) → Matrix (Out v) (Out v) ℂ)
    (hJ : ∀ v, IsStarProjection (J v)) (T : Finset V) (v : V) :
    IsStarProjection (productSiteMask J T v) := by
  classical
  by_cases hv : v ∈ T
  · simpa [productSiteMask, hv] using hJ v
  · simp [productSiteMask, hv]

omit [Fintype V] [∀ v, DecidableEq (Out v)] in
/-- A product of site orthogonal projections is an orthogonal projection. -/
theorem regionPhysicalProductMatrix_isStarProjection
    (J : (v : V) → Matrix (Out v) (Out v) ℂ)
    (hJ : ∀ v, IsStarProjection (J v)) (R : Finset V) :
    IsStarProjection (regionPhysicalProductMatrix R J) := by
  rw [isStarProjection_iff']
  constructor
  · rw [regionPhysicalProductMatrix_mul]
    congr 1
    funext v
    exact (hJ v).isIdempotentElem
  · rw [Matrix.star_eq_conjTranspose, regionPhysicalProductMatrix_conjTranspose]
    congr 1
    funext v
    exact (hJ v).isSelfAdjoint

omit [Fintype V] in
/-- A partial site mask absorbs the full regional site projection. -/
theorem regionPhysicalProductMatrix_productSiteMask_mul
    (J : (v : V) → Matrix (Out v) (Out v) ℂ)
    (hJ : ∀ v, IsStarProjection (J v)) (R T : Finset V) :
    regionPhysicalProductMatrix R (productSiteMask J T) *
        regionPhysicalProductMatrix R J = regionPhysicalProductMatrix R J := by
  classical
  rw [regionPhysicalProductMatrix_mul]
  congr 1
  funext v
  by_cases hv : v ∈ T
  · simpa [productSiteMask, hv] using
      (show J v * J v = J v from (hJ v).isIdempotentElem)
  · simp [productSiteMask, hv]

omit [Fintype V] in
/-- A regional product of selected site masks is an orthogonal projection. -/
theorem regionPhysicalProductMatrix_productSiteMask_isStarProjection
    (J : (v : V) → Matrix (Out v) (Out v) ℂ)
    (hJ : ∀ v, IsStarProjection (J v)) (R T : Finset V) :
    IsStarProjection (regionPhysicalProductMatrix R (productSiteMask J T)) :=
  regionPhysicalProductMatrix_isStarProjection _ (productSiteMask_isStarProjection J hJ T) R

/-- A supported regional orthogonal projection commutes with every product site mask. -/
theorem place_commute_globalProductSiteMask
    (J : (v : V) → Matrix (Out v) (Out v) ℂ)
    (hJ : ∀ v, IsStarProjection (J v)) (R T : Finset V)
    (H : Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → Out w.1) ℂ)
    (hH : IsStarProjection H)
    (hJH : regionPhysicalProductMatrix R J * H = H) :
    Commute (ManyBody.place R H) (globalProductSiteMask J T) := by
  have hM := regionPhysicalProductMatrix_productSiteMask_isStarProjection J hJ R T
  have hMH : regionPhysicalProductMatrix R (productSiteMask J T) * H = H := by
    calc
      _ = regionPhysicalProductMatrix R (productSiteMask J T) *
          (regionPhysicalProductMatrix R J * H) := by rw [hJH]
      _ = H := by
        rw [← Matrix.mul_assoc, regionPhysicalProductMatrix_productSiteMask_mul J hJ, hJH]
  have hHM : H * regionPhysicalProductMatrix R (productSiteMask J T) = H := by
    simpa only [star_mul, hM.isSelfAdjoint.star_eq, hH.isSelfAdjoint.star_eq] using
      congrArg star hMH
  exact (ManyBody.piKronecker_mul_place (productSiteMask J T)
    (hMH.trans hHM.symm)).symm

omit [Fintype V] [∀ v, DecidableEq (Out v)] in
/-- Support on the left by an orthogonal projection also gives support on the right. -/
theorem regionPhysicalProductMatrix_mul_supported_right
    (J : (v : V) → Matrix (Out v) (Out v) ℂ)
    (hJ : ∀ v, IsStarProjection (J v)) (R : Finset V)
    (H : Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → Out w.1) ℂ)
    (hH : IsStarProjection H)
    (hJH : regionPhysicalProductMatrix R J * H = H) :
    H * regionPhysicalProductMatrix R J = H := by
  have hJR := regionPhysicalProductMatrix_isStarProjection J hJ R
  simpa only [star_mul, hJR.isSelfAdjoint.star_eq, hH.isSelfAdjoint.star_eq] using
    congrArg star hJH

/-- A supported regional projection absorbs its own global product site mask. -/
theorem place_mul_globalProductSiteMask_self
    (J : (v : V) → Matrix (Out v) (Out v) ℂ)
    (hJ : ∀ v, IsStarProjection (J v)) (R : Finset V)
    (H : Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → Out w.1) ℂ)
    (hH : IsStarProjection H)
    (hJH : regionPhysicalProductMatrix R J * H = H) :
    ManyBody.place R H * globalProductSiteMask J R =
      ManyBody.place R H := by
  rw [globalProductSiteMask_eq_place, ← ManyBody.place_mul,
    regionPhysicalProductMatrix_mul_supported_right J hJ R H hH hJH]

/-- A product of two supported regional projections absorbs the site mask on their union. -/
theorem place_mul_absorbs_union
    (J : (v : V) → Matrix (Out v) (Out v) ℂ)
    (hJ : ∀ v, IsStarProjection (J v)) (R S : Finset V)
    (H : Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → Out w.1) ℂ)
    (K : Matrix ((w : {w : V // w ∈ S}) → Out w.1)
      ((w : {w : V // w ∈ S}) → Out w.1) ℂ)
    (hH : IsStarProjection H) (hK : IsStarProjection K)
    (hJH : regionPhysicalProductMatrix R J * H = H)
    (hJK : regionPhysicalProductMatrix S J * K = K) :
    (ManyBody.place R H * ManyBody.place S K) *
        globalProductSiteMask J (R ∪ S) =
      ManyBody.place R H * ManyBody.place S K := by
  have hcomm := place_commute_globalProductSiteMask J hJ S R K hK hJK
  rw [← globalProductSiteMask_mul J hJ]
  calc
    _ = ManyBody.place R H *
        (ManyBody.place S K * globalProductSiteMask J R) *
          globalProductSiteMask J S := by simp only [Matrix.mul_assoc]
    _ = ManyBody.place R H *
        (globalProductSiteMask J R * ManyBody.place S K) *
          globalProductSiteMask J S := by rw [hcomm.eq]
    _ = (ManyBody.place R H * globalProductSiteMask J R) *
        (ManyBody.place S K * globalProductSiteMask J S) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [place_mul_globalProductSiteMask_self J hJ R H hH hJH,
        place_mul_globalProductSiteMask_self J hJ S K hK hJK]

/-- Regional orthogonal projections intertwining through product site maps commute
when the virtual lifts commute and the site image projections are nonzero.
Only the complementary product is canceled; no ambient surjectivity is assumed. -/
theorem commute_place_of_productSiteTransport
    [∀ v, Fintype (In v)] [∀ v, DecidableEq (In v)] (R S : Finset V)
    (A : (v : V) → Matrix (Out v) (In v) ℂ)
    (L : (v : V) → Matrix (In v) (Out v) ℂ)
    (J : (v : V) → Matrix (Out v) (Out v) ℂ)
    (H_R : Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → Out w.1) ℂ)
    (H_S : Matrix ((w : {w : V // w ∈ S}) → Out w.1)
      ((w : {w : V // w ∈ S}) → Out w.1) ℂ)
    (K_R : Matrix ((w : {w : V // w ∈ R}) → In w.1)
      ((w : {w : V // w ∈ R}) → In w.1) ℂ)
    (K_S : Matrix ((w : {w : V // w ∈ S}) → In w.1)
      ((w : {w : V // w ∈ S}) → In w.1) ℂ)
    (hAL : ∀ v, A v * L v = J v)
    (hJ : ∀ v, IsStarProjection (J v)) (hJ0 : ∀ v, J v ≠ 0)
    (hH_R : IsStarProjection H_R) (hH_S : IsStarProjection H_S)
    (hsupport_R : regionPhysicalProductMatrix R J * H_R = H_R)
    (hsupport_S : regionPhysicalProductMatrix S J * H_S = H_S)
    (hintertwine_R : H_R * regionPhysicalProductMatrix R A =
      regionPhysicalProductMatrix R A * K_R)
    (hintertwine_S : H_S * regionPhysicalProductMatrix S A =
      regionPhysicalProductMatrix S A * K_S)
    (hcommute : Commute (ManyBody.place R K_R)
      (ManyBody.place S K_S)) :
    Commute (ManyBody.place R H_R) (ManyBody.place S H_S) := by
  classical
  let P := ManyBody.place R H_R
  let Q := ManyBody.place S H_S
  let B := Matrix.piKronecker A
  let D := P * Q - Q * P
  have hPB : P * B = B * ManyBody.place R K_R :=
    (ManyBody.piKronecker_mul_place A hintertwine_R.symm).symm
  have hQB : Q * B = B * ManyBody.place S K_S :=
    (ManyBody.piKronecker_mul_place A hintertwine_S.symm).symm
  have hDB : D * B = 0 := by
    calc
      _ = P * (Q * B) - Q * (P * B) := by simp only [D, Matrix.sub_mul, Matrix.mul_assoc]
      _ = (B * ManyBody.place R K_R) * ManyBody.place S K_S -
          (B * ManyBody.place S K_S) * ManyBody.place R K_R := by
        rw [hQB, hPB, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPB, hQB]
      _ = B * (ManyBody.place R K_R * ManyBody.place S K_S -
          ManyBody.place S K_S * ManyBody.place R K_R) := by
        rw [Matrix.mul_sub, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = 0 := by rw [hcommute.eq, sub_self, Matrix.mul_zero]
  have hBL : B * Matrix.piKronecker L = Matrix.piKronecker J := by
    dsimp [B]
    rw [Matrix.piKronecker_mul]
    congr 1
    funext v
    exact hAL v
  have hDJ : D * Matrix.piKronecker J = 0 := by
    rw [← hBL, ← Matrix.mul_assoc, hDB, Matrix.zero_mul]
  have hPQ := place_mul_absorbs_union J hJ R S H_R H_S
    hH_R hH_S hsupport_R hsupport_S
  have hQP := place_mul_absorbs_union J hJ S R H_S H_R
    hH_S hH_R hsupport_S hsupport_R
  have hDmask : D * globalProductSiteMask J (R ∪ S) = D := by
    dsimp [D, P, Q]
    rw [Matrix.sub_mul, hPQ]
    rw [Finset.union_comm S R] at hQP
    rw [hQP]
  obtain ⟨E, hE⟩ := exists_place_commutator_union R S H_R H_S
  change D = ManyBody.place (R ∪ S) E at hE
  have hEJ : E * regionPhysicalProductMatrix (R ∪ S) J = 0 :=
    (ManyBody.place_mul_piKronecker_eq_zero_iff J E
      (Matrix.piKronecker_ne_zero fun w ↦ hJ0 w)).mp (by rw [← hE]; exact hDJ)
  change P * Q = Q * P
  apply sub_eq_zero.mp
  change D = 0
  calc
    D = D * globalProductSiteMask J (R ∪ S) := hDmask.symm
    _ = ManyBody.place (R ∪ S) E *
        ManyBody.place (R ∪ S) (regionPhysicalProductMatrix (R ∪ S) J) := by
      rw [hE, globalProductSiteMask_eq_place]
    _ = ManyBody.place (R ∪ S)
        (E * regionPhysicalProductMatrix (R ∪ S) J) :=
      (ManyBody.place_mul _ _).symm
    _ = 0 := by rw [hEJ, ManyBody.place_zero]

end FiniteSites

end TNLean.PEPS
