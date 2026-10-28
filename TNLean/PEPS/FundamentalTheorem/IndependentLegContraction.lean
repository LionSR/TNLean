/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.PhysicalProductInvariance
import TNLean.PEPS.FundamentalTheorem.GaugeAction
import TNLean.PEPS.FundamentalTheorem.LocalGaugeExtraction

/-!
# Contraction after independent changes of virtual legs

Independent matrices at the two endpoints of an edge contract to the ordinary
transpose of the first times the second. Expanding the local changes expresses
the state as a physical product map on all independent incidence coordinates.
Invertible local changes preserve injectivity.

Source: arXiv:1804.04964, Applications, lines 1891–1894.
-/

noncomputable section

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}

/-- Contracted endpoint kernels are independent of the endpoint order when
the two external labels follow their endpoints. Neither invertibility nor
agreement between native and sorted edge orientation is assumed.
Supporting calculation for arXiv:1804.04964, lines 1891–1894. -/
theorem independentLegKernel_edge_eq_of_endpoints
    (A : Tensor Γ d)
    (K : (v : V) → (ie : IncidentEdge Γ v) →
      Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ)
    (ξ : OpenLocalConfig (G := Γ) A) (e : Edge Γ) {u v : V}
    (hu : e.1.1 = u ∨ e.1.2 = u) (hv : e.1.1 = v ∨ e.1.2 = v)
    (hne : u ≠ v) :
    ((show Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ from
        K e.1.1 (edgeLeftIncident (G := Γ) e))ᵀ *
      (show Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ from
        K e.1.2 (edgeRightIncident (G := Γ) e)))
        (leftIncidentValue A ξ e) (rightIncidentValue A ξ e) =
      ∑ j : Fin (A.bondDim e),
        K u ⟨e, hu⟩ j (ξ u ⟨e, hu⟩) * K v ⟨e, hv⟩ j (ξ v ⟨e, hv⟩) := by
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact False.elim (hne (hu.symm.trans hv))
  · subst u
    subst v
    rfl
  · subst u
    subst v
    change (∑ j : Fin (A.bondDim e),
        K e.1.1 (edgeLeftIncident (G := Γ) e) j (leftIncidentValue A ξ e) *
          K e.1.2 (edgeRightIncident (G := Γ) e) j (rightIncidentValue A ξ e)) =
      ∑ j : Fin (A.bondDim e),
        K e.1.2 (edgeRightIncident (G := Γ) e) j (rightIncidentValue A ξ e) *
          K e.1.1 (edgeLeftIncident (G := Γ) e) j (leftIncidentValue A ξ e)
    refine Finset.sum_congr rfl ?_
    intro j hj
    exact mul_comm
      (K e.1.1 (edgeLeftIncident (G := Γ) e) j (leftIncidentValue A ξ e) : ℂ)
      (K e.1.2 (edgeRightIncident (G := Γ) e) j (rightIncidentValue A ξ e) : ℂ)
  · exact False.elim (hne (hu.symm.trans hv))

end TNLean.PEPS


namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- Summing the original edge indices pairs independent endpoint kernels by
ordinary transpose and matrix multiplication. This is the edge calculation
in the construction supporting arXiv:1804.04964, lines 1891–1894. -/
private theorem sum_virtual_prod_independentLegKernel (A : Tensor G d)
    (K : (v : V) → (ie : IncidentEdge G v) →
      Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ)
    (ξ : OpenLocalConfig (G := G) A) :
    (∑ η : VirtualConfig A,
      ∏ v : V, ∏ ie : IncidentEdge G v, K v ie (η ie.1) (ξ v ie)) =
      ∏ e : Edge G,
        ((show Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ from
          K e.1.1 (edgeLeftIncident (G := G) e))ᵀ *
          (show Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ from
            K e.1.2 (edgeRightIncident (G := G) e)))
          (leftIncidentValue A ξ e) (rightIncidentValue A ξ e) := by
  classical
  calc
    _ = ∑ η : VirtualConfig A, ∏ e : Edge G,
          K e.1.1 (edgeLeftIncident (G := G) e) (η e)
              (leftIncidentValue A ξ e) *
            K e.1.2 (edgeRightIncident (G := G) e) (η e)
              (rightIncidentValue A ξ e) := by
        refine Finset.sum_congr rfl ?_
        intro η hη
        exact prod_incident_eq_prod_edge
          (fun v ie => K v ie (η ie.1) (ξ v ie))
    _ = ∏ e : Edge G, ∑ j : Fin (A.bondDim e),
          K e.1.1 (edgeLeftIncident (G := G) e) j
              (leftIncidentValue A ξ e) *
            K e.1.2 (edgeRightIncident (G := G) e) j
              (rightIncidentValue A ξ e) :=
        (Fintype.prod_sum (fun (e : Edge G) (j : Fin (A.bondDim e)) =>
          K e.1.1 (edgeLeftIncident (G := G) e) j (leftIncidentValue A ξ e) *
            K e.1.2 (edgeRightIncident (G := G) e) j
              (rightIncidentValue A ξ e))).symm
    _ = _ := rfl

/-- Expanding independent local changes of virtual coordinates expresses a PEPS
coefficient as a sum over all independent half-edge assignments. This is a
supporting identity for arXiv:1804.04964, lines 1891–1894; its local expansion
hypothesis must be derived before applying it to translation invariance. -/
private theorem stateCoeff_eq_sum_independentLegKernel (A : Tensor G d)
    (F : (v : V) → ((ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) → Fin d → ℂ)
    (K : (v : V) → (ie : IncidentEdge G v) →
      Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ)
    (hlocal : ∀ (v : V) (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1))
      (σ : Fin d), A.component v η σ =
        ∑ ξ : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1),
          (∏ ie : IncidentEdge G v, K v ie (η ie) (ξ ie)) * F v ξ σ)
    (σ : V → Fin d) :
    stateCoeff A σ =
      ∑ ξ : OpenLocalConfig (G := G) A,
        (∏ e : Edge G,
          ((show Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ from
            K e.1.1 (edgeLeftIncident (G := G) e))ᵀ *
            (show Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ from
              K e.1.2 (edgeRightIncident (G := G) e)))
            (leftIncidentValue A ξ e) (rightIncidentValue A ξ e)) *
          ∏ v : V, F v (ξ v) (σ v) := by
  classical
  have hprod (η : VirtualConfig A) :
      (∏ v : V, A.component v (fun ie => η ie.1) (σ v)) =
        ∑ ξ : OpenLocalConfig (G := G) A,
          ∏ v : V, (∏ ie : IncidentEdge G v, K v ie (η ie.1) (ξ v ie)) *
            F v (ξ v) (σ v) := by
    simp_rw [hlocal]
    exact Fintype.prod_sum (fun (v : V)
      (ξ : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) =>
        (∏ ie : IncidentEdge G v, K v ie (η ie.1) (ξ ie)) * F v ξ (σ v))
  unfold stateCoeff
  simp_rw [hprod]
  rw [Finset.sum_comm]
  calc
    _ = ∑ ξ : OpenLocalConfig (G := G) A,
          (∑ η : VirtualConfig A,
            ∏ v : V, ∏ ie : IncidentEdge G v, K v ie (η ie.1) (ξ v ie)) *
            ∏ v : V, F v (ξ v) (σ v) := by
        refine Finset.sum_congr rfl ?_
        intro ξ hξ
        calc
          _ = ∑ η : VirtualConfig A,
                (∏ v : V, ∏ ie : IncidentEdge G v,
                  K v ie (η ie.1) (ξ v ie)) * ∏ v : V, F v (ξ v) (σ v) := by
              refine Finset.sum_congr rfl ?_
              intro η hη
              rw [Finset.prod_mul_distrib]
          _ = _ := by rw [Finset.sum_mul]
    _ = _ := by simp_rw [sum_virtual_prod_independentLegKernel]

end TNLean.PEPS

namespace TNLean.PEPS
open TNLean.Lattice

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}

/-- The actual contracted product of independent endpoint kernels, as a
function on every independent half-edge assignment.
Supporting coefficient in arXiv:1804.04964, lines 1891–1894. -/
noncomputable def independentLegEdgeCoefficient (A : Tensor Γ d)
    (K : (v : V) → (ie : IncidentEdge Γ v) →
      Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ)
    (ξ : OpenLocalConfig (G := Γ) A) : ℂ :=
  ∏ e : Edge Γ,
    ((show Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ from
        K e.1.1 (edgeLeftIncident (G := Γ) e))ᵀ *
      (show Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ from
        K e.1.2 (edgeRightIncident (G := Γ) e)))
      (leftIncidentValue A ξ e) (rightIncidentValue A ξ e)

/-- The local orbit formula and actual local coordinate bijections put the
original PEPS vector in the image of one common local physical map.
Supporting composition for arXiv:1804.04964, lines 1891–1894. -/
theorem stateCoeff_eq_commonPhysicalProductFamilyMap
    {Xi : Type*} [Fintype Xi]
    (A : Tensor Γ d) (E : (v : V) → Xi ≃ LocalVirtualConfig A v)
    (F : Xi → Fin d → ℂ)
    (K : (v : V) → (ie : IncidentEdge Γ v) →
      Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ)
    (hlocal : ∀ (v : V) (η : LocalVirtualConfig A v) (σ : Fin d),
      A.component v η σ =
        ∑ ξ : LocalVirtualConfig A v,
          (∏ ie : IncidentEdge Γ v, K v ie (η ie) (ξ ie)) * F ((E v).symm ξ) σ) :
    stateCoeff A =
      dependentPhysicalProductFamilyMap (fun (_ : V) (σ : Fin d) (x : Xi) => F x σ)
        (fun x : V → Xi => independentLegEdgeCoefficient A K (fun v => E v (x v))) := by
  classical
  let R := independentLegEdgeCoefficient A K
  have hC : stateCoeff A =
      dependentPhysicalProductFamilyMap
        (fun (v : V) (σ : Fin d) (ξ : LocalVirtualConfig A v) => F ((E v).symm ξ) σ) R := by
    funext σ
    rw [stateCoeff_eq_sum_independentLegKernel A
      (fun v ξ σ => F ((E v).symm ξ) σ) K hlocal σ]
    change (∑ ξ : OpenLocalConfig (G := Γ) A,
        R ξ * ∏ v : V, F ((E v).symm (ξ v)) (σ v)) =
      ∑ ξ : OpenLocalConfig (G := Γ) A,
        (∏ v : V, F ((E v).symm (ξ v)) (σ v)) * R ξ
    exact Finset.sum_congr rfl (fun ξ _ => mul_comm _ _)
  have hE := dependentPhysicalProductFamilyMap_reindex_input E
    (fun (v : V) (σ : Fin d) (ξ : LocalVirtualConfig A v) => F ((E v).symm ξ) σ) R
  have hFloc :
      (fun (v : V) (σ : Fin d) (x : Xi) => F ((E v).symm (E v x)) σ) =
        (fun (_ : V) (σ : Fin d) (x : Xi) => F x σ) := by
    funext v σ x
    rw [Equiv.symm_apply_apply]
  rw [hFloc] at hE
  exact hC.trans hE.symm

end TNLean.PEPS

namespace TNLean.PEPS

/-- Independent invertible changes of virtual legs and a nonzero uniform
scalar preserve linear independence of the local tensor family. This
supplies injectivity of the final common tensor without any relation between
matrices at opposite edge endpoints.
Supporting calculation for arXiv:1804.04964, lines 1891–1894. -/
theorem linearIndependent_smul_piProductKernel
    {Leg : Type*} [Fintype Leg] [DecidableEq Leg] {n : Leg → Type*}
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    {M : Type*} [AddCommGroup M] [Module ℂ M]
    (F : ((i : Leg) → n i) → M) (hF : LinearIndependent ℂ F)
    (K : (i : Leg) → GL (n i) ℂ) (ρ : ℂ) (hρ : ρ ≠ 0) :
    LinearIndependent ℂ (fun x : (i : Leg) → n i =>
      ρ • ∑ y : (i : Leg) → n i,
        (∏ i, (K i : Matrix (n i) (n i) ℂ) (x i) (y i)) • F y) := by
  have hunit := piProductKernel_isUnit
    (fun i => (K i : Matrix (n i) (n i) ℂ))
    (fun i => (K i).inv)
    (fun i => (K i).val_inv) (fun i => (K i).inv_val)
  have hLI := linearIndependent_recombine F hF
    (Matrix.of (fun x y : (i : Leg) → n i =>
      ∏ i, (K i : Matrix (n i) (n i) ℂ) (x i) (y i))) hunit
  change LinearIndependent ℂ
    ((fun _ : (i : Leg) → n i => Units.mk0 ρ hρ) •
      (fun x : (i : Leg) → n i => ∑ y : (i : Leg) → n i,
        (∏ i, (K i : Matrix (n i) (n i) ℂ) (x i) (y i)) • F y))
  exact hLI.units_smul _

end TNLean.PEPS
