/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.MPO.TwoWindowPolynomialMPOFamily
import QICLean.Analysis.TensorProduct.MatrixTensorCoordinates
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import QICLean.Algebra.OperatorSchmidt.MatrixFactorExchange
import QICLean.Algebra.Combinatorics.TwoWindowSum
import QICLean.ManyBody.Sites.Twirl
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.MPO.PhysicalIntervalTransport
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.RegionalFactors.RegionalMiddleFactors
import QICLean.Spectral.LowEnergy.ChebyshevViability

/-!
# Tensor decompositions of a common physical polynomial family

A fixed physical middle family represents every polynomial through the
prescribed degree cutoff. Its matrix identity induces an identity of
continuous operators under the canonical tensor-coordinate isometry.
Exchanging the factors places the retained interval first. The same
family precedes every supported exterior operator and every polynomial.

The family retains its cardinality bound and coarse open bond bound.
The source-sharp bond estimate and running time are separate questions.

It also contains the following results.

* `TNLean.MPS.AreaLaw.exists_actual_regional_clipped_polynomial_family_fin`: common polynomial
  families for the actual clipped Hamiltonian.
* `TNLean.MPS.AreaLaw.exists_common_physical_chebyshev_viable_family_fin`: physical polynomial
  families and Chebyshev viability.

## References

Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333.
-/

open ManyBody (interval)

section PhysicalPolynomialTensorFamily

open Matrix QuantumCircuit
open scoped BigOperators Matrix Kronecker TensorProduct

noncomputable section

namespace TNLean.MPS.AreaLaw

/-- The common physical polynomial family gives both its literal whole-chain
matrix identity and its continuous tensor-action identity under one fixed
coordinate isometry. That isometry first separates exterior and middle
coordinates and then applies the inverse product orthonormal basis. The
same middle family precedes all supported exterior operators and every
polynomial through degree `k`. Supporting ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1311–1333, with the square-derived open bond bound;
no source-sharp bond, spectral contraction or running-time assertion is made. -/
private theorem exists_common_physical_aeval_mpo_clm_family_fin
    {L q ell a b B k : ℕ}
    (WL WR : Fin (2 * ell) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, ManyBody.IsSupportedOn (WL r)
      (interval L (a + r.val) (a + r.val + 2)))
    (hright : ∀ r, ManyBody.IsSupportedOn (WR r)
      (interval L (b + r.val) (b + r.val + 2)))
    (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ L - 1)
    (hell : 1 ≤ ell) (hq : 2 ≤ q) (hk : 1 ≤ k)
    (Acore : Fin ((b + 1) - (a + 2 * ell)) → MPOTensor q B)
    (C0 : Matrix (Fin B) (Fin B) ℂ) :
  let Ksites := interval L (a + 2 * ell) (b + 1)
  let eK := intervalShiftOrderIso
    (show a + 2 * ell ≤ b + 1 by omega) (show b + 1 ≤ L by omega)
  let Mphys := ManyBody.placeAlong (X := fun _ ↦ Fin q) eK.toEquiv.toEmbedding
    (Matrix.of fun σ τ : Fin ((b + 1) - (a + 2 * ell)) → Fin q ↦
      Matrix.trace (C0 * (List.ofFn (fun u ↦ Acore u (σ u, τ u))).prod))
  let Pmid := ManyBody.place (X := fun _ ↦ Fin q) Ksites Mphys
  let J := interval L (a + ell) (b + ell + 1)
  let eJ := intervalShiftOrderIso
    (show a + ell ≤ b + ell + 1 by omega)
    (show b + ell + 1 ≤ L by omega)
  let D := (q * k) ^ (18 * ell + 2 * (k / ell))
  let β := fun _ : Fin L ↦ Fin q
  let tau := (ManyBody.cutEquiv β J).trans (Equiv.prodComm _ _)
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
  let Phi := ((EuclideanSpace.basisFun (ManyBody.ComplConfig β J) ℂ).tensorProduct
    (EuclideanSpace.basisFun (ManyBody.RegionConfig β J) ℂ)).repr
  let T := U.trans Phi.symm
  ∃ (N : ℕ) (W : Fin N → Matrix (J → Fin q) (J → Fin q) ℂ),
    N ≤ D ^ 2 ∧
      (∀ r, IsOpenMPS ((b + ell + 1) - (a + ell)) (q * q)
        ((max 1 B) ^ (2 * k)) (fun w ↦ W r
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).1)
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).2))) ∧
      ∀ (PL PR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
        ManyBody.IsSupportedOn PL (interval L 0 (a + 1)) →
        ManyBody.IsSupportedOn PR (interval L (b + 2 * ell) L) →
        let F : ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) →
            Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
          Sum.elim (Sum.elim WL WR) ![PL, Pmid, PR]
        ∀ P : Polynomial ℂ, P.natDegree ≤ k →
          ∃ M : Fin N → Matrix ({v // v ∉ J} → Fin q) ({v // v ∉ J} → Fin q) ℂ,
            Polynomial.aeval (∑ a, F a) P =
              (∑ r, M r ⊗ₖ W r).submatrix
                ((ManyBody.cutEquiv (fun _ : Fin L ↦ Fin q) J).trans
                  (Equiv.prodComm _ _))
                ((ManyBody.cutEquiv (fun _ : Fin L ↦ Fin q) J).trans
                  (Equiv.prodComm _ _)) ∧
            T.toContinuousLinearEquiv.toContinuousLinearMap ∘L
                Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
                  (Polynomial.aeval (∑ a, F a) P) =
              (∑ r, TensorProduct.mapL
                (Matrix.toEuclideanCLM (𝕜 := ℂ)
                  (n := ManyBody.ComplConfig β J) (M r))
                (Matrix.toEuclideanCLM (𝕜 := ℂ)
                  (n := ManyBody.RegionConfig β J) (W r))) ∘L
                T.toContinuousLinearEquiv.toContinuousLinearMap := by
  let J := interval L (a + ell) (b + ell + 1)
  let β := fun _ : Fin L ↦ Fin q
  let tau := (ManyBody.cutEquiv β J).trans (Equiv.prodComm _ _)
  obtain ⟨N, W, hN, hW, _hTrace, hdecomp⟩ :=
    exists_common_physical_aeval_mpo_family_fin
      WL WR hleft hright hab hb hell hq hk Acore C0
  refine ⟨N, W, hN, hW, ?_⟩
  intro PL PR hPL hPR F P hP
  obtain ⟨M, hM⟩ := hdecomp PL PR hPL hPR P hP
  refine ⟨M, hM, ?_⟩
  rw [hM]
  exact Matrix.toEuclideanCLM_reindexed_kronecker_sum_intertwining tau M W

/-- The same common physical family gives a middle-first tensor decomposition
of the conjugated polynomial filter. Its fixed coordinate isometry first
separates exterior and middle, applies the inverse product orthonormal basis,
and exchanges the two tensor factors. The original matrix identity is retained.
The family and its count and natural open bond bounds precede every supported
exterior operator and polynomial choice. Supporting ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333, with the square-derived
bond bound; no spectral contraction, tradeoff or running-time assertion is made. -/
theorem exists_common_physical_aeval_mpo_middleFirst_family_fin
    {L q ell a b B k : ℕ}
    (WL WR : Fin (2 * ell) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, ManyBody.IsSupportedOn (WL r)
      (interval L (a + r.val) (a + r.val + 2)))
    (hright : ∀ r, ManyBody.IsSupportedOn (WR r)
      (interval L (b + r.val) (b + r.val + 2)))
    (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ L - 1)
    (hell : 1 ≤ ell) (hq : 2 ≤ q) (hk : 1 ≤ k)
    (Acore : Fin ((b + 1) - (a + 2 * ell)) → MPOTensor q B)
    (C0 : Matrix (Fin B) (Fin B) ℂ) :
  let Ksites := interval L (a + 2 * ell) (b + 1)
  let eK := intervalShiftOrderIso
    (show a + 2 * ell ≤ b + 1 by omega) (show b + 1 ≤ L by omega)
  let Mphys := ManyBody.placeAlong (X := fun _ ↦ Fin q) eK.toEquiv.toEmbedding
    (Matrix.of fun σ τ : Fin ((b + 1) - (a + 2 * ell)) → Fin q ↦
      Matrix.trace (C0 * (List.ofFn (fun u ↦ Acore u (σ u, τ u))).prod))
  let Pmid := ManyBody.place (X := fun _ ↦ Fin q) Ksites Mphys
  let J := interval L (a + ell) (b + ell + 1)
  let eJ := intervalShiftOrderIso
    (show a + ell ≤ b + ell + 1 by omega)
    (show b + ell + 1 ≤ L by omega)
  let D := (q * k) ^ (18 * ell + 2 * (k / ell))
  let β := fun _ : Fin L ↦ Fin q
  let tau := (ManyBody.cutEquiv β J).trans (Equiv.prodComm _ _)
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
  let Phi := ((EuclideanSpace.basisFun (ManyBody.ComplConfig β J) ℂ).tensorProduct
    (EuclideanSpace.basisFun (ManyBody.RegionConfig β J) ℂ)).repr
  let T : EuclideanSpace ℂ (Fin L → Fin q) ≃ₗᵢ[ℂ]
      (EuclideanSpace ℂ (ManyBody.ComplConfig β J) ⊗[ℂ]
        EuclideanSpace ℂ (ManyBody.RegionConfig β J)) := U.trans Phi.symm
  let Tm : EuclideanSpace ℂ (Fin L → Fin q) ≃ₗᵢ[ℂ]
      (EuclideanSpace ℂ (ManyBody.RegionConfig β J) ⊗[ℂ]
        EuclideanSpace ℂ (ManyBody.ComplConfig β J)) :=
    T.trans (TensorProduct.commIsometry ℂ
    (EuclideanSpace ℂ (ManyBody.ComplConfig β J))
    (EuclideanSpace ℂ (ManyBody.RegionConfig β J)))
  ∃ (N : ℕ) (W : Fin N → Matrix (J → Fin q) (J → Fin q) ℂ),
    N ≤ D ^ 2 ∧
      (∀ r, IsOpenMPS ((b + ell + 1) - (a + ell)) (q * q)
        ((max 1 B) ^ (2 * k)) (fun w ↦ W r
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).1)
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).2))) ∧
      ∀ (PL PR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
        ManyBody.IsSupportedOn PL (interval L 0 (a + 1)) →
        ManyBody.IsSupportedOn PR (interval L (b + 2 * ell) L) →
        let F : ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) →
            Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
          Sum.elim (Sum.elim WL WR) ![PL, Pmid, PR]
        ∀ P : Polynomial ℂ, P.natDegree ≤ k →
          ∃ M : Fin N → Matrix ({v // v ∉ J} → Fin q) ({v // v ∉ J} → Fin q) ℂ,
            Polynomial.aeval (∑ a, F a) P =
              (∑ r, M r ⊗ₖ W r).submatrix
                ((ManyBody.cutEquiv (fun _ : Fin L ↦ Fin q) J).trans
                  (Equiv.prodComm _ _))
                ((ManyBody.cutEquiv (fun _ : Fin L ↦ Fin q) J).trans
                  (Equiv.prodComm _ _)) ∧
            (Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
                Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
                  (Polynomial.aeval (∑ a, F a) P) =
              (∑ r, TensorProduct.mapL
                (Matrix.toEuclideanCLM (𝕜 := ℂ)
                  (n := ManyBody.RegionConfig β J) (W r))
                (Matrix.toEuclideanCLM (𝕜 := ℂ)
                  (n := ManyBody.ComplConfig β J) (M r))) ∘L
                Tm.toContinuousLinearEquiv.toContinuousLinearMap) ∧
            Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
                Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
                  (Polynomial.aeval (∑ a, F a) P) ∘L
                Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
              ∑ r, TensorProduct.mapL
                (Matrix.toEuclideanCLM (𝕜 := ℂ)
                  (n := ManyBody.RegionConfig β J) (W r))
                (Matrix.toEuclideanCLM (𝕜 := ℂ)
                  (n := ManyBody.ComplConfig β J) (M r)) := by
  intro Ksites eK Mphys Pmid J eJ D β tau U Phi T Tm
  obtain ⟨N, W, hN, hW, hdecomp⟩ :=
    exists_common_physical_aeval_mpo_clm_family_fin
      WL WR hleft hright hab hb hell hq hk Acore C0
  refine ⟨N, W, hN, hW, ?_⟩
  intro PL PR hPL hPR F P hP
  obtain ⟨M, hM, hT⟩ := hdecomp PL PR hPL hPR P hP
  refine ⟨M, hM, ?_⟩
  exact TensorProduct.intertwining_sum_mapL_commIsometry
    (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin L → Fin q))
    (L := EuclideanSpace ℂ (ManyBody.ComplConfig β J))
    (R := EuclideanSpace ℂ (ManyBody.RegionConfig β J)) (ι := Fin N) T
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
      (Polynomial.aeval (∑ a, F a) P))
    (fun r ↦ Matrix.toEuclideanCLM (𝕜 := ℂ)
      (n := ManyBody.ComplConfig β J) (M r))
    (fun r ↦ Matrix.toEuclideanCLM (𝕜 := ℂ)
      (n := ManyBody.RegionConfig β J) (W r)) hT

end TNLean.MPS.AreaLaw

end

end PhysicalPolynomialTensorFamily

section ActualClippedPolynomialFamily

/-!
## Common polynomial families for the actual clipped Hamiltonian

The actual five-region Hamiltonian determines its two-window alphabet. Every middle operator
supported on the retained interval has a finite trace representation. A common polynomial
family can then be transported to the prescribed physical interval, with the exact cardinality
cost of changing the region.

These results support ALVV, arXiv:1602.08828v2,
`def:hard-trunc`, lines 873–886, and Theorem `t:ais`, lines 1010–1024.
-/

section

open Matrix

open scoped BigOperators Kronecker

section

open scoped BigOperators

section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix QuantumCircuit

/-- The actual clipped five-region sum has the literal two-window alphabet,
with the common scalar energy shift placed in its left bulk term. All
supports follow from the original nearest-neighbour supports. Auxiliary to
ALVV, arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821,
`def:hard-trunc`, lines 873–886, and `t:ais`, lines 1010–1024.
No Hamiltonian identity, regional support, positivity or ground data is supplied. -/
private theorem actual_clipped_two_window_alphabet
    (L q a b ell : ℕ) (hell : 1 ≤ ell)
    (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ L - 1)
    (Φ : ManyBody.BondInteraction L q)
    (e : Fin 5 → ℝ) (t : ℝ) :
    let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
    let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
      ∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
        (fun i ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), Φ.term i
    let J := (Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ i.val + 1 ∈
        ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
    let Y := ∑ i ∈ J, Φ.term i
    let WL : Fin (2 * ell) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
      fun r ↦ Φ.term ⟨a + r.val, by omega⟩
    let WR : Fin (2 * ell) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
      fun r ↦ Φ.term ⟨b + r.val, by omega⟩
    let C := fun j : Fin 5 ↦ cfc (fun r : ℝ ↦ min r (e j + t)) (A j)
    let S : ℝ := ∑ j, e j
    let PL := C 0 - (S : ℂ) • 1
    let Pmid := C 2
    let PR := C 4
    let F := Sum.elim (Sum.elim WL WR) ![PL, Pmid, PR]
    let K : Finset (Fin 5) := {0, 2, 4}
    let B := (∑ j, ((if j ∈ K then C j else A j) - (e j : ℂ) • 1)) + Y
    (∀ r, ManyBody.IsSupportedOn (WL r)
      (interval L (a + r.val) (a + r.val + 2))) ∧
    (∀ r, ManyBody.IsSupportedOn (WR r)
      (interval L (b + r.val) (b + r.val + 2))) ∧
    ManyBody.IsSupportedOn PL (interval L 0 (a + 1)) ∧
    ManyBody.IsSupportedOn Pmid (interval L (a + 2 * ell) (b + 1)) ∧
    ManyBody.IsSupportedOn PR (interval L (b + 2 * ell) L) ∧
    (∑ r, F r) = B := by
  classical
  intro k A J Y WL WR C S PL Pmid PR F K B
  let R : Fin 5 → Finset (Fin L) := fun j ↦ interval L (k j.castSucc) (k j.succ)
  have hA (j : Fin 5) : ManyBody.IsSupportedOn (A j) (R j) := by
    change _ ∈ ManyBody.supportedOperators _ _
    apply sum_mem
    intro i hi
    exact (Φ.mem i).mono (ManyBody.internal_bond_support_subset hi)
  have hC (j : Fin 5) : C j ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) (R j : Finset (Fin L)) :=
    ManyBody.cfc_mem_supportedOperators _
      (hA j)
  have hPL : PL ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) (R 0 : Finset (Fin L)) :=
    sub_mem (hC 0)
      (SMulMemClass.smul_mem _ (one_mem (ManyBody.supportedOperators _ _)))
  refine ⟨?_, ?_, hPL,
    (hC 2),
    (hC 4), ?_⟩
  · intro r
    exact Φ.mem ⟨a + r.val, by omega⟩
  · intro r
    exact Φ.mem ⟨b + r.val, by omega⟩
  · have htotal : Φ.hamiltonian = (∑ j, A j) + Y := by
      have hraw := Fin.sum_eq_five_internal_add_crossings
        (A := Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (L := L)
        (k1 := a + 1) (k2 := a + 2 * ell) (k3 := b + 1) (k4 := b + 2 * ell)
        (by omega : a + 1 ≤ a + 2 * ell)
        (hab.trans (Nat.le_succ b)) (by omega : b + 1 ≤ b + 2 * ell) Φ.term
      rw [Fin.sum_univ_five]
      change Φ.hamiltonian =
        (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
          (fun i ↦ 0 ≤ i.val ∧ i.val + 1 < a + 1), Φ.term i) +
        (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
          (fun i ↦ a + 1 ≤ i.val ∧ i.val + 1 < a + 2 * ell), Φ.term i) +
        (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
          (fun i ↦ a + 2 * ell ≤ i.val ∧ i.val + 1 < b + 1), Φ.term i) +
        (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
          (fun i ↦ b + 1 ≤ i.val ∧ i.val + 1 < b + 2 * ell), Φ.term i) +
        (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
          (fun i ↦ b + 2 * ell ≤ i.val ∧ i.val + 1 < L), Φ.term i) +
        (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
          (fun i ↦ i.val + 1 ∈
            ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ)), Φ.term i)
      exact hraw
    have hwin : Φ.hamiltonian = A 0 + (∑ r, WL r) + A 2 + (∑ r, WR r) + A 4 :=
      Fin.sum_univ_eq_actual_two_window_alphabet L a b ell hab hb Φ.term
    have hbulk : (∑ r, WL r) + (∑ r, WR r) = A 1 + A 3 + Y := by
      calc
        (∑ r, WL r) + (∑ r, WR r) =
            (A 0 + (∑ r, WL r) + A 2 + (∑ r, WR r) + A 4) -
              A 0 - A 2 - A 4 := by abel
        _ = ((∑ j, A j) + Y) - A 0 - A 2 - A 4 :=
          congrArg (fun X ↦ X - A 0 - A 2 - A 4) (hwin.symm.trans htotal)
        _ = A 1 + A 3 + Y := by
          rw [Fin.sum_univ_five]
          abel
    have hsumc : (∑ j, (e j : ℂ) •
        (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)) = (S : ℂ) • 1 := by
      simp only [Complex.coe_smul, ← Finset.sum_smul, S]
    have hB : B = C 0 + A 1 + C 2 + A 3 + C 4 - (S : ℂ) • 1 + Y := by
      dsimp only [B]
      rw [Finset.sum_sub_distrib, hsumc]
      simp [K, Fin.sum_univ_five]
    have hF : (∑ r, F r) = (∑ r, WL r) + (∑ r, WR r) + (PL + Pmid + PR) := by
      simp only [F, Fintype.sum_sumElim, Fin.sum_univ_three]
      rfl
    rw [hF, hbulk, hB]
    dsimp only [PL, Pmid, PR]
    abel
end TNLean.MPS.AreaLaw
end
end

section

open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- Every polynomial of the actual three-bulk clipped Hamiltonian has one
common middle family. The central trace core and the two-window identity
are derived internally from the original supported bonds. The family is
chosen before the polynomial. Auxiliary to ALVV, arXiv:1602.08828v2,
`def:hard-trunc`, lines 873–886, Proposition 5.7, lines 1311–1333, and
Theorem `t:ais`, lines 1010–1024. No efficient central bond or running-time
bound is asserted. The regional energies remain arbitrary here; their
physical values are supplied by the separate low-cluster construction. -/
private theorem exists_actual_clipped_polynomial_family_fin
    (L q a b ell degree : ℕ) (hell : 1 ≤ ell) (hq : 2 ≤ q)
    (hdegree : 1 ≤ degree)
    (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ L - 1)
    (Φ : ManyBody.BondInteraction L q)
    (e : Fin 5 → ℝ) (t : ℝ) :
    let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
    let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
      ∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
        (fun i ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), Φ.term i
    let Cross := (Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ i.val + 1 ∈
        ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
    let Y := ∑ i ∈ Cross, Φ.term i
    let K : Finset (Fin 5) := {0, 2, 4}
    let B := (∑ j, ((if j ∈ K then
      cfc (fun r : ℝ ↦ min r (e j + t)) (A j) else A j) - (e j : ℂ) • 1)) + Y
    let J := interval L (a + ell) (b + ell + 1)
    let D := (q * degree) ^ (18 * ell + 2 * (degree / ell))
    ∃ (N : ℕ) (W : Fin N → Matrix (J → Fin q) (J → Fin q) ℂ),
      N ≤ D ^ 2 ∧
      ∀ Q : Polynomial ℂ, Q.natDegree ≤ degree →
        ∃ M : Fin N → Matrix ({v // v ∉ J} → Fin q) ({v // v ∉ J} → Fin q) ℂ,
          Polynomial.aeval B Q = (∑ r, M r ⊗ₖ W r).submatrix
            ((ManyBody.cutEquiv (fun _ : Fin L ↦ Fin q) J).trans
              (Equiv.prodComm _ _))
            ((ManyBody.cutEquiv (fun _ : Fin L ↦ Fin q) J).trans
              (Equiv.prodComm _ _)) := by
  classical
  intro k A Cross Y K B J D
  let WL : Fin (2 * ell) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
    fun r ↦ Φ.term ⟨a + r.val, by omega⟩
  let WR : Fin (2 * ell) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
    fun r ↦ Φ.term ⟨b + r.val, by omega⟩
  let C := fun j : Fin 5 ↦ cfc (fun r : ℝ ↦ min r (e j + t)) (A j)
  let PL := C 0 - ((∑ j, e j : ℝ) : ℂ) • 1
  let Pmid := C 2
  let PR := C 4
  obtain ⟨hWL, hWR, hPL, hPmid, hPR, hsum⟩ :=
    actual_clipped_two_window_alphabet L q a b ell hell hab hb Φ e t
  obtain ⟨bond, Acore, C0, hcore⟩ :=
    exists_traceChainOperator_of_supported_interval
      (show a + 2 * ell ≤ b + 1 by omega) (show b + 1 ≤ L by omega) Pmid hPmid
  let Pcore := ManyBody.place (X := fun _ ↦ Fin q) (interval L (a + 2 * ell) (b + 1))
    (ManyBody.placeAlong (X := fun _ ↦ Fin q) (intervalShiftOrderIso
      (show a + 2 * ell ≤ b + 1 by omega) (show b + 1 ≤ L by omega)).toEquiv.toEmbedding
      (MPOTensor.traceChainOperator Acore C0))
  have hPcore : Pcore = Pmid := hcore.symm
  obtain ⟨N, W, hN, _hW, _hTrace, hdecomp⟩ :=
    exists_common_physical_aeval_mpo_family_fin
      WL WR hWL hWR hab hb hell hq hdegree Acore C0
  refine ⟨N, W, hN, ?_⟩
  intro Q hQ
  obtain ⟨M, hM⟩ := hdecomp PL PR hPL hPR Q hQ
  have hsumCore : (∑ r, Sum.elim (Sum.elim WL WR) ![PL, Pcore, PR] r) = B := by
    rw [hPcore]
    exact hsum
  change Polynomial.aeval (∑ r, Sum.elim (Sum.elim WL WR) ![PL, Pcore, PR] r) Q =
    (∑ r, M r ⊗ₖ W r).submatrix
      ((ManyBody.cutEquiv (fun _ : Fin L ↦ Fin q) J).trans (Equiv.prodComm _ _))
      ((ManyBody.cutEquiv (fun _ : Fin L ↦ Fin q) J).trans (Equiv.prodComm _ _)) at hM
  exact ⟨M, hsumCore ▸ hM⟩
end TNLean.MPS.AreaLaw
end

section

open scoped BigOperators Kronecker TensorProduct ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- The actual clipped Hamiltonian admits one polynomial middle family on
any prescribed set of sites. Transferring the family costs the two configuration
spaces crossing the change of region. The same coefficients give the literal
middle-first continuous tensor decomposition. All tensor coordinates and the
central trace representation are derived, rather than supplied as hypotheses.
Auxiliary to ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333,
and Theorem `t:ais`, lines 1010–1024. The regional energies are arbitrary
inputs; no efficient central bond or running-time assertion is made. -/
theorem exists_actual_regional_clipped_polynomial_family_fin
    (L q a b ell degree : ℕ) (hell : 1 ≤ ell) (hq : 2 ≤ q)
    (hdegree : 1 ≤ degree)
    (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ L - 1)
    (Φ : ManyBody.BondInteraction L q)
    (e : Fin 5 → ℝ) (t : ℝ) (Jtarget : Finset (Fin L)) :
    let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
    let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
      ∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
        (fun i ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), Φ.term i
    let Cross := (Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ i.val + 1 ∈
        ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
    let Y := ∑ i ∈ Cross, Φ.term i
    let K : Finset (Fin 5) := {0, 2, 4}
    let B := (∑ j, ((if j ∈ K then
      cfc (fun r : ℝ ↦ min r (e j + t)) (A j) else A j) - (e j : ℂ) • 1)) + Y
    let J0 := interval L (a + ell) (b + ell + 1)
    let D0 := (q * degree) ^ (18 * ell + 2 * (degree / ell))
    let β := fun _ : Fin L ↦ Fin q
    let tau := (ManyBody.cutEquiv β Jtarget).trans (Equiv.prodComm _ _)
    let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
    let Phi := ((EuclideanSpace.basisFun (ManyBody.ComplConfig β Jtarget) ℂ).tensorProduct
      (EuclideanSpace.basisFun (ManyBody.RegionConfig β Jtarget) ℂ)).repr
    let T := U.trans Phi.symm
    let Tm := T.trans (TensorProduct.commIsometry ℂ
      (EuclideanSpace ℂ (ManyBody.ComplConfig β Jtarget))
      (EuclideanSpace ℂ (ManyBody.RegionConfig β Jtarget)))
    ∃ (N : ℕ) (W : Fin N → Matrix (Jtarget → Fin q) (Jtarget → Fin q) ℂ),
      N ≤ D0 ^ 2 * q ^ (2 * (J0 \ Jtarget).card + 2 * (Jtarget \ J0).card) ∧
      ∀ Q : Polynomial ℂ, Q.natDegree ≤ degree →
        ∃ M : Fin N → Matrix ({v // v ∉ Jtarget} → Fin q) ({v // v ∉ Jtarget} → Fin q) ℂ,
          Polynomial.aeval B Q = (∑ r, M r ⊗ₖ W r).submatrix tau tau ∧
          Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
              Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
                (Polynomial.aeval B Q) ∘L
              Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
            ∑ r, TensorProduct.mapL
              (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Jtarget → Fin q) (W r))
              (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := {v // v ∉ Jtarget} → Fin q) (M r)) := by
  classical
  intro k A Cross Y K B J0 D0 β tau U Phi T Tm
  obtain ⟨N0, W0, hN0, hpoly⟩ :=
    exists_actual_clipped_polynomial_family_fin L q a b ell degree hell hq
      hdegree hab hb Φ e t
  obtain ⟨N, W, hN, htransport⟩ :=
    exists_changingRegional_family_fin q J0 Jtarget W0
  refine ⟨N, W, ?_, ?_⟩
  · calc
      N = N0 * q ^ (2 * (J0 \ Jtarget).card + 2 * (Jtarget \ J0).card) := by
        simpa only [Fintype.card_fin] using hN
      _ ≤ D0 ^ 2 * q ^ (2 * (J0 \ Jtarget).card + 2 * (Jtarget \ J0).card) :=
        Nat.mul_le_mul_right _ hN0
  · intro Q hQ
    obtain ⟨M0, hM0⟩ := hpoly Q hQ
    obtain ⟨M, hM⟩ := htransport M0
    have hmatrix : Polynomial.aeval B Q = (∑ r, M r ⊗ₖ W r).submatrix tau tau :=
      hM0.trans hM
    have hconj := Matrix.toEuclideanCLM_middleFirst_conjugation_of_kronecker_sum
      (Z := Fin L → Fin q)
      (X := ManyBody.ComplConfig β Jtarget)
      (Y := ManyBody.RegionConfig β Jtarget) (ι := Fin N)
      tau M W (Polynomial.aeval B Q) hmatrix
    exact ⟨M, hmatrix, hconj⟩
end TNLean.MPS.AreaLaw
end
end

end ActualClippedPolynomialFamily

section PhysicalChebyshevViability

/-!
## Physical polynomial families and Chebyshev viability

The common physical polynomial family gives an enlargement of every
viable subspace of the retained interval. For the actual conjugated
Hamiltonian, closed spectral separation and an upper spectral bound yield
the Chebyshev contraction estimate. The dimension increases by at most
the squared family-count parameter. The chosen family precedes every
supported exterior operator and every spectral choice.

The open bond estimate remains the coarse bound inherited from the
polynomial family. This result does not assert the source-sharp bond
estimate or the running-time assertion of Proposition 5.7.

### References

Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333,
Definition `def:Cheby-AGSP`, lines 789–803, Theorem `thm:Cheby-AGSP`,
lines 809–853, and Lemma `l:er`, lines 597–622.
-/

open Matrix QuantumCircuit
open scoped BigOperators Matrix Kronecker TensorProduct InnerProductSpace

noncomputable section

namespace TNLean.MPS.AreaLaw

/-- A single physical middle family improves viability for the actual
Chebyshev polynomial filter under explicit symmetry, spectral-gap and
upper-spectrum assumptions. The middle family precedes all supported
exterior operators and spectral choices. Its count is at most `D^2` and
its natural open bond is at most `(max 1 B)^(2*k)`.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333,
Definition `def:Cheby-AGSP`, lines 789–803, Theorem `thm:Cheby-AGSP`,
lines 809–853, and Lemma `l:er`, lines 597–622.

**Local fix (spectral boundaries and positivity):** The hypotheses use the
closed low/high conditions and `δ < 1`. Positivity of the unsquared filter
is not asserted. See the companion notes:
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf
https://sirui-lu.com/QICLean/paper-gaps/alvv16_chebyshev_filter_positivity.pdf
This supporting result does not assert the source-sharp bond or running time. -/
theorem exists_common_physical_chebyshev_viable_family_fin
    {L q ell a b B k : ℕ}
    (WL WR : Fin (2 * ell) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, ManyBody.IsSupportedOn (WL r)
      (interval L (a + r.val) (a + r.val + 2)))
    (hright : ∀ r, ManyBody.IsSupportedOn (WR r)
      (interval L (b + r.val) (b + r.val + 2)))
    (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ L - 1)
    (hell : 1 ≤ ell) (hq : 2 ≤ q) (hk : 1 ≤ k)
    (Acore : Fin ((b + 1) - (a + 2 * ell)) → MPOTensor q B)
    (C0 : Matrix (Fin B) (Fin B) ℂ) :
  (by
    exact (show Prop from
      let Ksites := interval L (a + 2 * ell) (b + 1)
      let eK := intervalShiftOrderIso
        (show a + 2 * ell ≤ b + 1 by omega) (show b + 1 ≤ L by omega)
      let Mphys := ManyBody.placeAlong (X := fun _ ↦ Fin q) eK.toEquiv.toEmbedding
        (Matrix.of fun σ τ : Fin ((b + 1) - (a + 2 * ell)) → Fin q ↦
          Matrix.trace (C0 * (List.ofFn (fun u ↦ Acore u (σ u, τ u))).prod))
      let Pmid := ManyBody.place (X := fun _ ↦ Fin q) Ksites Mphys
      let J := interval L (a + ell) (b + ell + 1)
      let eJ := intervalShiftOrderIso
        (show a + ell ≤ b + ell + 1 by omega)
        (show b + ell + 1 ≤ L by omega)
      let D : ℕ := (q * k) ^ (18 * ell + 2 * (k / ell))
      let β := fun _ : Fin L ↦ Fin q
      let tau := (ManyBody.cutEquiv β J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (ManyBody.ComplConfig β J) ℂ).tensorProduct
        (EuclideanSpace.basisFun (ManyBody.RegionConfig β J) ℂ)).repr
      let T : EuclideanSpace ℂ (Fin L → Fin q) ≃ₗᵢ[ℂ]
          (EuclideanSpace ℂ (ManyBody.ComplConfig β J) ⊗[ℂ]
            EuclideanSpace ℂ (ManyBody.RegionConfig β J)) := U.trans Phi.symm
      let Tm : EuclideanSpace ℂ (Fin L → Fin q) ≃ₗᵢ[ℂ]
          (EuclideanSpace ℂ (ManyBody.RegionConfig β J) ⊗[ℂ]
            EuclideanSpace ℂ (ManyBody.ComplConfig β J)) :=
        T.trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (ManyBody.ComplConfig β J))
        (EuclideanSpace ℂ (ManyBody.RegionConfig β J)))
      let HM := EuclideanSpace ℂ (ManyBody.RegionConfig β J)
      let HE := EuclideanSpace ℂ (ManyBody.ComplConfig β J)
      let Hspace : Type := HM ⊗[ℂ] HE
      ∃ (N : ℕ) (W : Fin N → Matrix (J → Fin q) (J → Fin q) ℂ),
        let A : Fin N → HM →L[ℂ] HM := fun r ↦
          Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ManyBody.RegionConfig β J) (W r)
        let grow : Submodule ℂ HM → Submodule ℂ HM := fun S ↦
          ⨆ r : Fin N, S.map (A r : HM →ₗ[ℂ] HM)
        N ≤ D ^ (2 : ℕ) ∧
          (∀ r, IsOpenMPS ((b + ell + 1) - (a + ell)) (q * q)
            ((max 1 B) ^ (2 * k)) (fun w ↦ W r
              (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).1)
              (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).2))) ∧
          ∀ (PL PR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
            ManyBody.IsSupportedOn PL (interval L 0 (a + 1)) →
            ManyBody.IsSupportedOn PR (interval L (b + 2 * ell) L) →
            let F : ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) →
                Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
              Sum.elim (Sum.elim WL WR) ![PL, Pmid, PR]
            let Hphys : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, F i
            let Hm : Hspace →L[ℂ] Hspace :=
              Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
                Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) Hphys ∘L
                Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap
            ∀ hHm : (Hm : Hspace →ₗ[ℂ] Hspace).IsSymmetric,
              let n : ℕ := Module.finrank ℂ Hspace
              let hn : Module.finrank ℂ Hspace = n := rfl
              let eig : Fin n → ℝ := hHm.eigenvalues hn
              let eigBasis : OrthonormalBasis (Fin n) ℂ Hspace :=
                hHm.eigenvectorBasis hn
              ∀ η₀ η₁ u : ℝ, η₀ < η₁ → η₁ ≤ u →
                (∀ j, eig j ≤ u) → (∀ j, eig j ≤ η₀ ∨ η₁ ≤ eig j) →
                let G : Submodule ℂ Hspace := Submodule.span ℂ (eigBasis '' {j | eig j ≤ η₀})
                let Δ : ℝ := (2 * Real.exp
                  (-2 * (k : ℝ) * Real.sqrt ((η₁ - η₀) / (u - η₀)))) ^ (2 : ℕ)
                ∀ (S : Submodule ℂ HM) (δ : ℝ),
                  Submodule.IsViable (𝕜 := ℂ) (E := HM) (F := HE) δ S G → δ < 1 →
                  let V : Submodule ℂ HM := grow S
                  Module.finrank ℂ V ≤ D ^ (2 : ℕ) * Module.finrank ℂ S ∧
                    Submodule.IsViable (𝕜 := ℂ) (E := HM) (F := HE)
                      (Δ / (1 - δ) ^ (2 : ℕ)) V G)) := by
  intro resultType
  unfold resultType
  intro Ksites eK Mphys Pmid J eJ D β tau U Phi T Tm HM HE Hspace
  obtain ⟨N, W, hN, hW, hdecomp⟩ :=
    exists_common_physical_aeval_mpo_middleFirst_family_fin
      WL WR hleft hright hab hb hell hq hk Acore C0
  refine ⟨N, W, ?_⟩
  intro A grow
  refine ⟨hN, hW, ?_⟩
  intro PL PR hPL hPR F Hphys Hm hHm n hn eig eigBasis η₀ η₁ u
    hsep hupperEndpoint hupper hgap G Δ
  exact Matrix.chebyshev_viability_of_conjugated_polynomial_family_of_card_le
    (σ := Fin L → Fin q) (m := ManyBody.RegionConfig β J)
    (e := ManyBody.ComplConfig β J) (N := N) (k := k)
    Hphys W Tm (by
      intro Q hQ
      obtain ⟨M, _hmatrix, _hinter, hK⟩ := hdecomp PL PR hPL hPR Q hQ
      exact ⟨M, hK⟩) (D ^ (2 : ℕ)) hN
      hHm n hn η₀ η₁ u hsep hupperEndpoint hupper hgap

end TNLean.MPS.AreaLaw

end

end PhysicalChebyshevViability
