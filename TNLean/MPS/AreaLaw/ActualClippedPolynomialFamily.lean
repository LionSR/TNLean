/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import QICLean.Analysis.MatrixTensorCoordinates
import TNLean.Algebra.MatrixFactorExchange
import TNLean.Algebra.TwoWindowSum
import TNLean.MPS.AreaLaw.FiveRegionHamiltonian
import TNLean.MPS.AreaLaw.LocalSolution.SupersiteHierarchy
import TNLean.MPS.AreaLaw.PhysicalIntervalTransport
import TNLean.MPS.AreaLaw.PhysicalPolynomialTensorFamily
import TNLean.MPS.AreaLaw.RegionalMiddleFactors
import TNLean.MPS.AreaLaw.TwoWindowPolynomialMPOFamily

/-!
# Common polynomial families for the actual clipped Hamiltonian

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
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (e : Fin 5 → ℝ) (t : ℝ) :
    let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
    let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
      ∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
        (fun i ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), h i
    let J := (Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ i.val + 1 ∈
        ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
    let Y := ∑ i ∈ J, h i
    let WL : Fin (2 * ell) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
      fun r ↦ h ⟨a + r.val, by omega⟩
    let WR : Fin (2 * ell) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
      fun r ↦ h ⟨b + r.val, by omega⟩
    let C := fun j : Fin 5 ↦ cfc (fun r : ℝ ↦ min r (e j + t)) (A j)
    let S : ℝ := ∑ j, e j
    let PL := C 0 - (S : ℂ) • 1
    let Pmid := C 2
    let PR := C 4
    let F := Sum.elim (Sum.elim WL WR) ![PL, Pmid, PR]
    let K : Finset (Fin 5) := {0, 2, 4}
    let B := (∑ j, ((if j ∈ K then C j else A j) - (e j : ℂ) • 1)) + Y
    (∀ r, Entropy.IsSupportedOn (WL r)
      (interval L (a + r.val) (a + r.val + 2))) ∧
    (∀ r, Entropy.IsSupportedOn (WR r)
      (interval L (b + r.val) (b + r.val + 2))) ∧
    Entropy.IsSupportedOn PL (interval L 0 (a + 1)) ∧
    Entropy.IsSupportedOn Pmid (interval L (a + 2 * ell) (b + 1)) ∧
    Entropy.IsSupportedOn PR (interval L (b + 2 * ell) L) ∧
    (∑ r, F r) = B := by
  classical
  intro k A J Y WL WR C S PL Pmid PR F K B
  let R : Fin 5 → Finset (Fin L) := fun j ↦ interval L (k j.castSucc) (k j.succ)
  have hA (j : Fin 5) : Entropy.IsSupportedOn (A j) (R j) := by
    apply TNLean.Lattice.isSupportedOn_sum
    intro i hi
    exact (hs i).mono (internal_bond_support_subset hi)
  have hC (j : Fin 5) : C j ∈ supportedOperators q (R j : Set (Fin L)) :=
    LocalSolution.cfc_mem_supportedOperators _
      (mem_supportedOperators_of_isSupportedOn (hA j))
  have hPL : PL ∈ supportedOperators q (R 0 : Set (Fin L)) :=
    Submodule.sub_mem _ (hC 0)
      (Submodule.smul_mem _ _ (one_mem_supportedOperators _))
  refine ⟨?_, ?_, isSupportedOn_of_mem_supportedOperators hPL,
    isSupportedOn_of_mem_supportedOperators (hC 2),
    isSupportedOn_of_mem_supportedOperators (hC 4), ?_⟩
  · intro r
    exact hs ⟨a + r.val, by omega⟩
  · intro r
    exact hs ⟨b + r.val, by omega⟩
  · have htotal : (∑ i, h i) = (∑ j, A j) + Y := by
      have hraw := Finset.sum_five_internal_regions_add_crossings
        (A := Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (L := L)
        (k1 := a + 1) (k2 := a + 2 * ell) (k3 := b + 1) (k4 := b + 2 * ell)
        (by omega : a + 1 ≤ a + 2 * ell)
        (hab.trans (Nat.le_succ b)) (by omega : b + 1 ≤ b + 2 * ell) h
      rw [Fin.sum_univ_five]
      change (∑ i, h i) =
        (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
          (fun i ↦ 0 ≤ i.val ∧ i.val + 1 < a + 1), h i) +
        (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
          (fun i ↦ a + 1 ≤ i.val ∧ i.val + 1 < a + 2 * ell), h i) +
        (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
          (fun i ↦ a + 2 * ell ≤ i.val ∧ i.val + 1 < b + 1), h i) +
        (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
          (fun i ↦ b + 1 ≤ i.val ∧ i.val + 1 < b + 2 * ell), h i) +
        (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
          (fun i ↦ b + 2 * ell ≤ i.val ∧ i.val + 1 < L), h i) +
        (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
          (fun i ↦ i.val + 1 ∈
            ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ)), h i)
      exact hraw
    have hwin : (∑ i, h i) = A 0 + (∑ r, WL r) + A 2 + (∑ r, WR r) + A 4 :=
      Fin.sum_univ_eq_actual_two_window_alphabet L a b ell hab hb h
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
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (e : Fin 5 → ℝ) (t : ℝ) :
    let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
    let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
      ∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
        (fun i ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), h i
    let Cross := (Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ i.val + 1 ∈
        ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
    let Y := ∑ i ∈ Cross, h i
    let K : Finset (Fin 5) := {0, 2, 4}
    let B := (∑ j, ((if j ∈ K then
      cfc (fun r : ℝ ↦ min r (e j + t)) (A j) else A j) - (e j : ℂ) • 1)) + Y
    let J := interval L (a + ell) (b + ell + 1)
    let D := (q * degree) ^ (18 * ell + 2 * (degree / ell))
    ∃ (N : ℕ) (W : Fin N → Matrix (J → Fin q) (J → Fin q) ℂ),
      N ≤ D ^ 2 ∧
      ∀ Q : Polynomial ℂ, Q.natDegree ≤ degree →
        ∃ M : Fin N → Matrix (↥(Jᶜ) → Fin q) (↥(Jᶜ) → Fin q) ℂ,
          Polynomial.aeval B Q = (∑ r, M r ⊗ₖ W r).submatrix
            ((FiniteProduct.splitEquiv (fun _ : Fin L ↦ Fin q) J).trans
              (Equiv.prodComm _ _))
            ((FiniteProduct.splitEquiv (fun _ : Fin L ↦ Fin q) J).trans
              (Equiv.prodComm _ _)) := by
  classical
  intro k A Cross Y K B J D
  let WL : Fin (2 * ell) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
    fun r ↦ h ⟨a + r.val, by omega⟩
  let WR : Fin (2 * ell) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
    fun r ↦ h ⟨b + r.val, by omega⟩
  let C := fun j : Fin 5 ↦ cfc (fun r : ℝ ↦ min r (e j + t)) (A j)
  let PL := C 0 - ((∑ j, e j : ℝ) : ℂ) • 1
  let Pmid := C 2
  let PR := C 4
  obtain ⟨hWL, hWR, hPL, hPmid, hPR, hsum⟩ :=
    actual_clipped_two_window_alphabet L q a b ell hell hab hb h hs e t
  obtain ⟨bond, Acore, C0, hcore⟩ :=
    exists_traceChainOperator_of_supported_interval
      (show a + 2 * ell ≤ b + 1 by omega) (show b + 1 ≤ L by omega) Pmid hPmid
  let Pcore := QuantumCircuit.embedOp
    (Subtype.val : interval L (a + 2 * ell) (b + 1) → Fin L)
    (QuantumCircuit.embedOp (intervalShiftOrderIso
      (show a + 2 * ell ≤ b + 1 by omega) (show b + 1 ≤ L by omega))
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
      ((FiniteProduct.splitEquiv (fun _ : Fin L ↦ Fin q) J).trans (Equiv.prodComm _ _))
      ((FiniteProduct.splitEquiv (fun _ : Fin L ↦ Fin q) J).trans (Equiv.prodComm _ _)) at hM
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
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (e : Fin 5 → ℝ) (t : ℝ) (Jtarget : Finset (Fin L)) :
    let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
    let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
      ∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
        (fun i ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), h i
    let Cross := (Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ i.val + 1 ∈
        ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
    let Y := ∑ i ∈ Cross, h i
    let K : Finset (Fin 5) := {0, 2, 4}
    let B := (∑ j, ((if j ∈ K then
      cfc (fun r : ℝ ↦ min r (e j + t)) (A j) else A j) - (e j : ℂ) • 1)) + Y
    let J0 := interval L (a + ell) (b + ell + 1)
    let D0 := (q * degree) ^ (18 * ell + 2 * (degree / ell))
    let β := fun _ : Fin L ↦ Fin q
    let tau := (FiniteProduct.splitEquiv β Jtarget).trans (Equiv.prodComm _ _)
    let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
    let Phi := ((EuclideanSpace.basisFun (FiniteProduct.Configuration β Jtargetᶜ) ℂ).tensorProduct
      (EuclideanSpace.basisFun (FiniteProduct.Configuration β Jtarget) ℂ)).repr
    let T := U.trans Phi.symm
    let Tm := T.trans (TensorProduct.commIsometry ℂ
      (EuclideanSpace ℂ (FiniteProduct.Configuration β Jtargetᶜ))
      (EuclideanSpace ℂ (FiniteProduct.Configuration β Jtarget)))
    ∃ (N : ℕ) (W : Fin N → Matrix (Jtarget → Fin q) (Jtarget → Fin q) ℂ),
      N ≤ D0 ^ 2 * q ^ (2 * (J0 \ Jtarget).card + 2 * (Jtarget \ J0).card) ∧
      ∀ Q : Polynomial ℂ, Q.natDegree ≤ degree →
        ∃ M : Fin N → Matrix (↥(Jtargetᶜ) → Fin q) (↥(Jtargetᶜ) → Fin q) ℂ,
          Polynomial.aeval B Q = (∑ r, M r ⊗ₖ W r).submatrix tau tau ∧
          Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
              Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
                (Polynomial.aeval B Q) ∘L
              Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
            ∑ r, TensorProduct.mapL
              (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Jtarget → Fin q) (W r))
              (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ↥(Jtargetᶜ) → Fin q) (M r)) := by
  classical
  intro k A Cross Y K B J0 D0 β tau U Phi T Tm
  obtain ⟨N0, W0, hN0, hpoly⟩ :=
    exists_actual_clipped_polynomial_family_fin L q a b ell degree hell hq
      hdegree hab hb h hs e t
  obtain ⟨N, W, hN, htransport⟩ :=
    FiniteProduct.exists_changingRegional_family_fin q J0 Jtarget W0
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
      (X := FiniteProduct.Configuration β Jtargetᶜ)
      (Y := FiniteProduct.Configuration β Jtarget) (ι := Fin N)
      tau M W (Polynomial.aeval B Q) hmatrix
    exact ⟨M, hmatrix, hconj⟩
end TNLean.MPS.AreaLaw
end
end
