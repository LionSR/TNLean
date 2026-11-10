/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalPolynomialTensorFamily
import TNLean.MPS.MPDO.TraceChainLinearCombination
import TNLean.Circuit.SiteEmbeddingOrder
import QICLean.Algebra.MatrixPolynomialParameter

/-!
# Common physical polynomial families for polynomial closing matrices

A fixed native core and polynomial closing matrix determine one physical family
before the closing parameter and exterior operators are chosen. Integer
interpolation nodes affect only which existing common physical family is
selected. Their union retains each individual open-boundary bond bound.
The exterior operators remain fixed during interpolation, even when they
are later chosen as functions of the requested parameter.

The displayed open bond is the square-derived bound of the existing
physical family; no source-sharp bond or running-time estimate is claimed.
The common spanning interpolation is documented at:
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf

Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333,
and its use in the soft construction, lines 1373–1420.
-/

open Matrix QuantumCircuit
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- Enumerating a finite union of matrix families does not change its members.
Weights in a linear combination can be absorbed into the exterior factors.
Auxiliary to ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem exists_flattened_kronecker_family
    {alpha mu nu : Type*} [Fintype alpha]
    (n : alpha → ℕ) (Wnode : (a : alpha) → Fin (n a) → Matrix nu nu ℂ) :
    ∃ (N : ℕ) (W : Fin N → Matrix nu nu ℂ),
      N = ∑ a, n a ∧
      (∀ j, ∃ a i, W j = Wnode a i) ∧
      ∀ (Mnode : (a : alpha) → Fin (n a) → Matrix mu mu ℂ) (c : alpha → ℂ),
        ∃ M : Fin N → Matrix mu mu ℂ,
          (∑ a, c a • (∑ i, Mnode a i ⊗ₖ Wnode a i)) = ∑ j, M j ⊗ₖ W j := by
  classical
  let N := ∑ a, n a
  let e : (Σ a : alpha, Fin (n a)) ≃ Fin N := Fintype.equivFinOfCardEq (by simp [N])
  let W := fun j : Fin N ↦ Wnode (e.symm j).1 (e.symm j).2
  refine ⟨N, W, rfl, fun j ↦ ⟨(e.symm j).1, (e.symm j).2, rfl⟩, ?_⟩
  intro Mnode c
  refine ⟨fun j ↦ c (e.symm j).1 • Mnode (e.symm j).1 (e.symm j).2, ?_⟩
  calc
    (∑ a, c a • (∑ i, Mnode a i ⊗ₖ Wnode a i)) =
        ∑ s : Σ a : alpha, Fin (n a), (c s.1 • Mnode s.1 s.2) ⊗ₖ Wnode s.1 s.2 := by
      simp only [Fintype.sum_sigma, Matrix.smul_kronecker, Finset.smul_sum]
    _ = _ := (Fintype.sum_equiv e.symm _ _ (fun _ ↦ rfl)).symm

/-- The union of common families at fixed closing matrices represents every
weighted sum of their polynomial evaluations. The union is chosen before
the exterior operators, polynomial and weights. Auxiliary to ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333. -/
private theorem exists_common_physical_closing_nodes_family_fin
    {alpha : Type*} [Fintype alpha] {L q ell a b B k : ℕ}
    (WL WR : Fin (2 * ell) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, Entropy.IsSupportedOn (WL r)
      (interval L (a + r.val) (a + r.val + 2)))
    (hright : ∀ r, Entropy.IsSupportedOn (WR r)
      (interval L (b + r.val) (b + r.val + 2)))
    (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ L - 1)
    (hell : 1 ≤ ell) (hq : 2 ≤ q) (hk : 1 ≤ k)
    (Acore : Fin ((b + 1) - (a + 2 * ell)) → MPOTensor q B)
    (C : alpha → Matrix (Fin B) (Fin B) ℂ) :
    let Ksites := interval L (a + 2 * ell) (b + 1)
    let eK := intervalShiftOrderIso
      (show a + 2 * ell ≤ b + 1 by omega) (show b + 1 ≤ L by omega)
    let Pmid := fun r ↦ QuantumCircuit.embedOp (Subtype.val : Ksites → Fin L)
      (QuantumCircuit.embedOp eK (MPOTensor.traceChainOperator Acore (C r)))
    let J := interval L (a + ell) (b + ell + 1)
    let eJ := intervalShiftOrderIso
      (show a + ell ≤ b + ell + 1 by omega) (show b + ell + 1 ≤ L by omega)
    let D := (q * k) ^ (18 * ell + 2 * (k / ell))
    let beta := fun _ : Fin L ↦ Fin q
    let tau := (FiniteProduct.splitEquiv beta J).trans (Equiv.prodComm _ _)
    let H := fun PL PR r ↦ ∑ i, Sum.elim (Sum.elim WL WR) ![PL, Pmid r, PR] i
    ∃ (N : ℕ) (W : Fin N → Matrix (J → Fin q) (J → Fin q) ℂ),
      N ≤ Fintype.card alpha * D ^ 2 ∧
      (∀ i, IsOpenMPS ((b + ell + 1) - (a + ell)) (q * q)
        ((max 1 B) ^ (2 * k)) (fun w ↦ W i
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).1)
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).2))) ∧
      ∀ PL PR, Entropy.IsSupportedOn PL (interval L 0 (a + 1)) →
        Entropy.IsSupportedOn PR (interval L (b + 2 * ell) L) →
        ∀ Q : Polynomial ℂ, Q.natDegree ≤ k → ∀ c : alpha → ℂ,
        ∃ M : Fin N → Matrix (FiniteProduct.Configuration beta Jᶜ)
            (FiniteProduct.Configuration beta Jᶜ) ℂ,
          (∑ r, c r • Polynomial.aeval (H PL PR r) Q) =
            (∑ i, M i ⊗ₖ W i).submatrix tau tau := by
  classical
  intro Ksites eK Pmid J eJ D beta tau H
  have hnodes (r : alpha) := exists_common_physical_aeval_mpo_family_fin
    (L := L) (q := q) (ell := ell) (a := a) (b := b) (B := B) (k := k)
    WL WR hleft hright hab hb hell hq hk Acore (C r)
  choose n Wnode hn hbond _hTrace hnodePoly using hnodes
  obtain ⟨N, W, hN, hmember, hflatten⟩ :=
    exists_flattened_kronecker_family (mu := FiniteProduct.Configuration beta Jᶜ) n Wnode
  have hcount : N ≤ Fintype.card alpha * D ^ 2 := by
    calc
      N = ∑ r, n r := hN
      _ ≤ ∑ _r : alpha, D ^ 2 := Finset.sum_le_sum fun r _ ↦ hn r
      _ = _ := by simp
  have hW : ∀ i, IsOpenMPS ((b + ell + 1) - (a + ell)) (q * q)
      ((max 1 B) ^ (2 * k)) (fun w ↦ W i
        (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).1)
        (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).2)) := by
    intro i
    obtain ⟨r, j, hij⟩ := hmember i
    rw [hij]
    exact hbond r j
  refine ⟨N, W, hcount, hW, ?_⟩
  intro PL PR hPL hPR Q hQ c
  have hnode (r : alpha) :
      ∃ M : Fin (n r) → Matrix (FiniteProduct.Configuration beta Jᶜ)
          (FiniteProduct.Configuration beta Jᶜ) ℂ,
        Polynomial.aeval (H PL PR r) Q =
          (∑ i, M i ⊗ₖ Wnode r i).submatrix tau tau :=
    hnodePoly r PL PR hPL hPR Q hQ
  choose Mnode hMnode using hnode
  obtain ⟨M, hM⟩ := hflatten Mnode c
  refine ⟨M, ?_⟩
  calc
    (∑ r, c r • Polynomial.aeval (H PL PR r) Q) =
        ∑ r, c r • (∑ i, Mnode r i ⊗ₖ Wnode r i).submatrix tau tau := by
      apply Finset.sum_congr rfl
      intro r _
      exact congrArg (fun X ↦ c r • X) (hMnode r)
    _ = (∑ r, c r • (∑ i, Mnode r i ⊗ₖ Wnode r i)).submatrix tau tau := by
      ext sigma rho
      simp only [Matrix.sum_apply, Matrix.submatrix_apply, Matrix.smul_apply]
    _ = _ := congrArg (fun X ↦ X.submatrix tau tau) hM

/-- One actual physical family represents every polynomial in the closing
parameter, before that parameter, the exterior terms and the polynomial are
chosen. The individual open bond is unchanged by taking the finite node union.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333,
and the soft construction at lines 1373–1420. No spectral or running-time
conclusion is asserted. -/
theorem exists_common_physical_polynomial_closing_family_fin
    {L q ell a b B k m : ℕ}
    (WL WR : Fin (2 * ell) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, Entropy.IsSupportedOn (WL r)
      (interval L (a + r.val) (a + r.val + 2)))
    (hright : ∀ r, Entropy.IsSupportedOn (WR r)
      (interval L (b + r.val) (b + r.val + 2)))
    (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ L - 1)
    (hell : 1 ≤ ell) (hq : 2 ≤ q) (hk : 1 ≤ k)
    (Acore : Fin ((b + 1) - (a + 2 * ell)) → MPOTensor q B)
    (C : Fin (m + 1) → Matrix (Fin B) (Fin B) ℂ) :
    let Ksites := interval L (a + 2 * ell) (b + 1)
    let eK := intervalShiftOrderIso
      (show a + 2 * ell ≤ b + 1 by omega) (show b + 1 ≤ L by omega)
    let Cpoly := fun z : ℂ ↦ ∑ a, z ^ a.val • C a
    let Pmid := fun z ↦ QuantumCircuit.embedOp (Subtype.val : Ksites → Fin L)
      (QuantumCircuit.embedOp eK (MPOTensor.traceChainOperator Acore (Cpoly z)))
    let J := interval L (a + ell) (b + ell + 1)
    let eJ := intervalShiftOrderIso
      (show a + ell ≤ b + ell + 1 by omega) (show b + ell + 1 ≤ L by omega)
    let D := (q * k) ^ (18 * ell + 2 * (k / ell))
    let beta := fun _ : Fin L ↦ Fin q
    let tau := (FiniteProduct.splitEquiv beta J).trans (Equiv.prodComm _ _)
    let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
    let Phi := ((EuclideanSpace.basisFun (FiniteProduct.Configuration beta Jᶜ) ℂ).tensorProduct
      (EuclideanSpace.basisFun (FiniteProduct.Configuration beta J) ℂ)).repr
    let T := U.trans Phi.symm
    let Tm := T.trans (TensorProduct.commIsometry ℂ
      (EuclideanSpace ℂ (FiniteProduct.Configuration beta Jᶜ))
      (EuclideanSpace ℂ (FiniteProduct.Configuration beta J)))
    ∃ (N : ℕ) (W : Fin N → Matrix (J → Fin q) (J → Fin q) ℂ),
      N ≤ (m * k + 1) * D ^ 2 ∧
      (∀ i, IsOpenMPS ((b + ell + 1) - (a + ell)) (q * q)
        ((max 1 B) ^ (2 * k)) (fun w ↦ W i
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).1)
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).2))) ∧
      ∀ (z : ℂ) PL PR, Entropy.IsSupportedOn PL (interval L 0 (a + 1)) →
        Entropy.IsSupportedOn PR (interval L (b + 2 * ell) L) →
        let H := ∑ i, Sum.elim (Sum.elim WL WR) ![PL, Pmid z, PR] i
        ∀ Q : Polynomial ℂ, Q.natDegree ≤ k →
        ∃ M : Fin N → Matrix (FiniteProduct.Configuration beta Jᶜ)
            (FiniteProduct.Configuration beta Jᶜ) ℂ,
          Polynomial.aeval H Q = (∑ i, M i ⊗ₖ W i).submatrix tau tau ∧
          Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
              Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (Polynomial.aeval H Q) ∘L
              Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
            ∑ i, TensorProduct.mapL
              (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := FiniteProduct.Configuration beta J) (W i))
              (Matrix.toEuclideanCLM (𝕜 := ℂ)
                (n := FiniteProduct.Configuration beta Jᶜ) (M i)) := by
  classical
  intro Ksites eK Cpoly Pmid J eJ D beta tau U Phi T Tm
  have hnodes := exists_common_physical_closing_nodes_family_fin
    (L := L) (q := q) (ell := ell) (a := a) (b := b) (B := B) (k := k)
    WL WR hleft hright hab hb hell hq hk Acore
    (fun r : Fin (m * k + 1) ↦ Cpoly (r.val : ℂ))
  obtain ⟨N, W, hN, hW, hdecomp⟩ := hnodes
  have hcount : N ≤ (m * k + 1) * D ^ 2 := by
    simpa only [Fintype.card_fin] using hN
  let Bcoef := fun a : Fin (m + 1) ↦ QuantumCircuit.embedOp
    (Subtype.val : Ksites → Fin L)
    (QuantumCircuit.embedOp eK (MPOTensor.traceChainOperator Acore (C a)))
  have hPmid (z : ℂ) : Pmid z = ∑ a, z ^ a.val • Bcoef a := by
    let placement := (QuantumCircuit.embedOpLinearMap (d := q)
      (Subtype.val : Ksites → Fin L)).comp (QuantumCircuit.embedOpLinearMap (d := q) eK)
    change placement (MPOTensor.traceChainOperator Acore (∑ a, z ^ a.val • C a)) =
      ∑ a, z ^ a.val • placement (MPOTensor.traceChainOperator Acore (C a))
    simp only [MPOTensor.traceChainOperator_sum_smul_closing, map_sum, map_smul]
  let B0 := fun PL PR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ ↦
    (∑ r, WL r) + (∑ r, WR r) + PL + PR
  have hH (z : ℂ) (PL PR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
      (∑ i, Sum.elim (Sum.elim WL WR) ![PL, Pmid z, PR] i) =
        B0 PL PR + ∑ a, z ^ a.val • Bcoef a := by
    simp only [Fintype.sum_sumElim, Fin.sum_univ_three]
    change ((∑ r, WL r) + (∑ r, WR r)) + (PL + Pmid z + PR) = _
    rw [hPmid z]
    dsimp only [B0]
    abel
  refine ⟨N, W, hcount, hW, ?_⟩
  intro z PL PR hPL hPR H Q hQ
  have hinterp := Matrix.aeval_polynomial_parameter_eq_sum_lagrange
    (B0 PL PR) Bcoef Q hQ z
  have hinterp' : Polynomial.aeval H Q =
      ∑ r : Fin (m * k + 1),
        (Polynomial.eval z (Lagrange.basis Finset.univ
          (fun s : Fin (m * k + 1) ↦ (s.val : ℂ)) r)) •
          Polynomial.aeval
            (∑ i, Sum.elim (Sum.elim WL WR) ![PL, Pmid (r.val : ℂ), PR] i) Q := by
    simpa only [← hH] using hinterp
  obtain ⟨M, hnode⟩ := hdecomp PL PR hPL hPR Q hQ
    (fun r ↦ Polynomial.eval z (Lagrange.basis Finset.univ
      (fun s : Fin (m * k + 1) ↦ (s.val : ℂ)) r))
  have hmatrix : Polynomial.aeval H Q = (∑ i, M i ⊗ₖ W i).submatrix tau tau :=
    hinterp'.trans hnode
  exact ⟨M, hmatrix, Matrix.toEuclideanCLM_middleFirst_conjugation_of_kronecker_sum
    tau M W (Polynomial.aeval H Q) hmatrix⟩

end TNLean.MPS.AreaLaw
