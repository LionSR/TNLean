/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.TwoWindowPolynomialMPOFamily
import TNLean.MPS.MPDO.TraceChainOperator

/-!
# Identity-cap trace presentations of the common polynomial family

The same middle matrices representing every polynomial have site-dependent
periodic trace presentations. Each virtual dimension is at most `(max 1 B)^k`.
The supplied closing matrix is absorbed at the first site of the nonempty
retained interval, so the physical matrices and their common decomposition are
unchanged. Their general open-boundary estimate remains `(max 1 B)^(2*k)`.

These are supporting consequences for the explicit trace construction in ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333. No identification of
boundary conventions or running-time assertion is made.
-/

open Matrix QuantumCircuit
open scoped BigOperators Kronecker Matrix
open TNLean.Lattice.Sheet

noncomputable section

namespace TNLean.MPS.AreaLaw

/-- The same common family admits identity-cap trace presentations at virtual
dimension at most `(max 1 B)^k`. The target interval is nonempty by the supplied
geometric assumptions, so each actual closing matrix can be absorbed into its
first site without changing the virtual dimension or physical operator.
The count, old open-boundary estimate, capped trace certificate and full
polynomial decomposition are retained. Supporting explicit trace algebra for
ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333; no assertion about
an alternative boundary convention or running time is made. -/
theorem exists_common_physical_aeval_periodic_family_fin
    {L q ell a b B k : ℕ}
    (WL WR : Fin (2 * ell) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, Entropy.IsSupportedOn (WL r)
      (interval L (a + r.val) (a + r.val + 2)))
    (hright : ∀ r, Entropy.IsSupportedOn (WR r)
      (interval L (b + r.val) (b + r.val + 2)))
    (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ L - 1)
    (hell : 1 ≤ ell) (hq : 2 ≤ q) (hk : 1 ≤ k)
    (Acore : Fin ((b + 1) - (a + 2 * ell)) → MPOTensor q B)
    (C0 : Matrix (Fin B) (Fin B) ℂ) :
  let Ksites := interval L (a + 2 * ell) (b + 1)
  let eK := intervalShiftOrderIso
    (show a + 2 * ell ≤ b + 1 by omega) (show b + 1 ≤ L by omega)
  let Mphys := QuantumCircuit.embedOp eK
    (Matrix.of fun σ τ : Fin ((b + 1) - (a + 2 * ell)) → Fin q ↦
      Matrix.trace (C0 * (List.ofFn (fun u ↦ Acore u (σ u) (τ u))).prod))
  let Pmid := QuantumCircuit.embedOp (Subtype.val : Ksites → Fin L) Mphys
  let J := interval L (a + ell) (b + ell + 1)
  let eJ := intervalShiftOrderIso
    (show a + ell ≤ b + ell + 1 by omega)
    (show b + ell + 1 ≤ L by omega)
  let D := (q * k) ^ (18 * ell + 2 * (k / ell))
  ∃ (N : ℕ) (W : Fin N → Matrix (J → Fin q) (J → Fin q) ℂ),
    N ≤ D ^ 2 ∧
      (∀ r, IsOpenMPS ((b + ell + 1) - (a + ell)) (q * q)
        ((max 1 B) ^ (2 * k)) (fun w ↦ W r
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).1)
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).2))) ∧
      (∀ r : Fin N, ∃ Dr : ℕ, Dr ≤ (max 1 B) ^ k ∧
        ∃ Cr : Matrix (Fin Dr) (Fin Dr) ℂ,
        ∃ Ar : Fin ((b + ell + 1) - (a + ell)) → MPOTensor q Dr,
          (W r).submatrix (fun σ z ↦ σ (eJ.symm z))
            (fun σ z ↦ σ (eJ.symm z)) = MPOTensor.traceChainOperator Ar Cr) ∧
      (∀ r : Fin N, ∃ Dr : ℕ, Dr ≤ (max 1 B) ^ k ∧
        ∃ Ar : Fin ((b + ell + 1) - (a + ell)) → MPOTensor q Dr,
          (W r).submatrix (fun σ z ↦ σ (eJ.symm z))
            (fun σ z ↦ σ (eJ.symm z)) =
              MPOTensor.traceChainOperator Ar (1 : Matrix (Fin Dr) (Fin Dr) ℂ)) ∧
      ∀ (PL PR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
        Entropy.IsSupportedOn PL (interval L 0 (a + 1)) →
        Entropy.IsSupportedOn PR (interval L (b + 2 * ell) L) →
        let F : ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) →
            Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
          Sum.elim (Sum.elim WL WR) ![PL, Pmid, PR]
        ∀ P : Polynomial ℂ, P.natDegree ≤ k →
          ∃ M : Fin N → Matrix ((Jᶜ : Finset (Fin L)) → Fin q) ((Jᶜ : Finset (Fin L)) → Fin q) ℂ,
            Polynomial.aeval (∑ a, F a) P =
              (∑ r, M r ⊗ₖ W r).submatrix
                ((FiniteProduct.splitEquiv (fun _ : Fin L ↦ Fin q) J).trans
                  (Equiv.prodComm _ _))
                ((FiniteProduct.splitEquiv (fun _ : Fin L ↦ Fin q) J).trans
                  (Equiv.prodComm _ _)) := by
  obtain ⟨N, W, hN, hW, hTrace, hdecomp⟩ :=
    exists_common_physical_aeval_mpo_family_fin
      WL WR hleft hright hab hb hell hq hk Acore C0
  refine ⟨N, W, hN, hW, hTrace, ?_, hdecomp⟩
  intro r
  obtain ⟨Dr, hDr, Cr, Ar, hAr⟩ := hTrace r
  have hlen : 1 ≤ (b + ell + 1) - (a + ell) := by omega
  obtain ⟨Ar', hAr'⟩ := MPOTensor.exists_traceChainOperator_one hlen Ar Cr
  exact ⟨Dr, hDr, Ar', hAr.trans hAr'⟩

end TNLean.MPS.AreaLaw

end
