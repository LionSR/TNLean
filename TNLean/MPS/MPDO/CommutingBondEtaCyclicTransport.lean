/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CommutingBondEtaCyclicCore
import TNLean.MPS.MPDO.PhysicalSupportProductTransport

/-!
# Cyclic eta decomposition for a commuting bond

This file combines the dependency-neutral cyclic transport with the physical-support
product transport to obtain the finite-chain decomposition of eta-local structure data.
-/

open scoped BigOperators ComplexOrder Kronecker Matrix

namespace MPOTensor

variable {d : ℕ}

/-- **Scaled finite-chain cyclic neighboring-operator identity.** A positive
translation-invariant commuting bond admits one chain-independent unitary,
one collection of sector dimensions, and one positive neighboring family such
that, at every length at least two, conjugation by the sitewise tensor power
and cyclic regrouping give the direct sum of cyclic neighboring products, up
to the positive realization scalar.

**Local fix (proportionality scalar):** The converse argument in
arXiv:1606.00608, lines 1603--1605, passes from a matrix proportional to a
commuting-bond product to the coefficient-free equation sigmaNK2 without
retaining the proportionality scalar. The statement below preserves the
positive scalar at each chain length. This discrepancy is recorded in
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`.

This result uses neither zero correlation length, rank-one trace factorization,
a Markov decomposition, nor saturation of the area law, and it does not prove
Proposition `4to2`.

Source: arXiv:1606.00608, Appendix C.2, equation expression, lines 1571--1576,
and equation sigmaNK2 as invoked at lines 1603--1605.
Documented in `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem EtaLocalStructureData.exists_positive_cyclic_eta_block_decomposition
    {D : ℕ} {M : MPOTensor d D} (data : EtaLocalStructureData M) :
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
          letI : NeZero N := ⟨by omega⟩
          ∃ c : ℝ, 0 < c ∧
          Matrix.reindex
              (Matrix.etaCyclicEdgeEquiv dl dr e)
              (Matrix.etaCyclicEdgeEquiv dl dr e)
              (star (sitewisePhysicalMatrix U N) * mpo M N *
                sitewisePhysicalMatrix U N) =
            (c : ℂ) • Matrix.blockDiagonal' fun k : Fin N → Fin K ↦
              fun x y ↦ ∏ n : Fin N, η (k n) (k (n + 1)) (x n) (y n) := by
  classical
  obtain ⟨K, dl, dr, e, U, η, hU, hdl, hdr, hη, hB⟩ :=
    data.exists_positive_eta_pairBond_decomposition
  refine ⟨K, dl, dr, e, U, η, hU, hdl, hdr, hη, ?_⟩
  intro N hN
  letI : NeZero N := ⟨by omega⟩
  obtain ⟨c, hc, hreal⟩ := data.exists_positive_scalar_mpo_eq_product N hN
  refine ⟨c, hc, ?_⟩
  have hUco : U * Uᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp hU)
  have hUiso : Uᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp hU)
  have hV : (Uᴴ)ᴴ * Uᴴ = 1 := by
    simpa only [Matrix.conjTranspose_conjTranspose] using hUco
  have hV' : Uᴴ * (Uᴴ)ᴴ = 1 := by
    simpa only [Matrix.conjTranspose_conjTranspose] using hUiso
  change mpo M N = (c : ℂ) •
    (List.ofFn fun i : Fin N ↦
      embedLocalOperator 2 N hN i data.bondData.bond).prod at hreal
  have hconj :
      singleKrausMap (sitewisePhysicalMatrix Uᴴ N) (mpo M N) =
        (c : ℂ) • (List.ofFn fun i : Fin N ↦
          embedLocalOperator 2 N hN i
            (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
              (finTwoArrowEquiv (Fin d)).symm
              (star (U ⊗ₖ U) * data.pairBond * (U ⊗ₖ U)))).prod := by
    rw [hreal, (singleKrausMap (sitewisePhysicalMatrix Uᴴ N)).map_smul,
      singleKrausMap_bondProduct_of_unitary Uᴴ hV hV' hN]
    congr 1
    apply congrArg List.prod
    apply congrArg List.ofFn
    funext i
    rw [singleKrausMap_sitewise_conjTranspose_two_eq]
    rfl
  have hglobal :
      singleKrausMap (sitewisePhysicalMatrix Uᴴ N) (mpo M N) =
        star (sitewisePhysicalMatrix U N) * mpo M N *
          sitewisePhysicalMatrix U N := by
    simp only [singleKrausMap_apply, ← sitewisePhysicalMatrix_conjTranspose,
      Matrix.conjTranspose_conjTranspose, Matrix.star_eq_conjTranspose]
  have hcyclic := reindex_product_embedLocalOperator_of_etaPair_decomposition
    hN dl dr e η (star (U ⊗ₖ U) * data.pairBond * (U ⊗ₖ U)) hB
  calc
    Matrix.reindex (Matrix.etaCyclicEdgeEquiv dl dr e)
        (Matrix.etaCyclicEdgeEquiv dl dr e)
        (star (sitewisePhysicalMatrix U N) * mpo M N *
          sitewisePhysicalMatrix U N) =
      Matrix.reindex (Matrix.etaCyclicEdgeEquiv dl dr e)
        (Matrix.etaCyclicEdgeEquiv dl dr e)
        (singleKrausMap (sitewisePhysicalMatrix Uᴴ N) (mpo M N)) :=
          congrArg (Matrix.reindex (Matrix.etaCyclicEdgeEquiv dl dr e)
            (Matrix.etaCyclicEdgeEquiv dl dr e)) hglobal.symm
    _ = Matrix.reindex (Matrix.etaCyclicEdgeEquiv dl dr e)
        (Matrix.etaCyclicEdgeEquiv dl dr e)
        ((c : ℂ) • (List.ofFn fun i : Fin N ↦
          embedLocalOperator 2 N hN i
            (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
              (finTwoArrowEquiv (Fin d)).symm
              (star (U ⊗ₖ U) * data.pairBond * (U ⊗ₖ U)))).prod) :=
          congrArg (Matrix.reindex (Matrix.etaCyclicEdgeEquiv dl dr e)
            (Matrix.etaCyclicEdgeEquiv dl dr e)) hconj
    _ = (c : ℂ) • Matrix.reindex (Matrix.etaCyclicEdgeEquiv dl dr e)
        (Matrix.etaCyclicEdgeEquiv dl dr e)
        (List.ofFn fun i : Fin N ↦
          embedLocalOperator 2 N hN i
            (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
              (finTwoArrowEquiv (Fin d)).symm
              (star (U ⊗ₖ U) * data.pairBond * (U ⊗ₖ U)))).prod := by
          rfl
    _ = (c : ℂ) • Matrix.blockDiagonal' fun k : Fin N → Fin K ↦
        fun x y ↦ ∏ n : Fin N, η (k n) (k (n + 1)) (x n) (y n) :=
          congrArg ((c : ℂ) • ·) hcyclic

end MPOTensor
