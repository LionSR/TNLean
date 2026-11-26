/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.MPO.PhysicalPolynomialTensorFamily
import QICLean.Spectral.LowEnergy.ChebyshevViability

/-!
# Physical polynomial families and Chebyshev viability

The common physical polynomial family gives an enlargement of every
viable subspace of the retained interval. For the actual conjugated
Hamiltonian, closed spectral separation and an upper spectral bound yield
the Chebyshev contraction estimate. The dimension increases by at most
the squared family-count parameter. The chosen family precedes every
supported exterior operator and every spectral choice.

The open bond estimate remains the coarse bound inherited from the
polynomial family. This result does not assert the source-sharp bond
estimate or the running-time assertion of Proposition 5.7.

## References

Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333,
Definition `def:Cheby-AGSP`, lines 789–803, Theorem `thm:Cheby-AGSP`,
lines 809–853, and Lemma `l:er`, lines 597–622.
-/

open ManyBody (interval)

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
