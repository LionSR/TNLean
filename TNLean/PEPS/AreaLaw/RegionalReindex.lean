/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.TheoremStatements

/-!
# Regional states under a relabelling of sites

A site bijection preserving a chosen region identifies both regional and
complementary configuration spaces. Its pullback on coefficients transports
the pure vector. Partial trace is covariant under this identification, and
von Neumann entropy is invariant. Neither normalization nor preservation of
lattice adjacency is required for these finite-dimensional identities.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 2 (`sec:prelim`), lines 10–25, finite tensor-factor
conventions. Source revision:
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript and existing QICLean APIs;
no upstream Lean proof text is reused.
-/

open scoped ComplexOrder

namespace TNLean.PEPS.AreaLaw

/-- Configuration transport along a bijection of the physical sites.
Source: area-law `sec:prelim`, lines 10–25, finite tensor factors. -/
def configurationSiteEquiv {Λ Λ' : Finset (ℤ × ℤ)} (q : ℕ)
    (e : Site Λ ≃ Site Λ') : Configuration Λ q ≃ Configuration Λ' q :=
  Equiv.arrowCongr e (Equiv.refl (Fin q))

/-- Configuration transport of a region preserved by a site bijection.
Source: area-law `sec:prelim`, lines 10–25, finite tensor factors. -/
def regionConfigurationEquiv {Λ Λ' : Finset (ℤ × ℤ)} (q : ℕ)
    (A : Finset (Site Λ)) (A' : Finset (Site Λ'))
    (e : Site Λ ≃ Site Λ') (hA : ∀ x, x ∈ A ↔ e x ∈ A') :
    ({x : Site Λ // x ∈ A} → Fin q) ≃ ({x : Site Λ' // x ∈ A'} → Fin q) :=
  Equiv.arrowCongr (e.subtypeEquiv hA) (Equiv.refl (Fin q))

private theorem configurationSplit_pullback {Λ Λ' : Finset (ℤ × ℤ)} (q : ℕ)
    (A : Finset (Site Λ)) (A' : Finset (Site Λ'))
    (e : Site Λ ≃ Site Λ') (hA : ∀ x, x ∈ A ↔ e x ∈ A')
    (σ : Configuration Λ' q) :
    configurationSplit Λ q A (σ ∘ e) =
      ((regionConfigurationEquiv q A A' e hA).symm ((configurationSplit Λ' q A') σ).1,
        (Equiv.arrowCongr (e.subtypeEquiv (fun x ↦ not_congr (hA x)))
          (Equiv.refl (Fin q))).symm ((configurationSplit Λ' q A') σ).2) := by
  rfl

private theorem configurationSplit_symm_pullback {Λ Λ' : Finset (ℤ × ℤ)} (q : ℕ)
    (A : Finset (Site Λ)) (A' : Finset (Site Λ'))
    (e : Site Λ ≃ Site Λ') (hA : ∀ x, x ∈ A ↔ e x ∈ A')
    (x : ({x : Site Λ' // x ∈ A'} → Fin q) ×
      ({x : Site Λ' // x ∉ A'} → Fin q)) :
    (configurationSplit Λ' q A').symm x ∘ e =
      (configurationSplit Λ q A).symm
        (((regionConfigurationEquiv q A A' e hA).prodCongr
          (Equiv.arrowCongr (e.subtypeEquiv (fun x ↦ not_congr (hA x)))
            (Equiv.refl (Fin q)))).symm x) := by
  have h := congrArg (configurationSplit Λ q A).symm
    (configurationSplit_pullback q A A' e hA ((configurationSplit Λ' q A').symm x))
  simpa [Prod.map] using h

/-- The same physical vector written after relabelling its sites.
Source: area-law `sec:prelim`, lines 10–25, finite tensor factors. -/
noncomputable def relabelState {Λ Λ' : Finset (ℤ × ℤ)} (q : ℕ)
    (e : Site Λ ≃ Site Λ') (Ω : StateSpace Λ q) : StateSpace Λ' q :=
  (EuclideanSpace.equiv (Configuration Λ' q) ℂ).symm
    (fun σ ↦ Ω ((configurationSiteEquiv q e).symm σ))

/-- A reduced pure-state matrix is covariant under a site relabelling that
preserves the chosen region. No normalization or lattice-adjacency assumption
is required. Source: area-law `sec:prelim`, lines 10–25, finite tensor-factor
conventions. -/
theorem reducedState_relabel {Λ Λ' : Finset (ℤ × ℤ)} (q : ℕ)
    (A : Finset (Site Λ)) (A' : Finset (Site Λ'))
    (e : Site Λ ≃ Site Λ') (hA : ∀ x, x ∈ A ↔ e x ∈ A')
    (Ω : StateSpace Λ q) :
    reducedState Λ' q (relabelState q e Ω) A' =
      (reducedState Λ q Ω A).submatrix
        (regionConfigurationEquiv q A A' e hA).symm
        (regionConfigurationEquiv q A A' e hA).symm := by
  let eA := regionConfigurationEquiv q A A' e hA
  let eB : ({x : Site Λ // x ∉ A} → Fin q) ≃
      ({x : Site Λ' // x ∉ A'} → Fin q) :=
    Equiv.arrowCongr (e.subtypeEquiv (fun x ↦ not_congr (hA x))) (Equiv.refl (Fin q))
  refine Eq.trans ?_ (Matrix.partialTraceRight_submatrix_prod_equiv eA eB
    ((Matrix.vecMulVec (fun x ↦ Ω x) (star (fun x ↦ Ω x))).submatrix
      (configurationSplit Λ q A).symm (configurationSplit Λ q A).symm))
  unfold reducedState
  congr 1
  ext x y
  change Ω ((configurationSplit Λ' q A').symm x ∘ e) *
      star (Ω ((configurationSplit Λ' q A').symm y ∘ e)) =
    Ω ((configurationSplit Λ q A).symm ((eA.prodCongr eB).symm x)) *
      star (Ω ((configurationSplit Λ q A).symm ((eA.prodCongr eB).symm y)))
  rw [configurationSplit_symm_pullback q A A' e hA x,
    configurationSplit_symm_pullback q A A' e hA y]

/-- Regional entropy is unchanged by relabelling the physical sites and region.
Source: area-law `sec:prelim`, lines 10–25, finite tensor-factor conventions. -/
theorem regionalEntropy_relabel {Λ Λ' : Finset (ℤ × ℤ)} (q : ℕ)
    (A : Finset (Site Λ)) (A' : Finset (Site Λ'))
    (e : Site Λ ≃ Site Λ') (hA : ∀ x, x ∈ A ↔ e x ∈ A')
    (Ω : StateSpace Λ q) :
    regionalEntropy Λ' q (relabelState q e Ω) A' = regionalEntropy Λ q Ω A := by
  simpa only [regionalEntropy, reducedState_relabel q A A' e hA Ω] using
    vonNeumannEntropy_submatrix_equiv (regionConfigurationEquiv q A A' e hA).symm
      (reducedState Λ q Ω A) (reducedState_isHermitian Λ q Ω A)

/-- Relabelling sites preserves the Euclidean norm of a physical vector.
Source: area-law `sec:prelim`, lines 10–25, finite tensor factors. -/
@[simp] theorem norm_relabelState {Λ Λ' : Finset (ℤ × ℤ)} (q : ℕ)
    (e : Site Λ ≃ Site Λ') (Ω : StateSpace Λ q) :
    ‖relabelState q e Ω‖ = ‖Ω‖ :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (configurationSiteEquiv q e)).norm_map Ω

end TNLean.PEPS.AreaLaw
