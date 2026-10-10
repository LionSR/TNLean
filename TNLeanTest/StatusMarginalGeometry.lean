/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.StatusMarginalMoments

/-!
# Actual status containment and zero-band budget regressions

No nonempty family of bands is needed to construct the common budget. Both
physical status kinds use the complement of the far side, and the common
moment estimate accepts negative real parameters without an extra premise.
-/

set_option autoImplicit false

open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan SpectralFilter
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section
namespace TNLeanTest.StatusMarginalGeometry

example {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
    (S : CollarScan V I) {k L : ℕ} (h : History S.K S.m S.M k) (g : Fin S.K)
    (hL : 8 * S.K * S.m ≤ L) :
    (receiving (S.state h g) true)ᶜ ⊆ S.truncationSet L ∧
      (receiving (S.oldChargeState h g) true)ᶜ ⊆ S.truncationSet L :=
  ⟨S.state_far_compl_subset_truncationSet h g hL,
    S.oldChargeState_far_compl_subset_truncationSet h g hL⟩

-- The common budget exists even though there is no band to use for its lower bound.
example {q : ℕ} (hq : 1 ≤ q) (R : ℕ) {Cr : ℝ} (hCr : 0 ≤ Cr) :
    ∃ CB : ℝ, 0 < CB ∧
      ∀ (Λ T : Finset (ℤ × ℤ)) (hT : T.Nonempty)
        (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)),
        S.graph = domainGraph Λ →
        S.depth = (fun x ↦ ambientDepth T hT x.val) →
        (∀ i, S.anchor i ∈ i.val) →
        ∀ L : ℕ, 2 ≤ S.n →
        S.r₀ = ⌈Cr * Real.log (S.n : ℝ) ^ 2⌉₊ →
        S.r₀ ≤ S.D → 1 ≤ S.D → 4 * S.D ≤ S.m → 8 * S.K * S.m ≤ L →
        (∀ d : ℕ, 1 ≤ d → d ≤ L →
          (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
        (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
          ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
        S.K = 0 →
        1 ≤ CB * ((S.n : ℝ) * S.D * Real.log (S.n : ℝ) ^ 12) ∧
          IsEmpty (Fin S.K) := by
  obtain ⟨CB, hCB, hb⟩ := CollarScan.exists_statusMarginal_cutBudget_le_log hq R hCr
  refine ⟨CB, hCB, ?_⟩
  intro Λ T hT S hgraph hdepth hanchor L hn hradius hr hDpos hD hL hrows hclear hzero
  refine ⟨(hb Λ T hT S hgraph hdepth hanchor L hn hradius
    hr hDpos hD hL hrows hclear).1, ?_⟩
  rw [hzero]
  infer_instance

example {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J Δ e B u : ℝ} [NeZero q]
    (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
    (h : LocalHamiltonian Λ q R J) (Ω Ωt : StateSpace Λ q)
    (hgraph : S.graph = domainGraph Λ) (hanchor : ∀ i, S.anchor i ∈ i.val)
    (hΔ : 0 < Δ) (hΩ : ‖Ω‖ = 1) (L : ℕ)
    (hgs : IsGappedGroundState Λ q (∑ i, S.truncatedEnergyTerm h Ω Δ L i) e Ωt
      ((Δ / positiveNormalization 1 (Δ / 2) J) / 2))
    (Q : Finset (Site Λ))
    (hB : cutBudget q S.graph (S.truncationSet L) S.r₀ S.anchor Q ≤ B)
    (hu : |u| ≤ (1 / (32 * Real.sqrt
      (1 + 2 / (Δ / positiveNormalization 1 (Δ / 2) J)))) / Real.sqrt B) :
    Real.log (Entropy.surprisalMoment (reducedState_isHermitian Λ q Ωt Q).eigenvalues (-u)) ≤
      (-u) * regionalEntropy Λ q Ωt Q +
        512 * Real.exp 1 * (2 / (Δ / positiveNormalization 1 (Δ / 2) J)) * B * (-u) ^ 2 :=
  S.log_surprisalMoment_truncated_reducedState_le_common h Ω hgraph hanchor hΔ hΩ L
    hgs Q hB (by simpa only [abs_neg] using hu)

end TNLeanTest.StatusMarginalGeometry
