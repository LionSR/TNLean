/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.Isometry.UnitaryMulVecInner
import TNLean.MPS.MPU.DomainWall.FiniteGroupDetectorTransport
import TNLean.MPS.FundamentalTheorem.OperatorGroup.DomainWallStringGroup

/-!
# Conditional detection of the domain-wall cyclic invariant

The source is arXiv:2405.00439, Section V, `detectG`,
`Papers/2405.00439/MPU-DW.tex` lines 2108–2117, together with `Intequiv`,
lines 2013–2023. The actual domain-wall family already satisfies
`IsDomainWallFamily.prod_eq_inv_cyclicInvariant`; no identification of its
B-coefficients with an arbitrary truncation is implicit in that result.

**Scope restriction (comparisons on intermediate excitations):** the full
detector results below require each forward action to have the specified
domain-wall coefficient. Undo steps either retain explicit phases or are
deduced from unitary forward comparisons on the reference vectors. The
truncations and reference vectors are not constructed by these results.

The final result supplies the first crossed comparison from the source's
canonical strings, conditional on equality of the truncation and canonical
actions on the ground state and its first excitation. It derives the actual
coefficient `B g (g • x) x`, with the orientation needed by `Intequiv`.
It does not establish comparisons for all later excitations or undo steps.
The unrestricted detection assertion remains open; see
https://sirui-lu.com/TNLean/paper-gaps/gs24_truncation_detector_endpoint_dependence.pdf.

## Canonical strings crossing one wall with arbitrary exterior chains

Source: arXiv:2405.00439, `eq:localcdefG` and `detectG`,
`Papers/2405.00439/MPU-DW.tex` lines 1896–1921 and 2108–2117.
A canonical string crossing one wall from `y` to `z` acquires the actual
coefficient `B g y z`. The exterior chains below are arbitrary rectangular
matrix-valued functions, so they can contain spectator walls and their
surrounding blocks. Only the interior wall and its two buffered regions are
acted on. This supplies a local contraction for every wall type, rather
than only for the first two-wall excitation.

**Scope restriction (canonical strings):** this result is for the canonical
string with separating left inverses and the nonzero wall family's blocked
local action. It does not identify that string's action with the action of
an arbitrary retained-circuit interval, nor construct the complete detector
sequence or calibrate its undo phases. The unrestricted `detectG` remains
open; see
https://sirui-lu.com/TNLean/paper-gaps/gs24_truncation_detector_endpoint_dependence.pdf.
-/

section

open Matrix
open scoped Matrix

namespace MPOTensor.GroupFamily.BlockActionData

variable {d : ℕ} {G : Type} {X : Type*} [Group G] {F : GroupFamily G d}
  [MulAction G X] {D : X → ℕ} {A : (x : X) → MPSTensor d (D x)}
  {ad : BlockActionData F A}
  {e : (y z : X) → Fin d → Matrix (Fin (D y)) (Fin (D z)) ℂ}
  {B : G → X → X → ℂ}

section Transport

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Under individual comparisons with the actual domain-wall B-coefficients,
the detector measures the inverse cyclic invariant times all undo phases.
This is a conditional form of arXiv:2405.00439, `detectG` and `Intequiv`,
lines 2013–2023 and 2108–2117, with every extra comparison explicit. -/
theorem detectorTransportWord_mulVec_eq_inv_cyclicInvariant_of_phased_states
    (fd : FusionData F) (hB : ad.IsDomainWallFamily e B)
    (hF : F.IsNormalRepresentation) (hA : ∀ x, Kraus.IsNormal (A x)) (hD : ∀ x, 0 < D x)
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x)))
    {g : G} {m : ℕ} (hg : g ^ m = 1) (x : X)
    (T U : ℕ → Matrix ι ι ℂ) (v w : ℕ → ι → ℂ) (q : ℕ → ℂ) (ψ : ι → ℂ)
    (hstart : T 0 *ᵥ ψ = v 0)
    (hforward : ∀ r < m,
      T (r + 1) *ᵥ v r = B g (g ^ r • g • x) (g ^ r • x) • v (r + 1))
    (hjoin : w 0 = v m)
    (hundo : ∀ r < m + 1, (U r)ᴴ *ᵥ w r = q r • w (r + 1))
    (hfinish : w (m + 1) = ψ) :
    FiniteGroupDetector.detectorTransportWord T U m *ᵥ ψ =
      ((((ScalarThreeCochain.cyclicInvariant fd.omega g m)⁻¹ : ℂˣ) : ℂ) *
        ((List.range (m + 1)).map q).prod) • ψ := by
  have hprod : ((List.range m).map fun r ↦ B g (g ^ r • g • x) (g ^ r • x)).prod =
      (((ScalarThreeCochain.cyclicInvariant fd.omega g m)⁻¹ : ℂˣ) : ℂ) := by
    rw [← List.prod_toFinset _ (List.nodup_range : (List.range m).Nodup)]
    have hrange : (List.range m).toFinset = Finset.range m := by
      ext k
      simp
    rw [hrange]
    exact hB.prod_eq_inv_cyclicInvariant fd hF hA hD hperm hg x
  rw [FiniteGroupDetector.detectorTransportWord_mulVec_of_phased_intermediate_states
    T U v w _ q m ψ hstart hforward hjoin hundo hfinish, hprod]

/-- A unitary undo interval is determined on the reference excitation by its
forward action. Under these phase-free undo comparisons and the individual
B-coefficient comparisons, the detector acts by the inverse cyclic invariant.
Project conditional form of arXiv:2405.00439, `detectG`, lines 2108–2117. -/
theorem detectorTransportWord_mulVec_eq_inv_cyclicInvariant_of_intermediate_states
    (fd : FusionData F) (hB : ad.IsDomainWallFamily e B)
    (hF : F.IsNormalRepresentation) (hA : ∀ x, Kraus.IsNormal (A x)) (hD : ∀ x, 0 < D x)
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x)))
    {g : G} {m : ℕ} (hg : g ^ m = 1) (x : X)
    (T U : ℕ → Matrix ι ι ℂ) (v w : ℕ → ι → ℂ) (ψ : ι → ℂ)
    (hstart : T 0 *ᵥ ψ = v 0)
    (hforward : ∀ r < m,
      T (r + 1) *ᵥ v r = B g (g ^ r • g • x) (g ^ r • x) • v (r + 1))
    (hjoin : w 0 = v m) (hunitary : ∀ r < m + 1, U r ∈ unitaryGroup ι ℂ)
    (hundo : ∀ r < m + 1, U r *ᵥ w (r + 1) = w r)
    (hfinish : w (m + 1) = ψ) :
    FiniteGroupDetector.detectorTransportWord T U m *ᵥ ψ =
      (((ScalarThreeCochain.cyclicInvariant fd.omega g m)⁻¹ : ℂˣ) : ℂ) • ψ := by
  simpa using detectorTransportWord_mulVec_eq_inv_cyclicInvariant_of_phased_states
    fd hB hF hA hD hperm hg x T U v w (fun _ ↦ 1) ψ hstart hforward hjoin
    (fun r hr ↦ by
      simpa using Matrix.conjTranspose_mulVec_eq_of_mulVec_eq (hunitary r hr) (hundo r hr))
    hfinish

/-- The conditional expectation equals the inverse cyclic invariant times
the squared norm of the initial state, hence equals the invariant for a
normalized state. Project conditional form of arXiv:2405.00439, `detectG`,
lines 2108–2117; no whole-detector equality is an input. -/
theorem star_dotProduct_detectorTransportWord_eq_inv_cyclicInvariant
    (fd : FusionData F) (hB : ad.IsDomainWallFamily e B)
    (hF : F.IsNormalRepresentation) (hA : ∀ x, Kraus.IsNormal (A x)) (hD : ∀ x, 0 < D x)
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x)))
    {g : G} {m : ℕ} (hg : g ^ m = 1) (x : X)
    (T U : ℕ → Matrix ι ι ℂ) (v w : ℕ → ι → ℂ) (ψ : ι → ℂ)
    (hstart : T 0 *ᵥ ψ = v 0)
    (hforward : ∀ r < m,
      T (r + 1) *ᵥ v r = B g (g ^ r • g • x) (g ^ r • x) • v (r + 1))
    (hjoin : w 0 = v m) (hunitary : ∀ r < m + 1, U r ∈ unitaryGroup ι ℂ)
    (hundo : ∀ r < m + 1, U r *ᵥ w (r + 1) = w r)
    (hfinish : w (m + 1) = ψ) :
    star ψ ⬝ᵥ (FiniteGroupDetector.detectorTransportWord T U m *ᵥ ψ) =
      (((ScalarThreeCochain.cyclicInvariant fd.omega g m)⁻¹ : ℂˣ) : ℂ) *
        (star ψ ⬝ᵥ ψ) := by
  rw [detectorTransportWord_mulVec_eq_inv_cyclicInvariant_of_intermediate_states
    fd hB hF hA hD hperm hg x T U v w ψ hstart hforward hjoin hunitary hundo hfinish,
    dotProduct_smul, smul_eq_mul]

end Transport

section CanonicalComparison

variable [Fintype X] (ad : BlockActionData F A) (g : G)
  (Â : (x : X) → Fin d → Matrix (Fin (D x)) (Fin (D x)) ℂ)

/-- The first crossed truncation step has coefficient `B^g_{gx,x}` when the
first interval agrees with the canonical string on the ground state and the
second agrees on the resulting excitation. The coefficient and four-wall
vector follow from the canonical string theorem, rather than being assumed.
This is the first comparison needed by arXiv:2405.00439, `detectG`,
lines 2108–2117, under explicit additional truncation comparisons. -/
theorem interval_mul_interval_mulVec_mpv_cross_of_canonical_comparisons
    (hÂ : IsSeparatingLeftInverseFamily Â A) (hB : ad.IsDomainWallFamily e B) (x : X) :
    ∃ N : ℕ, ∀ (u u' v w' w L : ℕ)
      (h₂ : u + 1 + (u' + 1 + v + 1 + w') + 1 + w = L)
      (h₃ : u + 1 + (u' + 1 + v) + 1 + (w' + 1 + w) = L)
      (h₄ : u + 1 + u' + 1 + (v + 1 + w') + 1 + w = L), N ≤ v → N ≤ w' →
      ∀ T₀ T₁ : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ,
      T₀ *ᵥ (fun σ ↦ MPSTensor.mpv (A x) σ) =
        ad.groupWallString g Â e u (u' + 1 + v) (w' + 1 + w) h₃ *ᵥ
          (fun σ ↦ MPSTensor.mpv (A x) σ) →
      T₁ *ᵥ (ad.groupWallString g Â e u (u' + 1 + v) (w' + 1 + w) h₃ *ᵥ
          (fun σ ↦ MPSTensor.mpv (A x) σ)) =
        ad.groupWallString g Â e (u + 1 + u') (v + 1 + w') w h₄ *ᵥ
          (ad.groupWallString g Â e u (u' + 1 + v) (w' + 1 + w) h₃ *ᵥ
            (fun σ ↦ MPSTensor.mpv (A x) σ)) →
      ∀ p a μ₁ i ν j μ₃ b q,
      ((T₁ * T₀) *ᵥ (fun σ ↦ MPSTensor.mpv (A x) σ))
          (wallConfig h₂ (p, a, wallSplit u' v w' (μ₁, i, ν, j, μ₃), b, q)) =
        B g (g • x) x *
          nestedWallCoeff (A x) (e x (g • x)) (A (g • x)) (e (g • x) (g • g • x))
            (A (g • g • x)) (e (g • g • x) (g • x)) (e (g • x) x)
            p a μ₁ i ν j μ₃ b q := by
  classical
  obtain ⟨N, hN⟩ := ad.groupWallString_cross_mulVec_mpv_apply hÂ hB x
  refine ⟨N, fun u u' v w' w L h₂ h₃ h₄ hv hw' T₀ T₁ h₀ h₁ p a μ₁ i ν j μ₃ b q ↦ ?_⟩
  rw [← mulVec_mulVec, h₀, h₁, mulVec_mulVec]
  exact hN u u' v w' w L h₂ h₃ h₄ hv hw' p a μ₁ i ν j μ₃ b q

end CanonicalComparison

end MPOTensor.GroupFamily.BlockActionData

end

section

open Matrix
open scoped Matrix

namespace MPOTensor.GroupFamily.BlockActionData

variable {d : ℕ} {G X : Type*} [Group G] {F : GroupFamily G d}
  [MulAction G X] {D : X → ℕ} {A : (x : X) → MPSTensor d (D x)} [Fintype X]
  (ad : BlockActionData F A) (g : G)
  (Â : (x : X) → Fin d → Matrix (Fin (D x)) (Fin (D x)) ℂ)
  {e : (y z : X) → Fin d → Matrix (Fin (D y)) (Fin (D z)) ℂ}
  {B : G → X → X → ℂ}

/-- A canonical string crossing a wall `e y z` in an arbitrary exterior trace
has coefficient `B g y z`. The exterior functions may contain other walls;
no assertion about actual circuit truncations is assumed or concluded.
Project local comparison for arXiv:2405.00439, `eq:localcdefG` and `detectG`,
lines 1896–1921 and 2108–2117. -/
theorem groupWallString_mulVec_trace_wall
    (hÂ : IsSeparatingLeftInverseFamily Â A) (hB : ad.IsDomainWallFamily e B) (y z : X) :
    ∃ N : ℕ, ∀ (k v w n L : ℕ) (h : k + 1 + (v + 1 + w) + 1 + n = L),
      N ≤ v → N ≤ w → ∀ (t : ℕ)
      (P : (Fin k → Fin d) → Matrix (Fin t) (Fin (D y)) ℂ)
      (Q : (Fin n → Fin d) → Matrix (Fin (D z)) (Fin t) ℂ)
      (ψ : (Fin L → Fin d) → ℂ),
      (∀ p a μ b q, ψ (wallConfig h (p, a, μ, b, q)) =
        (P p * A y a * wallChain (A y) (e y z) (A z) μ * A z b * Q q).trace) →
      ∀ p a μ b q,
      (ad.groupWallString g Â e k (v + 1 + w) n h *ᵥ ψ)
          (wallConfig h (p, a, μ, b, q)) =
        B g y z *
          (P p * e y (g • y) a * wallChain (A (g • y)) (e (g • y) (g • z))
            (A (g • z)) μ * e (g • z) z b * Q q).trace := by
  classical
  obtain ⟨N, hN⟩ := (hB g y z).physAct_eq
  refine ⟨N, fun k v w n L h hv hw t P Q ψ hψ p a μ b q ↦ ?_⟩
  rw [groupWallString, stringOperator_mulVec_trace _ _ _ h P (A y)
    (wallChain (A y) (e y z) (A z)) (A z) Q ψ hψ,
    leftAct_groupWallLeftEndpoint ad hÂ, rightAct_groupWallRightEndpoint ad hÂ]
  have hrel := hN v w hv hw μ
  simp only [castIndex_rfl, Matrix.one_mul, Matrix.mul_one] at hrel
  calc
    _ = (P p * e y (g • y) a *
        (ad.V g y * physAct (F.tensor g) (wallChain (A y) (e y z) (A z)) μ * ad.W g z) *
          e (g • z) z b * Q q).trace := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hrel]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

end MPOTensor.GroupFamily.BlockActionData

end
