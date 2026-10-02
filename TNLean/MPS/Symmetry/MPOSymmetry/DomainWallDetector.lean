/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TruncationCommutator
import TNLean.MPS.Symmetry.MPOSymmetry.DomainWallStringExchange

/-!
# Detecting the anomaly with truncations that act as domain-wall strings

Garre-Rubio and Schuch (arXiv:2405.00439, Section V, `Papers/2405.00439/MPU-DW.tex` lines
2069--2102) detect the anomaly of a `ℤ₂` matrix product unitary symmetry `U` by the expectation
value on a symmetry-broken ground state `|ψ_A⟩` of the commutator of two truncations
`U^{[i₁,j₁]}` and `U^{[i₂,j₂]}`, `i₂ < i₁ < j₁ < j₂`:

`⟨ψ_A| (U^{[i₂,j₂]})† (U^{[i₁,j₁]})† U^{[i₂,j₂]} U^{[i₁,j₁]} |ψ_A⟩ = ω`  (`detecZ2`).

The argument of the source treats the truncation `U^{[i,j]}` as the domain-wall string
`O^{[i,j]}` of Section III.E on the states it meets: on `|ψ_A⟩` it creates the walls of
`|ψ(A-B-A)⟩`, and inside the `B` region created by the other truncation it creates the walls
of `|ψ(B-A-B)⟩`, which must be the images under `U` of the walls it creates on `|ψ_A⟩`. This
file proves the detection for unitary operators whose two products on `|ψ_A⟩` agree with the
products of the domain-wall strings, from the exchange relation `signphysop` of the strings
and the commutator lemma `Matrix.star_dotProduct_groupCommutator_mulVec`.

**Scope restriction (truncations acting as domain-wall strings):** the detection is proved for
unitaries `U₁`, `U₂` with `U₂ U₁ |ψ_A⟩ = O^{[i₂,j₂]} O^{[i₁,j₁]} |ψ_A⟩` and
`U₁ U₂ |ψ_A⟩ = O^{[i₁,j₁]} O^{[i₂,j₂]} |ψ_A⟩`, not for the circuit truncations of the source.
For an arbitrary circuit truncation the printed claim fails: two truncations of the on-site
symmetry `X^{⊗N}` dressed by `Z` at one endpoint give `-1` although the anomaly is trivial
(`Matrix.groupCommutator_dressed_onSiteTruncation_pauliX`). Documented in
`docs/paper-gaps/gs24_truncation_detector_endpoint_dependence.tex`.

## Main results

* `MPOTensor.GroupFamily.BlockActionData.star_dotProduct_groupCommutator_mulVec_mpv_of_wallString`:
  the commutator of two unitaries acting as nested domain-wall strings on `|ψ_A⟩` has
  expectation value `c_{AB} c_{BA} ⟨ψ_A|ψ_A⟩`.
* `MPOTensor.GroupFamily.BlockActionData.star_dotProduct_groupCommutator_mulVec_mpv_eq_omega`:
  for an involution of a normal representation, this is `ω(g,g,g) ω(g,1,g) ⟨ψ_A|ψ_A⟩`.

## References
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- Garre-Rubio, Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*
-/

open scoped Matrix

namespace MPOTensor

variable {d : ℕ}

namespace GroupFamily

variable {G : Type} {X : Type*} [Group G] {F : GroupFamily G d} [MulAction G X] {D : X → ℕ}
  {A : (x : X) → MPSTensor d (D x)}

namespace BlockActionData

variable (ad : BlockActionData F A) {g : G} {x y : X} {hxy : g • x = y} {hyx : g • y = x}
  {Âx : Fin d → Matrix (Fin (D x)) (Fin (D x)) ℂ} {Ây : Fin d → Matrix (Fin (D y)) (Fin (D y)) ℂ}
  {eAB : Fin d → Matrix (Fin (D x)) (Fin (D y)) ℂ} {eBA : Fin d → Matrix (Fin (D y)) (Fin (D x)) ℂ}

/-- **The detector of truncations acting as domain-wall strings** (arXiv:2405.00439, `detecZ2`,
`Papers/2405.00439/MPU-DW.tex` lines 2077--2102, under the scope restriction of the module
docstring). Let `O₁ = O^{[i₁,j₁]}` and `O₂ = O^{[i₂,j₂]}` be domain-wall strings on sites
`i₂ < i₁ < j₁ < j₂`, here at `u + 1 + u'`, `u + 1 + u' + 1 + v` and `u`,
`u + 1 + u' + 1 + v + 1 + w'`, whose three inner regions are longer than a fixed buffer. If
`U₁` and `U₂` are unitary with `U₂ U₁ |ψ_A⟩ = O₂ O₁ |ψ_A⟩` and
`U₁ U₂ |ψ_A⟩ = O₁ O₂ |ψ_A⟩`, then

`⟨ψ_A| U₂† U₁† U₂ U₁ |ψ_A⟩ = c_{AB} c_{BA} ⟨ψ_A|ψ_A⟩`.

The strings satisfy `O₂ O₁ |ψ_A⟩ = c_{AB} c_{BA} O₁ O₂ |ψ_A⟩`
(`wallString_mul_wallString_mulVec_mpv`), so `U₂ U₁ |ψ_A⟩ = c_{AB} c_{BA} U₁ U₂ |ψ_A⟩`, and the
commutator of two unitaries then acts on `|ψ_A⟩` by this phase
(`Matrix.star_dotProduct_groupCommutator_mulVec`). -/
theorem star_dotProduct_groupCommutator_mulVec_mpv_of_wallString
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x)))
    (hÂ : IsSeparatingLeftInverse Âx Ây (A x) (A y)) {cAB cBA : ℂ}
    (hAB : ad.IsDomainWallAction g hxy hyx eAB eBA cAB)
    (hBA : ad.IsDomainWallAction g hyx hxy eBA eAB cBA) :
    ∃ N : ℕ, ∀ (u u' v w' w L : ℕ) (h₁ : u + 1 + u' + 1 + v + 1 + (w' + 1 + w) = L)
      (h₂ : u + 1 + (u' + 1 + v + 1 + w') + 1 + w = L), N ≤ u' → N ≤ v → N ≤ w' →
      ∀ U₁ U₂ : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ, U₁ᴴ * U₁ = 1 → U₂ᴴ * U₂ = 1 →
      (U₂ * U₁) *ᵥ (fun σ ↦ MPSTensor.mpv (A x) σ) =
          (ad.wallString g hxy hyx Âx Ây eAB eBA u (u' + 1 + v + 1 + w') w h₂ *
            ad.wallString g hxy hyx Âx Ây eAB eBA (u + 1 + u') v (w' + 1 + w) h₁) *ᵥ
            (fun σ ↦ MPSTensor.mpv (A x) σ) →
      (U₁ * U₂) *ᵥ (fun σ ↦ MPSTensor.mpv (A x) σ) =
          (ad.wallString g hxy hyx Âx Ây eAB eBA (u + 1 + u') v (w' + 1 + w) h₁ *
            ad.wallString g hxy hyx Âx Ây eAB eBA u (u' + 1 + v + 1 + w') w h₂) *ᵥ
            (fun σ ↦ MPSTensor.mpv (A x) σ) →
      star (fun σ ↦ MPSTensor.mpv (A x) σ) ⬝ᵥ
          (Matrix.groupCommutator U₁ U₂ *ᵥ (fun σ ↦ MPSTensor.mpv (A x) σ)) =
        (cAB * cBA) *
          (star (fun σ : Fin L → Fin d ↦ MPSTensor.mpv (A x) σ) ⬝ᵥ
            (fun σ : Fin L → Fin d ↦ MPSTensor.mpv (A x) σ)) := by
  obtain ⟨N, hN⟩ := ad.wallString_mul_wallString_mulVec_mpv hperm hÂ hAB hBA
  refine ⟨N, fun u u' v w' w L h₁ h₂ hu' hv hw' U₁ U₂ hU₁ hU₂ h₂₁ h₁₂ ↦ ?_⟩
  refine Matrix.star_dotProduct_groupCommutator_mulVec hU₁ hU₂ ?_
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h₂₁, h₁₂, hN u u' v w' w L h₁ h₂ hu' hv hw']

/-- **The detector of truncations acting as domain-wall strings measures the anomaly**
(arXiv:2405.00439, `detecZ2`, `Papers/2405.00439/MPU-DW.tex` lines 2077--2102, with `eq:CC-LL`,
lines 1020--1121, under the scope restriction of the module docstring): for an involution `g`
of a normal representation exchanging the blocks `x` and `y`, and unitaries `U₁`, `U₂` whose two
products on `|ψ_A⟩` agree with those of the nested domain-wall strings,

`⟨ψ_A| U₂† U₁† U₂ U₁ |ψ_A⟩ = ω(g,g,g) ω(g,1,g) ⟨ψ_A|ψ_A⟩`.

For fusion tensors trivial on the identity, as in the source, `ω(g,1,g) = 1`. -/
theorem star_dotProduct_groupCommutator_mulVec_mpv_eq_omega {fd : FusionData F}
    (hF : F.IsNormalRepresentation) (hA : ∀ x, Kraus.IsNormal (A x)) (hD : ∀ x, 0 < D x)
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x))) (hg : g * g = 1)
    (hÂ : IsSeparatingLeftInverse Âx Ây (A x) (A y)) {cAB cBA : ℂ}
    (hAB : ad.IsDomainWallAction g hxy hyx eAB eBA cAB)
    (hBA : ad.IsDomainWallAction g hyx hxy eBA eAB cBA) :
    ∃ N : ℕ, ∀ (u u' v w' w L : ℕ) (h₁ : u + 1 + u' + 1 + v + 1 + (w' + 1 + w) = L)
      (h₂ : u + 1 + (u' + 1 + v + 1 + w') + 1 + w = L), N ≤ u' → N ≤ v → N ≤ w' →
      ∀ U₁ U₂ : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ, U₁ᴴ * U₁ = 1 → U₂ᴴ * U₂ = 1 →
      (U₂ * U₁) *ᵥ (fun σ ↦ MPSTensor.mpv (A x) σ) =
          (ad.wallString g hxy hyx Âx Ây eAB eBA u (u' + 1 + v + 1 + w') w h₂ *
            ad.wallString g hxy hyx Âx Ây eAB eBA (u + 1 + u') v (w' + 1 + w) h₁) *ᵥ
            (fun σ ↦ MPSTensor.mpv (A x) σ) →
      (U₁ * U₂) *ᵥ (fun σ ↦ MPSTensor.mpv (A x) σ) =
          (ad.wallString g hxy hyx Âx Ây eAB eBA (u + 1 + u') v (w' + 1 + w) h₁ *
            ad.wallString g hxy hyx Âx Ây eAB eBA u (u' + 1 + v + 1 + w') w h₂) *ᵥ
            (fun σ ↦ MPSTensor.mpv (A x) σ) →
      star (fun σ ↦ MPSTensor.mpv (A x) σ) ⬝ᵥ
          (Matrix.groupCommutator U₁ U₂ *ᵥ (fun σ ↦ MPSTensor.mpv (A x) σ)) =
        ((fd.omega g g g * fd.omega g 1 g : ℂˣ) : ℂ) *
          (star (fun σ : Fin L → Fin d ↦ MPSTensor.mpv (A x) σ) ⬝ᵥ
            (fun σ : Fin L → Fin d ↦ MPSTensor.mpv (A x) σ)) := by
  rw [← IsDomainWallAction.mul_eq_omega_of_mul_self_eq_one (fd := fd) hF hA hD hperm hg hAB hBA]
  exact ad.star_dotProduct_groupCommutator_mulVec_mpv_of_wallString hperm hÂ hAB hBA

end BlockActionData

end GroupFamily

end MPOTensor
