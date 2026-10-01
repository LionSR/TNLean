/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.DomainWallString

/-!
# Exchange of domain-wall strings and of their left endpoints

Garre-Rubio and Schuch (arXiv:2405.00439, Section III.F, `Papers/2405.00439/MPU-DW.tex` lines
1427--1672) compare products of the domain-wall string operators `O^{[i,j]}` of `eq:DWophys` on
the symmetry-broken ground state `|ψ_A⟩`. Two products are compared in this file.

* **Two strings** (`signphysop`, lines 1667--1672): for strings on sites `i₂ < i₁ < j₁ < j₂`, the
  two orders differ by `c_{AB} c_{BA}`.
* **Two left endpoints** (`eq:z2int`, lines 1427--1659): the source cuts a string in the middle
  into the half-chain operators `O^{[i]}_x`, which carry the left endpoint at `i` and leave the
  bond of the operator string open with the value `x` at a right cut, and proves, for `i > j`,

  `O^{[j]}_x O^{[i]}_y |ψ_A⟩ = c_{AB} O^{[i]}_x O^{[j]}_y |ψ_A⟩`.

  The two sides differ only in which left endpoint carries which label at the right cut, and the
  source notes that the open legs `x`, `y` are left untouched (lines 1453--1458). Here the
  half-chain operators are glued back with the other halves of their strings, as the source
  requires to obtain a state (lines 1501--1505): the labels `x` and `y` are the bonds closed by
  right endpoints at the sites `r₁` and `r₂`, both to the right of `i`, so that the relation reads

  `O^{[j,r₁]} O^{[i,r₂]} |ψ_A⟩ = c_{AB} O^{[i,r₁]} O^{[j,r₂]} |ψ_A⟩`.

  Both orders of the two right endpoints are proved. For `r₂ < r₁` the left side is a nested pair
  whose outer string acts second and acquires `c_{AB} c_{BA}`, and the right side is a crossed
  pair whose second string passes over the wall `e_{BA}` and acquires `c_{BA}`; for `r₁ < r₂`
  the left side is a crossed pair whose second string passes over the wall `e_{AB}` and acquires
  `c_{AB}`, and the right side is a nested pair whose inner string acts second.

All four products are multiples of the periodic state with the domain walls `e_{AB}`, `e_{BA}`,
`e_{AB}`, `e_{BA}` at the four endpoint sites (`MPOTensor.fourWallCoeff`).

**Scope restriction (glued half-chain operators):** `eq:z2int` is proved for the half-chain
operators glued with right endpoints of domain-wall strings,
`wallString_mul_wallString_mulVec_mpv_swap_left_far` and
`wallString_mul_wallString_mulVec_mpv_swap_left_near`, not as an identity of half-chain tensors
with open legs; documented in `docs/paper-gaps/gs24_domain_wall_half_string_gluing.tex`.

**Local fix (nondegenerate domain walls, blocked local action):** the results of this module are
stated for `IsDomainWallAction`, whose walls and phase are nonzero and whose local relation holds
against regions longer than a buffer, so the regions between the walls are long; documented in
`docs/paper-gaps/gs24_domain_wall_nondegenerate.tex`.

## Main definitions

* `MPOTensor.fourWallCoeff`: the coefficient of the periodic state with four domain walls.

## Main results

* `MPOTensor.GroupFamily.BlockActionData.wallString_mul_wallString_mulVec_mpv`: `signphysop`,
  with the phase on the side it is acquired, and
  `...wallString_mul_wallString_mulVec_mpv_of_mpo_mul_self_eq_one` in the printed orientation,
  under `U² = 1`.
* `MPOTensor.GroupFamily.BlockActionData.wallString_mul_wallString_mulVec_mpv_swap_left_far`,
  `MPOTensor.GroupFamily.BlockActionData.wallString_mul_wallString_mulVec_mpv_swap_left_near`:
  `eq:z2int`, for the two orders of the right endpoints.

## References
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- Garre-Rubio, Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d : ℕ}

/-! ### Splitting a chain at four sites -/

/-- Two splits of a chain of `L` sites give the same configuration when their words agree. -/
theorem wallConfig_eq_wallConfig {k l n k' l' n' L : ℕ} (h : k + 1 + l + 1 + n = L)
    (h' : k' + 1 + l' + 1 + n' = L)
    (s : (Fin k → Fin d) × Fin d × (Fin l → Fin d) × Fin d × (Fin n → Fin d))
    (s' : (Fin k' → Fin d) × Fin d × (Fin l' → Fin d) × Fin d × (Fin n' → Fin d))
    (hs : List.ofFn s.1 ++ s.2.1 :: (List.ofFn s.2.2.1 ++ s.2.2.2.1 :: List.ofFn s.2.2.2.2) =
      List.ofFn s'.1 ++ s'.2.1 :: (List.ofFn s'.2.2.1 ++ s'.2.2.2.1 :: List.ofFn s'.2.2.2.2)) :
    wallConfig h s = wallConfig h' s' := by
  apply List.ofFn_injective
  rw [ofFn_wallConfig, ofFn_wallConfig, hs]

/-- The periodic state with two domain walls on a split configuration. -/
theorem twoWallMPV_wallConfig_comp_cast {D D' k l n L : ℕ} (B : MPSTensor d D)
    (e : Fin d → Matrix (Fin D) (Fin D') ℂ) (C : MPSTensor d D')
    (f : Fin d → Matrix (Fin D') (Fin D) ℂ) (h : k + 1 + l + 1 + n = L) (p : Fin k → Fin d)
    (a : Fin d) (μ : Fin l → Fin d) (b : Fin d) (q : Fin n → Fin d) :
    twoWallMPV B e C f (wallConfig h (p, a, μ, b, q) ∘ Fin.cast h) =
      (Kraus.evalWord B (List.ofFn p) * e a * Kraus.evalWord C (List.ofFn μ) * f b *
        Kraus.evalWord B (List.ofFn q)).trace := by
  rw [wallConfig_comp_cast]
  exact twoWallMPV_append B e C f p a μ b q

/-- **The periodic state with four domain walls**: the coefficient
`tr(B^p e^a C^{μ₁} f^i B^ν e^j C^{μ₃} f^b B^q)` of the state with the domain walls `e`, `f`, `e`,
`f` between alternating `B` and `C` regions.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 1427--1659 (the states compared
in `eq:z2int`) and lines 1667--1672 (`signphysop`). -/
noncomputable def fourWallCoeff {D D' u u' v w' w : ℕ} (B : MPSTensor d D)
    (e : Fin d → Matrix (Fin D) (Fin D') ℂ) (C : MPSTensor d D')
    (f : Fin d → Matrix (Fin D') (Fin D) ℂ) (p : Fin u → Fin d) (a : Fin d)
    (μ₁ : Fin u' → Fin d) (i : Fin d) (ν : Fin v → Fin d) (j : Fin d) (μ₃ : Fin w' → Fin d)
    (b : Fin d) (q : Fin w → Fin d) : ℂ :=
  (Kraus.evalWord B (List.ofFn p) * e a * Kraus.evalWord C (List.ofFn μ₁) * f i *
    Kraus.evalWord B (List.ofFn ν) * e j * Kraus.evalWord C (List.ofFn μ₃) * f b *
      Kraus.evalWord B (List.ofFn q)).trace

/-- A configuration split at one pair of sites splits further at a second pair inside the middle
region. -/
theorem exists_wallConfig_wallSplit {u w L : ℕ} (u' v w' : ℕ)
    (h : u + 1 + (u' + 1 + v + 1 + w') + 1 + w = L) (τ : Fin L → Fin d) :
    ∃ (p : Fin u → Fin d) (a : Fin d) (μ₁ : Fin u' → Fin d) (i : Fin d) (ν : Fin v → Fin d)
      (j : Fin d) (μ₃ : Fin w' → Fin d) (b : Fin d) (q : Fin w → Fin d),
      τ = wallConfig h (p, a, wallSplit u' v w' (μ₁, i, ν, j, μ₃), b, q) := by
  obtain ⟨⟨p, a, μ, b, q⟩, rfl⟩ := (wallConfig h).surjective τ
  obtain ⟨⟨μ₁, i, ν, j, μ₃⟩, rfl⟩ := (wallSplit u' v w').surjective μ
  exact ⟨p, a, μ₁, i, ν, j, μ₃, b, q, rfl⟩

/-! ### Products of two domain-wall strings -/

namespace GroupFamily

variable {G X : Type*} [Group G] {F : GroupFamily G d} [MulAction G X] {D : X → ℕ}
  {A : (x : X) → MPSTensor d (D x)}

namespace BlockActionData

variable (ad : BlockActionData F A) {g : G} {x y : X} {hxy : g • x = y} {hyx : g • y = x}
  {Âx : Fin d → Matrix (Fin (D x)) (Fin (D x)) ℂ} {Ây : Fin d → Matrix (Fin (D y)) (Fin (D y)) ℂ}
  {eAB : Fin d → Matrix (Fin (D x)) (Fin (D y)) ℂ} {eBA : Fin d → Matrix (Fin (D y)) (Fin (D x)) ℂ}

/-- **A nested pair of strings, outer string second.** For strings on sites
`i₂ < i₁ < j₁ < j₂`, here at `u`, `u + 1 + u'`, `u + 1 + u' + 1 + v` and
`u + 1 + u' + 1 + v + 1 + w'`, the outer string acting second passes over the two walls created by
the inner one and acquires `c_{AB} c_{BA}`: `O^{[i₂,j₂]} O^{[i₁,j₁]} |ψ_A⟩` is `c_{AB} c_{BA}`
times the state with four domain walls, whenever the three inner regions are longer than a fixed
buffer.

Source: arXiv:2405.00439, `signphysop`, `Papers/2405.00439/MPU-DW.tex` lines 1667--1672, and
`eq:z2int`, lines 1427--1659. -/
theorem wallString_outer_mul_inner_mulVec_mpv_apply
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x)))
    (hÂ : IsSeparatingLeftInverse Âx Ây (A x) (A y)) {cAB cBA : ℂ}
    (hAB : ad.IsDomainWallAction g hxy hyx eAB eBA cAB)
    (hBA : ad.IsDomainWallAction g hyx hxy eBA eAB cBA) :
    ∃ N : ℕ, ∀ (u u' v w' w L : ℕ) (h₁ : u + 1 + u' + 1 + v + 1 + (w' + 1 + w) = L)
      (h₂ : u + 1 + (u' + 1 + v + 1 + w') + 1 + w = L), N ≤ u' → N ≤ v → N ≤ w' →
      ∀ p a μ₁ i ν j μ₃ b q,
      ((ad.wallString g hxy hyx Âx Ây eAB eBA u (u' + 1 + v + 1 + w') w h₂ *
          ad.wallString g hxy hyx Âx Ây eAB eBA (u + 1 + u') v (w' + 1 + w) h₁) *ᵥ
          (fun σ ↦ MPSTensor.mpv (A x) σ))
          (wallConfig h₂ (p, a, wallSplit u' v w' (μ₁, i, ν, j, μ₃), b, q)) =
        (cAB * cBA) * fourWallCoeff (A x) eAB (A y) eBA p a μ₁ i ν j μ₃ b q := by
  obtain ⟨N, hN⟩ := BlockActionData.IsDomainWallAction.pair hperm hAB hBA
  refine ⟨N, fun u u' v w' w L h₁ h₂ hu' hv hw' p a μ₁ i ν j μ₃ b q ↦ ?_⟩
  rw [← Matrix.mulVec_mulVec, wallString_mulVec_mpv_left ad hÂ h₁]
  -- the outer string passes over the two walls created by the inner one
  have hψ : ∀ p a μ b q, twoWallMPV (A x) eAB (A y) eBA (wallConfig h₂ (p, a, μ, b, q) ∘
      Fin.cast h₁) = (Kraus.evalWord (A x) (List.ofFn p) * A x a *
        twoWallChain (A x) eAB (A y) eBA μ * A x b * Kraus.evalWord (A x) (List.ofFn q)).trace := by
    intro p a μ b q
    obtain ⟨⟨μ₁, i, ν, j, μ₃⟩, rfl⟩ := (wallSplit u' v w').surjective μ
    rw [← wallConfig_resplit h₁ h₂, twoWallMPV_wallConfig_comp_cast,
      show ∀ s, wallSplit (d := d) u' v w' s = Fin.append (Fin.append (Fin.append
      (Fin.append s.1 ![s.2.1]) s.2.2.1) ![s.2.2.2.1]) s.2.2.2.2 from fun _ ↦ rfl,
      twoWallChain_append]
    simp only [List.ofFn_fin_append]
    simp [Kraus.evalWord_append, Kraus.evalWord_cons, Matrix.mul_assoc]
  rw [wallString, stringOperator_mulVec_trace _ _ _ h₂
    (fun p ↦ Kraus.evalWord (A x) (List.ofFn p)) (A x) (twoWallChain (A x) eAB (A y) eBA) (A x)
    (fun q ↦ Kraus.evalWord (A x) (List.ofFn q)) _ hψ, leftAct_wallLeftEndpoint_left ad hÂ,
    rightAct_wallRightEndpoint_left ad hÂ,
    show wallSplit (d := d) u' v w' (μ₁, i, ν, j, μ₃) = Fin.append (Fin.append (Fin.append
      (Fin.append μ₁ ![i]) ν) ![j]) μ₃ from rfl, physAct_twoWallChain]
  have hpair := hN (List.ofFn μ₁) (List.ofFn ν) (List.ofFn μ₃) i j (by simpa using hu')
    (by simpa using hv) (by simpa using hw')
  have key := congrArg (fun M ↦ Kraus.evalWord (A x) (List.ofFn p) * eAB a * M *
    (eBA b * Kraus.evalWord (A x) (List.ofFn q))) hpair
  simp only [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul] at key
  simp only [Matrix.mul_assoc]
  rw [key, Matrix.trace_smul, smul_eq_mul, fourWallCoeff]
  simp only [Matrix.mul_assoc]

/-- **A nested pair of strings, inner string second.** For strings on sites
`i₂ < i₁ < j₁ < j₂`, the inner string acting second meets only the `B` region created by the outer
one: `O^{[i₁,j₁]} O^{[i₂,j₂]} |ψ_A⟩` is the state with four domain walls.

Source: arXiv:2405.00439, `signphysop`, `Papers/2405.00439/MPU-DW.tex` lines 1667--1672, and
`eq:z2int`, lines 1427--1659. -/
theorem wallString_inner_mul_outer_mulVec_mpv_apply
    (hÂ : IsSeparatingLeftInverse Âx Ây (A x) (A y)) {u u' v w' w L : ℕ}
    (h₁ : u + 1 + u' + 1 + v + 1 + (w' + 1 + w) = L)
    (h₂ : u + 1 + (u' + 1 + v + 1 + w') + 1 + w = L) (p : Fin u → Fin d) (a : Fin d)
    (μ₁ : Fin u' → Fin d) (i : Fin d) (ν : Fin v → Fin d) (j : Fin d) (μ₃ : Fin w' → Fin d)
    (b : Fin d) (q : Fin w → Fin d) :
    ((ad.wallString g hxy hyx Âx Ây eAB eBA (u + 1 + u') v (w' + 1 + w) h₁ *
        ad.wallString g hxy hyx Âx Ây eAB eBA u (u' + 1 + v + 1 + w') w h₂) *ᵥ
        (fun σ ↦ MPSTensor.mpv (A x) σ))
          (wallConfig h₂ (p, a, wallSplit u' v w' (μ₁, i, ν, j, μ₃), b, q)) =
      fourWallCoeff (A x) eAB (A y) eBA p a μ₁ i ν j μ₃ b q := by
  rw [← Matrix.mulVec_mulVec, wallString_mulVec_mpv_left ad hÂ h₂]
  have hψ : ∀ P' a' ν' b' Q', twoWallMPV (A x) eAB (A y) eBA
      (wallConfig h₁ (P', a', ν', b', Q') ∘ Fin.cast h₂) =
        (wallChain (A x) eAB (A y) P' * A y a' * Kraus.evalWord (A y) (List.ofFn ν') * A y b' *
          wallChain (A y) eBA (A x) Q').trace := by
    intro P' a' ν' b' Q'
    rw [eq_append_append P', eq_append_append Q', wallConfig_resplit h₁ h₂,
      twoWallMPV_wallConfig_comp_cast,
      show ∀ s, wallSplit (d := d) u' v w' s = Fin.append (Fin.append (Fin.append
      (Fin.append s.1 ![s.2.1]) s.2.2.1) ![s.2.2.2.1]) s.2.2.2.2 from fun _ ↦ rfl,
      wallChain_append, wallChain_append]
    simp only [List.ofFn_fin_append]
    simp [Kraus.evalWord_append, Kraus.evalWord_cons, Matrix.mul_assoc]
  rw [← wallConfig_resplit h₁ h₂, wallString,
    stringOperator_mulVec_trace _ _ _ h₁
    (wallChain (A x) eAB (A y)) (A y) (fun ν ↦ Kraus.evalWord (A y) (List.ofFn ν)) (A y)
    (wallChain (A y) eBA (A x)) _ hψ, leftAct_wallLeftEndpoint_right ad hÂ,
    rightAct_wallRightEndpoint_right ad hÂ, physAct_evalWord, wallChain_append, wallChain_append]
  have hr := (isReduction_castIndex (ad.isReduction g y) hyx).evalWord (List.ofFn ν)
  rw [fourWallCoeff, ← hr]
  simp only [Matrix.mul_assoc]

/-- **A crossed pair of strings, the second string over the wall `e_{BA}`.** For strings on
`[j, r₂]` and `[i, r₁]` with `j < i < r₂ < r₁`, here at `u`, `u + 1 + u' + 1 + v`,
`u + 1 + u'` and `u + 1 + u' + 1 + v + 1 + w'`, the string on `[i, r₁]` acting second starts in
the `B` region, passes over the wall `e_{BA}` at `r₂` and ends in the `A` region:
`O^{[i,r₁]} O^{[j,r₂]} |ψ_A⟩` is `c_{BA}` times the state with four domain walls, whenever the
regions on both sides of `r₂` are longer than a fixed buffer.

Source: arXiv:2405.00439, `eq:z2int`, `Papers/2405.00439/MPU-DW.tex` lines 1427--1659. -/
theorem wallString_cross_over_right_mulVec_mpv_apply
    (hÂ : IsSeparatingLeftInverse Âx Ây (A x) (A y)) {cBA : ℂ}
    (hBA : ad.IsDomainWallAction g hyx hxy eBA eAB cBA) :
    ∃ N : ℕ, ∀ (u u' v w' w L : ℕ) (h₂ : u + 1 + (u' + 1 + v + 1 + w') + 1 + w = L)
      (h₃ : u + 1 + (u' + 1 + v) + 1 + (w' + 1 + w) = L)
      (h₄ : u + 1 + u' + 1 + (v + 1 + w') + 1 + w = L), N ≤ v → N ≤ w' →
      ∀ p a μ₁ i ν j μ₃ b q,
      ((ad.wallString g hxy hyx Âx Ây eAB eBA (u + 1 + u') (v + 1 + w') w h₄ *
          ad.wallString g hxy hyx Âx Ây eAB eBA u (u' + 1 + v) (w' + 1 + w) h₃) *ᵥ
          (fun σ ↦ MPSTensor.mpv (A x) σ))
          (wallConfig h₂ (p, a, wallSplit u' v w' (μ₁, i, ν, j, μ₃), b, q)) =
        cBA * fourWallCoeff (A x) eAB (A y) eBA p a μ₁ i ν j μ₃ b q := by
  obtain ⟨N, hN⟩ := hBA.physAct_eq
  refine ⟨N, fun u u' v w' w L h₂ h₃ h₄ hv hw' p a μ₁ i ν j μ₃ b q ↦ ?_⟩
  rw [← Matrix.mulVec_mulVec, wallString_mulVec_mpv_left ad hÂ h₃]
  have hψ : ∀ P a' M b' q', twoWallMPV (A x) eAB (A y) eBA
      (wallConfig h₄ (P, a', M, b', q') ∘ Fin.cast h₃) =
        (wallChain (A x) eAB (A y) P * A y a' * wallChain (A y) eBA (A x) M * A x b' *
          Kraus.evalWord (A x) (List.ofFn q')).trace := by
    intro P a' M b' q'
    obtain ⟨P₁, P₂, P₃, rfl⟩ : ∃ P₁ P₂ P₃, P = Fin.append (Fin.append P₁ ![P₂]) P₃ :=
      ⟨_, _, _, eq_append_append P⟩
    obtain ⟨M₁, M₂, M₃, rfl⟩ : ∃ M₁ M₂ M₃, M = Fin.append (Fin.append M₁ ![M₂]) M₃ :=
      ⟨_, _, _, eq_append_append M⟩
    rw [wallConfig_eq_wallConfig h₄ h₃ _
      (P₁, P₂, Fin.append (Fin.append P₃ ![a']) M₁, M₂, Fin.append (Fin.append M₃ ![b']) q')
      (by simp only [List.ofFn_fin_append]; simp), twoWallMPV_wallConfig_comp_cast,
      wallChain_append, wallChain_append]
    simp only [List.ofFn_fin_append]
    simp [Kraus.evalWord_append, Kraus.evalWord_cons, Matrix.mul_assoc]
  rw [wallConfig_eq_wallConfig h₂ h₄ _
      (Fin.append (Fin.append p ![a]) μ₁, i, Fin.append (Fin.append ν ![j]) μ₃, b, q)
      (by simp only [wallSplit, Equiv.coe_fn_mk, List.ofFn_fin_append]; simp),
    wallString, stringOperator_mulVec_trace _ _ _ h₄ (wallChain (A x) eAB (A y)) (A y)
      (wallChain (A y) eBA (A x)) (A x) (fun q ↦ Kraus.evalWord (A x) (List.ofFn q)) _ hψ,
    leftAct_wallLeftEndpoint_right ad hÂ, rightAct_wallRightEndpoint_left ad hÂ]
  have hrel := hN v w' hv hw' (Fin.append (Fin.append ν ![j]) μ₃)
  have key := congrArg (fun M ↦ wallChain (A x) eAB (A y) (Fin.append (Fin.append p ![a]) μ₁) *
    eBA i * M * (eBA b * Kraus.evalWord (A x) (List.ofFn q))) hrel
  simp only [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul] at key
  simp only [Matrix.mul_assoc]
  rw [key, Matrix.trace_smul, smul_eq_mul, fourWallCoeff, wallChain_append, wallChain_append]
  simp only [Matrix.mul_assoc]

/-- **A crossed pair of strings, the second string over the wall `e_{AB}`.** For strings on
`[i, r₂]` and `[j, r₁]` with `j < i < r₁ < r₂`, here at `u + 1 + u'`,
`u + 1 + u' + 1 + v + 1 + w'`, `u` and `u + 1 + u' + 1 + v`, the string on `[j, r₁]` acting second
starts in the `A` region, passes over the wall `e_{AB}` at `i` and ends in the `B` region:
`O^{[j,r₁]} O^{[i,r₂]} |ψ_A⟩` is `c_{AB}` times the state with four domain walls, whenever the
regions on both sides of `i` are longer than a fixed buffer.

Source: arXiv:2405.00439, `eq:z2int`, `Papers/2405.00439/MPU-DW.tex` lines 1427--1659. -/
theorem wallString_cross_over_left_mulVec_mpv_apply
    (hÂ : IsSeparatingLeftInverse Âx Ây (A x) (A y)) {cAB : ℂ}
    (hAB : ad.IsDomainWallAction g hxy hyx eAB eBA cAB) :
    ∃ N : ℕ, ∀ (u u' v w' w L : ℕ) (h₂ : u + 1 + (u' + 1 + v + 1 + w') + 1 + w = L)
      (h₃ : u + 1 + (u' + 1 + v) + 1 + (w' + 1 + w) = L)
      (h₄ : u + 1 + u' + 1 + (v + 1 + w') + 1 + w = L), N ≤ u' → N ≤ v →
      ∀ p a μ₁ i ν j μ₃ b q,
      ((ad.wallString g hxy hyx Âx Ây eAB eBA u (u' + 1 + v) (w' + 1 + w) h₃ *
          ad.wallString g hxy hyx Âx Ây eAB eBA (u + 1 + u') (v + 1 + w') w h₄) *ᵥ
          (fun σ ↦ MPSTensor.mpv (A x) σ))
          (wallConfig h₂ (p, a, wallSplit u' v w' (μ₁, i, ν, j, μ₃), b, q)) =
        cAB * fourWallCoeff (A x) eAB (A y) eBA p a μ₁ i ν j μ₃ b q := by
  obtain ⟨N, hN⟩ := hAB.physAct_eq
  refine ⟨N, fun u u' v w' w L h₂ h₃ h₄ hu' hv p a μ₁ i ν j μ₃ b q ↦ ?_⟩
  rw [← Matrix.mulVec_mulVec, wallString_mulVec_mpv_left ad hÂ h₄]
  have hψ : ∀ p' a' M b' Q, twoWallMPV (A x) eAB (A y) eBA
      (wallConfig h₃ (p', a', M, b', Q) ∘ Fin.cast h₄) =
        (Kraus.evalWord (A x) (List.ofFn p') * A x a' * wallChain (A x) eAB (A y) M * A y b' *
          wallChain (A y) eBA (A x) Q).trace := by
    intro p' a' M b' Q
    obtain ⟨M₁, M₂, M₃, rfl⟩ : ∃ M₁ M₂ M₃, M = Fin.append (Fin.append M₁ ![M₂]) M₃ :=
      ⟨_, _, _, eq_append_append M⟩
    obtain ⟨Q₁, Q₂, Q₃, rfl⟩ : ∃ Q₁ Q₂ Q₃, Q = Fin.append (Fin.append Q₁ ![Q₂]) Q₃ :=
      ⟨_, _, _, eq_append_append Q⟩
    rw [wallConfig_eq_wallConfig h₃ h₄ _
      (Fin.append (Fin.append p' ![a']) M₁, M₂, Fin.append (Fin.append M₃ ![b']) Q₁, Q₂, Q₃)
      (by simp only [List.ofFn_fin_append]; simp), twoWallMPV_wallConfig_comp_cast,
      wallChain_append, wallChain_append]
    simp only [List.ofFn_fin_append]
    simp [Kraus.evalWord_append, Kraus.evalWord_cons, Matrix.mul_assoc]
  rw [wallConfig_eq_wallConfig h₂ h₃ _
      (p, a, Fin.append (Fin.append μ₁ ![i]) ν, j, Fin.append (Fin.append μ₃ ![b]) q)
      (by simp only [wallSplit, Equiv.coe_fn_mk, List.ofFn_fin_append]; simp),
    wallString, stringOperator_mulVec_trace _ _ _ h₃ (fun p ↦ Kraus.evalWord (A x) (List.ofFn p))
      (A x) (wallChain (A x) eAB (A y)) (A y) (wallChain (A y) eBA (A x)) _ hψ,
    leftAct_wallLeftEndpoint_left ad hÂ, rightAct_wallRightEndpoint_right ad hÂ]
  have hrel := hN u' v hu' hv (Fin.append (Fin.append μ₁ ![i]) ν)
  have key := congrArg (fun M ↦ Kraus.evalWord (A x) (List.ofFn p) * eAB a * M *
    (eAB j * wallChain (A y) eBA (A x) (Fin.append (Fin.append μ₃ ![b]) q))) hrel
  simp only [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul] at key
  simp only [Matrix.mul_assoc]
  rw [key, Matrix.trace_smul, smul_eq_mul, fourWallCoeff, wallChain_append, wallChain_append]
  simp only [Matrix.mul_assoc]

/-- **Exchange of two domain-wall strings** (arXiv:2405.00439, `signphysop`,
`Papers/2405.00439/MPU-DW.tex` lines 1667--1672): for strings on sites `i₂ < i₁ < j₁ < j₂`,
here `O^{[i₂,j₂]}` with endpoints at `u` and `u + 1 + u' + 1 + v + 1 + w'` and
`O^{[i₁,j₁]}` with endpoints at `u + 1 + u'` and `u + 1 + u' + 1 + v`,

`O^{[i₂,j₂]} O^{[i₁,j₁]} |ψ_A⟩ = c_{AB} c_{BA} O^{[i₁,j₁]} O^{[i₂,j₂]} |ψ_A⟩`

whenever the three regions between the walls are longer than a fixed buffer. Both sides are
multiples of the state with the four domain walls `e_{AB}`, `e_{BA}`, `e_{AB}`, `e_{BA}` at
`i₂, i₁, j₁, j₂`: the outer string acting second passes over the walls of the inner one and
acquires `c_{AB} c_{BA}` (`IsDomainWallAction.pair`), while the inner string acting second meets
only the `B` region. The source prints the phase on the other side; that form is
`wallString_mul_wallString_mulVec_mpv_of_mpo_mul_self_eq_one`, under `U² = 1`
(lines 835--839). -/
theorem wallString_mul_wallString_mulVec_mpv
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x)))
    (hÂ : IsSeparatingLeftInverse Âx Ây (A x) (A y)) {cAB cBA : ℂ}
    (hAB : ad.IsDomainWallAction g hxy hyx eAB eBA cAB)
    (hBA : ad.IsDomainWallAction g hyx hxy eBA eAB cBA) :
    ∃ N : ℕ, ∀ (u u' v w' w L : ℕ) (h₁ : u + 1 + u' + 1 + v + 1 + (w' + 1 + w) = L)
      (h₂ : u + 1 + (u' + 1 + v + 1 + w') + 1 + w = L), N ≤ u' → N ≤ v → N ≤ w' →
      (ad.wallString g hxy hyx Âx Ây eAB eBA u (u' + 1 + v + 1 + w') w h₂ *
          ad.wallString g hxy hyx Âx Ây eAB eBA (u + 1 + u') v (w' + 1 + w) h₁) *ᵥ
          (fun σ ↦ MPSTensor.mpv (A x) σ) =
        (cAB * cBA) • ((ad.wallString g hxy hyx Âx Ây eAB eBA (u + 1 + u') v (w' + 1 + w) h₁ *
          ad.wallString g hxy hyx Âx Ây eAB eBA u (u' + 1 + v + 1 + w') w h₂) *ᵥ
            (fun σ ↦ MPSTensor.mpv (A x) σ)) := by
  obtain ⟨N, hN⟩ := ad.wallString_outer_mul_inner_mulVec_mpv_apply hperm hÂ hAB hBA
  refine ⟨N, fun u u' v w' w L h₁ h₂ hu' hv hw' ↦ funext fun τ ↦ ?_⟩
  obtain ⟨p, a, μ₁, i, ν, j, μ₃, b, q, rfl⟩ := exists_wallConfig_wallSplit u' v w' h₂ τ
  rw [Pi.smul_apply, smul_eq_mul, hN u u' v w' w L h₁ h₂ hu' hv hw',
    ad.wallString_inner_mul_outer_mulVec_mpv_apply hÂ h₁ h₂]

/-- **Exchange of two domain-wall strings, in the printed orientation** (arXiv:2405.00439,
`signphysop`, `Papers/2405.00439/MPU-DW.tex` lines 1667--1672): if `U = O_g` squares to the
identity on every nonempty chain, then
`O^{[i₁,j₁]} O^{[i₂,j₂]} |ψ_A⟩ = c_{AB} c_{BA} O^{[i₂,j₂]} O^{[i₁,j₁]} |ψ_A⟩`.
The two orientations agree because `(c_{AB} c_{BA})² = 1`, which follows from `U² = 1` as in the
source (lines 835--839,
`MPOTensor.GroupFamily.BlockActionData.IsDomainWallAction.mul_sq_eq_one_of_mpo_mul_self_eq_one`);
the blocks are normal because they have left inverses. -/
theorem wallString_mul_wallString_mulVec_mpv_of_mpo_mul_self_eq_one
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x)))
    (hU : ∀ L, 0 < L → mpo (F.tensor g) L * mpo (F.tensor g) L = 1)
    (hÂ : IsSeparatingLeftInverse Âx Ây (A x) (A y)) {cAB cBA : ℂ}
    (hAB : ad.IsDomainWallAction g hxy hyx eAB eBA cAB)
    (hBA : ad.IsDomainWallAction g hyx hxy eBA eAB cBA) :
    ∃ N : ℕ, ∀ (u u' v w' w L : ℕ) (h₁ : u + 1 + u' + 1 + v + 1 + (w' + 1 + w) = L)
      (h₂ : u + 1 + (u' + 1 + v + 1 + w') + 1 + w = L), N ≤ u' → N ≤ v → N ≤ w' →
      (ad.wallString g hxy hyx Âx Ây eAB eBA (u + 1 + u') v (w' + 1 + w) h₁ *
          ad.wallString g hxy hyx Âx Ây eAB eBA u (u' + 1 + v + 1 + w') w h₂) *ᵥ
          (fun σ ↦ MPSTensor.mpv (A x) σ) =
        (cAB * cBA) • ((ad.wallString g hxy hyx Âx Ây eAB eBA u (u' + 1 + v + 1 + w') w h₂ *
          ad.wallString g hxy hyx Âx Ây eAB eBA (u + 1 + u') v (w' + 1 + w) h₁) *ᵥ
            (fun σ ↦ MPSTensor.mpv (A x) σ)) := by
  have hc := hAB.mul_sq_eq_one_of_mpo_mul_self_eq_one
    (isInjective_of_physPairing_eq_one hÂ.left_left).isNormal
    (isInjective_of_physPairing_eq_one hÂ.right_right).isNormal hperm hU hBA
  obtain ⟨N, hN⟩ := ad.wallString_mul_wallString_mulVec_mpv hperm hÂ hAB hBA
  refine ⟨N, fun u u' v w' w L h₁ h₂ hu' hv hw' ↦ ?_⟩
  rw [hN u u' v w' w L h₁ h₂ hu' hv hw', smul_smul, ← sq, hc, one_smul]

/-! ### Exchange of two left endpoints -/

/-- **Exchange of two left endpoints, glued at the far right endpoint** (arXiv:2405.00439,
`eq:z2int`, `Papers/2405.00439/MPU-DW.tex` lines 1427--1659): for `j < i`, the half-chain
operators `O^{[j]}_x` and `O^{[i]}_y` glued with right endpoints at `r₁` and `r₂`, here with
`j`, `i`, `r₂`, `r₁` at `u`, `u + 1 + u'`, `u + 1 + u' + 1 + v` and
`u + 1 + u' + 1 + v + 1 + w'`, satisfy

`O^{[j,r₁]} O^{[i,r₂]} |ψ_A⟩ = c_{AB} O^{[i,r₁]} O^{[j,r₂]} |ψ_A⟩`

whenever the three regions between the four endpoints are longer than a fixed buffer. The left
side is `c_{AB} c_{BA}` times the state with four domain walls
(`wallString_outer_mul_inner_mulVec_mpv_apply`), and the right side is `c_{BA}` times the same
state (`wallString_cross_over_right_mulVec_mpv_apply`). -/
theorem wallString_mul_wallString_mulVec_mpv_swap_left_far
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x)))
    (hÂ : IsSeparatingLeftInverse Âx Ây (A x) (A y)) {cAB cBA : ℂ}
    (hAB : ad.IsDomainWallAction g hxy hyx eAB eBA cAB)
    (hBA : ad.IsDomainWallAction g hyx hxy eBA eAB cBA) :
    ∃ N : ℕ, ∀ (u u' v w' w L : ℕ) (h₁ : u + 1 + u' + 1 + v + 1 + (w' + 1 + w) = L)
      (h₂ : u + 1 + (u' + 1 + v + 1 + w') + 1 + w = L)
      (h₃ : u + 1 + (u' + 1 + v) + 1 + (w' + 1 + w) = L)
      (h₄ : u + 1 + u' + 1 + (v + 1 + w') + 1 + w = L), N ≤ u' → N ≤ v → N ≤ w' →
      (ad.wallString g hxy hyx Âx Ây eAB eBA u (u' + 1 + v + 1 + w') w h₂ *
          ad.wallString g hxy hyx Âx Ây eAB eBA (u + 1 + u') v (w' + 1 + w) h₁) *ᵥ
          (fun σ ↦ MPSTensor.mpv (A x) σ) =
        cAB • ((ad.wallString g hxy hyx Âx Ây eAB eBA (u + 1 + u') (v + 1 + w') w h₄ *
          ad.wallString g hxy hyx Âx Ây eAB eBA u (u' + 1 + v) (w' + 1 + w) h₃) *ᵥ
            (fun σ ↦ MPSTensor.mpv (A x) σ)) := by
  obtain ⟨N₁, hN₁⟩ := ad.wallString_outer_mul_inner_mulVec_mpv_apply hperm hÂ hAB hBA
  obtain ⟨N₂, hN₂⟩ := ad.wallString_cross_over_right_mulVec_mpv_apply hÂ hBA
  refine ⟨N₁ + N₂, fun u u' v w' w L h₁ h₂ h₃ h₄ hu' hv hw' ↦ funext fun τ ↦ ?_⟩
  obtain ⟨p, a, μ₁, i, ν, j, μ₃, b, q, rfl⟩ := exists_wallConfig_wallSplit u' v w' h₂ τ
  rw [Pi.smul_apply, smul_eq_mul, hN₁ u u' v w' w L h₁ h₂ (by omega) (by omega) (by omega),
    hN₂ u u' v w' w L h₂ h₃ h₄ (by omega) (by omega), mul_assoc]

/-- **Exchange of two left endpoints, glued at the near right endpoint** (arXiv:2405.00439,
`eq:z2int`, `Papers/2405.00439/MPU-DW.tex` lines 1427--1659): for `j < i`, the half-chain
operators `O^{[j]}_x` and `O^{[i]}_y` glued with right endpoints at `r₁` and `r₂`, here with
`j`, `i`, `r₁`, `r₂` at `u`, `u + 1 + u'`, `u + 1 + u' + 1 + v` and
`u + 1 + u' + 1 + v + 1 + w'`, satisfy

`O^{[j,r₁]} O^{[i,r₂]} |ψ_A⟩ = c_{AB} O^{[i,r₁]} O^{[j,r₂]} |ψ_A⟩`

whenever the two regions on both sides of `i` are longer than a fixed buffer. The left side is
`c_{AB}` times the state with four domain walls
(`wallString_cross_over_left_mulVec_mpv_apply`), and the right side is that state
(`wallString_inner_mul_outer_mulVec_mpv_apply`). -/
theorem wallString_mul_wallString_mulVec_mpv_swap_left_near
    (hÂ : IsSeparatingLeftInverse Âx Ây (A x) (A y)) {cAB : ℂ}
    (hAB : ad.IsDomainWallAction g hxy hyx eAB eBA cAB) :
    ∃ N : ℕ, ∀ (u u' v w' w L : ℕ) (h₁ : u + 1 + u' + 1 + v + 1 + (w' + 1 + w) = L)
      (h₂ : u + 1 + (u' + 1 + v + 1 + w') + 1 + w = L)
      (h₃ : u + 1 + (u' + 1 + v) + 1 + (w' + 1 + w) = L)
      (h₄ : u + 1 + u' + 1 + (v + 1 + w') + 1 + w = L), N ≤ u' → N ≤ v →
      (ad.wallString g hxy hyx Âx Ây eAB eBA u (u' + 1 + v) (w' + 1 + w) h₃ *
          ad.wallString g hxy hyx Âx Ây eAB eBA (u + 1 + u') (v + 1 + w') w h₄) *ᵥ
          (fun σ ↦ MPSTensor.mpv (A x) σ) =
        cAB • ((ad.wallString g hxy hyx Âx Ây eAB eBA (u + 1 + u') v (w' + 1 + w) h₁ *
          ad.wallString g hxy hyx Âx Ây eAB eBA u (u' + 1 + v + 1 + w') w h₂) *ᵥ
            (fun σ ↦ MPSTensor.mpv (A x) σ)) := by
  obtain ⟨N, hN⟩ := ad.wallString_cross_over_left_mulVec_mpv_apply hÂ hAB
  refine ⟨N, fun u u' v w' w L h₁ h₂ h₃ h₄ hu' hv ↦ funext fun τ ↦ ?_⟩
  obtain ⟨p, a, μ₁, i, ν, j, μ₃, b, q, rfl⟩ := exists_wallConfig_wallSplit u' v w' h₂ τ
  rw [Pi.smul_apply, smul_eq_mul, hN u u' v w' w L h₂ h₃ h₄ hu' hv,
    ad.wallString_inner_mul_outer_mulVec_mpv_apply hÂ h₁ h₂]

end BlockActionData

end GroupFamily

end MPOTensor
