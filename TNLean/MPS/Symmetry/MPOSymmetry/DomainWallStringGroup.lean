/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.DomainWallFamily
import TNLean.MPS.Symmetry.MPOSymmetry.DomainWallStringExchange

/-!
# Domain-wall strings of a finite group and the exchange of two `g`-domain walls

Garre-Rubio and Schuch (arXiv:2405.00439, Section IV.B, `Papers/2405.00439/MPU-DW.tex`
lines 1934–2005) create a pair of domain walls from `x` to `g x` on the ground state `|ψ_{A_x}⟩`
by a string of the matrix product unitary `U_g` on the sites `i, …, j`, closed by endpoint
tensors (`eq:DWophysG`). The left endpoint is the sum over all blocks (`eq:defEndTG`)

`∑_x V_{g,x} e_{x,gx} Â_x`,

with `Â_x` a left inverse of the injective tensor `A_x` and `V_{g,x}` the left action tensor of
`g` on `A_x`; the right endpoint is built in the same way from `W_{g,x} e_{gx,x} Â_x`. Cutting
the string in the middle, the source compares the two orders of two left endpoints `i > j` of
`g`-strings and finds `O^{[j]}_{g,a} O^{[i]}_{g,b} |ψ_x⟩ = B^g_{x,gx} O^{[i]}_{g,a} O^{[j]}_{g,b}
|ψ_x⟩`, "the phase factor from the interchange of two `g`-domain walls on top of the ground
state" (lines 1990–2002).

**Formalized here.** For a finite set of blocks with left inverses of separated supports
(`IsSeparatingLeftInverseFamily`) and a family of domain walls `e_{yz}` on which the group acts
with phases `B^g_{y,z}` (`MPOTensor.GroupFamily.BlockActionData.IsDomainWallFamily`,
`eq:localcdefG`):

* the string `O_g^{[i,j]}` with the endpoints of `eq:defEndTG` creates the walls `e_{x,gx}` and
  `e_{gx,x}` on `|ψ_{A_x}⟩` (`groupWallString_mulVec_mpv`, `eq:DWophysG`);
* for two strings on `i₂ < i₁ < j₁ < j₂`, the outer string acting second acquires
  `B^g_{x,gx} B^g_{gx,x}` (`groupWallString_mul_groupWallString_mulVec_mpv`);
* gluing the half strings with right endpoints, as in `eq:z2int` of the `ℤ₂` case, the exchange
  of the two left endpoints of `g`-strings gives the phase `B^g_{x,gx}`
  (`groupWallString_mul_groupWallString_mulVec_mpv_swap_left`).

Every one of these states is a multiple of the periodic state with the four walls
`e_{x,gx}`, `e_{gx,g²x}`, `e_{g²x,gx}`, `e_{gx,x}` (`nestedWallCoeff`). For `g² x = x` this is
the setting of `TNLean/MPS/Symmetry/MPOSymmetry/DomainWallStringExchange.lean`.

**Local fix (nondegenerate domain walls, blocked local action):** the walls of the family and its
phases are nonzero, and the local relation `eq:localcdefG` holds against regions longer than a
buffer, through `IsDomainWallAction`; the endpoints act on one site, as at the renormalization
fixed point of the source (lines 1358 and 1422–1425). Documented in
`docs/paper-gaps/gs24_domain_wall_nondegenerate.tex`.

**Scope restriction (glued half-chain operators):** the exchange of two left endpoints is proved
for the half-chain operators glued with right endpoints of `g`-strings, not as an identity of
half-chain tensors with open legs; documented in
`docs/paper-gaps/gs24_domain_wall_half_string_gluing.tex`.

## Main definitions

* `MPOTensor.GroupFamily.IsSeparatingLeftInverseFamily`: left inverses of all blocks with
  separated supports.
* `MPOTensor.GroupFamily.BlockActionData.groupWallLeftEndpoint`,
  `MPOTensor.GroupFamily.BlockActionData.groupWallRightEndpoint`: the endpoints of `eq:defEndTG`.
* `MPOTensor.GroupFamily.BlockActionData.groupWallString`: the string `O_g^{[i,j]}`.
* `MPOTensor.nestedWallCoeff`: the coefficient of the periodic state with four domain walls
  between the blocks `x`, `gx`, `g²x`, `gx`, `x`.

## Main results

* `MPOTensor.GroupFamily.BlockActionData.groupWallString_mulVec_mpv`: `eq:DWophysG`.
* `MPOTensor.GroupFamily.BlockActionData.groupWallString_mul_groupWallString_mulVec_mpv`: the two
  orders of nested strings differ by `B^g_{x,gx} B^g_{gx,x}`.
* `MPOTensor.GroupFamily.BlockActionData.groupWallString_mul_groupWallString_mulVec_mpv_swap_left`:
  the exchange of two `g`-domain walls gives `B^g_{x,gx}`.

## References
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- Garre-Rubio, Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D₁ m n : ℕ}

/-! ### Sums of endpoint tensors -/

/-- The left action of the zero endpoint tensor on any tensor is zero. -/
theorem leftAct_zero (C : Fin d → Matrix (Fin m) (Fin n) ℂ) (a : Fin d) :
    leftAct (0 : Fin d → Fin d → Matrix (Fin 1) (Fin D₁) ℂ) C a = 0 := by
  ext
  simp [leftAct]

/-- The right action of the zero endpoint tensor on any tensor is zero. -/
theorem rightAct_zero (C : Fin d → Matrix (Fin m) (Fin n) ℂ) (b : Fin d) :
    rightAct (0 : Fin d → Fin d → Matrix (Fin D₁) (Fin 1) ℂ) C b = 0 := by
  ext
  simp [rightAct]

/-- The action of a left endpoint is additive over finite sums of endpoints. -/
theorem leftAct_sum {ι : Type*} (s : Finset ι) (E : ι → Fin d → Fin d → Matrix (Fin 1) (Fin D₁) ℂ)
    (C : Fin d → Matrix (Fin m) (Fin n) ℂ) (a : Fin d) :
    leftAct (∑ z ∈ s, E z) C a = ∑ z ∈ s, leftAct (E z) C a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [leftAct_zero]
  | insert z s hz ih => rw [Finset.sum_insert hz, Finset.sum_insert hz, leftAct_add, ih]

/-- The action of a right endpoint is additive over finite sums of endpoints. -/
theorem rightAct_sum {ι : Type*} (s : Finset ι)
    (E : ι → Fin d → Fin d → Matrix (Fin D₁) (Fin 1) ℂ) (C : Fin d → Matrix (Fin m) (Fin n) ℂ)
    (b : Fin d) :
    rightAct (∑ z ∈ s, E z) C b = ∑ z ∈ s, rightAct (E z) C b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rightAct_zero]
  | insert z s hz ih => rw [Finset.sum_insert hz, Finset.sum_insert hz, rightAct_add, ih]

/-- **The periodic state with four domain walls between three blocks**: the coefficient
`tr(B^p e₁^a C^{μ₁} e₂^i E^ν f₂^j C^{μ₃} f₁^b B^q)` of the state with the regions `B`, `C`, `E`,
`C`, `B` separated by the walls `e₁`, `e₂`, `f₂`, `f₁`. For `B = A_x`, `C = A_{gx}` and
`E = A_{g²x}`, it is the state created by two nested or crossed `g`-strings on `|ψ_{A_x}⟩`.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 1990–2002. -/
noncomputable def nestedWallCoeff {D D' D'' u u' v w' w : ℕ} (B : MPSTensor d D)
    (e₁ : Fin d → Matrix (Fin D) (Fin D') ℂ) (C : MPSTensor d D')
    (e₂ : Fin d → Matrix (Fin D') (Fin D'') ℂ) (E : MPSTensor d D'')
    (f₂ : Fin d → Matrix (Fin D'') (Fin D') ℂ) (f₁ : Fin d → Matrix (Fin D') (Fin D) ℂ)
    (p : Fin u → Fin d) (a : Fin d) (μ₁ : Fin u' → Fin d) (i : Fin d) (ν : Fin v → Fin d)
    (j : Fin d) (μ₃ : Fin w' → Fin d) (b : Fin d) (q : Fin w → Fin d) : ℂ :=
  (Kraus.evalWord B (List.ofFn p) * e₁ a * Kraus.evalWord C (List.ofFn μ₁) * e₂ i *
    Kraus.evalWord E (List.ofFn ν) * f₂ j * Kraus.evalWord C (List.ofFn μ₃) * f₁ b *
      Kraus.evalWord B (List.ofFn q)).trace

namespace GroupFamily

variable {G X : Type*} [Group G] {F : GroupFamily G d} [MulAction G X] {D : X → ℕ}
  {A : (x : X) → MPSTensor d (D x)}

/-- **Left inverses of all blocks with separated supports** (arXiv:2405.00439,
`Papers/2405.00439/MPU-DW.tex` lines 1422–1425 and `eq:defEndTG`, lines 1963–1979): `Â_x` is a
left inverse of `A_x` and annihilates every other block, so that each term of the endpoint
tensor `∑_x V_{g,x} e_{x,gx} Â_x` acts only on its own ground state. -/
structure IsSeparatingLeftInverseFamily (Â : (x : X) → Fin d → Matrix (Fin (D x)) (Fin (D x)) ℂ)
    (A : (x : X) → MPSTensor d (D x)) : Prop where
  /-- `Â_x` is a left inverse of `A_x`. -/
  self : ∀ x, physPairing (Â x) (A x) = 1
  /-- `Â_x` annihilates `A_y` for `y ≠ x`. -/
  ne : ∀ x y, x ≠ y → physPairing (Â x) (A y) = 0

namespace BlockActionData

variable [Fintype X] (ad : BlockActionData F A) (g : G)
  (Â : (x : X) → Fin d → Matrix (Fin (D x)) (Fin (D x)) ℂ)
  (e : (y z : X) → Fin d → Matrix (Fin (D y)) (Fin (D z)) ℂ)

/-- **The left endpoint tensor of a `g`-string** (arXiv:2405.00439, `eq:defEndTG`,
`Papers/2405.00439/MPU-DW.tex` lines 1963–1979): `∑_x V_{g,x} e_{x,gx} Â_x`. -/
noncomputable def groupWallLeftEndpoint : Fin d → Fin d → Matrix (Fin 1) (Fin (F.bondDim g)) ℂ :=
  ∑ z, leftEndpoint (Â z) (e z (g • z)) (ad.V g z)

/-- **The right endpoint tensor of a `g`-string** (arXiv:2405.00439,
`Papers/2405.00439/MPU-DW.tex` line 1421, for the right endpoint): `∑_x W_{g,x} e_{gx,x} Â_x`. -/
noncomputable def groupWallRightEndpoint : Fin d → Fin d → Matrix (Fin (F.bondDim g)) (Fin 1) ℂ :=
  ∑ z, rightEndpoint (Â z) (ad.W g z) (e (g • z) z)

/-- **The `g`-string** `O_g^{[i,j]}` (arXiv:2405.00439, `eq:DWophysG`,
`Papers/2405.00439/MPU-DW.tex` lines 1938–1962): the string of `O_g` on the periodic chain of
`L = k + 1 + l + 1 + n` sites, with the endpoints of `eq:defEndTG` at the sites `i = k` and
`j = k + 1 + l`. -/
noncomputable def groupWallString {L : ℕ} (k l n : ℕ) (h : k + 1 + l + 1 + n = L) :
    Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ :=
  stringOperator (F.tensor g) (ad.groupWallLeftEndpoint g Â e) (ad.groupWallRightEndpoint g Â e)
    k l n h

variable {g Â e}

/-- On `A_x` the left endpoint leaves `e_{x,gx} V_{g,x}`. -/
theorem leftAct_groupWallLeftEndpoint (hÂ : IsSeparatingLeftInverseFamily Â A) (x : X)
    (a : Fin d) :
    leftAct (ad.groupWallLeftEndpoint g Â e) (A x) a = e x (g • x) a * ad.V g x := by
  classical
  rw [groupWallLeftEndpoint, leftAct_sum, Fintype.sum_eq_single x fun z hz ↦
    leftAct_leftEndpoint_eq_zero _ _ _ (hÂ.ne z x hz) a, leftAct_leftEndpoint _ _ _ (hÂ.self x)]

/-- On `A_x` the right endpoint leaves `W_{g,x} e_{gx,x}`. -/
theorem rightAct_groupWallRightEndpoint (hÂ : IsSeparatingLeftInverseFamily Â A) (x : X)
    (b : Fin d) :
    rightAct (ad.groupWallRightEndpoint g Â e) (A x) b = ad.W g x * e (g • x) x b := by
  classical
  rw [groupWallRightEndpoint, rightAct_sum, Fintype.sum_eq_single x fun z hz ↦
    rightAct_rightEndpoint_eq_zero _ _ _ (hÂ.ne z x hz) b,
    rightAct_rightEndpoint _ _ _ (hÂ.self x)]

/-- **The `g`-string creates two domain walls** (arXiv:2405.00439, `eq:DWophysG`,
`Papers/2405.00439/MPU-DW.tex` lines 1938–1962): `O_g^{[i,j]} |ψ_{A_x}⟩ = |ψ(x,gx)⟩`, the
periodic state with the domain wall `e_{x,gx}` at `i`, the block `A_{gx}` between the walls and
`e_{gx,x}` at `j`, on the periodic chain of every length `L ≥ 2`. -/
theorem groupWallString_mulVec_mpv (hÂ : IsSeparatingLeftInverseFamily Â A) {k l n L : ℕ}
    (h : k + 1 + l + 1 + n = L) (x : X) :
    ad.groupWallString g Â e k l n h *ᵥ (fun σ ↦ MPSTensor.mpv (A x) σ) =
      fun τ ↦ twoWallMPV (A x) (e x (g • x)) (A (g • x)) (e (g • x) x) (τ ∘ Fin.cast h) := by
  funext τ
  obtain ⟨⟨p, a, μ, b, q⟩, rfl⟩ := (wallConfig h).surjective τ
  rw [groupWallString, stringOperator_mulVec_trace _ _ _ h
    (fun p ↦ Kraus.evalWord (A x) (List.ofFn p)) (A x)
    (fun μ ↦ Kraus.evalWord (A x) (List.ofFn μ)) (A x)
    (fun q ↦ Kraus.evalWord (A x) (List.ofFn q)) _ (fun p a μ b q ↦ mpv_wallConfig _ h p a μ b q),
    wallConfig_comp_cast, leftAct_groupWallLeftEndpoint ad hÂ,
    rightAct_groupWallRightEndpoint ad hÂ, physAct_evalWord]
  have hr := (ad.isReduction g x).evalWord (List.ofFn μ)
  rw [show wallSplit k l n (p, a, μ, b, q) = Fin.append (Fin.append (Fin.append (Fin.append p ![a])
    μ) ![b]) q from rfl, twoWallMPV_append, ← hr]
  simp only [Matrix.mul_assoc]

variable {B : G → X → X → ℂ}

/-- **A nested pair of `g`-strings, outer string second.** For strings on sites
`i₂ < i₁ < j₁ < j₂`, here at `u`, `u + 1 + u'`, `u + 1 + u' + 1 + v` and
`u + 1 + u' + 1 + v + 1 + w'`, the outer string passes over the walls `e_{x,gx}` and `e_{gx,x}`
created by the inner one and acquires `B^g_{x,gx} B^g_{gx,x}`, whenever the three inner regions
are longer than a fixed buffer.

Source: arXiv:2405.00439, `eq:localcdefG` and `eq:DWophysG`, `Papers/2405.00439/MPU-DW.tex`
lines 1896–1962. -/
theorem groupWallString_outer_mul_inner_mulVec_mpv_apply
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x)))
    (hÂ : IsSeparatingLeftInverseFamily Â A) (hB : ad.IsDomainWallFamily e B) (x : X) :
    ∃ N : ℕ, ∀ (u u' v w' w L : ℕ) (h₁ : u + 1 + u' + 1 + v + 1 + (w' + 1 + w) = L)
      (h₂ : u + 1 + (u' + 1 + v + 1 + w') + 1 + w = L), N ≤ u' → N ≤ v → N ≤ w' →
      ∀ p a μ₁ i ν j μ₃ b q,
      ((ad.groupWallString g Â e u (u' + 1 + v + 1 + w') w h₂ *
          ad.groupWallString g Â e (u + 1 + u') v (w' + 1 + w) h₁) *ᵥ
          (fun σ ↦ MPSTensor.mpv (A x) σ))
          (wallConfig h₂ (p, a, wallSplit u' v w' (μ₁, i, ν, j, μ₃), b, q)) =
        (B g x (g • x) * B g (g • x) x) *
          nestedWallCoeff (A x) (e x (g • x)) (A (g • x)) (e (g • x) (g • g • x)) (A (g • g • x))
            (e (g • g • x) (g • x)) (e (g • x) x) p a μ₁ i ν j μ₃ b q := by
  obtain ⟨N, hN⟩ := IsDomainWallAction.pair hperm (hB g x (g • x)) (hB g (g • x) x)
  refine ⟨N, fun u u' v w' w L h₁ h₂ hu' hv hw' p a μ₁ i ν j μ₃ b q ↦ ?_⟩
  rw [← Matrix.mulVec_mulVec, groupWallString_mulVec_mpv ad hÂ h₁]
  have hψ : ∀ p a μ b q, twoWallMPV (A x) (e x (g • x)) (A (g • x)) (e (g • x) x)
      (wallConfig h₂ (p, a, μ, b, q) ∘ Fin.cast h₁) = (Kraus.evalWord (A x) (List.ofFn p) *
        A x a * twoWallChain (A x) (e x (g • x)) (A (g • x)) (e (g • x) x) μ * A x b *
          Kraus.evalWord (A x) (List.ofFn q)).trace := by
    intro p a μ b q
    obtain ⟨⟨μ₁, i, ν, j, μ₃⟩, rfl⟩ := (wallSplit u' v w').surjective μ
    rw [← wallConfig_resplit h₁ h₂, twoWallMPV_wallConfig_comp_cast,
      show ∀ s, wallSplit (d := d) u' v w' s = Fin.append (Fin.append (Fin.append
      (Fin.append s.1 ![s.2.1]) s.2.2.1) ![s.2.2.2.1]) s.2.2.2.2 from fun _ ↦ rfl,
      twoWallChain_append]
    simp only [List.ofFn_fin_append]
    simp [Kraus.evalWord_append, Kraus.evalWord_cons, Matrix.mul_assoc]
  rw [groupWallString, stringOperator_mulVec_trace _ _ _ h₂
    (fun p ↦ Kraus.evalWord (A x) (List.ofFn p)) (A x)
    (twoWallChain (A x) (e x (g • x)) (A (g • x)) (e (g • x) x)) (A x)
    (fun q ↦ Kraus.evalWord (A x) (List.ofFn q)) _ hψ, leftAct_groupWallLeftEndpoint ad hÂ,
    rightAct_groupWallRightEndpoint ad hÂ,
    show wallSplit (d := d) u' v w' (μ₁, i, ν, j, μ₃) = Fin.append (Fin.append (Fin.append
      (Fin.append μ₁ ![i]) ν) ![j]) μ₃ from rfl, physAct_twoWallChain]
  have hpair := hN (List.ofFn μ₁) (List.ofFn ν) (List.ofFn μ₃) i j (by simpa using hu')
    (by simpa using hv) (by simpa using hw')
  simp only [castIndex_rfl, Matrix.one_mul, Matrix.mul_one] at hpair
  have key := congrArg (fun M ↦ Kraus.evalWord (A x) (List.ofFn p) * e x (g • x) a * M *
    (e (g • x) x b * Kraus.evalWord (A x) (List.ofFn q))) hpair
  simp only [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul] at key
  simp only [Matrix.mul_assoc]
  rw [key, Matrix.trace_smul, smul_eq_mul, nestedWallCoeff]
  simp only [Matrix.mul_assoc]

/-- **A nested pair of `g`-strings, inner string second.** For strings on sites
`i₂ < i₁ < j₁ < j₂`, the inner string acting second meets only the `A_{gx}` region created by the
outer one and creates the walls `e_{gx,g²x}` and `e_{g²x,gx}` there.

Source: arXiv:2405.00439, `eq:DWophysG`, `Papers/2405.00439/MPU-DW.tex` lines 1938–1962. -/
theorem groupWallString_inner_mul_outer_mulVec_mpv_apply
    (hÂ : IsSeparatingLeftInverseFamily Â A) (x : X) {u u' v w' w L : ℕ}
    (h₁ : u + 1 + u' + 1 + v + 1 + (w' + 1 + w) = L)
    (h₂ : u + 1 + (u' + 1 + v + 1 + w') + 1 + w = L) (p : Fin u → Fin d) (a : Fin d)
    (μ₁ : Fin u' → Fin d) (i : Fin d) (ν : Fin v → Fin d) (j : Fin d) (μ₃ : Fin w' → Fin d)
    (b : Fin d) (q : Fin w → Fin d) :
    ((ad.groupWallString g Â e (u + 1 + u') v (w' + 1 + w) h₁ *
        ad.groupWallString g Â e u (u' + 1 + v + 1 + w') w h₂) *ᵥ
        (fun σ ↦ MPSTensor.mpv (A x) σ))
          (wallConfig h₂ (p, a, wallSplit u' v w' (μ₁, i, ν, j, μ₃), b, q)) =
      nestedWallCoeff (A x) (e x (g • x)) (A (g • x)) (e (g • x) (g • g • x)) (A (g • g • x))
        (e (g • g • x) (g • x)) (e (g • x) x) p a μ₁ i ν j μ₃ b q := by
  rw [← Matrix.mulVec_mulVec, groupWallString_mulVec_mpv ad hÂ h₂]
  have hψ : ∀ P' a' ν' b' Q', twoWallMPV (A x) (e x (g • x)) (A (g • x)) (e (g • x) x)
      (wallConfig h₁ (P', a', ν', b', Q') ∘ Fin.cast h₂) =
        (wallChain (A x) (e x (g • x)) (A (g • x)) P' * A (g • x) a' *
          Kraus.evalWord (A (g • x)) (List.ofFn ν') * A (g • x) b' *
            wallChain (A (g • x)) (e (g • x) x) (A x) Q').trace := by
    intro P' a' ν' b' Q'
    rw [eq_append_append P', eq_append_append Q', wallConfig_resplit h₁ h₂,
      twoWallMPV_wallConfig_comp_cast,
      show ∀ s, wallSplit (d := d) u' v w' s = Fin.append (Fin.append (Fin.append
      (Fin.append s.1 ![s.2.1]) s.2.2.1) ![s.2.2.2.1]) s.2.2.2.2 from fun _ ↦ rfl,
      wallChain_append, wallChain_append]
    simp only [List.ofFn_fin_append]
    simp [Kraus.evalWord_append, Kraus.evalWord_cons, Matrix.mul_assoc]
  rw [← wallConfig_resplit h₁ h₂, groupWallString,
    stringOperator_mulVec_trace _ _ _ h₁
    (wallChain (A x) (e x (g • x)) (A (g • x))) (A (g • x))
    (fun ν ↦ Kraus.evalWord (A (g • x)) (List.ofFn ν)) (A (g • x))
    (wallChain (A (g • x)) (e (g • x) x) (A x)) _ hψ, leftAct_groupWallLeftEndpoint ad hÂ,
    rightAct_groupWallRightEndpoint ad hÂ, physAct_evalWord, wallChain_append, wallChain_append]
  have hr := (ad.isReduction g (g • x)).evalWord (List.ofFn ν)
  rw [nestedWallCoeff, ← hr]
  simp only [Matrix.mul_assoc]

/-- **Exchange of nested `g`-strings** (arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex`
lines 1896–1962; the finite-group form of `signphysop`): for strings on sites
`i₂ < i₁ < j₁ < j₂`, `O_g^{[i₂,j₂]} O_g^{[i₁,j₁]} |ψ_{A_x}⟩ =
B^g_{x,gx} B^g_{gx,x} O_g^{[i₁,j₁]} O_g^{[i₂,j₂]} |ψ_{A_x}⟩` whenever the three inner regions are
longer than a fixed buffer. -/
theorem groupWallString_mul_groupWallString_mulVec_mpv
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x)))
    (hÂ : IsSeparatingLeftInverseFamily Â A) (hB : ad.IsDomainWallFamily e B) (x : X) :
    ∃ N : ℕ, ∀ (u u' v w' w L : ℕ) (h₁ : u + 1 + u' + 1 + v + 1 + (w' + 1 + w) = L)
      (h₂ : u + 1 + (u' + 1 + v + 1 + w') + 1 + w = L), N ≤ u' → N ≤ v → N ≤ w' →
      (ad.groupWallString g Â e u (u' + 1 + v + 1 + w') w h₂ *
          ad.groupWallString g Â e (u + 1 + u') v (w' + 1 + w) h₁) *ᵥ
          (fun σ ↦ MPSTensor.mpv (A x) σ) =
        (B g x (g • x) * B g (g • x) x) •
          ((ad.groupWallString g Â e (u + 1 + u') v (w' + 1 + w) h₁ *
            ad.groupWallString g Â e u (u' + 1 + v + 1 + w') w h₂) *ᵥ
              (fun σ ↦ MPSTensor.mpv (A x) σ)) := by
  obtain ⟨N, hN⟩ := ad.groupWallString_outer_mul_inner_mulVec_mpv_apply hperm hÂ hB x
  refine ⟨N, fun u u' v w' w L h₁ h₂ hu' hv hw' ↦ funext fun τ ↦ ?_⟩
  obtain ⟨p, a, μ₁, i, ν, j, μ₃, b, q, rfl⟩ := exists_wallConfig_wallSplit u' v w' h₂ τ
  rw [Pi.smul_apply, smul_eq_mul, hN u u' v w' w L h₁ h₂ hu' hv hw',
    groupWallString_inner_mul_outer_mulVec_mpv_apply ad hÂ x h₁ h₂]

/-- **A crossed pair of `g`-strings.** For strings on `[j, r₂]` and `[i, r₁]` with
`j < i < r₂ < r₁`, here at `u`, `u + 1 + u' + 1 + v`, `u + 1 + u'` and
`u + 1 + u' + 1 + v + 1 + w'`, the string on `[i, r₁]` acting second starts in the `A_{gx}`
region, passes over the wall `e_{gx,x}` at `r₂` and ends in the `A_x` region: the result is
`B^g_{gx,x}` times the state with four domain walls, whenever the regions on both sides of `r₂`
are longer than a fixed buffer.

Source: arXiv:2405.00439, `eq:localcdefG` and `eq:DWophysG`, `Papers/2405.00439/MPU-DW.tex`
lines 1896–1962. -/
theorem groupWallString_cross_mulVec_mpv_apply (hÂ : IsSeparatingLeftInverseFamily Â A)
    (hB : ad.IsDomainWallFamily e B) (x : X) :
    ∃ N : ℕ, ∀ (u u' v w' w L : ℕ) (h₂ : u + 1 + (u' + 1 + v + 1 + w') + 1 + w = L)
      (h₃ : u + 1 + (u' + 1 + v) + 1 + (w' + 1 + w) = L)
      (h₄ : u + 1 + u' + 1 + (v + 1 + w') + 1 + w = L), N ≤ v → N ≤ w' →
      ∀ p a μ₁ i ν j μ₃ b q,
      ((ad.groupWallString g Â e (u + 1 + u') (v + 1 + w') w h₄ *
          ad.groupWallString g Â e u (u' + 1 + v) (w' + 1 + w) h₃) *ᵥ
          (fun σ ↦ MPSTensor.mpv (A x) σ))
          (wallConfig h₂ (p, a, wallSplit u' v w' (μ₁, i, ν, j, μ₃), b, q)) =
        B g (g • x) x *
          nestedWallCoeff (A x) (e x (g • x)) (A (g • x)) (e (g • x) (g • g • x)) (A (g • g • x))
            (e (g • g • x) (g • x)) (e (g • x) x) p a μ₁ i ν j μ₃ b q := by
  obtain ⟨N, hN⟩ := (hB g (g • x) x).physAct_eq
  refine ⟨N, fun u u' v w' w L h₂ h₃ h₄ hv hw' p a μ₁ i ν j μ₃ b q ↦ ?_⟩
  rw [← Matrix.mulVec_mulVec, groupWallString_mulVec_mpv ad hÂ h₃]
  have hψ : ∀ P a' M b' q', twoWallMPV (A x) (e x (g • x)) (A (g • x)) (e (g • x) x)
      (wallConfig h₄ (P, a', M, b', q') ∘ Fin.cast h₃) =
        (wallChain (A x) (e x (g • x)) (A (g • x)) P * A (g • x) a' *
          wallChain (A (g • x)) (e (g • x) x) (A x) M * A x b' *
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
    groupWallString, stringOperator_mulVec_trace _ _ _ h₄
      (wallChain (A x) (e x (g • x)) (A (g • x))) (A (g • x))
      (wallChain (A (g • x)) (e (g • x) x) (A x)) (A x)
      (fun q ↦ Kraus.evalWord (A x) (List.ofFn q)) _ hψ,
    leftAct_groupWallLeftEndpoint ad hÂ, rightAct_groupWallRightEndpoint ad hÂ]
  have hrel := hN v w' hv hw' (Fin.append (Fin.append ν ![j]) μ₃)
  simp only [castIndex_rfl, Matrix.one_mul, Matrix.mul_one] at hrel
  have key := congrArg (fun M ↦
    wallChain (A x) (e x (g • x)) (A (g • x)) (Fin.append (Fin.append p ![a]) μ₁) *
      e (g • x) (g • g • x) i * M * (e (g • x) x b * Kraus.evalWord (A x) (List.ofFn q))) hrel
  simp only [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul] at key
  simp only [Matrix.mul_assoc]
  rw [key, Matrix.trace_smul, smul_eq_mul, nestedWallCoeff, wallChain_append, wallChain_append]
  simp only [Matrix.mul_assoc]

/-- **The exchange of two `g`-domain walls** (arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex`
lines 1990–2002): for `j < i`, the half-chain operators `O^{[j]}_g` and `O^{[i]}_g` glued with
right endpoints at `r₁` and `r₂`, here with `j`, `i`, `r₂`, `r₁` at `u`, `u + 1 + u'`,
`u + 1 + u' + 1 + v` and `u + 1 + u' + 1 + v + 1 + w'`, satisfy

`O_g^{[j,r₁]} O_g^{[i,r₂]} |ψ_{A_x}⟩ = B^g_{x,gx} O_g^{[i,r₁]} O_g^{[j,r₂]} |ψ_{A_x}⟩`

whenever the three regions between the four endpoints are longer than a fixed buffer. The left
side is `B^g_{x,gx} B^g_{gx,x}` times the state with four domain walls
(`groupWallString_outer_mul_inner_mulVec_mpv_apply`), and the right side is `B^g_{gx,x}` times
the same state (`groupWallString_cross_mulVec_mpv_apply`). -/
theorem groupWallString_mul_groupWallString_mulVec_mpv_swap_left
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x)))
    (hÂ : IsSeparatingLeftInverseFamily Â A) (hB : ad.IsDomainWallFamily e B) (x : X) :
    ∃ N : ℕ, ∀ (u u' v w' w L : ℕ) (h₁ : u + 1 + u' + 1 + v + 1 + (w' + 1 + w) = L)
      (h₂ : u + 1 + (u' + 1 + v + 1 + w') + 1 + w = L)
      (h₃ : u + 1 + (u' + 1 + v) + 1 + (w' + 1 + w) = L)
      (h₄ : u + 1 + u' + 1 + (v + 1 + w') + 1 + w = L), N ≤ u' → N ≤ v → N ≤ w' →
      (ad.groupWallString g Â e u (u' + 1 + v + 1 + w') w h₂ *
          ad.groupWallString g Â e (u + 1 + u') v (w' + 1 + w) h₁) *ᵥ
          (fun σ ↦ MPSTensor.mpv (A x) σ) =
        B g x (g • x) • ((ad.groupWallString g Â e (u + 1 + u') (v + 1 + w') w h₄ *
          ad.groupWallString g Â e u (u' + 1 + v) (w' + 1 + w) h₃) *ᵥ
            (fun σ ↦ MPSTensor.mpv (A x) σ)) := by
  obtain ⟨N₁, hN₁⟩ := ad.groupWallString_outer_mul_inner_mulVec_mpv_apply hperm hÂ hB x
  obtain ⟨N₂, hN₂⟩ := ad.groupWallString_cross_mulVec_mpv_apply hÂ hB x
  refine ⟨N₁ + N₂, fun u u' v w' w L h₁ h₂ h₃ h₄ hu' hv hw' ↦ funext fun τ ↦ ?_⟩
  obtain ⟨p, a, μ₁, i, ν, j, μ₃, b, q, rfl⟩ := exists_wallConfig_wallSplit u' v w' h₂ τ
  rw [Pi.smul_apply, smul_eq_mul, hN₁ u u' v w' w L h₁ h₂ (by omega) (by omega) (by omega),
    hN₂ u u' v w' w L h₂ h₃ h₄ (by omega) (by omega), mul_assoc]

end BlockActionData

end GroupFamily

end MPOTensor
