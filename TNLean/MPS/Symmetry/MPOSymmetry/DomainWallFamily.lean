/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.LSymbolDomainWall
import TNLean.Algebra.ScalarThreeCocycleCyclicDomainWall
import TNLean.MPS.Symmetry.MPOSymmetry.DomainWall

/-!
# Families of domain walls permuted by a group

Garre-Rubio and Schuch (arXiv:2405.00439, Section IV.B, `Papers/2405.00439/MPU-DW.tex` lines
1889--1933) consider a domain wall `e_{yz}` for every ordered pair of blocks, and assume that
every group element permutes them: `g` carries `e_{yz}` to `e_{gy,gz}` with a phase `B^g_{y,z}`
(`eq:localcdefG`). This file formalizes the consequences of `PentLB` drawn there:

* **The interchange phase** (`Intequiv`, lines 2013--2023). For `g` with `g^n = 1`,
  `∏_{k<n} B^g_{g^k(gx), g^k x} = ∏_{k<n} L^{gx}_{g,g^k} / L^x_{g,g^k} = (∏_{k<n} ω(g,g^k,g))⁻¹`,
  which is `∏_{i=1}^{n} ω⁻¹(g,g^i,g)` of the source. The middle product includes the factor
  `k = 0`, `L^{gx}_{g,1} / L^x_{g,1}`, which is one for the source's normalized L-symbols; the
  source's range `1 ≤ k < n` is `TNLean.Algebra.LSymbol.prod_Ico_div_eq_inv_cyclicInvariant`.
  The interchange phase depends only on `ω`, so it is independent of the action tensors, the
  domain walls and the ground state `x`.
* **The unbroken subgroup acts projectively** (lines 2028--2036). For `h₁, h₂` fixing both
  blocks `y` and `z`, `B^{h₁}_{y,z} B^{h₂}_{y,z} = (L^y_{h₁,h₂}/L^z_{h₁,h₂}) B^{h₁h₂}_{y,z}`,
  and `(h₁, h₂) ↦ L^y_{h₁,h₂}/L^z_{h₁,h₂}` is a two-cocycle on the subgroup fixing `y` and `z`;
  for `y = z` the action is linear.

The source states the second item for the subgroup fixing every block; the subgroup fixing the
two blocks adjacent to the wall contains it, and the statement here holds on that larger
stabilizer subgroup.

**Local fix (nondegenerate domain walls, blocked local action):** the walls of a family are
nonzero and their phases are nonzero, through the local action `IsDomainWallAction` (the walls are
excitations and `B` are "phase factors", line 1894), and the local action holds against blocked
regions; documented in `docs/paper-gaps/gs24_domain_wall_nondegenerate.tex`.

## Main definitions

* `MPOTensor.GroupFamily.BlockActionData.IsDomainWallFamily`: the assumption of line 1894.

## Main results

* `MPOTensor.GroupFamily.BlockActionData.IsDomainWallFamily.mul_eq`: `PentLB`.
* `MPOTensor.GroupFamily.BlockActionData.IsDomainWallFamily.prod_eq_prod_lSymbol`,
  `MPOTensor.GroupFamily.BlockActionData.IsDomainWallFamily.prod_eq_inv_cyclicInvariant`:
  `Intequiv`.
* `MPOTensor.GroupFamily.BlockActionData.IsDomainWallFamily.mul_eq_of_fixed`: the projective
  action of the subgroup fixing the two blocks (Mathlib's `fixingSubgroup`), with the two-cocycle
  of `TNLean.Algebra.LSymbol.ratioCocycle_isCocycle` (`TNLean/Algebra/LSymbolDomainWall.lean`).

## References
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- Garre-Rubio, Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*
-/

open scoped Matrix Kronecker
open TNLean.Algebra


namespace MPOTensor.GroupFamily.BlockActionData

variable {d : ℕ} {G X : Type*} [Group G] {F : GroupFamily G d} [MulAction G X] {D : X → ℕ}
  {A : (x : X) → MPSTensor d (D x)}

/-- The local action on domain walls transports along equalities of the target blocks, for a
family of domain walls indexed by pairs of blocks. -/
theorem IsDomainWallAction.congr_target {ad : BlockActionData F A} {g : G} {x y x' y' x'' y'' : X}
    {hx : g • x = x'} {hy : g • y = y'} {e : Fin d → Matrix (Fin (D x)) (Fin (D y)) ℂ}
    {E : (a b : X) → Fin d → Matrix (Fin (D a)) (Fin (D b)) ℂ} {c : ℂ}
    (h : ad.IsDomainWallAction g hx hy e (E x' y') c) (ex : x' = x'') (ey : y' = y'') :
    ad.IsDomainWallAction g (hx.trans ex) (hy.trans ey) e (E x'' y'') c := by
  subst ex ey
  exact h

variable (ad : BlockActionData F A)

/-- **A family of domain walls permuted by the group** (arXiv:2405.00439,
`Papers/2405.00439/MPU-DW.tex` lines 1889--1921): a nonzero domain wall `e_{yz}` for every
ordered pair of blocks, such that every group element `g` carries `e_{yz}` to `e_{gy,gz}` with a
nonzero phase `B^g_{y,z}` (`eq:localcdefG`; "the MPUs permute between the different domain
walls", line 1894). The phase of the wall `e_{yz}` with left block `y` is written `B g y z`;
the source writes it `B^g_{y,z}` in `PentLB` and `Intequiv`. -/
def IsDomainWallFamily (e : (y z : X) → Fin d → Matrix (Fin (D y)) (Fin (D z)) ℂ)
    (B : G → X → X → ℂ) : Prop :=
  ∀ g y z, ad.IsDomainWallAction g rfl rfl (e y z) (e (g • y) (g • z)) (B g y z)

namespace IsDomainWallFamily

variable {ad} {e : (y z : X) → Fin d → Matrix (Fin (D y)) (Fin (D z)) ℂ} {B : G → X → X → ℂ}
  (fd : FusionData F)

/-- The phases of a family of domain walls are nonzero. -/
theorem phase_ne_zero (hB : ad.IsDomainWallFamily e B) (g : G) (y z : X) : B g y z ≠ 0 :=
  (hB g y z).phase_ne_zero

/-- The domain walls of a family are nonzero. -/
theorem ne_zero (hB : ad.IsDomainWallFamily e B) (y z : X) : e y z ≠ 0 :=
  (hB 1 y z).source_ne_zero

end IsDomainWallFamily

end MPOTensor.GroupFamily.BlockActionData

/-! ### L-symbol relations for a family of domain walls

L-symbols are indexed by groups in `Type`, the universe of Mathlib's group cohomology. -/

namespace MPOTensor.GroupFamily.BlockActionData

variable {d : ℕ} {G : Type} {X : Type*} [Group G] {F : GroupFamily G d} [MulAction G X] {D : X → ℕ}
  {A : (x : X) → MPSTensor d (D x)}

namespace IsDomainWallFamily

variable {ad : BlockActionData F A} {e : (y z : X) → Fin d → Matrix (Fin (D y)) (Fin (D z)) ℂ}
  {B : G → X → X → ℂ} (fd : FusionData F)

/-- **Fractionalization of the symmetry on a family of domain walls** (arXiv:2405.00439,
`PentLB`, `Papers/2405.00439/MPU-DW.tex` lines 1928--1933):
`B^g_{hy,hz} B^h_{y,z} = (L^y_{g,h} / L^z_{g,h}) B^{gh}_{y,z}`. -/
theorem mul_eq (hB : ad.IsDomainWallFamily e B) (hA : ∀ x, Kraus.IsNormal (A x))
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x))) (g h : G) (y z : X) :
    B g (h • y) (h • z) * B h y z =
      ((ad.lSymbol fd y g h / ad.lSymbol fd z g h : ℂˣ) : ℂ) * B (g * h) y z :=
  IsDomainWallAction.mul_eq (fd := fd) hA hperm (hB h y z) (hB g (h • y) (h • z))
    ((hB (g * h) y z).congr_target (mul_smul g h y) (mul_smul g h z))

/-- **The interchange phase as a product of L-symbols** (arXiv:2405.00439, `Intequiv`, first
equality, in the normalization-free form with the factor `k = 0`,
`Papers/2405.00439/MPU-DW.tex` lines 2017--2023): for `g ^ n = 1`,
`∏_{k<n} B^g_{g^k(gx), g^k x} = ∏_{k<n} L^{gx}_{g,g^k} / L^x_{g,g^k}`. The walls
`e_{g^k(gx), g^k x}` are those of the source, `e_{g^i x, g^{i-1} x}` for `i = k + 1`. -/
theorem prod_eq_prod_lSymbol (hB : ad.IsDomainWallFamily e B) (hA : ∀ x, Kraus.IsNormal (A x))
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x))) {g : G} {n : ℕ} (hg : g ^ n = 1)
    (x : X) :
    ∏ k ∈ Finset.range n, B g (g ^ k • g • x) (g ^ k • x) =
      ∏ k ∈ Finset.range n,
        ((ad.lSymbol fd (g • x) g (g ^ k) / ad.lSymbol fd x g (g ^ k) : ℂˣ) : ℂ) := by
  set β : ℕ → ℂ := fun k ↦ B (g ^ k) (g • x) x
  have hstep : ∀ k, B g (g ^ k • g • x) (g ^ k • x) * β k =
      ((ad.lSymbol fd (g • x) g (g ^ k) / ad.lSymbol fd x g (g ^ k) : ℂˣ) : ℂ) * β (k + 1) := by
    intro k
    simp only [β, pow_succ']
    exact hB.mul_eq fd hA hperm g (g ^ k) (g • x) x
  have hβ : ∀ k, β k ≠ 0 := fun k ↦ hB.phase_ne_zero _ _ _
  have hshift : ∏ k ∈ Finset.range n, β (k + 1) = ∏ k ∈ Finset.range n, β k := by
    have h1 := Finset.prod_range_succ β n
    have h2 := Finset.prod_range_succ' β n
    have hn : β n = β 0 := by simp only [β, hg, pow_zero]
    rw [hn] at h1
    exact mul_right_cancel₀ (hβ 0) (h2.symm.trans h1)
  have hprod := Finset.prod_congr rfl fun k (_ : k ∈ Finset.range n) ↦ hstep k
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hshift] at hprod
  exact mul_right_cancel₀ (Finset.prod_ne_zero_iff.mpr fun k _ ↦ hβ k) hprod

/-- **The interchange phase is the inverse cyclic invariant of the anomaly**
(arXiv:2405.00439, `Intequiv`, `Papers/2405.00439/MPU-DW.tex` lines 2017--2023): for
`g ^ n = 1`, `∏_{k<n} B^g_{g^k(gx), g^k x} = (∏_{k<n} ω(g,g^k,g))⁻¹`, which is
`∏_{i=1}^{n} ω⁻¹(g,g^i,g)` of the source. The left side is therefore independent of the action
tensors, the domain walls and the block `x`, and it is invariant under fusion gauges. -/
theorem prod_eq_inv_cyclicInvariant (hB : ad.IsDomainWallFamily e B)
    (hF : F.IsNormalRepresentation) (hA : ∀ x, Kraus.IsNormal (A x)) (hD : ∀ x, 0 < D x)
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x))) {g : G} {n : ℕ} (hg : g ^ n = 1)
    (x : X) :
    ∏ k ∈ Finset.range n, B g (g ^ k • g • x) (g ^ k • x) =
      (((ScalarThreeCochain.cyclicInvariant fd.omega g n)⁻¹ : ℂˣ) : ℂ) := by
  rw [hB.prod_eq_prod_lSymbol fd hA hperm hg x, ← LSymbol.prod_div_eq_inv_cyclicInvariant
    (isCompatible_lSymbol (fd := fd) (ad := ad) hF hA hD hperm) x hg, Units.coe_prod]

/-- **The interchange phase is the domain-wall phase of the anomaly** (arXiv:2405.00439,
`Intequiv`, `Papers/2405.00439/MPU-DW.tex` lines 2013--2023): for `g` of finite order,
`∏_{k<o(g)} B^g_{g^k(gx), g^k x} = ∏_{i=1}^{o(g)} ω⁻¹(g,g^i,g)`, the phase
`TNLean.Algebra.ScalarThreeCochain.domainWallPhase` of the anomaly three-cochain. -/
theorem prod_eq_domainWallPhase (hB : ad.IsDomainWallFamily e B)
    (hF : F.IsNormalRepresentation) (hA : ∀ x, Kraus.IsNormal (A x)) (hD : ∀ x, 0 < D x)
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x))) (g : G) (x : X) :
    ∏ k ∈ Finset.range (orderOf g), B g (g ^ k • g • x) (g ^ k • x) =
      (ScalarThreeCochain.domainWallPhase fd.omega g : ℂ) := by
  rw [hB.prod_eq_inv_cyclicInvariant fd hF hA hD hperm (pow_orderOf_eq_one g) x,
    ScalarThreeCochain.domainWallPhase_eq_inv_cyclicInvariant]

/-- **The subgroup fixing two blocks acts projectively on the domain walls between them**
(arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 2028--2036): for `a, b` fixing `y` and
`z`, `B^a_{y,z} B^b_{y,z} = α(a, b) B^{ab}_{y,z}` with the two-cocycle
`α(a, b) = L^y_{a,b} / L^z_{a,b}` of `TNLean.Algebra.LSymbol.ratioCocycle_isCocycle`. The source
states this on the subgroup fixing every block, which is contained in the subgroup here; see
`docs/paper-gaps/gs24_unbroken_subgroup_stabilizer.tex` for the stabilizer reading. -/
theorem mul_eq_of_fixed (hB : ad.IsDomainWallFamily e B) (hA : ∀ x, Kraus.IsNormal (A x))
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x))) {y z : X}
    (a b : fixingSubgroup G ({y, z} : Set X)) :
    B a y z * B b y z =
      (LSymbol.ratioCocycle (ad.lSymbol fd) y z a b : ℂ) * B (a * b : G) y z := by
  have h := hB.mul_eq fd hA hperm a b y z
  rw [((mem_fixingSubgroup_iff G).mp b.2) y (by simp),
    ((mem_fixingSubgroup_iff G).mp b.2) z (by simp)] at h
  exact h

include fd in
/-- **Local excitations transform linearly** (arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex`
lines 2034--2035): for `y = z`, the phases of the stabilizer of `y` multiply. -/
theorem mul_eq_of_fixed_self (hB : ad.IsDomainWallFamily e B) (hA : ∀ x, Kraus.IsNormal (A x))
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x))) {y : X}
    (a b : fixingSubgroup G ({y, y} : Set X)) :
    B a y y * B b y y = B (a * b : G) y y := by
  rw [hB.mul_eq_of_fixed fd hA hperm a b]
  simp [LSymbol.ratioCocycle]

end IsDomainWallFamily

end MPOTensor.GroupFamily.BlockActionData
