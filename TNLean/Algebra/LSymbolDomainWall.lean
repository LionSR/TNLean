/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CocycleCohomology
import TNLean.Algebra.ScalarThreeCocycleCyclicInvariant

/-!
# Scalar L-symbol identities for domain walls

The scalar steps of arXiv:2405.00439, Section IV.C (`Papers/2405.00439/MPU-DW.tex` lines
2013--2036), for L-symbols compatible with a scalar three-cochain
(`TNLean.Algebra.LSymbol.IsCompatible`, the equation `coupledpent` of the source):

* the interchange product `∏_{k<n} L^{gx}_{g,g^k} / L^x_{g,g^k}` is the inverse cyclic invariant
  `(∏_{k<n} ω(g,g^k,g))⁻¹` when `g^n = 1` (`Intequiv`);
* the ratio `(a, b) ↦ L^y_{a,b} / L^z_{a,b}` is a two-cocycle on Mathlib's `fixingSubgroup` of
  `{y, z}`, stated with the existing `TNLean.Algebra.ScalarCocycle.IsCocycle` and with Mathlib's
  `groupCohomology.IsMulCocycle₂`.

## Main results

* `TNLean.Algebra.LSymbol.prod_div_eq_inv_cyclicInvariant`,
  `TNLean.Algebra.LSymbol.prod_Ico_div_eq_inv_cyclicInvariant`
* `TNLean.Algebra.LSymbol.ratioCocycle_isCocycle`,
  `TNLean.Algebra.LSymbol.ratioCocycle_isMulCocycle₂`

## References
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- Garre-Rubio, Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*
-/

open TNLean.Algebra

namespace TNLean.Algebra.LSymbol

variable {G X : Type*} [Group G] [MulAction G X]

/-- **The interchange product of L-symbols is the inverse cyclic invariant.** If `L` is
compatible with `ω` and `g ^ n = 1`, then
`∏_{k<n} L^{gx}_{g,g^k} / L^x_{g,g^k} = (∏_{k<n} ω(g,g^k,g))⁻¹`.

Source: arXiv:2405.00439, `Intequiv`, `Papers/2405.00439/MPU-DW.tex` lines 2017--2023, second
equality, which uses `coupledpent` at `(g, g^i, g)`. -/
theorem prod_div_eq_inv_cyclicInvariant {L : LSymbol G X} {ω : ScalarThreeCochain G}
    (hL : IsCompatible L ω) (x : X) {g : G} {n : ℕ} (hg : g ^ n = 1) :
    ∏ k ∈ Finset.range n, L (g • x) g (g ^ k) / L x g (g ^ k) =
      (ScalarThreeCochain.cyclicInvariant ω g n)⁻¹ := by
  have hterm : ∀ k : ℕ, L (g • x) g (g ^ k) / L x g (g ^ k) =
      (ω g (g ^ k) g)⁻¹ * ((L x g (g ^ (k + 1)) / L x g (g ^ k)) *
        (L x (g ^ (k + 1)) g / L x (g ^ k) g)⁻¹) := by
    intro k
    have h := hL x g (g ^ k) g
    rw [← pow_succ, ← pow_succ'] at h
    apply Units.ext
    have h' := congrArg Units.val h
    simp only [Units.val_mul] at h'
    simp only [Units.val_mul, Units.val_div_eq_div_val, Units.val_inv_eq_inv_val]
    have h1 := (L (g • x) g (g ^ k)).ne_zero
    have h2 := (L x g (g ^ k)).ne_zero
    have h3 := (L x (g ^ k) g).ne_zero
    have h4 := (L x (g ^ (k + 1)) g).ne_zero
    have h5 := (ω g (g ^ k) g).ne_zero
    field_simp
    linear_combination -h'
  simp only [hterm, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    Finset.prod_range_div (fun k ↦ L x g (g ^ k)), Finset.prod_range_div (fun k ↦ L x (g ^ k) g),
    hg, pow_zero, div_self', inv_one, mul_one, ScalarThreeCochain.cyclicInvariant]

/-- The ratio `L^y_{a,b} / L^z_{a,b}` on the subgroup fixing `y` and `z`. -/
def ratioCocycle (L : LSymbol G X) (y z : X) : ScalarCocycle (fixingSubgroup G ({y, z} : Set X)) :=
  fun a b ↦ L y a b / L z a b

/-- **The L-symbol ratio is a two-cocycle on the subgroup fixing two blocks** (arXiv:2405.00439,
`Papers/2405.00439/MPU-DW.tex` lines 2028--2034): if `L` is compatible with `ω`, then
`(a, b) ↦ L^y_{a,b} / L^z_{a,b}` satisfies the two-cocycle equation on the elements fixing `y`
and `z`; the three-cocycle cancels in the ratio. -/
theorem ratioCocycle_isCocycle {L : LSymbol G X} {ω : ScalarThreeCochain G}
    (hL : IsCompatible L ω) (y z : X) : (ratioCocycle L y z).IsCocycle := by
  rintro ⟨a, -⟩ ⟨b, -⟩ ⟨c, hc⟩
  have hy := hL y a b c
  have hz := hL z a b c
  rw [((mem_fixingSubgroup_iff G).mp hc) y (by simp)] at hy
  rw [((mem_fixingSubgroup_iff G).mp hc) z (by simp)] at hz
  simp only [ratioCocycle, Subgroup.coe_mul]
  rw [div_mul_div_comm, div_mul_div_comm, mul_comm (L y a b), mul_comm (L z a b)]
  rw [show L y (a * b) c * L y a b = (ω a b c)⁻¹ * (L y a (b * c) * L y b c) by
      rw [mul_comm, hy]; group,
    show L z (a * b) c * L z a b = (ω a b c)⁻¹ * (L z a (b * c) * L z b c) by
      rw [mul_comm, hz]; group]
  rw [mul_div_mul_left_eq_div]

/-- The two-cocycle `L^y/L^z` in the form of Mathlib's multiplicative two-cocycles
(`groupCohomology.IsMulCocycle₂`), through
`TNLean.Algebra.ScalarCocycle.isCocycle_iff_isMulCocycle₂`. -/
theorem ratioCocycle_isMulCocycle₂ {L : LSymbol G X} {ω : ScalarThreeCochain G}
    (hL : IsCompatible L ω) (y z : X) :
    letI := ScalarCocycle.trivialMulDistribMulAction (G := fixingSubgroup G ({y, z} : Set X))
    groupCohomology.IsMulCocycle₂ (Function.uncurry (ratioCocycle L y z)) :=
  (ScalarCocycle.isCocycle_iff_isMulCocycle₂ _).mp (ratioCocycle_isCocycle hL y z)

/-- **The interchange product over the source's range.** For normalized L-symbols the factor
`k = 0` is one, and the product of `TNLean.Algebra.LSymbol.prod_div_eq_inv_cyclicInvariant` is
the source's `∏_{i=1}^{n-1} L^{gx}_{g,g^i} / L^x_{g,g^i}`.

Source: arXiv:2405.00439, `Intequiv`, `Papers/2405.00439/MPU-DW.tex` lines 2017--2023, middle
expression. -/
theorem prod_Ico_div_eq_inv_cyclicInvariant {L : LSymbol G X} {ω : ScalarThreeCochain G}
    (hL : IsCompatible L ω) (hLn : IsNormalized L) (x : X) {g : G} {n : ℕ} (hg : g ^ n = 1) :
    ∏ k ∈ Finset.Ico 1 n, L (g • x) g (g ^ k) / L x g (g ^ k) =
      (ScalarThreeCochain.cyclicInvariant ω g n)⁻¹ := by
  rw [← prod_div_eq_inv_cyclicInvariant hL x hg]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Finset.range_eq_Ico, Finset.prod_eq_prod_Ico_succ_bot hn]
    simp [hLn.1]

end TNLean.Algebra.LSymbol
