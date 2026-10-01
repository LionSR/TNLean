/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import TNLean.Algebra.KleinCocycleTable
import TNLean.Algebra.ScalarThreeCocycleGroupCohomology

/-!
# The eight three-cocycle classes of the Klein four-group

Every complex-unit-valued three-cocycle on the Klein four-group is cohomologous
to exactly one of the eight representatives of `kleinCocycleFamily`.
Their parameters add under multiplication, giving an additive equivalence
between Mathlib's degree-three cohomology and three copies of `ZMod 2`.
This proves the classification asserted in arXiv:2203.12563, Section 6,
`Papers/2203.12563/REsubmission.tex`, lines 1845–1852, with `ℂˣ` coefficients.

**Scope restriction (coefficients):** the source classifies `H³(ℤ₂ × ℤ₂, U(1))`. This module
uses `ℂˣ` coefficients and does not compare the two groups in degree three. Documented in
`docs/paper-gaps/glm23_klein_h3_circle_coefficients.tex`.

The three order-two cyclic invariants detect cohomology classes without any
normalization assumption. For normalized cocycles these are the three diagonal
values in the source's table. The proof first normalizes an arbitrary cocycle,
then uses one complex square root to fix six entries by a two-cochain gauge.
The cocycle equation determines all remaining entries from the three signs.

## Main results

* `cohomologousTo_of_klein_diagonal_eq`: normalized Klein cocycles with the same three
  diagonal values are cohomologous.
* `cohomologousTo_iff_klein_cyclicInvariant_eq`: the order-two cyclic invariants detect
  cohomology classes.
* `exists_cohomologousTo_kleinCocycleFamily`,
  `existsUnique_cohomologousTo_kleinCocycleFamily`: every cocycle is cohomologous to exactly
  one representative.
* `kleinCocycleFamily_add`: the parameters add under multiplication.
* `kleinAnomalyClass`, `kleinAnomalyClass_bijective`, `kleinH3Equiv`: the additive
  equivalence between degree-three cohomology and `ZMod 2 × ZMod 2 × ZMod 2`.
-/

namespace TNLean.Algebra.ScalarThreeCochain
local notation "ka" => (Multiplicative.ofAdd (1, 0) : Multiplicative (ZMod 2 × ZMod 2))
local notation "kb" => (Multiplicative.ofAdd (0, 1) : Multiplicative (ZMod 2 × ZMod 2))
local notation "kc" => (Multiplicative.ofAdd (1, 1) : Multiplicative (ZMod 2 × ZMod 2))
/-- A normalized Klein cocycle with trivial diagonal values is determined by six entries.
This is the finite cocycle-equation calculation behind arXiv:2203.12563, lines 1845–1852. -/
private theorem eq_one_of_klein_entries
    {ω : ScalarThreeCochain (Multiplicative (ZMod 2 × ZMod 2))}
    (hw : IsCocycle ω) (hn : IsNormalized ω)
    (h112 : ω ka ka kb = 1)
    (h121 : ω ka kb ka = 1)
    (h122 : ω ka kb kb = 1)
    (h123 : ω ka kb kc = 1)
    (h211 : ω kb ka ka = 1)
    (h212 : ω kb ka kb = 1)
    (h111 : ω ka ka ka = 1)
    (h222 : ω kb kb kb = 1)
    (h333 : ω kc kc kc = 1)
    : ω = 1 := by
  have h113 : ω ka ka kc = 1 := by
    have h := hw ka ka ka kb
    change ω 1 ka kb * ω ka ka kc =
      ω ka ka ka * ω ka 1 kb * ω ka ka kb at h
    simpa only [hn.1, h111, hn.2.1, h112, one_mul, mul_one] using h
  have h131 : ω ka kc ka = 1 := by
    have h := hw ka ka kb ka
    change ω 1 kb ka * ω ka ka kc =
      ω ka ka kb * ω ka kc ka * ω ka kb ka at h
    simpa only [hn.1, h113, h112, h121, one_mul, mul_one] using h.symm
  have h132 : ω ka kc kb = 1 := by
    have h := hw ka ka kb kb
    change ω 1 kb kb * ω ka ka 1 =
      ω ka ka kb * ω ka kc kb * ω ka kb kb at h
    simpa only [hn.1, hn.2.2, h112, h122, one_mul, mul_one] using h.symm
  have h133 : ω ka kc kc = 1 := by
    have h := hw ka ka kb kc
    change ω 1 kb kc * ω ka ka ka =
      ω ka ka kb * ω ka kc kc * ω ka kb kc at h
    simpa only [hn.1, h111, h112, h123, one_mul, mul_one] using h.symm
  have h311 : ω kc ka ka = 1 := by
    have h := hw ka kb ka ka
    change ω kc ka ka * ω ka kb 1 =
      ω ka kb ka * ω ka kc ka * ω kb ka ka at h
    simpa only [hn.2.2, h121, h131, h211, one_mul, mul_one] using h
  have h312 : ω kc ka kb = 1 := by
    have h := hw ka kb ka kb
    change ω kc ka kb * ω ka kb kc =
      ω ka kb ka * ω ka kc kb * ω kb ka kb at h
    simpa only [h123, h121, h132, h212, one_mul, mul_one] using h
  have h322 : ω kc kb kb = 1 := by
    have h := hw ka kb kb kb
    change ω kc kb kb * ω ka kb 1 =
      ω ka kb kb * ω ka 1 kb * ω kb kb kb at h
    simpa only [hn.2.2, h122, hn.2.1, h222, one_mul, mul_one] using h
  have h233 : ω kb kc kc = 1 := by
    have h := hw ka kb kc kc
    change ω kc kc kc * ω ka kb 1 =
      ω ka kb kc * ω ka ka kc * ω kb kc kc at h
    simpa only [h333, hn.2.2, h123, h113, one_mul, mul_one] using h.symm
  have h213 : ω kb ka kc = 1 := by
    have h := hw kb ka ka kb
    change ω kc ka kb * ω kb ka kc =
      ω kb ka ka * ω kb 1 kb * ω ka ka kb at h
    simpa only [h312, h211, hn.2.1, h112, one_mul, mul_one] using h
  have h313 : ω kc ka kc = 1 := by
    have h := hw ka kb ka kc
    change ω kc ka kc * ω ka kb kb =
      ω ka kb ka * ω ka kc kc * ω kb ka kc at h
    simpa only [h122, h121, h133, h213, one_mul, mul_one] using h
  have h232 : ω kb kc kb = 1 := by
    have h := hw kb ka kb kb
    change ω kc kb kb * ω kb ka 1 =
      ω kb ka kb * ω kb kc kb * ω ka kb kb at h
    simpa only [h322, hn.2.2, h212, h122, one_mul, mul_one] using h.symm
  have h332 : ω kc kc kb = 1 := by
    have h := hw ka kb kc kb
    change ω kc kc kb * ω ka kb ka =
      ω ka kb kc * ω ka ka kb * ω kb kc kb at h
    simpa only [h121, h123, h112, h232, one_mul, mul_one] using h
  have h323 : ω kc kb kc = 1 := by
    have h := hw kb ka kb kc
    change ω kc kb kc * ω kb ka ka =
      ω kb ka kb * ω kb kc kc * ω ka kb kc at h
    simpa only [h211, h212, h233, h123, one_mul, mul_one] using h
  have h223 : ω kb kb kc = 1 := by
    have h := hw ka kb kb kc
    change ω kc kb kc * ω ka kb ka =
      ω ka kb kb * ω ka 1 kc * ω kb kb kc at h
    simpa only [h323, h121, h122, hn.2.1, one_mul, mul_one] using h.symm
  have h221 : ω kb kb ka = 1 := by
    have h := hw kb kb ka kb
    change ω 1 ka kb * ω kb kb kc =
      ω kb kb ka * ω kb kc kb * ω kb ka kb at h
    simpa only [hn.1, h223, h232, h212, one_mul, mul_one] using h.symm
  have h321 : ω kc kb ka = 1 := by
    have h := hw ka kb kb ka
    change ω kc kb ka * ω ka kb kc =
      ω ka kb kb * ω ka 1 ka * ω kb kb ka at h
    simpa only [h123, h122, hn.2.1, h221, one_mul, mul_one] using h
  have h231 : ω kb kc ka = 1 := by
    have h := hw kb ka kb ka
    change ω kc kb ka * ω kb ka kc =
      ω kb ka kb * ω kb kc ka * ω ka kb ka at h
    simpa only [h321, h213, h212, h121, one_mul, mul_one] using h.symm
  have h331 : ω kc kc ka = 1 := by
    have h := hw ka kb kc ka
    change ω kc kc ka * ω ka kb kb =
      ω ka kb kc * ω ka ka ka * ω kb kc ka at h
    simpa only [h122, h123, h111, h231, one_mul, mul_one] using h
  have hcases (g : Multiplicative (ZMod 2 × ZMod 2)) :
      g = 1 ∨ g = ka ∨ g = kb ∨ g = kc := by
    revert g
    decide
  funext g h k
  rcases hcases g with rfl | rfl | rfl | rfl <;>
    rcases hcases h with rfl | rfl | rfl | rfl <;>
    rcases hcases k with rfl | rfl | rfl | rfl <;>
    simp only [Pi.one_apply, hn.1, hn.2.1, hn.2.2,
      h111, h112, h113, h121, h122, h123, h131, h132, h133, h211, h212, h213, h221, h222,
      h223, h231, h232, h233, h311, h312, h313, h321, h322, h323, h331, h332, h333]
/-- A normalized Klein cocycle with all diagonal signs equal to one is a coboundary.
This is the trivial-class case of arXiv:2203.12563, lines 1845–1852. -/
theorem isTrivialGaugeClass_of_klein_diagonal_eq_one
    {ω : ScalarThreeCochain (Multiplicative (ZMod 2 × ZMod 2))}
    (hw : IsCocycle ω) (hn : IsNormalized ω)
    (hd : ∀ g, ω g g g = 1) : IsTrivialGaugeClass ω := by
  let a := ω ka ka kb
  let b := ω ka kb ka
  let c := ω ka kb kb
  let d := ω ka kb kc
  let e := ω kb ka ka
  let f := ω kb ka kb
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (↑(a * e / b) : ℂ) (by decide : 0 < 2)
  have hz0 : z ≠ 0 := by
    intro h
    exact (a * e / b).ne_zero (by simpa [h] using hz.symm)
  let x := Units.mk0 z hz0
  have hx : x ^ 2 = a * e / b := Units.ext hz
  let β : ScalarCocycle (Multiplicative (ZMod 2 × ZMod 2)) := fun g h ↦
    if g = ka then
      if h = ka then x * d / (c * f) else if h = kb then 1 / c
      else if h = kc then x * a * d / f else 1
    else if g = kb then
      if h = ka then 1 / (x * c) else if h = kc then f / x else 1
    else if g = kc ∧ h = ka then a * d / (b * f) else 1
  have hβ : β.IsNormalized := by
    constructor <;> intro g <;>
      simp [β, show (1 : Multiplicative (ZMod 2 × ZMod 2)) ≠ ka from by decide,
        show (1 : Multiplicative (ZMod 2 × ZMod 2)) ≠ kb from by decide,
        show (1 : Multiplicative (ZMod 2 × ZMod 2)) ≠ kc from by decide]
  have hb112 : coboundary β ka ka kb = a := by
    change (x * a * d / f) * (1 / c) / ((x * d / (c * f)) * 1) = a
    apply Units.ext
    push_cast
    field_simp
  have hb121 : coboundary β ka kb ka = b := by
    change (x * a * d / f) * (1 / (x * c)) / ((1 / c) * (a * d / (b * f))) = b
    apply Units.ext
    push_cast
    field_simp
  have hb122 : coboundary β ka kb kb = c := by
    change 1 * 1 / ((1 / c) * 1) = c
    simp
  have hb123 : coboundary β ka kb kc = d := by
    change (x * d / (c * f)) * (f / x) / ((1 / c) * 1) = d
    apply Units.ext
    push_cast
    field_simp
  have hb211 : coboundary β kb ka ka = e := by
    change 1 * (x * d / (c * f)) / ((1 / (x * c)) * (a * d / (b * f))) = e
    calc
      _ = x ^ 2 * b / a := by
        apply Units.ext
        push_cast
        field_simp
      _ = e := by rw [hx]; simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hb212 : coboundary β kb ka kb = f := by
    change (f / x) * (1 / c) / ((1 / (x * c)) * 1) = f
    apply Units.ext
    push_cast
    field_simp
  let η := fusionGauge β⁻¹ ω
  have hη (g h k) : η g h k = ω g h k / coboundary β g h k := by
    dsimp [η, fusionGauge, coboundary]
    apply Units.ext
    push_cast
    field_simp
  have hηn : IsNormalized η := hn.fusionGauge (by
    constructor <;> intro g <;> simp only [Pi.inv_apply, hβ.1, hβ.2, inv_one])
  have hηdiag (g) : η g g g = 1 := by
    have hg : g * g = (1 : Multiplicative (ZMod 2 × ZMod 2)) := by
      revert g
      decide
    rw [hη, hd, coboundary, hg, hβ.1, hβ.2]
    simp
  have hηone : η = 1 := by
    apply eq_one_of_klein_entries (hw.fusionGauge _) hηn
    · change η ka ka kb = 1
      rw [hη, hb112]
      exact div_self' a
    · change η ka kb ka = 1
      rw [hη, hb121]
      exact div_self' b
    · change η ka kb kb = 1
      rw [hη, hb122]
      exact div_self' c
    · change η ka kb kc = 1
      rw [hη, hb123]
      exact div_self' d
    · change η kb ka ka = 1
      rw [hη, hb211]
      exact div_self' e
    · change η kb ka kb = 1
      rw [hη, hb212]
      exact div_self' f
    · exact hηdiag ka
    · exact hηdiag kb
    · exact hηdiag kc
  exact (CohomologousTo.symm ⟨β⁻¹, hηone⟩)

/-- The diagonal values determine a normalized Klein cocycle up to gauge
(arXiv:2203.12563, lines 1850–1852). -/
theorem cohomologousTo_of_klein_diagonal_eq
    {ω ν : ScalarThreeCochain (Multiplicative (ZMod 2 × ZMod 2))}
    (hw : IsCocycle ω) (hn : IsNormalized ω) (hv : IsCocycle ν) (hvn : IsNormalized ν)
    (hd : ∀ g, ω g g g = ν g g g) : CohomologousTo ω ν := by
  have hvi : IsCocycle ν⁻¹ := by
    intro g h k l
    have he := congrArg Inv.inv (hv g h k l)
    simpa [mul_comm, mul_left_comm, mul_assoc] using he
  have hq : IsCocycle (ω * ν⁻¹) := hw.mul hvi
  have hqn : IsNormalized (ω * ν⁻¹) := hn.mul (by
    constructor
    · intro g h; simp only [Pi.inv_apply, hvn.1, inv_one]
    · constructor
      · intro g h; simp only [Pi.inv_apply, hvn.2.1, inv_one]
      · intro g h; simp only [Pi.inv_apply, hvn.2.2, inv_one])
  have hqd (g) : (ω * ν⁻¹) g g g = 1 := by
    simp only [Pi.mul_apply, Pi.inv_apply, hd, mul_inv_cancel]
  obtain ⟨β, hβ⟩ := isTrivialGaugeClass_of_klein_diagonal_eq_one hq hqn hqd
  refine ⟨β, ?_⟩
  funext g h k
  have he := congrFun (congrFun (congrFun hβ g) h) k
  simp only [fusionGauge, mul_one, Pi.mul_apply, Pi.inv_apply] at he
  simp only [fusionGauge, he, mul_assoc, inv_mul_cancel, mul_one]

/-- Order-two cyclic invariants determine arbitrary Klein cocycles up to gauge.
This is the normalization-independent form of arXiv:2203.12563, lines 1850–1852. -/
theorem cohomologousTo_iff_klein_cyclicInvariant_eq
    {ω ν : ScalarThreeCochain (Multiplicative (ZMod 2 × ZMod 2))}
    (hw : IsCocycle ω) (hv : IsCocycle ν) :
    CohomologousTo ω ν ↔ ∀ g, cyclicInvariant ω g 2 = cyclicInvariant ν g 2 := by
  have hg (g : Multiplicative (ZMod 2 × ZMod 2)) : g ^ 2 = 1 := by
    revert g
    decide
  constructor
  · intro h g
    exact h.cyclicInvariant_eq (hg g)
  · intro h
    obtain ⟨ω', hw', hn', hc'⟩ := exists_isNormalized_cohomologousTo hw
    obtain ⟨ν', hv', hvn', hcv'⟩ := exists_isNormalized_cohomologousTo hv
    refine hc'.symm.trans ((cohomologousTo_of_klein_diagonal_eq hw' hn' hv' hvn' ?_).trans hcv')
    intro g
    have he := (hc'.cyclicInvariant_eq (hg g)).trans
      ((h g).trans (hcv'.cyclicInvariant_eq (hg g)).symm)
    simpa [cyclicInvariant, Finset.prod_range_succ, hn'.2.1, hvn'.2.1] using he

/-- Each diagonal value of a normalized Klein cocycle is a sign
(arXiv:2203.12563, lines 1850–1852). -/
private theorem exists_klein_diagonal_sign
    {ω : ScalarThreeCochain (Multiplicative (ZMod 2 × ZMod 2))}
    (hw : IsCocycle ω) (hn : IsNormalized ω) (g) :
    ∃ p : ZMod 2, ω g g g = (-1) ^ p.val := by
  have hg : g * g = (1 : Multiplicative (ZMod 2 × ZMod 2)) := by revert g; decide
  have he := hw g g g g
  simp only [hg, hn.1, hn.2.1, hn.2.2, mul_one] at he
  have hi : (ω g g g)⁻¹ = ω g g g := by
    calc
      _ = (ω g g g)⁻¹ * 1 := (mul_one _).symm
      _ = (ω g g g)⁻¹ * (ω g g g * ω g g g) := by rw [← he]
      _ = ω g g g := by simp
  rcases (Units.inv_eq_self_iff _).mp hi with h | h
  · exact ⟨0, by simpa using h⟩
  · exact ⟨1, by simpa [ZMod.val_one] using h⟩

/-- Every normalized Klein cocycle belongs to one of the eight classes
(arXiv:2203.12563, lines 1845–1852). -/
private theorem exists_cohomologousTo_kleinCocycleFamily_of_isNormalized
    {ω : ScalarThreeCochain (Multiplicative (ZMod 2 × ZMod 2))}
    (hw : IsCocycle ω) (hn : IsNormalized ω) :
    ∃ p q r : ZMod 2, CohomologousTo ω (kleinCocycleFamily p q r) := by
  obtain ⟨p, hp⟩ := exists_klein_diagonal_sign hw hn ka
  obtain ⟨q, hq⟩ := exists_klein_diagonal_sign hw hn kb
  obtain ⟨t, ht⟩ := exists_klein_diagonal_sign hw hn kc
  refine ⟨p, q, p + q + t, cohomologousTo_of_klein_diagonal_eq hw hn
    (kleinCocycleFamily_isCocycle _ _ _)
    (kleinCocycleFamily_isNormalized _ _ _) ?_⟩
  intro g
  have hcases : g = 1 ∨ g = ka ∨ g = kb ∨ g = kc := by revert g; decide
  rcases hcases with rfl | rfl | rfl | rfl
  · rw [hn.1]
    exact ((kleinCocycleFamily_isNormalized _ _ _).1 _ _).symm
  · simpa [kleinCocycleFamily] using hp
  · simpa [kleinCocycleFamily] using hq
  · rw [ht]
    fin_cases p <;> fin_cases q <;> fin_cases t <;> rfl

/-- The eight displayed cocycles exhaust all Klein three-cocycle classes, with no
normalization assumption (arXiv:2203.12563, lines 1845–1852). -/
theorem exists_cohomologousTo_kleinCocycleFamily
    {ω : ScalarThreeCochain (Multiplicative (ZMod 2 × ZMod 2))}
    (hw : IsCocycle ω) : ∃ p q r : ZMod 2, CohomologousTo ω (kleinCocycleFamily p q r) := by
  obtain ⟨ν, hv, hvn, hc⟩ := exists_isNormalized_cohomologousTo hw
  obtain ⟨p, q, r, he⟩ := exists_cohomologousTo_kleinCocycleFamily_of_isNormalized hv hvn
  exact ⟨p, q, r, hc.symm.trans he⟩

/-- Every Klein three-cocycle has a unique parameter triple in the source table
(arXiv:2203.12563, lines 1845–1882). -/
theorem existsUnique_cohomologousTo_kleinCocycleFamily
    {ω : ScalarThreeCochain (Multiplicative (ZMod 2 × ZMod 2))} (hw : IsCocycle ω) :
    ∃! p : ZMod 2 × ZMod 2 × ZMod 2,
      CohomologousTo ω (kleinCocycleFamily p.1 p.2.1 p.2.2) := by
  obtain ⟨p, q, r, he⟩ := exists_cohomologousTo_kleinCocycleFamily hw
  refine ⟨(p, q, r), he, ?_⟩
  rintro ⟨p', q', r'⟩ h
  obtain ⟨rfl, rfl, rfl⟩ := (kleinCocycleFamily_cohomologousTo_iff p' q' r' p q r).mp
    (h.symm.trans he)
  rfl

/-- The parameter triples add under multiplication of cocycles
(arXiv:2203.12563, lines 1845–1848). -/
theorem kleinCocycleFamily_add (p q r p' q' r' : ZMod 2) :
    kleinCocycleFamily (p + p') (q + q') (r + r') =
      kleinCocycleFamily p q r * kleinCocycleFamily p' q' r' := by
  funext g h k
  simp only [Pi.mul_apply, kleinCocycleFamily, neg_one_pow_val_add]
  congr 2
  ring

/-- The order-two cyclic invariant at the identity is always trivial. -/
private theorem cyclicInvariant_one_of_isCocycle {G : Type*} [Group G] {ω : ScalarThreeCochain G}
    (hw : IsCocycle ω) : cyclicInvariant ω 1 2 = 1 := by
  have he := hw 1 1 1 1
  simp only [one_mul] at he
  have he' : (ω 1 1 1 * ω 1 1 1) * 1 = (ω 1 1 1 * ω 1 1 1) * ω 1 1 1 := by
    simpa only [mul_one] using he
  have h0 : ω 1 1 1 = 1 := (mul_left_cancel he').symm
  simp [cyclicInvariant, h0]

/-- The three nonidentity cyclic invariants detect every Klein cohomology class
(arXiv:2203.12563, lines 1850–1852), without a normalization assumption. -/
theorem cohomologousTo_iff_klein_three_cyclicInvariants
    {ω ν : ScalarThreeCochain (Multiplicative (ZMod 2 × ZMod 2))}
    (hw : IsCocycle ω) (hv : IsCocycle ν) :
    CohomologousTo ω ν ↔
      cyclicInvariant ω ka 2 = cyclicInvariant ν ka 2 ∧
      cyclicInvariant ω kb 2 = cyclicInvariant ν kb 2 ∧
      cyclicInvariant ω kc 2 = cyclicInvariant ν kc 2 := by
  rw [cohomologousTo_iff_klein_cyclicInvariant_eq hw hv]
  constructor
  · intro h
    exact ⟨h ka, h kb, h kc⟩
  · rintro ⟨ha, hb, hc⟩ g
    have hcases : g = 1 ∨ g = ka ∨ g = kb ∨ g = kc := by revert g; decide
    rcases hcases with rfl | rfl | rfl | rfl
    · rw [cyclicInvariant_one_of_isCocycle hw, cyclicInvariant_one_of_isCocycle hv]
    · exact ha
    · exact hb
    · exact hc

open CategoryTheory groupCohomology

/-- Multiplication of scalar cocycles induces addition in Mathlib cohomology. -/
private theorem anomalyClass_mul {G : Type} [Group G]
    (ω ν : {ω : ScalarThreeCochain G // IsCocycle ω}) :
    anomalyClass ⟨ω.1 * ν.1, ω.2.mul ν.2⟩ = anomalyClass ω + anomalyClass ν := by
  simp only [anomalyClass, ← map_add]
  congr 1
  apply (ModuleCat.mono_iff_injective (iCocycles (scalarH2Representation G) 3)).1 inferInstance
  rw [map_add, iCocycles_toCocycles, iCocycles_toCocycles, iCocycles_toCocycles]
  funext g
  exact (scalarRepresentationEquiv G).map_add _ _

/-- The homomorphism from the three binary parameters to their degree-three cohomology
class (arXiv:2203.12563, lines 1845–1848). -/
noncomputable def kleinAnomalyClass : (ZMod 2 × ZMod 2 × ZMod 2) →+
    groupCohomology (scalarH2Representation (Multiplicative (ZMod 2 × ZMod 2))) 3 :=
  AddMonoidHom.mk' (fun p ↦ anomalyClass
    ⟨kleinCocycleFamily p.1 p.2.1 p.2.2, kleinCocycleFamily_isCocycle _ _ _⟩) (by
      intro p q
      simpa only [Prod.fst_add, Prod.snd_add, kleinCocycleFamily_add] using
        anomalyClass_mul
          ⟨kleinCocycleFamily p.1 p.2.1 p.2.2, kleinCocycleFamily_isCocycle _ _ _⟩
          ⟨kleinCocycleFamily q.1 q.2.1 q.2.2, kleinCocycleFamily_isCocycle _ _ _⟩)

/-- The eight binary triples give every degree-three cohomology class exactly once
(arXiv:2203.12563, lines 1845–1852). -/
theorem kleinAnomalyClass_bijective : Function.Bijective kleinAnomalyClass := by
  constructor
  · rintro ⟨p, q, r⟩ ⟨p', q', r'⟩ h
    have he : CohomologousTo (kleinCocycleFamily p q r) (kleinCocycleFamily p' q' r') :=
      (cohomologousTo_iff_anomalyClass_eq _ _).2 h
    obtain ⟨rfl, rfl, rfl⟩ := (kleinCocycleFamily_cohomologousTo_iff p q r p' q' r').1 he
    rfl
  · intro c
    obtain ⟨ω, rfl⟩ := anomalyClass_surjective c
    obtain ⟨p, q, r, he⟩ := exists_cohomologousTo_kleinCocycleFamily ω.2
    exact ⟨(p, q, r), ((cohomologousTo_iff_anomalyClass_eq _ _).1 he).symm⟩

/-- The isomorphism `H³(ℤ₂ × ℤ₂, ℂˣ) ≃ ℤ₂³`, on Mathlib’s cohomology type; the source
states it with `U(1)` coefficients (arXiv:2203.12563, lines 1845–1852). -/
noncomputable def kleinH3Equiv :
    groupCohomology (scalarH2Representation (Multiplicative (ZMod 2 × ZMod 2))) 3 ≃+
      (ZMod 2 × ZMod 2 × ZMod 2) :=
  (AddEquiv.ofBijective kleinAnomalyClass kleinAnomalyClass_bijective).symm

end TNLean.Algebra.ScalarThreeCochain
