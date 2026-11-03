/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalDGInterleavedNode
import TNLean.MPS.AreaLaw.IntervalMergeChoice

/-!
# An actual balanced tree with interleaved collective trims

The original chain fixes one common reference and a physical family for each
long interval before all child spaces and Haar choices. A successful local
unitary defines each parent by its actual sample and interleaved family
applications and collective trims. The balanced recursion then retains the
same original full ground target, dimension and recorded weighted ranks at
every interval. The chosen unitary and literal operation are recorded.

This supports ALVV, arXiv:1602.08828v2, Figure `fig:merge-prime`,
lines 1668–1670, and the degenerate-ground-space induction, lines 1797–1805.

**Scope restriction (block leaves, fixed failure scale and capped gap):**
Leaves are full spaces of length at most `4 * ell`, the nominal sample size
uses the fixed target `(L+1)^(-2)`, and quantitative dependence retains
`min gamma 1`. See `docs/paper-gaps/alvv16_approximation_parameters.tex`.
No adaptive joint probability, energy-estimation invariant, final spectral
extraction or running time is asserted.

**Local fix (assignment and integer rounds):** Each round acts on the
current space, with the larger integer count documented in the same note.

The family is polynomial in the actual hard-clipped Hamiltonian. Retaining its
word bounds does not identify it with the soft family in the printed Generate
procedure. This distinction is recorded in
`docs/paper-gaps/alvv16_approximation_parameters.tex`.
-/

open scoped TensorProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The original physical chain constructs one balanced recursive tree
whose long parents use actual samples and interleaved collective trims.
The same full original ground space remains viable at every interval;
actual generator ranks are retained without an all-span rank assertion.
Supporting ALVV, arXiv:1602.08828v2, Figure `fig:merge-prime`,
lines 1668–1670, and `t:alg1`, lines 1777–1817.
The ordered-word bounds retain these same chosen operators and target,
including the separate energy candidate of Figure `fig:algo1`, line 1631.
-/
theorem exists_physical_dg_interleaved_interval_tree_with_word_powers :
    ∃ Ctail C Kref : ℝ, 21 ≤ Ctail ∧ 21 ≤ C ∧ 0 < Kref ∧ ∀ (L q : ℕ),
    ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (_hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2)))
      (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1) (mu nu gamma : ℝ),
    0 < gamma →
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
    (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let rG := Module.finrank ℂ G
    let g := min gamma 1
    let m := max q 50
    let w := 1 + Real.log (rG : ℝ) + 2 * Real.log ((L : ℝ) + 1)
    let v := 1 + Real.log (m : ℝ) + Real.log (1 / g) + Real.log (1 + w)
    let ell := Nat.ceil (C * (v ^ 6 / g + Real.sqrt w * v ^ 3 / Real.sqrt g))
    let D := (m * ell ^ 2) ^ (22 * ell)
    let s := Nat.ceil (4096 * (rG : ℝ) * (Real.log (D : ℝ) + w))
    let a := 3 / (32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)
    let tau := a ^ 2 / 1048576
    let epsilon := 200 * tau
    let t := Ctail * (1 + Real.log (1 / g) + Real.log (1 / tau))
    let Delta := (1 / 200000 : ℝ) / (D : ℝ) ^ 12
    21 ≤ ell ∧ 2 ≤ D ∧ 1 ≤ s ∧ 0 < a ∧ a ≤ 1 / 100 ∧
      0 < epsilon ∧ epsilon ≤ 1 ∧ 21 ≤ t ∧
      (288 * Real.exp (11 / 8)) * Real.exp (-(t - g) / 8) ≤ epsilon * g / 1000000 ∧
      (D : ℝ) ^ 12 * Delta < 1 / 100000 ∧
    let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
    let bref := 16 + Real.log (1 / g) + Real.log (32 * (rG : ℝ) * ((L : ℝ) + 1) / tau)
    ∃ B : ℕ, 1 ≤ B ∧
      Real.log (B : ℝ) ≤
        Kref * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * bref ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log bref) ∧
    ∃ U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
      Module.finrank ℂ U = rG ∧
      (∀ z ∈ U, IsOpenMPS L q (rG ^ 2 * B) (fun x ↦ z x)) ∧
    let Dref := rG ^ 2 * B
    let xiMax := a / (256 * (Dref : ℝ) * Real.sqrt ((L : ℝ) + 1))
    0 < xiMax ∧
    let width := 4 * ell
    ∃ hwidth : 1 ≤ width,
    ∃ (T : LongIntervalIndex L width →
        Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
      (N : LongIntervalIndex L width → ℕ)
      (F : ∀ J : LongIntervalIndex L width,
        Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
          EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)),
      (∀ J, N J ≤ D ^ 2) ∧
      (∀ J, Module.finrank ℂ (T J) = rG ∧
        Submodule.IsCloseTo tau (T J) G ∧ Submodule.IsCloseTo tau G (T J) ∧
        Submodule.IsCloseTo (4 * tau) (T J) U ∧
        Submodule.IsCloseTo (4 * tau) U (T J) ∧
        (∀ (power : ℕ)
          (S : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))) (delta : ℝ),
          Submodule.IsViable delta S
            ((T J).map (Entropy.regionTensorCoordinates q
              (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap) → delta < 1 →
          let grow := ⨆ w : Fin power → Fin (N J),
            S.map ((List.ofFn (fun j ↦ F J (w j))).prod : _ →ₗ[ℂ] _)
          Module.finrank ℂ grow ≤ (D ^ 2) ^ power * Module.finrank ℂ S ∧
            Submodule.IsViable (Delta ^ power / (1 - delta) ^ 2) grow
              ((T J).map (Entropy.regionTensorCoordinates q
                (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap))) ∧
      ∀ xi : ℝ, 0 < xi → xi ≤ xiMax →
      ∃ operation : IntervalMergeOperation L q,
        (∀ (p r : ℕ), p ≤ r → r ≤ L →
          let S := balancedIntervalSpace operation width hwidth p r
          Submodule.IsViable (3 / 200 : ℝ) S
            (G.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) ∧
          Module.finrank ℂ S ≤ D ^ 6 * s ^ 3 ∧
          IsIntervalSpanWithRankBound L q p r (D ^ 6 * s ^ 3) xi S) ∧
        ∀ (J : LongIntervalIndex L width) (k : ℕ)
          (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2),
          let S1 := balancedIntervalSpace operation width hwidth J.val.1 k
          let S2 := balancedIntervalSpace operation width hwidth k J.val.2
          ∃ U : Matrix.unitaryGroup
            (Fin (Module.finrank ℂ (adjacentIntervalMerge L q
              J.val.1 k J.val.2 hpk hkr S1 S2))) ℂ,
            operation J.val.1 k J.val.2 hpk hkr S1 S2 =
              sampledIntervalInterleavedTrim L q J.val.1 J.val.2 D s (F J) xi
                (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2) U := by
  classical
  obtain ⟨Ctail, C, Kref, hCtail, hC, hKref, hfamily⟩ :=
    exists_physical_dg_interleaved_interval_node_event_with_word_powers
  refine ⟨Ctail, C, Kref, hCtail, hC, hKref, ?_⟩
  intro L q h hsupp h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G rG g m w v ell D s a tau epsilon t Delta
  obtain ⟨hell, hD, hs, ha, haSmall, hepsilon, hepsilon1, ht, htail, htradeoff,
    B, hB, hlogB, Uref, hdimU, hUMPS, hxiMax, hinterval⟩ :=
    hfamily L q h hsupp h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  change 21 ≤ ell at hell
  refine ⟨hell, hD, hs, ha, haSmall, hepsilon, hepsilon1, ht, htail, htradeoff, ?_⟩
  intro u bref
  refine ⟨B, hB, hlogB, Uref, hdimU, hUMPS, ?_⟩
  intro Dref xiMax
  refine ⟨hxiMax, ?_⟩
  intro width
  have hwidth : 1 ≤ width := by dsimp only [width]; omega
  refine ⟨hwidth, ?_⟩
  have hfamilies := fun J : LongIntervalIndex L width ↦
    hinterval J.val.1 J.val.2 J.property.1 J.property.2.1 J.property.2.2
  choose T N F hN hdimT hTG hGT hTU hUT hwords hEvents using hfamilies
  clear hfamily hinterval
  refine ⟨T, N, F, hN, ?_, ?_⟩
  · intro J
    exact ⟨hdimT J, hTG J, hGT J, hTU J, hUT J, hwords J⟩
  · intro xi hxi hxiMax
    let count := D ^ 6 * s ^ 3
    have hG : G ≠ ⊥ := hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl
    have hrG : 1 ≤ rG := Submodule.one_le_finrank_iff.mpr hG
    have hq : 1 ≤ q := (by decide : 1 ≤ 2).trans
      (hH.two_le_local_dimension_of_two_spectral_values hmu hnu (ne_of_lt hmunu))
    have hDref : 1 ≤ Dref := by
      simpa only [Dref, one_mul] using Nat.mul_le_mul (Nat.one_le_pow 2 rG hrG) hB
    have hDrefR : (1 : ℝ) ≤ Dref := by exact_mod_cast hDref
    have hroot : 1 ≤ Real.sqrt ((L : ℝ) + 1) :=
      Real.one_le_sqrt.mpr (by linarith only [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)])
    have hprod := one_le_mul_of_one_le_of_one_le hDrefR hroot
    have hxiMax1 : xiMax ≤ 1 := by
      dsimp only [xiMax]
      apply (div_le_one (by positivity)).mpr
      nlinarith only [haSmall, hprod]
    have hxi1 : xi ≤ 1 := hxiMax.trans hxiMax1
    have hell2 : 1 ≤ ell ^ 2 := Nat.one_le_pow 2 ell (by omega)
    have hmBase : m ≤ m * ell ^ 2 := by
      simpa only [mul_one] using Nat.mul_le_mul_left m hell2
    have hqmBase : q ≤ m * ell ^ 2 := (Nat.le_max_left q 50).trans hmBase
    have hbase : 2 ≤ m * ell ^ 2 := (by omega : 2 ≤ m).trans hmBase
    have hleafCount : q ^ width ≤ count := by
      calc
        q ^ width ≤ (m * ell ^ 2) ^ (4 * ell) := Nat.pow_le_pow_left hqmBase _
        _ ≤ (m * ell ^ 2) ^ ((22 * ell) * 6) := Nat.pow_le_pow_right (by omega) (by omega)
        _ = D ^ 6 := pow_mul (m * ell ^ 2) (22 * ell) 6
        _ ≤ D ^ 6 * s ^ 3 := by
          simpa only [mul_one] using Nat.mul_le_mul_left (D ^ 6) (Nat.one_le_pow 3 s hs)
    let P := fun (p r : ℕ) (S : Submodule ℂ
        (EuclideanSpace ℂ (interval L p r → Fin q))) ↦
      Submodule.IsViable (3 / 200 : ℝ) S
        (G.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) ∧
      Module.finrank ℂ S ≤ count ∧ IsIntervalSpanWithRankBound L q p r count xi S
    let I := fun (J : LongIntervalIndex L width) (k : ℕ)
        (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2)
        (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
        (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q))) ↦
      ↥(Matrix.unitaryGroup (Fin (Module.finrank ℂ
        (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2))) ℂ)
    let candidate := fun (J : LongIntervalIndex L width) (k : ℕ)
        (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2)
        (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
        (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q)))
        (U : I J k hpk hkr S1 S2) ↦
      sampledIntervalInterleavedTrim L q J.val.1 J.val.2 D s (F J) xi
        (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2) U
    have hleaf (p r : ℕ) (_hpr : p ≤ r) (_hrL : r ≤ L) (hshort : r - p ≤ width) :
        P p r ⊤ := by
      have hdim : Module.finrank ℂ
          (EuclideanSpace ℂ (interval L p r → Fin q)) ≤ count := by
        calc
          _ = q ^ (interval L p r).card := by
            rw [finrank_euclideanSpace, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
          _ ≤ q ^ width := Nat.pow_le_pow_right hq ((card_interval_le _ _).trans hshort)
          _ ≤ count := hleafCount
      exact ⟨Submodule.isViable_top _ (by norm_num) _, by simpa only [finrank_top] using hdim,
        isIntervalSpanWithRankBound_top hq hdim hxi.le hxi1⟩
    have hchoice (J : LongIntervalIndex L width) (k : ℕ)
        (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2)
        (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
        (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q)))
        (hS1 : P J.val.1 k S1) (hS2 : P k J.val.2 S2) :
        ∃ U : I J k hpk hkr S1 S2, P J.val.1 J.val.2 (candidate J k hpk hkr S1 S2 U) := by
      obtain ⟨Good, _hGood, hnonempty, _hbad, _hprob, hout⟩ :=
        hEvents J xi hxi hxiMax k hpk hkr S1 S2 hS1.1 hS2.1 hS1.2.1 hS2.2.1
      obtain ⟨U, hU⟩ := hnonempty
      obtain ⟨hdim, hrank, _hclipped, hground⟩ := hout U hU
      exact ⟨U, hground, hdim, hrank⟩
    obtain ⟨operation, hliteral, htree⟩ :=
      exists_balanced_interval_tree_of_choices hwidth P I candidate hleaf hchoice
    refine ⟨operation, htree, ?_⟩
    intro J k hpk hkr S1 S2
    obtain ⟨U, heq, _hP⟩ := hliteral J k hpk hkr S1 S2
      (htree J.val.1 k hpk (hkr.trans J.property.2.1))
      (htree k J.val.2 hkr J.property.2.1)
    exact ⟨U, heq⟩

/-- The original conclusion follows by forgetting the additional ordered-word
bounds of the same physical family. Supporting ALVV, arXiv:1602.08828v2,
Figure `fig:merge-prime`, lines 1668–1670; the separate energy candidate uses
this same family as in Figure `fig:algo1`, line 1631. -/
theorem exists_physical_dg_interleaved_interval_tree :
    ∃ Ctail C Kref : ℝ, 21 ≤ Ctail ∧ 21 ≤ C ∧ 0 < Kref ∧ ∀ (L q : ℕ),
    ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (_hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2)))
      (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1) (mu nu gamma : ℝ),
    0 < gamma →
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
    (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let rG := Module.finrank ℂ G
    let g := min gamma 1
    let m := max q 50
    let w := 1 + Real.log (rG : ℝ) + 2 * Real.log ((L : ℝ) + 1)
    let v := 1 + Real.log (m : ℝ) + Real.log (1 / g) + Real.log (1 + w)
    let ell := Nat.ceil (C * (v ^ 6 / g + Real.sqrt w * v ^ 3 / Real.sqrt g))
    let D := (m * ell ^ 2) ^ (22 * ell)
    let s := Nat.ceil (4096 * (rG : ℝ) * (Real.log (D : ℝ) + w))
    let a := 3 / (32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)
    let tau := a ^ 2 / 1048576
    let epsilon := 200 * tau
    let t := Ctail * (1 + Real.log (1 / g) + Real.log (1 / tau))
    let Delta := (1 / 200000 : ℝ) / (D : ℝ) ^ 12
    21 ≤ ell ∧ 2 ≤ D ∧ 1 ≤ s ∧ 0 < a ∧ a ≤ 1 / 100 ∧
      0 < epsilon ∧ epsilon ≤ 1 ∧ 21 ≤ t ∧
      (288 * Real.exp (11 / 8)) * Real.exp (-(t - g) / 8) ≤ epsilon * g / 1000000 ∧
      (D : ℝ) ^ 12 * Delta < 1 / 100000 ∧
    let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
    let bref := 16 + Real.log (1 / g) + Real.log (32 * (rG : ℝ) * ((L : ℝ) + 1) / tau)
    ∃ B : ℕ, 1 ≤ B ∧
      Real.log (B : ℝ) ≤
        Kref * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * bref ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log bref) ∧
    ∃ U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
      Module.finrank ℂ U = rG ∧
      (∀ z ∈ U, IsOpenMPS L q (rG ^ 2 * B) (fun x ↦ z x)) ∧
    let Dref := rG ^ 2 * B
    let xiMax := a / (256 * (Dref : ℝ) * Real.sqrt ((L : ℝ) + 1))
    0 < xiMax ∧
    let width := 4 * ell
    ∃ hwidth : 1 ≤ width,
    ∃ (N : LongIntervalIndex L width → ℕ)
      (F : ∀ J : LongIntervalIndex L width,
        Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
          EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)),
      (∀ J, N J ≤ D ^ 2) ∧
      ∀ xi : ℝ, 0 < xi → xi ≤ xiMax →
      ∃ operation : IntervalMergeOperation L q,
        (∀ (p r : ℕ), p ≤ r → r ≤ L →
          let S := balancedIntervalSpace operation width hwidth p r
          Submodule.IsViable (3 / 200 : ℝ) S
            (G.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) ∧
          Module.finrank ℂ S ≤ D ^ 6 * s ^ 3 ∧
          IsIntervalSpanWithRankBound L q p r (D ^ 6 * s ^ 3) xi S) ∧
        ∀ (J : LongIntervalIndex L width) (k : ℕ)
          (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2),
          let S1 := balancedIntervalSpace operation width hwidth J.val.1 k
          let S2 := balancedIntervalSpace operation width hwidth k J.val.2
          ∃ U : Matrix.unitaryGroup
            (Fin (Module.finrank ℂ (adjacentIntervalMerge L q
              J.val.1 k J.val.2 hpk hkr S1 S2))) ℂ,
            operation J.val.1 k J.val.2 hpk hkr S1 S2 =
              sampledIntervalInterleavedTrim L q J.val.1 J.val.2 D s (F J) xi
                (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2) U := by
  classical
  obtain ⟨Ctail, C, Kref, hCtail, hC, hKref, hfamily⟩ :=
    exists_physical_dg_interleaved_interval_tree_with_word_powers
  refine ⟨Ctail, C, Kref, hCtail, hC, hKref, ?_⟩
  intro L q h hsupp h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G rG g m w v ell D s a tau epsilon t Delta
  obtain ⟨hell, hD, hs, ha, haSmall, hepsilon, hepsilon1, ht, htail, htradeoff,
    B, hB, hlogB, U, hdimU, hUMPS, hxiMax, hinterval⟩ :=
    hfamily L q h hsupp h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  refine ⟨hell, hD, hs, ha, haSmall, hepsilon, hepsilon1, ht, htail, htradeoff, ?_⟩
  intro u bref
  refine ⟨B, hB, hlogB, U, hdimU, hUMPS, ?_⟩
  intro Dref xiMax
  refine ⟨hxiMax, ?_⟩
  intro width
  obtain ⟨hwidth, _T, N, F, hN, _htargets, hoperation⟩ := hinterval
  exact ⟨hwidth, N, F, hN, hoperation⟩

end TNLean.MPS.AreaLaw
