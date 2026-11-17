/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.UniqueGroundStateTree
import TNLean.MPS.AreaLaw.PhysicalDGTreeApproximation

/-!
# A merge tree of length-independent node dimension for a unique frustration-free ground state

ALVV, arXiv:1602.08828v2, Theorem `t:unique`, lines 1829–1855, treats a frustration-free
nearest-neighbour chain with a unique ground state `Γ` and spectral gap `γ`. Its improvement
over Theorem `t:alg1` is that the viable space at every node of the merge tree has dimension
independent of the chain length.

This file proves that dimension bound. The deterministic recursive tree of the degenerate-gap
case, run at ground energy `0` with ground-space dimension `1`, has at every node a
`3/200`-viable space for `ℂ Γ` of dimension at most `D⁶ s³`, where `D = (m ℓ²)^{22ℓ}` and `s`
depend only on the local dimension, the gap and a sampling parameter `β`, and not on `L`. The
literal raw-filter-and-trim iterates of its root give a line mutually `η/2`-close to `ℂ Γ` of
matrix product states.

**Scope restriction (degenerate-gap tree witness):** the per-node families are the families of
the degenerate-gap tree, not the frustration-free family of Theorem `t:aisff`; the per-node
bound is `D⁶ s³` rather than the source's `D s²`; the tree is a recursive witness, with no
sampling probability; the bond dimension of the output grows with `L`; and the chain has at
least one site. See `docs/paper-gaps/alvv16_unique_ground_state_tree.tex`.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

open TNLean.MPS.AreaLaw

/-- A nonempty chain of local dimension at least two whose kernel is a line has a positive
spectral value above a gap. Auxiliary to ALVV, arXiv:1602.08828v2, Theorem `t:unique`,
lines 1829–1855. -/
theorem exists_pos_mem_spectrum_of_unique_ground_state {L q : ℕ} (hq : 2 ≤ q) (hL : 1 ≤ L)
    {H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hH : H.IsHermitian) {gamma : ℝ}
    (hgamma : 0 < gamma) (Γ : EuclideanSpace ℂ (Fin L → Fin q))
    (huniq : ∀ x : EuclideanSpace ℂ (Fin L → Fin q), H *ᵥ x.ofLp = 0 → x ∈ ℂ ∙ Γ)
    (hgap : ∀ z ∈ spectrum ℝ H, z = 0 ∨ gamma ≤ z) :
    ∃ nu ∈ spectrum ℝ H, 0 < nu := by
  by_contra hnot
  push Not at hnot
  have hzero : hH.eigenvalues = 0 := by
    funext j
    have hmem := hH.eigenvalues_mem_spectrum_real j
    rcases hgap _ hmem with h | h
    · exact h
    · exact absurd (hnot _ hmem) (not_le.mpr (hgamma.trans_le h))
  have hH0 : H = 0 := hH.eigenvalues_eq_zero_iff.mp hzero
  have htop : (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) ≤ ℂ ∙ Γ := by
    intro x _
    exact huniq x (by simp [hH0])
  have hle := Submodule.finrank_mono htop
  rw [finrank_top, finrank_euclideanSpace, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin] at hle
  have hspan : Module.finrank ℂ (ℂ ∙ Γ) ≤ 1 := by
    simpa using finrank_span_le_card (R := ℂ) ({Γ} : Set (EuclideanSpace ℂ (Fin L → Fin q)))
  have hpow : q ≤ q ^ L := Nat.le_self_pow (by omega) q
  omega

open Classical in
/-- **A merge tree of length-independent node dimension for a unique frustration-free ground
state.** Let `H = ∑ hᵢ` be a nearest-neighbour chain of `L ≥ 1` sites of local dimension
`q ≥ 2` with `0 ≤ hᵢ ≤ 1`, frustration free with ground state `Γ ≠ 0` (`H Γ = 0`), unique
(every vector of the kernel is a multiple of `Γ`), and with spectral gap `γ > 0` (every other
spectral value is at least `γ`). With one universal constant `C ≥ 1`, put `g = min (γ, 1)`,
`m = max (q, 50)`, `v = 1 + log m + log (1/g)`, `ℓ = ⌈C v² / g⌉`, `D = (m ℓ²)^{22ℓ}` and
leaf width `4ℓ`. One family of at most `D²` operators is fixed on every long interval. For
every `η > 0` and every `0 < β < 1`, with `s = ⌈4096 (1 + log D + log (1/β))⌉` and
`count = D⁶ s³`, there is a merge tree whose long parents are literal sampled-and-trimmed merges
with these families, whose node spaces are all `3/200`-viable for `ℂ Γ` of dimension at most
`count`, and whose root, after its raw-filter-and-trim iterates and Ritz extraction, gives a
line mutually `η/2`-close to `ℂ Γ` of matrix product states. The bound `count` does not depend
on `L`.

Existence form of ALVV, arXiv:1602.08828v2, Theorem `t:unique`, lines 1829–1855, under the
scope restriction of this module; the running time is not formalized. -/
theorem exists_unique_ground_state_tree_ritz_approximation :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (L q : ℕ), 2 ≤ q → 1 ≤ L →
    ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (_hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2)))
      (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1) (gamma : ℝ), 0 < gamma →
    ∀ Γ : EuclideanSpace ℂ (Fin L → Fin q),
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    Γ ≠ 0 → H *ᵥ Γ.ofLp = 0 →
    (∀ x : EuclideanSpace ℂ (Fin L → Fin q), H *ᵥ x.ofLp = 0 → x ∈ ℂ ∙ Γ) →
    (∀ z ∈ spectrum ℝ H, z = 0 ∨ gamma ≤ z) →
    let G := ℂ ∙ Γ
    let g := min gamma 1
    let Kraw := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (1 - ‖H‖⁻¹ • H)
    let m := max q 50
    let v := 1 + Real.log (m : ℝ) + Real.log (1 / g)
    let ell : ℕ := Nat.ceil (C * v ^ 2 / g)
    let Dfilter := (m * ell ^ 2) ^ (22 * ell)
    let width := 4 * ell
    ∃ hwidth : 1 ≤ width,
    ∃ (Nfam : LongIntervalIndex L width → ℕ)
      (F : ∀ J : LongIntervalIndex L width,
        Fin (Nfam J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
          EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)),
      (∀ J, Nfam J ≤ Dfilter ^ 2) ∧
      ∀ eta : ℝ, 0 < eta → ∀ beta : ℝ, 0 < beta → beta < 1 →
      let s := Nat.ceil (4096 * (1 + Real.log (Dfilter : ℝ) + Real.log (1 / beta)))
      let count := Dfilter ^ 6 * s ^ 3
      ∃ (xi : ℝ) (n Bout : ℕ) (operation : IntervalMergeOperation L q), 0 < xi ∧
        (∀ (J : LongIntervalIndex L width) (k : ℕ) (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2)
          (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
          (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q))),
          Submodule.IsViable (3 / 200 : ℝ) S1
            (G.map (Entropy.regionTensorCoordinates q
              (interval L J.val.1 k)).toLinearEquiv.toLinearMap) →
          Submodule.IsViable (3 / 200 : ℝ) S2
            (G.map (Entropy.regionTensorCoordinates q
              (interval L k J.val.2)).toLinearEquiv.toLinearMap) →
          Module.finrank ℂ S1 ≤ count → Module.finrank ℂ S2 ≤ count →
          ∃ V : Matrix.unitaryGroup
            (Fin (Module.finrank ℂ (adjacentIntervalMerge L q
              J.val.1 k J.val.2 hpk hkr S1 S2))) ℂ,
            operation J.val.1 k J.val.2 hpk hkr S1 S2 =
              sampledIntervalTrim L q J.val.1 J.val.2 (F J)
                (Nat.clog Dfilter (Dfilter ^ 2 * s)) s xi
                (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2) V) ∧
        (∀ p r : ℕ, p ≤ r → r ≤ L →
          let S := balancedIntervalSpace operation width hwidth p r
          Submodule.IsViable (3 / 200 : ℝ) S
            (G.map (Entropy.regionTensorCoordinates q
              (interval L p r)).toLinearEquiv.toLinearMap) ∧
          Module.finrank ℂ S ≤ count) ∧
        let S0 := balancedIntervalSpace operation width hwidth 0 L
        let S := fullIntervalFilterTrimIterate L q Kraw xi S0 n
        let W := nativeFullIntervalSpace L q S
        let R := W.ritzSubspace (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) 1
        Module.finrank ℂ S ≤ count ∧ R ≤ W ∧ Module.finrank ℂ R = 1 ∧
          Submodule.IsCloseTo (eta / 2) G R ∧ Submodule.IsCloseTo (eta / 2) R G ∧
          ∀ w ∈ R, IsOpenMPS L q Bout (fun x ↦ w x) := by
  classical
  obtain ⟨C, Ktree, Kref, hC, -, -, hall⟩ := exists_physical_dg_tree_ritz_approximation
  refine ⟨C, hC, ?_⟩
  intro L q hq hL h hsupp h0 h1 gamma hgamma Γ H hH hΓ0 hΓ huniq hgap
    G g Kraw m v ell Dfilter width
  obtain ⟨nu, hnu, hnu0⟩ :=
    exists_pos_mem_spectrum_of_unique_ground_state hq hL hH hgamma Γ huniq hgap
  have hGeq := spectralSpanLE_zero_eq_span_singleton hH hgamma Γ hΓ huniq hgap
  have hmu := zero_mem_spectrum_of_mulVec_eq_zero hH hgamma Γ hΓ0 hΓ hgap
  have hgap' : ∀ z ∈ spectrum ℝ H, z = 0 ∨ 0 + gamma ≤ z := by
    simpa only [zero_add] using hgap
  have key := hall L q h hsupp h0 h1 0 nu gamma hgamma hmu hnu hnu0 hgap'
  have hrank : Module.finrank ℂ (ℂ ∙ Γ) = 1 := finrank_span_singleton hΓ0
  dsimp only at key
  rw [hGeq, hrank] at key
  simp only [Nat.cast_one, Real.log_one, add_zero, one_mul, mul_one, one_pow] at key
  obtain ⟨hell, -, Btree, -, -, Nfam, F, hNfam, hrest⟩ := key
  refine ⟨by simp only [width, ell, m, v, g] at hell ⊢; omega, Nfam, F, hNfam, ?_⟩
  intro eta heta beta hbeta hbeta1 s count
  obtain ⟨B, -, -, Uref, -, -, -, -, hxi, -, -, hfinal⟩ := hrest eta heta
  obtain ⟨-, operation, hliteral, hspaces, -, -, hdimS, hRW, hdimR, hGR, hRG, hmps⟩ :=
    hfinal beta hbeta hbeta1
  have e1 : (1 : ℕ) ^ 2 * Btree = Btree := by simp
  have e2 : (1 : ℕ) ^ 2 * B = B := by simp
  rw [e1, e2] at hdimS hdimR
  exact ⟨_, _, _, operation, hxi, hliteral, fun p r hpr hrL ↦
    ⟨(hspaces p r hpr hrL).1, (hspaces p r hpr hrL).2.1⟩, hdimS, hRW, hdimR, hGR, hRG, hmps⟩

end TNLean.MPS.AreaLaw.ALVV
