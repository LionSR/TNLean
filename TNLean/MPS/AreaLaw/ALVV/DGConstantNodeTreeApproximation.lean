/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.DGConstantNodeTree
import TNLean.MPS.AreaLaw.PhysicalDGAutomaticRefinement

/-!
# The refined root of the degenerate-gap tree of constant node dimension

ALVV, arXiv:1602.08828v2, Theorem `t:alg1`, lines 1777–1818, returns from the root of the merge
tree an `r`-dimensional space of matrix product states approximating the ground space of a chain
satisfying Assumption (DG). This file runs the final raw-filter-and-trim iteration and the Ritz
extraction on the root of the tree of `exists_physical_dg_constant_node_tree`, whose nodes have
dimension at most `D^{2k} s ≤ D² s²`, independent of the chain length.

**Local fix (rounding of the number of rounds):** the source, line 1797, takes
`k = ⌈log_D s⌉ / 2`, not an integer when `⌈log_D s⌉` is odd; the least integer `k` with
`D^{2k} ≥ s` gives the node bound `D² s²`, up to a factor `D` above the source's `D s²` in that
case. See `docs/paper-gaps/alvv16_approximation_parameters.tex`.

**Local fix (normalized gain):** the final iteration count is explicit in the projection target
`ρ`, which controls the Ritz energy; it is not the count printed in the source. See
`docs/paper-gaps/alvv16_final_filter_gain.tex`.

**Scope restriction (tree witness, block leaves, one final trim and capped gap):** the tree is a
recursive witness, with no joint sampling probability; leaves are full blocks of length at most
`4 ℓ`; each long node applies one collective trim after its `k` rounds; the parameters use
`min γ 1`; and the bond dimension of the output grows with `L` through the trimming threshold.
See `docs/paper-gaps/alvv16_approximation_parameters.tex`.
-/

open ManyBody (interval)

open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

open TNLean.MPS.AreaLaw TNLean.Lattice

/-- **The root of the degenerate-gap tree of constant node dimension, refined.** The original
ground space `G` of dimension `r` has an `r`-dimensional space of matrix product states, mutually
`η/2`-close to `G`, obtained from the root of the merge tree of node dimension
`count = D^{2k} s ≤ D² s²`, with `k = ⌈⌈log_D s⌉ / 2⌉` rounds at every merge, through its literal
raw-filter-and-trim iterates and the Ritz extraction. The families precede the precision, the
common trimming threshold, the sampling parameter and the child spaces; no viable space,
reference, family or trial energy is a hypothesis. The node bound does not depend on `L`.

Existence form of ALVV, arXiv:1602.08828v2, Theorem `t:alg1`, lines 1777–1818, under the local
fixes and the scope restriction of this module; the running time is not formalized. -/
theorem exists_physical_dg_constant_node_tree_ritz_approximation :
    ∃ C Ktree Kref : ℝ, 1 ≤ C ∧ 0 < Ktree ∧ 0 < Kref ∧ ∀ (L q : ℕ),
    ∀ (Φ : ManyBody.BondInteraction L q)
      (h0 : ∀ i, 0 ≤ Φ.term i) (_h1 : ∀ i, Φ.term i ≤ 1) (mu nu gamma : ℝ),
    0 < gamma →
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
    (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let rG := Module.finrank ℂ G
    let g := min gamma 1
    let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
    let A := ‖H‖ - mu
    let c := gamma / A
    let Kraw := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (1 - ‖H‖⁻¹ • H)
    let epsilonTree : ℝ := 1 / 10000
    let btree := 16 + Real.log (1 / g) +
      Real.log (32 * (rG : ℝ) * ((L : ℝ) + 1) / epsilonTree)
    let m := max q 50
    let v := 1 + Real.log (m : ℝ) + Real.log (1 / g)
    let ell : ℕ := Nat.ceil (C * v ^ 2 / g)
    let Dfilter := (m * ell ^ 2) ^ (22 * ell)
    ∃ _hell : 21 ≤ ell,
    Real.log (Dfilter : ℝ) ≤
      22 * (C + 1) * (6 + 2 * Real.log (C + 1)) / g * v ^ 3 ∧
    ∃ Btree : ℕ, 1 ≤ Btree ∧
    Real.log (Btree : ℝ) ≤
      Ktree * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * btree ^ (3 / 4 : ℝ) * u) *
        (1 + Real.log btree) ∧
    let Dtree := rG ^ 2 * Btree
    let width := 4 * ell
    let hwidth : 1 ≤ width := by omega
    ∃ (Nfam : LongIntervalIndex L width → ℕ)
      (F : ∀ J : LongIntervalIndex L width,
        Fin (Nfam J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
          EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)),
      (∀ J, Nfam J ≤ Dfilter ^ 2) ∧
      ∀ eta : ℝ, 0 < eta →
      let rho := eta * gamma / (2 * A + eta * gamma)
      let n := Nat.ceil (4 / c * Real.log (1 / rho)) + 1
      let epsilonRef := c ^ 2 * rho / 32768
      let bref := 16 + Real.log (1 / g) +
        Real.log (32 * (rG : ℝ) * ((L : ℝ) + 1) / epsilonRef)
      ∃ B : ℕ, 1 ≤ B ∧
      Real.log (B : ℝ) ≤
        Kref * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * bref ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log bref) ∧
      let b := rG ^ 2 * B
      let Dcommon := max Dtree b
      let N := Nat.ceil (100 * (Dfilter : ℝ) ^ 12 / (c * rho))
      let xi := 1 / (1000 * ((Dcommon * N : ℕ) : ℝ) * Real.sqrt ((L : ℝ) + 1))
      ∃ Uref : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
        Module.finrank ℂ Uref = rG ∧
        Submodule.IsCloseTo epsilonRef Uref G ∧ Submodule.IsCloseTo epsilonRef G Uref ∧
        (∀ w ∈ Uref, IsOpenMPS L q b (fun x ↦ w x)) ∧
        0 < xi ∧
        xi ≤ 1 / (1000 * (Dtree : ℝ) * Real.sqrt ((L : ℝ) + 1)) ∧
        Real.sqrt ((L : ℝ) * (rG : ℝ) * (b : ℝ)) * xi <
          eta / (10000 * (Dfilter : ℝ) ^ 12) ∧
        ∀ beta : ℝ, 0 < beta → beta < 1 →
        let sampleLog := 1 + Real.log (rG : ℝ) + Real.log (Dfilter : ℝ) + Real.log (1 / beta)
        let s := Nat.ceil (4096 * (rG : ℝ) * sampleLog)
        let k := (Nat.clog Dfilter s + 1) / 2
        let count := Dfilter ^ (2 * k) * s
        (s : ℝ) ≤ 4097 * (rG : ℝ) * sampleLog ∧ count ≤ Dfilter ^ 2 * s ^ 2 ∧
        ∃ operation : IntervalMergeOperation L q,
          (∀ (J : LongIntervalIndex L width) (j : ℕ) (hpj : J.val.1 ≤ j) (hjr : j ≤ J.val.2)
            (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 j → Fin q)))
            (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L j J.val.2 → Fin q))),
            Submodule.IsViable (3 / 200 : ℝ) S1
              (G.map (Entropy.regionTensorCoordinates q
                (interval L J.val.1 j)).toLinearEquiv.toLinearMap) →
            Submodule.IsViable (3 / 200 : ℝ) S2
              (G.map (Entropy.regionTensorCoordinates q
                (interval L j J.val.2)).toLinearEquiv.toLinearMap) →
            Module.finrank ℂ S1 ≤ count → Module.finrank ℂ S2 ≤ count →
            ∃ V : Matrix.unitaryGroup
              (Fin (Module.finrank ℂ (adjacentIntervalMerge L q
                J.val.1 j J.val.2 hpj hjr S1 S2))) ℂ,
              operation J.val.1 j J.val.2 hpj hjr S1 S2 =
                sampledIntervalTrim L q J.val.1 J.val.2 (F J)
                  k s xi
                  (adjacentIntervalMerge L q J.val.1 j J.val.2 hpj hjr S1 S2) V) ∧
          (∀ p r : ℕ, p ≤ r → r ≤ L →
            let S := balancedIntervalSpace operation width hwidth p r
            Submodule.IsViable (3 / 200 : ℝ) S
              (G.map (Entropy.regionTensorCoordinates q
                (interval L p r)).toLinearEquiv.toLinearMap) ∧
            Module.finrank ℂ S ≤ count ∧ IsIntervalSpanWithRankBound L q p r count xi S) ∧
          let S0 := balancedIntervalSpace operation width hwidth 0 L
          let S := fullIntervalFilterTrimIterate L q Kraw xi S0 n
          let W := nativeFullIntervalSpace L q S
          let R := W.ritzSubspace (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) rG
          0 < n ∧ Submodule.IsCloseTo rho W G ∧ Module.finrank ℂ S ≤ count ∧
            R ≤ W ∧ Module.finrank ℂ R = rG ∧
            Submodule.IsCloseTo (eta / 2) G R ∧ Submodule.IsCloseTo (eta / 2) R G ∧
            ∀ w ∈ R, IsOpenMPS L q
              (1000000 * (Dcommon * N) ^ 2 * (L + 1) * count ^ 2) (fun x ↦ w x) := by
  classical
  obtain ⟨C, Ktree, hC, hKtree, htree⟩ := exists_physical_dg_constant_node_tree
  obtain ⟨Kref, hKref, hrefine⟩ := exists_physical_dg_automatic_same_candidate_refinement
  refine ⟨C, Ktree, Kref, hC, hKtree, hKref, ?_⟩
  intro L q Φ h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G rG g u A c Kraw epsilonTree btree m v ell Dfilter
  obtain ⟨hell, hlogD, Btree, hBtree, hlogBtree, hfamilies⟩ :=
    htree L q Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  refine ⟨hell, hlogD, Btree, hBtree, hlogBtree, ?_⟩
  intro Dtree width hwidth
  have hrG : 1 ≤ rG := Submodule.one_le_finrank_iff.mpr
    (hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl)
  have hDtree : 1 ≤ Dtree := by
    dsimp only [Dtree]
    simpa only [one_mul] using Nat.mul_le_mul (Nat.one_le_pow 2 rG hrG) hBtree
  have hm : 1 ≤ m := (by decide : 1 ≤ 50).trans (Nat.le_max_right q 50)
  have hbase : 1 ≤ m * ell ^ 2 := by
    simpa only [one_mul] using Nat.mul_le_mul hm (Nat.one_le_pow 2 ell (by omega))
  have hDfilter : 1 ≤ Dfilter := Nat.one_le_pow (22 * ell) (m * ell ^ 2) hbase
  obtain ⟨Nfam, F, hNfam, hparents⟩ := hfamilies
  refine ⟨Nfam, F, hNfam, ?_⟩
  intro eta heta rho n epsilonRef bref
  obtain ⟨B, hB, hlogB, hfinal⟩ :=
    hrefine L q Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
      Dtree Dfilter hDtree hDfilter eta heta
  refine ⟨B, hB, hlogB, ?_⟩
  intro b Dcommon N xi
  obtain ⟨Uref, hdimU, hUG, hGU, hUMPS, hxi, hxiTree, hxiSource, hterminal⟩ := hfinal
  refine ⟨Uref, hdimU, hUG, hGU, hUMPS, hxi, hxiTree, hxiSource, ?_⟩
  intro beta hbeta hbeta1 sampleLog s k count
  obtain ⟨hscount, hcount2, operation, hliteral, hspaces⟩ :=
    hparents xi hxi hxiTree beta hbeta hbeta1
  refine ⟨hscount, hcount2, operation, hliteral, hspaces, ?_⟩
  let S0 := balancedIntervalSpace operation width hwidth 0 L
  have hroot := hspaces 0 L (Nat.zero_le L) le_rfl
  have hcloseRoot : Submodule.IsCloseTo (3 / 200 : ℝ) (nativeFullIntervalSpace L q S0) G :=
    (isViable_fullInterval_iff_isCloseTo S0 G).mp hroot.1
  exact hterminal count S0 hroot.2.1 hcloseRoot

end TNLean.MPS.AreaLaw.ALVV
