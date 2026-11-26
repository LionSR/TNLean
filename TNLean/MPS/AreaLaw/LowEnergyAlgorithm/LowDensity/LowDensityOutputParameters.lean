/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Log
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.LowDensity.PhysicalLDTreeRefinement
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.LowDensity.PhysicalLDTreeNode
import QICLean.Spectral.LowEnergy.WindowExtraction

/-!
# Scalar choices for the output clause of the low-density algorithm

ALVV, arXiv:1602.08828v2, Theorem `t:alg2`, lines 1869–1878, outputs states of energy at most
`E₀ + η - μ + δ`. The refinement of the low-density tree bounds the energy of its Ritz vectors
by `E₀ + ((1 + 1/ρ) x + (1 + ρ) A δ') / (1 - δ')` for every `ρ > 0`, where `x` is the top of the
shortened window, `A = ‖H - E₀‖` and `δ'` the accuracy of the refinement. This file chooses `ρ`
and `δ'` from the printed `δ`, so that the bound is at most `x + δ`, and compares the shortened
window with the printed `η - μ` for the source's buffer `w = μ / (3 log n)`.

It also contains the following results.

* `TNLean.MPS.AreaLaw.ALVV.exists_orthonormal_ritz_energy_le`,
  `TNLean.MPS.AreaLaw.ALVV.exists_low_density_tree_algorithm_output`: the output clause of the
  low-density algorithm.
* `TNLean.MPS.AreaLaw.exists_low_density_tree_algorithm`: the merge-tree algorithm for a low-density
  spectrum.
-/

section LowDensityOutputParameters

namespace TNLean.MPS.AreaLaw.ALVV

/-- For `x ≥ 0`, `A ≥ 0` and `δ > 0`, the choice `ρ = 3x/δ + 1` and
`δ' = min (1/2) (δ / (3 ((1 + ρ) A + x + δ + 1)))` gives `0 < δ' < 1` and
`((1 + 1/ρ) x + (1 + ρ) A δ') / (1 - δ') ≤ x + δ`. Auxiliary to ALVV, arXiv:1602.08828v2,
Theorem `t:alg2`, lines 1869–1878. -/
theorem low_density_output_accuracy {x A δ : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A) (hδ : 0 < δ) :
    let ρ := 3 * x / δ + 1
    let d := min (1 / 2) (δ / (3 * ((1 + ρ) * A + x + δ + 1)))
    0 < ρ ∧ 0 < d ∧ d < 1 ∧ ((1 + 1 / ρ) * x + (1 + ρ) * A * d) / (1 - d) ≤ x + δ := by
  intro ρ d
  have hρ1 : 1 ≤ ρ := by
    have : 0 ≤ 3 * x / δ := by positivity
    dsimp only [ρ]; linarith
  have hρ : 0 < ρ := by linarith
  have hden : 0 < 3 * ((1 + ρ) * A + x + δ + 1) := by positivity
  have hd0 : 0 < d := lt_min (by norm_num) (by positivity)
  have hdhalf : d ≤ 1 / 2 := min_le_left _ _
  have hd1 : d < 1 := by linarith
  refine ⟨hρ, hd0, hd1, ?_⟩
  have hdle : d ≤ δ / (3 * ((1 + ρ) * A + x + δ + 1)) := min_le_right _ _
  have hdmul : d * (3 * ((1 + ρ) * A + x + δ + 1)) ≤ δ := by
    rwa [le_div_iff₀ hden] at hdle
  -- `x / ρ ≤ δ / 3`
  have hxρ : x / ρ ≤ δ / 3 := by
    have h3 : 3 * x / δ ≤ ρ := by dsimp only [ρ]; linarith
    have h3' : 3 * x ≤ ρ * δ := (div_le_iff₀ hδ).mp h3
    rw [div_le_iff₀ hρ]
    linarith
  have hp1 : 0 ≤ d * ((1 + ρ) * A + 1) := by positivity
  have hp2 : 0 ≤ d * (x + δ + 1) := by positivity
  have hA' : (1 + ρ) * A * d ≤ δ / 3 := by linarith
  have hxd : (x + δ) * d ≤ δ / 3 := by linarith
  rw [div_le_iff₀ (by linarith)]
  have h1 : (1 + 1 / ρ) * x = x + x / ρ := by ring
  rw [h1]
  nlinarith

/-- The source's buffer `w = μ / (3 log L)`, with the natural logarithm, shortens the window by
at least `μ` over `⌈log₂ L⌉ + 1` levels: `μ ≤ 3w (⌈log₂ L⌉ + 1)` for `L ≥ 2` and `μ ≥ 0`.
Auxiliary to ALVV, arXiv:1602.08828v2, Theorem `t:alg2`, lines 1869–1878. -/
theorem source_buffer_le_window_shortening {L : ℕ} (hL : 2 ≤ L) {μ : ℝ} (hμ : 0 ≤ μ) :
    μ ≤ 3 * (μ / (3 * Real.log L)) * ((Nat.clog 2 L : ℝ) + 1) := by
  have hLR : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hlog : 0 < Real.log L := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- `log L ≤ clog₂ L · log 2 ≤ clog₂ L + 1`
  have hpow : (L : ℝ) ≤ 2 ^ Nat.clog 2 L := by exact_mod_cast Nat.le_pow_clog (by norm_num) L
  have hlogpow : Real.log L ≤ (Nat.clog 2 L : ℝ) * Real.log 2 := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by linarith) hpow
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hc : 0 ≤ (Nat.clog 2 L : ℝ) := Nat.cast_nonneg _
  have hkey : Real.log L ≤ (Nat.clog 2 L : ℝ) + 1 := by nlinarith
  rw [show 3 * (μ / (3 * Real.log L)) = μ / Real.log L by field_simp]
  rw [div_mul_eq_mul_div, le_div_iff₀ hlog]
  nlinarith

/-- The energy bound of the low-density output, `E₀ + (η - 3w) + δ` with
`η = η_LD - 3w ⌈log₂ L⌉`, is at most the printed `E₀ + η_LD - μ + δ` for the source's buffer
`w = μ / (3 log L)`, `L ≥ 2` and `μ ≥ 0`. ALVV, arXiv:1602.08828v2, Theorem `t:alg2`,
lines 1869–1870. -/
theorem shortened_window_le_source_window {L : ℕ} (hL : 2 ≤ L) {μ : ℝ} (hμ : 0 ≤ μ)
    (etaLD E₀ δ : ℝ) :
    let w := μ / (3 * Real.log L)
    E₀ + ((etaLD - 3 * w * Nat.clog 2 L) - 3 * w) + δ ≤ E₀ + (etaLD - μ) + δ := by
  intro w
  have h := source_buffer_le_window_shortening hL hμ
  linarith

end TNLean.MPS.AreaLaw.ALVV

end LowDensityOutputParameters

section LowDensityTreeAlgorithm

/-!
## The merge-tree algorithm for a low-density spectrum

This assembles the existence content of ALVV, arXiv:1602.08828v2,
Theorem `t:alg2`, lines 1869–1878, from its three stages, each applied to
the output of the previous one.

1. The sampled merge tree is run with the low-density word families on every
   long interval, with a window that shrinks by `3w` at each level. Every node
   is viable for the window of its level and has dimension at most `D^6 s^3`.
2. Its root is refined, for every `0 < δ < 1`, by one more application of the
   words on the whole chain and a collective trim. The output `R` is `δ`-close
   to the window `G(η - 3w)` with `η = etaLD - 3w · clog₂ L`, and consists of
   matrix product states.
3. Inside `R`, the projection of the window has the dimension of the window
   and is `δ`-close to it in both directions, and the Ritz space of the same
   dimension of the Hamiltonian compressed to `R` has energies at most
   `E₀ + ((1 + 1/ρ)(η - 3w) + (1 + ρ) ‖H - E₀‖ δ)/(1 - δ)` for every `ρ > 0`.
   Both consist of matrix product states, as subspaces of `R`.

Assumption (LD), lines 281–284, enters only through the fixed bandwidth
`etaLD`; the window dimension `dim G(etaLD)` sets the sample size.

**Scope restriction (existence of the algorithm's output):** The statement
asserts successful samples, not a success probability or a running time. The
tree has full leaves and one final trim per node, and the Ritz space is
controlled only in energy, because the window has no gap at its edge. The
energy-output and number-of-states clause of lines 1869–1878 is not verified
against the source, whose text is not in the repository; no hypothesis is drawn
from a paraphrase of it. See `docs/paper-gaps/alvv16_low_energy_family_scope.tex`.

**Local fix (buffer and levels):** The buffer `w` is free, subject to
`3w (clog₂ L + 2) ≤ etaLD`. With the source's buffer `w = μ / (3 log n)` this
holds once `μ` is at most a fixed fraction of `etaLD` (`log 2 / 4` for the
natural logarithm, `1/4` for the binary one), a constant factor stricter than
a nonempty shortened window. See
`docs/paper-gaps/alvv16_low_energy_family_scope.tex`.
-/

open ManyBody (interval)

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.MPS.AreaLaw

open Matrix

/-- The merge-tree algorithm for a low-density spectrum, as an existence
statement. The original nearest-neighbour Hamiltonian determines one
low-density family on every long interval. For a buffer `w` with
`3w (clog₂ L + 2) ≤ etaLD` there is a reference bond and, for every failure
parameter, an actual sampled tree whose nodes are viable for the windows of
their levels. For every `0 < δ < 1`, the refinement `R` of its root is
`δ`-close to the window `G(η - 3w)`, its vectors are matrix product states,
and inside `R` the projected window and the Ritz space of the window's
dimension satisfy the displayed closeness and energy bounds. ALVV,
arXiv:1602.08828v2, Theorem `t:alg2`, lines 1869–1878, with Theorem `t:alg1`,
lines 1777–1817, and the families of Theorem `t:aisgapless`, lines 1027–1041.
The energy-output clause of the source is not verified. -/
theorem exists_low_density_tree_algorithm (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ C Cr K : ℝ, 100 ≤ C ∧ 19 + etaLD ≤ C ∧ 100 ≤ Cr ∧ 0 < K ∧
      ∀ (L q m : ℕ) (w : ℝ) (hq : 2 ≤ q), q ≤ m → 0 < w →
      let mi := 4 * m
      let g := min w 1
      let u := 1 + Real.log (mi : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈C * u ^ 2 / g⌉₊
      let D := (mi * ell ^ 2) ^ (22 * ell)
      ∀ (Φ : ManyBody.BondInteraction L q),
      ∀ (h0 : ∀ i, 0 ≤ Φ.term i), (∀ i, Φ.term i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := Φ.hamiltonian
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      let G := fun eta : ℝ ↦ Submodule.spectralSpanLE
        hRaw.eigenvectorBasis hRaw.eigenvalues (minEigenvalue hRaw + eta)
      let rG := Module.finrank ℂ (G etaLD)
      ∃ _hell : 21 ≤ ell,
      Real.log (D : ℝ) ≤ 22 * (C + 1) * (6 + 2 * Real.log (C + 1)) / g * u ^ 3 ∧
      let width := 4 * ell
      let hwidth : 1 ≤ width := by omega
      let target := fun p r : ℕ ↦ G (etaLD - 3 * w * Nat.clog 2 (r - p))
      ∃ (N : LongIntervalIndex L width → ℕ)
        (F : ∀ J : LongIntervalIndex L width,
          Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
            EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)),
        (∀ J, N J ≤ D ^ 2) ∧
        (3 * w * ((Nat.clog 2 L : ℝ) + 1) ≤ etaLD →
        ∃ Dref : ℕ, 1 ≤ Dref ∧
        let xi := 1 / (1000 * (Dref : ℝ) * Real.sqrt ((L : ℝ) + 1))
        ∀ beta : ℝ, 0 < beta → beta < 1 →
        let A := 1 + Real.log (rG : ℝ) + Real.log (D : ℝ) + Real.log (1 / beta)
        let s := Nat.ceil (4096 * (rG : ℝ) * A)
        let count := D ^ 6 * s ^ 3
        (s : ℝ) ≤ 4097 * (rG : ℝ) * A ∧
        ∃ operation : IntervalMergeOperation L q,
          (∀ (J : LongIntervalIndex L width) (k : ℕ) (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2),
            k = J.val.1 + (J.val.2 - J.val.1) / 2 →
            ∀ (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
              (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q))),
            Submodule.IsViable (3 / 200 : ℝ) S1
              ((target J.val.1 k).map (Entropy.regionTensorCoordinates q
                (interval L J.val.1 k)).toLinearEquiv.toLinearMap) →
            Submodule.IsViable (3 / 200 : ℝ) S2
              ((target k J.val.2).map (Entropy.regionTensorCoordinates q
                (interval L k J.val.2)).toLinearEquiv.toLinearMap) →
            Module.finrank ℂ S1 ≤ count → Module.finrank ℂ S2 ≤ count →
            ∃ U : Matrix.unitaryGroup
              (Fin (Module.finrank ℂ (adjacentIntervalMerge L q
                J.val.1 k J.val.2 hpk hkr S1 S2))) ℂ,
              operation J.val.1 k J.val.2 hpk hkr S1 S2 =
                sampledIntervalTrim L q J.val.1 J.val.2 (F J) (Nat.clog D (D ^ 2 * s)) s xi
                  (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2) U) ∧
          (∀ p r : ℕ, p ≤ r → r ≤ L →
            let S := balancedIntervalSpace operation width hwidth p r
            Submodule.IsViable (3 / 200 : ℝ) S
              ((target p r).map (Entropy.regionTensorCoordinates q
                (interval L p r)).toLinearEquiv.toLinearMap) ∧
            Module.finrank ℂ S ≤ count ∧ IsIntervalSpanWithRankBound L q p r count xi S) ∧
          let S0 := balancedIntervalSpace operation width hwidth 0 L
          Submodule.IsCloseTo (3 / 200 : ℝ) (nativeFullIntervalSpace L q S0)
            (G (etaLD - 3 * w * Nat.clog 2 L)) ∧
          (∀ v ∈ S0, IsOpenMPS L q (1000000 * Dref ^ 2 * (L + 1) * count ^ 2)
            (fullIntervalRead L q v)) ∧
          (3 * w * ((Nat.clog 2 L : ℝ) + 2) ≤ etaLD →
          let eta := etaLD - 3 * w * Nat.clog 2 L
          ∀ delta : ℝ, 0 < delta → delta < 1 →
          let iδ := Nat.clog 16 ⌈1 / delta⌉₊
          let mδ := m * 2 ^ iδ
          let uδ := 1 + Real.log (mδ : ℝ) + Real.log (1 / g)
          let ellδ : ℕ := ⌈Cr * uδ ^ 2 / g⌉₊
          let Dδ := (mδ * ellδ ^ 2) ^ (22 * ellδ)
          let aδ := Nat.clog 2 ⌈32 / delta⌉₊
          let v := etaLD - (eta - 3 * w)
          let rInner := Module.finrank ℂ (G (eta - 3 * w))
          let gRef := min (min v (etaLD / 2) / 6) 1
          let uRef := 1 + Real.log (q : ℝ) + Real.log (1 / gRef)
          let aRef := 16 + Real.log (1 / gRef) +
            Real.log (1024 * ((L : ℝ) + 1) * ((rInner : ℝ) + 1) / (delta / 48))
          ∃ B : ℕ, 1 ≤ B ∧ Real.log (B : ℝ) ≤
            K * (uRef ^ 3 / gRef + (1 / gRef) ^ (1 / 4 : ℝ) * aRef ^ (3 / 4 : ℝ) * uRef) *
              (1 + Real.log aRef) ∧
          let DrefR := rInner * rG * B
          let xiR := delta / (16 * (DrefR : ℝ) * Real.sqrt ((L : ℝ) + 1))
          let M := max (q ^ (4 * ellδ)) (Dδ ^ (2 * aδ) * count)
          let bond := M * ⌈256 * (DrefR : ℝ) ^ 2 * ((L : ℝ) + 1) * M / delta ^ 2⌉₊
          ∃ R : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q)),
            ((L ≤ 4 * ellδ ∧ R = ⊤) ∨
              ∃ (Nδ : ℕ) (Fδ : Fin Nδ → EuclideanSpace ℂ (interval L 0 L → Fin q) →L[ℂ]
                  EuclideanSpace ℂ (interval L 0 L → Fin q)),
                Nδ ≤ Dδ ^ 2 ∧
                R = intervalTrimSubspace L q 0 L xiR (fun k ↦
                  (stdOrthonormalBasis ℂ ↥(⨆ x : Fin aδ → Fin Nδ,
                    S0.map ((List.ofFn (fun j ↦ Fδ (x j))).prod :
                      EuclideanSpace ℂ (interval L 0 L → Fin q) →ₗ[ℂ]
                        EuclideanSpace ℂ (interval L 0 L → Fin q)) :
                      Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))) k :
                    EuclideanSpace ℂ (interval L 0 L → Fin q)))) ∧
            let Rn := nativeFullIntervalSpace L q R
            let Gw := G (eta - 3 * w)
            let V := Gw.map Rn.starProjection.toLinearMap
            let Rz := Rn.ritzSubspace (Matrix.isSymmetric_toEuclideanLin_iff.mpr hRaw)
              (Module.finrank ℂ Gw)
            let A0 := ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
              (H - (minEigenvalue hRaw : ℂ) • 1)‖
            Submodule.IsCloseTo delta Rn Gw ∧
            (∀ y ∈ Rn, IsOpenMPS L q bond (fun x ↦ y x)) ∧
            V ≤ Rn ∧ Module.finrank ℂ V = Module.finrank ℂ Gw ∧
            Submodule.IsCloseTo delta V Gw ∧ Submodule.IsCloseTo delta Gw V ∧
            Rz ≤ Rn ∧ Module.finrank ℂ Rz = Module.finrank ℂ Gw ∧
            ∀ ρ : ℝ, 0 < ρ → ∀ y ∈ Rz,
              (inner ℂ y (Matrix.toEuclideanLin H y)).re ≤
                (minEigenvalue hRaw + ((1 + 1 / ρ) * (eta - 3 * w) + (1 + ρ) * A0 * delta) /
                  (1 - delta)) * ‖y‖ ^ 2)) := by
  classical
  obtain ⟨Cr, K, hCr, _hCreta, hK, hrefine⟩ := exists_physical_ld_root_refinement etaLD hLD
  obtain ⟨C, hC, hCeta, htree⟩ := exists_physical_ld_sampled_interval_tree_of_clause etaLD hLD
    (fun L q m w hq Φ h0 count Dref S0 ↦
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := Φ.hamiltonian
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      let G := fun eta : ℝ ↦ Submodule.spectralSpanLE
        hRaw.eigenvectorBasis hRaw.eigenvalues (minEigenvalue hRaw + eta)
      let rG := Module.finrank ℂ (G etaLD)
      let g := min w 1
      Submodule.IsCloseTo (3 / 200 : ℝ) (nativeFullIntervalSpace L q S0)
        (G (etaLD - 3 * w * Nat.clog 2 L)) ∧
      (∀ v ∈ S0, IsOpenMPS L q (1000000 * Dref ^ 2 * (L + 1) * count ^ 2)
        (fullIntervalRead L q v)) ∧
      (3 * w * ((Nat.clog 2 L : ℝ) + 2) ≤ etaLD →
      let eta := etaLD - 3 * w * Nat.clog 2 L
      ∀ delta : ℝ, 0 < delta → delta < 1 →
      let iδ := Nat.clog 16 ⌈1 / delta⌉₊
      let mδ := m * 2 ^ iδ
      let uδ := 1 + Real.log (mδ : ℝ) + Real.log (1 / g)
      let ellδ : ℕ := ⌈Cr * uδ ^ 2 / g⌉₊
      let Dδ := (mδ * ellδ ^ 2) ^ (22 * ellδ)
      let aδ := Nat.clog 2 ⌈32 / delta⌉₊
      let v := etaLD - (eta - 3 * w)
      let rInner := Module.finrank ℂ (G (eta - 3 * w))
      let gRef := min (min v (etaLD / 2) / 6) 1
      let uRef := 1 + Real.log (q : ℝ) + Real.log (1 / gRef)
      let aRef := 16 + Real.log (1 / gRef) +
        Real.log (1024 * ((L : ℝ) + 1) * ((rInner : ℝ) + 1) / (delta / 48))
      ∃ B : ℕ, 1 ≤ B ∧ Real.log (B : ℝ) ≤
        K * (uRef ^ 3 / gRef + (1 / gRef) ^ (1 / 4 : ℝ) * aRef ^ (3 / 4 : ℝ) * uRef) *
          (1 + Real.log aRef) ∧
      let DrefR := rInner * rG * B
      let xiR := delta / (16 * (DrefR : ℝ) * Real.sqrt ((L : ℝ) + 1))
      let M := max (q ^ (4 * ellδ)) (Dδ ^ (2 * aδ) * count)
      let bond := M * ⌈256 * (DrefR : ℝ) ^ 2 * ((L : ℝ) + 1) * M / delta ^ 2⌉₊
      ∃ R : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q)),
        ((L ≤ 4 * ellδ ∧ R = ⊤) ∨
          ∃ (Nδ : ℕ) (Fδ : Fin Nδ → EuclideanSpace ℂ (interval L 0 L → Fin q) →L[ℂ]
              EuclideanSpace ℂ (interval L 0 L → Fin q)),
            Nδ ≤ Dδ ^ 2 ∧
            R = intervalTrimSubspace L q 0 L xiR (fun k ↦
              (stdOrthonormalBasis ℂ ↥(⨆ x : Fin aδ → Fin Nδ,
                S0.map ((List.ofFn (fun j ↦ Fδ (x j))).prod :
                  EuclideanSpace ℂ (interval L 0 L → Fin q) →ₗ[ℂ]
                    EuclideanSpace ℂ (interval L 0 L → Fin q)) :
                  Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))) k :
                EuclideanSpace ℂ (interval L 0 L → Fin q)))) ∧
        let Rn := nativeFullIntervalSpace L q R
        let Gw := G (eta - 3 * w)
        let V := Gw.map Rn.starProjection.toLinearMap
        let Rz := Rn.ritzSubspace (Matrix.isSymmetric_toEuclideanLin_iff.mpr hRaw)
          (Module.finrank ℂ Gw)
        let A0 := ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
          (H - (minEigenvalue hRaw : ℂ) • 1)‖
        Submodule.IsCloseTo delta Rn Gw ∧
        (∀ y ∈ Rn, IsOpenMPS L q bond (fun x ↦ y x)) ∧
        V ≤ Rn ∧ Module.finrank ℂ V = Module.finrank ℂ Gw ∧
        Submodule.IsCloseTo delta V Gw ∧ Submodule.IsCloseTo delta Gw V ∧
        Rz ≤ Rn ∧ Module.finrank ℂ Rz = Module.finrank ℂ Gw ∧
        ∀ ρ : ℝ, 0 < ρ → ∀ y ∈ Rz,
          (inner ℂ y (Matrix.toEuclideanLin H y)).re ≤
            (minEigenvalue hRaw + ((1 + 1 / ρ) * (eta - 3 * w) + (1 + ρ) * A0 * delta) /
              (1 - delta)) * ‖y‖ ^ 2))
    (by
      intro L q m w hq hqm hw Φ h0 h1 config H hRaw G count Dref S0 hroot hdim hrootMPS
      let : Nonempty (Fin L → Fin q) := config
      refine ⟨hroot, hrootMPS, fun hdepth ↦ ?_⟩
      intro eta delta hdelta hdelta1
      have hK0 : (0 : ℝ) ≤ Nat.clog 2 L := Nat.cast_nonneg _
      have heta6 : 6 * w ≤ eta := by dsimp only [eta]; nlinarith only [hdepth, hw, hK0]
      have hetaLD : eta ≤ etaLD := by dsimp only [eta]; nlinarith only [hw, hK0]
      obtain ⟨B, hB, hlogB, R, hdesc, hclose, _hspan, hRMPS⟩ :=
        hrefine L q m w hq hqm hw Φ h0 h1 eta heta6 hetaLD count S0 hroot hdim delta hdelta
          hdelta1.le
      refine ⟨B, hB, hlogB, R, hdesc, ?_⟩
      intro Rn Gw V Rz A0
      obtain ⟨hVR, hVdim, hVG, hGV, hRzR, hRzdim, henergy⟩ :=
        Matrix.window_extraction_of_isCloseTo hRaw (c := eta - 3 * w) (by linarith only [heta6, hw])
          hdelta.le hdelta1 Rn hclose
      refine ⟨hclose, ?_, hVR, hVdim, hVG, hGV, hRzR, hRzdim, henergy⟩
      rintro _ ⟨x, hx, rfl⟩
      exact hRMPS x hx)
  exact ⟨C, Cr, K, hC, hCeta, hCr, hK, htree⟩

end TNLean.MPS.AreaLaw

end LowDensityTreeAlgorithm

section LowDensityAlgorithmOutput

/-!
## The output clause of the low-density algorithm

ALVV, arXiv:1602.08828v2, Theorem 6.3 (`t:alg2`, lines 1869–1870), runs the merge tree of
Theorem `t:alg1` with the low-density improving families of Theorem `t:aisgapless`,
lines 1027–1041, under Assumption (LD), lines 282–284. It reads: "Let `H` be a local
Hamiltonian satisfying Assumption (LD), `η > 0` the associated energy parameter,
`μ = Ω(1/log n)` and `δ ≥ poly⁻¹(n)`. With probability at least `1 - 1/n` the set `{|z_i⟩}`
returned by LOW`(H, δ, (η, μ))` is an orthonormal set of `r` states each having energy at most
`ε₀ + η - μ + δ` with respect to `H`. The algorithm runs in time `2^{poly log(n)}`." Assumption
(LD), lines 282–284, defines `r`: "The dimension of the space of all eigenvectors of `H` with
eigenvalue in the range `[ε₀, ε₀ + η]`, for some constant `η > 0`, is `r = poly(n)`."

This file states the existence content with an output clause of that form. For every `δ` with
`0 < δ < 1` the refinement of the root of the sampled tree, at an accuracy chosen from `δ`,
contains `r' = dim G(η_LD - 3w (⌈log₂ L⌉ + 1))` orthonormal matrix product states in its Ritz
space, each of energy at most `E₀ + η_LD - 3w (⌈log₂ L⌉ + 1) + δ`. For the source's buffer
`w = μ / (3 log L)` the shortened window satisfies `η_LD - 3w (⌈log₂ L⌉ + 1) ≤ η_LD - μ`
(`source_buffer_le_window_shortening`), so these energies are at most the printed
`E₀ + η - μ + δ` with `η = η_LD` (`shortened_window_le_source_window`, in the form of the energy
bound below).

**Scope restriction (number of output states):** the number of states is the dimension
`r' = dim G(η_LD - 3w (⌈log₂ L⌉ + 1))` of the shortened window, whereas the printed count is
`r = dim G(η_LD)`. Since the shortened window lies inside `G(η_LD)`, `r' ≤ r`, with equality only
when `H` has no eigenvalue in `(E₀ + η_LD - 3w (⌈log₂ L⌉ + 1), E₀ + η_LD]`. Whether `r`
orthonormal states of energy at most `E₀ + η - μ + δ` can be extracted is not established; the
remark after the theorem, line 1880, derives the energy bound from "the closest vectors to
`H_{[ε₀, ε₀ + η - μ]}` in `W`", a space of dimension at most `dim G(η - μ)`. The states are an
orthonormal basis of the Ritz space of the refinement, not eigenstates, as that remark also
says. As in `LowDensityTreeAlgorithm`, the samples are asserted to exist rather than drawn
with a success probability, the tree has full leaves and one final trim per node, the buffer
satisfies `3w (⌈log₂ L⌉ + 2) ≤ η_LD`, and no running time is asserted. See
`docs/paper-gaps/alvv16_low_energy_family_scope.tex`.
-/

open ManyBody (interval)

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.MPS.AreaLaw.ALVV

open TNLean.MPS.AreaLaw Matrix

/-- If a subspace `R` is `δ'`-close to the window `G_c` of a Hermitian `H`, at the accuracy `δ'`
of `low_density_output_accuracy` chosen from `δ > 0`, then the Ritz space of `H` compressed to `R`
of dimension `dim G_c` has an orthonormal basis of vectors of energy at most `E₀ + c + δ`.
Auxiliary to ALVV, arXiv:1602.08828v2, Theorem `t:alg2`, lines 1869–1878. -/
theorem exists_orthonormal_ritz_energy_le {σ : Type*} [Fintype σ] [DecidableEq σ] [Nonempty σ]
    {H : Matrix σ σ ℂ} (hH : H.IsHermitian) {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ)
    (R : Submodule ℂ (EuclideanSpace ℂ σ)) :
    let Gc := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues (minEigenvalue hH + c)
    let A := ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ) (H - (minEigenvalue hH : ℂ) • 1)‖
    let ρ := 3 * c / δ + 1
    let d := min (1 / 2) (δ / (3 * ((1 + ρ) * A + c + δ + 1)))
    Submodule.IsCloseTo d R Gc →
    ∃ ψ : Fin (Module.finrank ℂ Gc) → EuclideanSpace ℂ σ,
      Orthonormal ℂ ψ ∧
      (∀ i, ψ i ∈ R.ritzSubspace (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH)
        (Module.finrank ℂ Gc)) ∧
      ∀ i, (inner ℂ (ψ i) (Matrix.toEuclideanLin H (ψ i))).re ≤ minEigenvalue hH + c + δ := by
  intro Gc A ρ d hR
  obtain ⟨hρ, hd0, hd1, hbound⟩ := low_density_output_accuracy hc (norm_nonneg _ : 0 ≤ A) hδ
  obtain ⟨-, -, -, -, -, hRzdim, henergy⟩ :=
    Matrix.window_extraction_of_isCloseTo hH hc hd0.le hd1 R hR
  set Rz := R.ritzSubspace (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) (Module.finrank ℂ Gc)
  let b := stdOrthonormalBasis ℂ Rz
  let ψ : Fin (Module.finrank ℂ Gc) → EuclideanSpace ℂ σ :=
    fun i ↦ Rz.subtypeₗᵢ (b (Fin.cast hRzdim.symm i))
  have hψ : Orthonormal ℂ ψ :=
    (b.orthonormal.comp_linearIsometry Rz.subtypeₗᵢ).comp _ (Fin.cast_injective _)
  have hψmem (i) : ψ i ∈ Rz := (b (Fin.cast hRzdim.symm i)).property
  refine ⟨ψ, hψ, hψmem, fun i ↦ ?_⟩
  have hE := henergy ρ hρ (ψ i) (hψmem i)
  rw [hψ.1 i, one_pow, mul_one] at hE
  linarith only [hE, hbound]

/-- **Theorem 6.3: the output of the low-density algorithm, as an existence statement.** With
the families, the reference bond and the sampled tree of `exists_low_density_tree_algorithm`,
and a buffer with `3w (⌈log₂ L⌉ + 2) ≤ η_LD`, for every `0 < δ < 1` there are a refinement
accuracy `0 < δ' < 1` and a refinement `R` of the root (the whole space, or the collective trim
of a word image of the root) that is `δ'`-close to the window `G(η - 3w)`,
`η = η_LD - 3w ⌈log₂ L⌉`, together with `dim G(η - 3w)` orthonormal vectors of the Ritz space of
`H` compressed to `R`. They are matrix product states and each has energy at most
`E₀ + (η - 3w) + δ`. ALVV, arXiv:1602.08828v2, Theorem `t:alg2`, lines 1869–1878, under the
scope restriction of this module. -/
theorem exists_low_density_tree_algorithm_output (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ C Cr K : ℝ, 100 ≤ C ∧ 19 + etaLD ≤ C ∧ 100 ≤ Cr ∧ 0 < K ∧
      ∀ (L q m : ℕ) (w : ℝ) (hq : 2 ≤ q), q ≤ m → 0 < w →
      let mi := 4 * m
      let g := min w 1
      let u := 1 + Real.log (mi : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈C * u ^ 2 / g⌉₊
      let D := (mi * ell ^ 2) ^ (22 * ell)
      ∀ (Φ : ManyBody.BondInteraction L q),
      ∀ (h0 : ∀ i, 0 ≤ Φ.term i), (∀ i, Φ.term i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := Φ.hamiltonian
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      let G := fun eta : ℝ ↦ Submodule.spectralSpanLE
        hRaw.eigenvectorBasis hRaw.eigenvalues (minEigenvalue hRaw + eta)
      let rG := Module.finrank ℂ (G etaLD)
      ∃ _hell : 21 ≤ ell,
      Real.log (D : ℝ) ≤ 22 * (C + 1) * (6 + 2 * Real.log (C + 1)) / g * u ^ 3 ∧
      let width := 4 * ell
      let hwidth : 1 ≤ width := by omega
      let target := fun p r : ℕ ↦ G (etaLD - 3 * w * Nat.clog 2 (r - p))
      ∃ (N : LongIntervalIndex L width → ℕ)
        (F : ∀ J : LongIntervalIndex L width,
          Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
            EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)),
        (∀ J, N J ≤ D ^ 2) ∧
        (3 * w * ((Nat.clog 2 L : ℝ) + 1) ≤ etaLD →
        ∃ Dref : ℕ, 1 ≤ Dref ∧
        let xi := 1 / (1000 * (Dref : ℝ) * Real.sqrt ((L : ℝ) + 1))
        ∀ beta : ℝ, 0 < beta → beta < 1 →
        let A := 1 + Real.log (rG : ℝ) + Real.log (D : ℝ) + Real.log (1 / beta)
        let s := Nat.ceil (4096 * (rG : ℝ) * A)
        let count := D ^ 6 * s ^ 3
        (s : ℝ) ≤ 4097 * (rG : ℝ) * A ∧
        ∃ operation : IntervalMergeOperation L q,
          (∀ (J : LongIntervalIndex L width) (k : ℕ) (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2),
            k = J.val.1 + (J.val.2 - J.val.1) / 2 →
            ∀ (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
              (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q))),
            Submodule.IsViable (3 / 200 : ℝ) S1
              ((target J.val.1 k).map (Entropy.regionTensorCoordinates q
                (interval L J.val.1 k)).toLinearEquiv.toLinearMap) →
            Submodule.IsViable (3 / 200 : ℝ) S2
              ((target k J.val.2).map (Entropy.regionTensorCoordinates q
                (interval L k J.val.2)).toLinearEquiv.toLinearMap) →
            Module.finrank ℂ S1 ≤ count → Module.finrank ℂ S2 ≤ count →
            ∃ U : Matrix.unitaryGroup
              (Fin (Module.finrank ℂ (adjacentIntervalMerge L q
                J.val.1 k J.val.2 hpk hkr S1 S2))) ℂ,
              operation J.val.1 k J.val.2 hpk hkr S1 S2 =
                sampledIntervalTrim L q J.val.1 J.val.2 (F J) (Nat.clog D (D ^ 2 * s)) s xi
                  (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2) U) ∧
          (∀ p r : ℕ, p ≤ r → r ≤ L →
            let S := balancedIntervalSpace operation width hwidth p r
            Submodule.IsViable (3 / 200 : ℝ) S
              ((target p r).map (Entropy.regionTensorCoordinates q
                (interval L p r)).toLinearEquiv.toLinearMap) ∧
            Module.finrank ℂ S ≤ count ∧ IsIntervalSpanWithRankBound L q p r count xi S) ∧
          let S0 := balancedIntervalSpace operation width hwidth 0 L
          Submodule.IsCloseTo (3 / 200 : ℝ) (nativeFullIntervalSpace L q S0)
            (G (etaLD - 3 * w * Nat.clog 2 L)) ∧
          (∀ v ∈ S0, IsOpenMPS L q (1000000 * Dref ^ 2 * (L + 1) * count ^ 2)
            (fullIntervalRead L q v)) ∧
          (3 * w * ((Nat.clog 2 L : ℝ) + 2) ≤ etaLD →
          let eta := etaLD - 3 * w * Nat.clog 2 L
          ∀ δ : ℝ, 0 < δ → δ < 1 →
          ∃ (delta : ℝ) (R : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))) (bond : ℕ)
            (ψ : Fin (Module.finrank ℂ (G (eta - 3 * w))) → EuclideanSpace ℂ (Fin L → Fin q)),
            0 < delta ∧ delta < 1 ∧
            (R = ⊤ ∨ ∃ (a Nδ : ℕ) (xiR : ℝ)
                (Fδ : Fin Nδ → EuclideanSpace ℂ (interval L 0 L → Fin q) →L[ℂ]
                  EuclideanSpace ℂ (interval L 0 L → Fin q)),
                R = intervalTrimSubspace L q 0 L xiR (fun k ↦
                  (stdOrthonormalBasis ℂ ↥(⨆ x : Fin a → Fin Nδ,
                    S0.map ((List.ofFn (fun j ↦ Fδ (x j))).prod :
                      EuclideanSpace ℂ (interval L 0 L → Fin q) →ₗ[ℂ]
                        EuclideanSpace ℂ (interval L 0 L → Fin q)) :
                      Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))) k :
                    EuclideanSpace ℂ (interval L 0 L → Fin q)))) ∧
            Submodule.IsCloseTo delta (nativeFullIntervalSpace L q R) (G (eta - 3 * w)) ∧
            Orthonormal ℂ ψ ∧
            (∀ i, ψ i ∈ (nativeFullIntervalSpace L q R).ritzSubspace
              (Matrix.isSymmetric_toEuclideanLin_iff.mpr hRaw)
              (Module.finrank ℂ (G (eta - 3 * w)))) ∧
            (∀ i, IsOpenMPS L q bond (fun x ↦ ψ i x)) ∧
            ∀ i, (inner ℂ (ψ i) (Matrix.toEuclideanLin H (ψ i))).re ≤
              minEigenvalue hRaw + (eta - 3 * w) + δ)) := by
  classical
  obtain ⟨Cr, K, hCr, _hCreta, hK, hrefine⟩ := exists_physical_ld_root_refinement etaLD hLD
  obtain ⟨C, hC, hCeta, htree⟩ := exists_physical_ld_sampled_interval_tree_of_clause etaLD hLD
    (fun L q m w hq Φ h0 count Dref S0 ↦
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := Φ.hamiltonian
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      let G := fun eta : ℝ ↦ Submodule.spectralSpanLE
        hRaw.eigenvectorBasis hRaw.eigenvalues (minEigenvalue hRaw + eta)
      Submodule.IsCloseTo (3 / 200 : ℝ) (nativeFullIntervalSpace L q S0)
        (G (etaLD - 3 * w * Nat.clog 2 L)) ∧
      (∀ v ∈ S0, IsOpenMPS L q (1000000 * Dref ^ 2 * (L + 1) * count ^ 2)
        (fullIntervalRead L q v)) ∧
      (3 * w * ((Nat.clog 2 L : ℝ) + 2) ≤ etaLD →
      let eta := etaLD - 3 * w * Nat.clog 2 L
      ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∃ (delta : ℝ) (R : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))) (bond : ℕ)
        (ψ : Fin (Module.finrank ℂ (G (eta - 3 * w))) → EuclideanSpace ℂ (Fin L → Fin q)),
        0 < delta ∧ delta < 1 ∧
        (R = ⊤ ∨ ∃ (a Nδ : ℕ) (xiR : ℝ)
            (Fδ : Fin Nδ → EuclideanSpace ℂ (interval L 0 L → Fin q) →L[ℂ]
              EuclideanSpace ℂ (interval L 0 L → Fin q)),
            R = intervalTrimSubspace L q 0 L xiR (fun k ↦
              (stdOrthonormalBasis ℂ ↥(⨆ x : Fin a → Fin Nδ,
                S0.map ((List.ofFn (fun j ↦ Fδ (x j))).prod :
                  EuclideanSpace ℂ (interval L 0 L → Fin q) →ₗ[ℂ]
                    EuclideanSpace ℂ (interval L 0 L → Fin q)) :
                  Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))) k :
                EuclideanSpace ℂ (interval L 0 L → Fin q)))) ∧
        Submodule.IsCloseTo delta (nativeFullIntervalSpace L q R) (G (eta - 3 * w)) ∧
        Orthonormal ℂ ψ ∧
        (∀ i, ψ i ∈ (nativeFullIntervalSpace L q R).ritzSubspace
          (Matrix.isSymmetric_toEuclideanLin_iff.mpr hRaw)
          (Module.finrank ℂ (G (eta - 3 * w)))) ∧
        (∀ i, IsOpenMPS L q bond (fun x ↦ ψ i x)) ∧
        ∀ i, (inner ℂ (ψ i) (Matrix.toEuclideanLin H (ψ i))).re ≤
          minEigenvalue hRaw + (eta - 3 * w) + δ))
    (by
      intro L q m w hq hqm hw Φ h0 h1 config H hRaw G count Dref S0 hroot hdim hrootMPS
      let : Nonempty (Fin L → Fin q) := config
      refine ⟨hroot, hrootMPS, fun hdepth ↦ ?_⟩
      intro eta δ hδ hδ1
      have hK0 : (0 : ℝ) ≤ Nat.clog 2 L := Nat.cast_nonneg _
      have heta6 : 6 * w ≤ eta := by dsimp only [eta]; nlinarith only [hdepth, hw, hK0]
      have hetaLD : eta ≤ etaLD := by dsimp only [eta]; nlinarith only [hw, hK0]
      have hx : 0 ≤ eta - 3 * w := by linarith only [heta6, hw]
      obtain ⟨-, hd0, hd1, -⟩ := low_density_output_accuracy hx
        (norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
          (H - (minEigenvalue hRaw : ℂ) • 1))) hδ
      obtain ⟨B, -, -, R, hdesc, hclose, -, hRMPS⟩ :=
        hrefine L q m w hq hqm hw Φ h0 h1 eta heta6 hetaLD count S0 hroot hdim _ hd0 hd1.le
      obtain ⟨bond, hRMPS⟩ : ∃ bond : ℕ, ∀ v ∈ R, IsOpenMPS L q bond (fullIntervalRead L q v) :=
        ⟨_, hRMPS⟩
      obtain ⟨ψ, hψ, hψmem, hψE⟩ :=
        exists_orthonormal_ritz_energy_le hRaw hx hδ (nativeFullIntervalSpace L q R) hclose
      refine ⟨_, R, bond, ψ, hd0, hd1, ?_, hclose, hψ, hψmem, fun i ↦ ?_, hψE⟩
      · rcases hdesc with ⟨-, hR⟩ | ⟨Nδ, Fδ, -, hR⟩
        · exact Or.inl hR
        · exact Or.inr ⟨_, Nδ, _, Fδ, hR⟩
      · obtain ⟨y, hy, hyψ⟩ := Submodule.ritzSubspace_le _ _ _ (hψmem i)
        rw [← hyψ]
        exact hRMPS y hy)
  exact ⟨C, Cr, K, hC, hCeta, hCr, hK, htree⟩

end TNLean.MPS.AreaLaw.ALVV

end LowDensityAlgorithmOutput
