/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalLDTreeRefinement
import TNLean.MPS.AreaLaw.PhysicalLDTree
import TNLean.MPS.AreaLaw.LowDensityTreeExtraction

/-!
# The merge-tree algorithm for a low-density spectrum

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
        window_extraction_of_isCloseTo hRaw (c := eta - 3 * w) (by linarith only [heta6, hw])
          hdelta.le hdelta1 Rn hclose
      refine ⟨hclose, ?_, hVR, hVdim, hVG, hGV, hRzR, hRzdim, henergy⟩
      rintro _ ⟨x, hx, rfl⟩
      exact hRMPS x hx)
  exact ⟨C, Cr, K, hC, hCeta, hCr, hK, htree⟩

end TNLean.MPS.AreaLaw
