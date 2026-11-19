/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowDensityTreeAlgorithm
import TNLean.MPS.AreaLaw.ALVV.LowDensityOutputParameters

/-!
# The output clause of the low-density algorithm

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
  obtain ⟨-, -, -, -, -, hRzdim, henergy⟩ := window_extraction_of_isCloseTo hH hc hd0.le hd1 R hR
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
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
      (∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2))) →
      ∀ (h0 : ∀ i, 0 ≤ h i), (∀ i, h i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := ∑ i, h i
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
    (fun L q m w hq h h0 count Dref S0 ↦
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := ∑ i, h i
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
      intro L q m w hq hqm hw h hs h0 h1 config H hRaw G count Dref S0 hroot hdim hrootMPS
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
        hrefine L q m w hq hqm hw h hs h0 h1 eta heta6 hetaLD count S0 hroot hdim _ hd0 hd1.le
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
