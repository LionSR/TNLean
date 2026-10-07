/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusWindowCornerRegion
import TNLean.PEPS.TorusGaugeUniqueness

/-!
# Gauge uniqueness from injective torus windows

Suppose two invertible edge gauge families give the same local tensor relation,
possibly with different site scalars whose torus-volume powers are one. Normal
positive-length arc windows for the second tensor imply that the edge matrices
are proportional at every edge, at torus sizes 2L + 1 by 2K + 1 or larger.

The proof translates a punctured corner rectangle so that the chosen edge crosses
its boundary. Both this region and its complement are injective. The local tensor
relations yield the same bare-edge insertion coefficients, and the injective
region comparison determines the conjugating matrix up to a nonzero scalar.

This is the uniqueness argument in arXiv:1804.04964, Theorem 3 and the normal TI
PEPS corollary, lines 1471 and 2297–2318 of `Papers/1804.04964/paper_normal.tex`.
The uniqueness statement applies to all positive window lengths; it requires no
lower bound of seven on either torus size.
-/

namespace TNLean.PEPS
variable {width height L K : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]

/-- The rightward edge from the omitted corner crosses the punctured rectangle. -/
private theorem isRegionBoundaryEdge_windowCornerRegion_right (hL : 0 < L)
    (hw : 2 * L + 1 ≤ width) (hh : 2 * K + 1 ≤ height) :
    IsRegionBoundaryEdge (G := torusGraph width height) (windowCornerRegion L K)
      (torusRightEdge (windowCornerVertex L K : TorusVertex width height)) := by
  have h1 : (windowCornerVertex L K : TorusVertex width height).1.val = L :=
    ZMod.val_cast_of_lt (by omega)
  have h2 : (windowCornerVertex L K : TorusVertex width height).2.val = K :=
    ZMod.val_cast_of_lt (by omega)
  obtain ⟨hf, hs⟩ := torusRightEdge_endpoints_of_lt
    (p := windowCornerVertex L K) (by rw [h1]; omega)
  rw [IsRegionBoundaryEdge, hf, hs]
  refine Or.inr ⟨windowCornerVertex_notMem hw hh, ?_⟩
  rw [mem_windowCornerRegion]
  have h3 : ((windowCornerVertex L K : TorusVertex width height).1 + 1).val =
      L + 1 := by
    rw [show (windowCornerVertex L K : TorusVertex width height).1 + 1 =
        ((L + 1 : ℕ) : ZMod width) by simp [windowCornerVertex]]
    exact ZMod.val_cast_of_lt (by omega)
  dsimp only
  omega


variable {d : ℕ}

/-- Every torus edge is a boundary edge of an injective translated corner region whose
complement is also injective, under the positive-window and minimal-size hypotheses. -/
private theorem exists_injective_region_boundary_of_normalArcWindows
    (B : Tensor (torusGraph width height) d)
    (hB : NormalTorusArcWindowInjectivityHypotheses L K (regionInjectivityDataOf B))
    (hBTI : IsTorusTranslationInvariant B)
    (hposB : ∀ e : Edge (torusGraph width height), 0 < B.bondDim e)
    (hL : 0 < L) (hK : 0 < K)
    (hw : 2 * L + 1 ≤ width) (hh : 2 * K + 1 ≤ height)
    (e : Edge (torusGraph width height)) :
    ∃ R : Finset (TorusVertex width height), IsRegionBoundaryEdge R e ∧
      RegionBlockedTensorInjective B R ∧ RegionBlockedTensorInjective B (Finset.univ \ R) := by
  classical
  let R : Finset (TorusVertex width height) := windowCornerRegion L K
  let q : TorusVertex width height := windowCornerVertex L K
  have hU := regionInjectivityUnionClosure_of_overlap B hposB
  have hR : RegionBlockedTensorInjective B R :=
    hB.windowCornerRegion_injective hU hL hK hw hh
  have hCR : RegionBlockedTensorInjective B (Finset.univ \ R) :=
    hB.compl_windowCornerRegion_injective hU hL hK hw hh
  have htr (a : ZMod width) (b : ZMod height) (e₀ : Edge (torusGraph width height))
      (hb : IsRegionBoundaryEdge R e₀) (he : Edge.map (translate a b) e₀ = e) :
      ∃ Q : Finset (TorusVertex width height), IsRegionBoundaryEdge Q e ∧
        RegionBlockedTensorInjective B Q ∧
        RegionBlockedTensorInjective B (Finset.univ \ Q) := by
    have hmapinj (Q : Finset (TorusVertex width height))
        (hQ : RegionBlockedTensorInjective B Q) :
        RegionBlockedTensorInjective B (Region.map (translate a b) Q) :=
      regionBlockedTensorInjective_translate hBTI a b Q hQ
    refine ⟨Region.map (translate a b) R, ?_, hmapinj R hR, ?_⟩
    · rw [← he]
      exact (isRegionBoundaryEdge_map (translate a b) R e₀).mpr hb
    · rw [← Region_map_compl]
      exact hmapinj _ hCR
  rcases torusEdge_horizontal_or_vertical e with he | he
  · obtain ⟨p, rfl⟩ := isHorizontalTorusEdge_eq_rightEdge he
    apply htr (p.1 - q.1) (p.2 - q.2) (torusRightEdge q)
      (isRegionBoundaryEdge_windowCornerRegion_right hL hw hh)
    rw [← translateEdge_eq_map, translateEdge_torusRightEdge]
    congr 1
    apply Prod.ext <;> simp
  · obtain ⟨p, rfl⟩ := isVerticalTorusEdge_eq_upEdge he
    apply htr (p.1 - q.1) (p.2 - q.2) (torusUpEdge q)
      (isRegionBoundaryEdge_windowCornerRegion hK hw hh)
    rw [← translateEdge_eq_map, translateEdge_torusUpEdge]
    congr 1
    apply Prod.ext <;> simp


/-- If two edge gauge families give local tensor relations with volume-one scalar powers,
their matrices are proportional at each edge. Only the second tensor needs positive-length
normal arc windows, translation invariance and positive bond dimensions. The torus sizes
are the minimal window bounds.

Source: arXiv:1804.04964, Theorem 3 and the normal TI PEPS corollary, lines 1471 and
2297–2318 of `Papers/1804.04964/paper_normal.tex` (uniqueness up to a multiplicative constant). -/
theorem torusGauge_unique_scalar_of_normalArcWindows
    {A B : Tensor (torusGraph width height) d}
    (hB : NormalTorusArcWindowInjectivityHypotheses L K (regionInjectivityDataOf B))
    (hBTI : IsTorusTranslationInvariant B)
    (hposB : ∀ e : Edge (torusGraph width height), 0 < B.bondDim e)
    (hL : 0 < L) (hK : 0 < K)
    (hw : 2 * L + 1 ≤ width) (hh : 2 * K + 1 ≤ height)
    (hbond : A.bondDim = B.bondDim)
    (X X' : (e : Edge (torusGraph width height)) → GL (Fin (B.bondDim e)) ℂ)
    {lam lam' : ℂ}
    (hPV : ∀ (v : TorusVertex width height)
      (η : (ie : IncidentEdge (torusGraph width height) v) → Fin (A.bondDim ie.1))
      (σ : Fin d),
      A.component v η σ =
        lam * gaugeVertex B X v (fun ie => Fin.cast (congr_fun hbond ie.1) (η ie)) σ)
    (hlam : lam ^ (width * height) = 1)
    (hPV' : ∀ (v : TorusVertex width height)
      (η : (ie : IncidentEdge (torusGraph width height) v) → Fin (A.bondDim ie.1))
      (σ : Fin d),
      A.component v η σ =
        lam' * gaugeVertex B X' v (fun ie => Fin.cast (congr_fun hbond ie.1) (η ie)) σ)
    (hlam' : lam' ^ (width * height) = 1)
    (e : Edge (torusGraph width height)) :
    ∃ c : ℂˣ, (X' e : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) =
      (c : ℂ) • (X e : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) := by
  obtain ⟨R, hf, hR, hCR⟩ :=
    exists_injective_region_boundary_of_normalArcWindows B hB hBTI hposB hL hK hw hh e
  exact torusAbsorbedGauge_unique_scalar_of_region hbond R ⟨e, hf⟩ hR hCR hposB X X'
    (edgeAbsorbed_of_perVertex hbond X hPV hlam e)
    (edgeAbsorbed_of_perVertex hbond X' hPV' hlam' e)

end TNLean.PEPS
