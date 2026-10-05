/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusWindowCrossTensorTransfer
import TNLean.PEPS.TorusWitnessIsoTransport

/-!
# A vertical reference-edge coefficient identity

Exchange the torus coordinates and apply the horizontal staircase construction at placement
`(1, 0)`, with the window lengths exchanged. Pull the resulting witness back to the original
tensor pair. The distinguished edge does not cross a coordinate seam, so its first stored
endpoint is preserved by the coordinate exchange.

All positive window lengths are allowed. The torus bounds are `2L+1 ≤ width` and
`2K+1 ≤ height`, without a larger-window injectivity assumption. The derivation is recorded
in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`.

Source: arXiv:1804.04964, the exchange of directions at lines 2368--2444 of
`Papers/1804.04964/paper_normal.tex`.
-/

namespace TNLean.PEPS
variable {width height d L K : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]

/-- Normal translation-invariant tensors generating the same torus state have a vertical
reference-edge coefficient identity, with its first stored endpoint in the witnessing region.
The torus sizes are the original window bounds; no larger rectangle is assumed injective.

Source: arXiv:1804.04964, the two-dimensional comparison at lines 2368--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_verticalEdgeCoeffIdentityWitness_of_normalArcWindows
    (A B : Tensor (torusGraph width height) d)
    (hA : NormalTorusArcWindowInjectivityHypotheses L K (regionInjectivityDataOf A))
    (hB : NormalTorusArcWindowInjectivityHypotheses L K (regionInjectivityDataOf B))
    (hATI : IsTorusTranslationInvariant A) (hBTI : IsTorusTranslationInvariant B)
    (hAB : SameState A B)
    (hposA : ∀ e : Edge (torusGraph width height), 0 < A.bondDim e)
    (hposB : ∀ e : Edge (torusGraph width height), 0 < B.bondDim e)
    (hL : 0 < L) (hK : 0 < K)
    (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height) :
    ∃ e : Edge (torusGraph width height), IsVerticalTorusEdge e ∧
      ∃ (hE : A.bondDim e = B.bondDim e) (Z : GL (Fin (B.bondDim e)) ℂ)
        (w : EdgeCoeffIdentityWitness A B e Z Z hE), e.1.1 ∈ w.region := by
  classical
  obtain ⟨hE, Z, w, hR, hmem⟩ := exists_staircaseWindowEdgeCoeffIdentityWitness
    (a := 1) (b := 0) (A.transport torusCoordinateSwap) (B.transport torusCoordinateSwap)
    (hA.transportCoordinateSwap A) (hB.transportCoordinateSwap B)
    (hATI.transportCoordinateSwap A) (hBTI.transportCoordinateSwap B)
    (hAB.transport torusCoordinateSwap)
    (fun e ↦ hposA (Edge.map torusCoordinateSwap.symm e))
    (fun e ↦ hposB (Edge.map torusCoordinateSwap.symm e)) hK hL
    (by omega) (by omega) (by omega) hyh hxw
  let eh := horizontalStaircaseReferenceEdge
    (((1 : ℕ) : ZMod height), ((0 : ℕ) : ZMod width)) K L
  let p : TorusVertex width height :=
    (((L - 1 : ℕ) : ZMod width), (1 : ZMod height) + ((K - 1 : ℕ) : ZMod height))
  have hmap : Edge.map torusCoordinateSwap.symm eh = torusUpEdge p := by
    simp only [eh, horizontalStaircaseReferenceEdge, Nat.cast_one, Nat.cast_zero, zero_add,
      torusCoordinateSwap_symm, Edge.map_torusCoordinateSwap_rightEdge]
    rfl
  have hp : p.2.val + 1 < height := by
    have hk : (1 : ZMod height) + ((K - 1 : ℕ) : ZMod height) = (K : ZMod height) := by
      rw [← Nat.cast_one, ← Nat.cast_add]
      congr 1
      omega
    simp only [p, hk, ZMod.val_natCast_of_lt (show K < height by omega)]
    omega
  have hUp := torusUpEdge_endpoints_of_lt (p := p) hp
  have hRight := torusRightEdge_endpoints_of_lt (p := (p.2, p.1)) hp
  have hfirst : torusCoordinateSwap (Edge.map torusCoordinateSwap.symm eh).1.1 = eh.1.1 := by
    rw [hmap, hUp.1]
    simpa only [torusCoordinateSwap_apply, eh, horizontalStaircaseReferenceEdge,
      Nat.cast_one, Nat.cast_zero, zero_add, p] using hRight.1.symm
  have hPull := exists_edgeCoeffIdentityWitness_of_transport
    (A := A) (B := B) torusCoordinateSwap (Edge.map torusCoordinateSwap.symm eh)
  generalize hImage : Edge.map torusCoordinateSwap
    (Edge.map torusCoordinateSwap.symm eh) = ehImage at hPull
  rw [Edge.map_map_symm] at hImage
  subst ehImage
  obtain ⟨hE₀, Z₀, w₀, hm₀, _⟩ := hPull hE Z w hfirst hmem
  refine ⟨Edge.map torusCoordinateSwap.symm eh, ?_, hE₀, Z₀, w₀, hm₀⟩
  rw [hmap]
  exact isVerticalTorusEdge_torusUpEdge p

end TNLean.PEPS
