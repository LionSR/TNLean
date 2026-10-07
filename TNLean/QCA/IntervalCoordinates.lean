/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.LocalAlgebra
import Mathlib.Data.Int.Interval

/-!
# Consecutive interval coordinates for local observables

The integer interval of length \(N\) beginning at \(a\) is numbered by
\(i\mapsto a+i\), with \(0\leq i<N\). This identifies its configurations
and local matrix algebra with the usual length-\(N\) coordinates. Under this
identification, adjoining sites to an interval is the inclusion that acts as
the identity on the complementary sites.

These are finite-coordinate consequences of the local observable conventions
in Nachtergaele, arXiv:cond-mat/9410110, Section 3, and of the identity-tensor
inclusions in arXiv:1703.09188, Appendix, lines 2285--2295. Empty intervals
are included. No completion or infinite-volume state is constructed here.
-/

namespace SpinChain

/-- The half-open integer interval of \(N\) consecutive sites beginning at \(a\).
This is the finite chain used to interpret the finite-size operator \(U^{(N)}\)
in arXiv:1703.09188, equation `eq:appendix-1`, lines 2300--2306, and the
interval convention of Nachtergaele, arXiv:cond-mat/9410110, Section 3. -/
abbrev finiteChainRegion (a : ℤ) (N : ℕ) : Finset ℤ := Finset.Ico a (a + N)

/-- A finite chain of length \(N\) has \(N\) sites.
Source: arXiv:1703.09188, equation `eq:appendix-1`, lines 2300--2306. -/
@[simp]
lemma card_finiteChainRegion (a : ℤ) (N : ℕ) : (finiteChainRegion a N).card = N := by
  simp [finiteChainRegion, Int.card_Ico]

/-- Numbering the sites of an integer interval from left to right, identifying
the cyclic site labels `Fin N` with the chosen finite chain.
Source: arXiv:1703.09188, equation `eq:appendix-1`, lines 2300--2306; Nachtergaele, arXiv:cond-mat/9410110, Section 3, interval convention. -/
def finiteChainSiteEquiv (a : ℤ) (N : ℕ) : Fin N ≃ finiteChainRegion a N where
  toFun i := ⟨a + i, by simp only [finiteChainRegion, Finset.mem_Ico]; omega⟩
  invFun x := ⟨(x.1 - a).toNat, by
    have hx := Finset.mem_Ico.mp x.2
    omega⟩
  left_inv i := by
    apply Fin.ext
    dsimp
    omega
  right_inv x := by
    apply Subtype.ext
    have hx := Finset.mem_Ico.mp x.2
    dsimp
    omega

/-- The numbered site has integer coordinate \(a+i\).
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 3, interval convention. -/
@[simp] theorem finiteChainSiteEquiv_val (a : ℤ) (N : ℕ) (i : Fin N) :
    ((finiteChainSiteEquiv a N) i : ℤ) = a + i.val := rfl

/-- Configurations in consecutive coordinates and in integer-site coordinates.
Source: arXiv:1703.09188, Appendix, lines 2285--2292, and equation
`eq:appendix-1`, lines 2300--2306. -/
def finiteChainConfigEquiv (d N : ℕ) (a : ℤ) :
    (Fin N → Fin d) ≃ Config d (finiteChainRegion a N) :=
  Equiv.arrowCongr (finiteChainSiteEquiv a N) (Equiv.refl _)

/-- The star-algebra coordinate equivalence for a consecutive interval.
Source: arXiv:1703.09188, Appendix, lines 2285--2292. -/
noncomputable def intervalCoordinates (d : ℕ) (a : ℤ) (N : ℕ) :
    LocalAlgebra d (finiteChainRegion a N) ≃⋆ₐ[ℂ]
      Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
  (CStarMatrix.reindexₐ ℂ ℂ (finiteChainConfigEquiv d N a).symm).trans
    CStarMatrix.ofMatrixStarAlgEquiv.symm

/-- The coordinate equivalence reindexes both matrix indices.
Source: arXiv:1703.09188, Appendix, lines 2285--2292. -/
@[simp] theorem intervalCoordinates_apply (d : ℕ) (a : ℤ) (N : ℕ)
    (A : LocalAlgebra d (finiteChainRegion a N)) (σ τ : Fin N → Fin d) :
    intervalCoordinates d a N A σ τ =
      A (finiteChainConfigEquiv d N a σ) (finiteChainConfigEquiv d N a τ) := rfl

/-- Adjoining sites on the left and right enlarges an interval.
Source: arXiv:1703.09188, Appendix, lines 2292--2295. -/
theorem finiteChainRegion_subset_expanded (a : ℤ) (N b c : ℕ) :
    finiteChainRegion a N ⊆ finiteChainRegion (a - b) ((b + N) + c) := by
  intro x hx
  simp only [finiteChainRegion, Finset.mem_Ico] at *
  omega

private theorem finiteChainConfigEquiv_restrict (d : ℕ) (a : ℤ) (N b c : ℕ)
    (σ : Fin ((b + N) + c) → Fin d) :
    (finiteChainConfigEquiv d N a).symm
      (Config.restrict (finiteChainRegion_subset_expanded a N b c)
        (finiteChainConfigEquiv d ((b + N) + c) (a - b) σ)) =
      fun i => σ ⟨b + i.val, by omega⟩ := by
  funext i
  change σ _ = σ _
  congr 1
  apply Fin.ext
  dsimp [finiteChainSiteEquiv]
  omega

private theorem finiteChainConfigEquiv_complement_eq_iff (d : ℕ) (a : ℤ) (N b c : ℕ)
    (σ τ : Fin ((b + N) + c) → Fin d) :
    (Config.splitEquiv (finiteChainRegion_subset_expanded a N b c)
      (finiteChainConfigEquiv d ((b + N) + c) (a - b) σ)).2 =
        (Config.splitEquiv (finiteChainRegion_subset_expanded a N b c)
          (finiteChainConfigEquiv d ((b + N) + c) (a - b) τ)).2 ↔
      ∀ i : Fin ((b + N) + c), ¬ (b ≤ i.val ∧ i.val < b + N) → σ i = τ i := by
  constructor
  · intro h i hi
    have hx : ((finiteChainSiteEquiv (a - b) ((b + N) + c)) i : ℤ) ∈
        finiteChainRegion (a - b) ((b + N) + c) \ finiteChainRegion a N := by
      simp only [Finset.mem_sdiff, finiteChainRegion, Finset.mem_Ico, finiteChainSiteEquiv_val]
      omega
    have h' := congrFun h ⟨_, hx⟩
    change σ ((finiteChainSiteEquiv (a - b) ((b + N) + c)).symm
      ((finiteChainSiteEquiv (a - b) ((b + N) + c)) i)) =
        τ ((finiteChainSiteEquiv (a - b) ((b + N) + c)).symm
          ((finiteChainSiteEquiv (a - b) ((b + N) + c)) i)) at h'
    simpa only [Equiv.symm_apply_apply] using h'
  · intro h
    funext x
    let i := (finiteChainSiteEquiv (a - b) ((b + N) + c)).symm
      ⟨x.1, (Finset.mem_sdiff.mp x.2).1⟩
    have hi : ¬ (b ≤ i.val ∧ i.val < b + N) := by
      have hx := Finset.mem_sdiff.mp x.2
      simp only [finiteChainRegion, Finset.mem_Ico] at hx
      dsimp [i, finiteChainSiteEquiv]
      omega
    exact h i hi

/-- In interval coordinates, a local inclusion keeps the middle coordinates
and forces equality on all added sites. Source: arXiv:1703.09188, Appendix,
lines 2292--2295, identity-tensor inclusion. -/
theorem intervalCoordinates_localInclusion_apply (d : ℕ) (a : ℤ) (N b c : ℕ)
    (A : LocalAlgebra d (finiteChainRegion a N))
    (σ τ : Fin ((b + N) + c) → Fin d) :
    intervalCoordinates d (a - b) ((b + N) + c)
      (localInclusion (finiteChainRegion_subset_expanded a N b c) A) σ τ =
        intervalCoordinates d a N A (fun i => σ ⟨b + i.val, by omega⟩)
          (fun i => τ ⟨b + i.val, by omega⟩) *
            if ∀ i : Fin ((b + N) + c), ¬ (b ≤ i.val ∧ i.val < b + N) → σ i = τ i
            then 1 else 0 := by
  simp only [intervalCoordinates_apply, localInclusion_apply,
    finiteChainConfigEquiv_complement_eq_iff]
  have hσ := congrArg (finiteChainConfigEquiv d N a)
    (finiteChainConfigEquiv_restrict d a N b c σ)
  have hτ := congrArg (finiteChainConfigEquiv d N a)
    (finiteChainConfigEquiv_restrict d a N b c τ)
  simp only [Equiv.apply_symm_apply] at hσ hτ
  rw [hσ, hτ]

end SpinChain
