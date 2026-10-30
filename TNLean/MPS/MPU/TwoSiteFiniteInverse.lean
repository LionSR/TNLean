/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TwoSiteBufferedAction
import TNLean.QCA.FiniteInverseLocality

/-!
# Finite inverse locality from the supplied MPU standard form

The inverse of the actual finite-chain conjugation is conjugation by the
adjoint periodic MPU. Every outside singleton whose forward window lies
inside the chain and is disjoint from the target commutes with this inverse
observable. Finite tensor generation and the relative commutant recover
its support on the retained region.

The buffer and disjointness assumptions below are explicit finite geometry.
They are not assumptions about an inverse family, inverse compatibility,
or a quasi-local automorphism. Treating periodic boundary singletons with
a uniform cyclic neighborhood remains a separate step.

Source: arXiv:1703.09188, StandardForm/SF, lines 603–622, and
Appendix eq:appendix-1, lines 2292–2306.

**Scope restriction (supplied standard form):** These results consume
actual MPU unitarity, a positive block length and supplied two-site
standard-form data, and their neighbourhoods are measured in that block
length. The standard-form construction from bare MPU data and the source
bond-dimension radius remain separate. See
`docs/paper-gaps/mpu_qca_complete_block_heisenberg_scope.tex`.
-/

namespace SpinChain

/-- The inverse finite automorphism is the actual adjoint-MPU conjugation.
Source: arXiv:1703.09188, eq:appendix-1, lines 2300–2306. -/
@[simp] theorem finiteChainConjugation_symm_apply
    {d D : ℕ} {U : MPOTensor d D} (hU : U.IsMPU)
    {N : ℕ} (hN : 1 < N) (a : ℤ) (B : LocalAlgebra d (finiteChainRegion a N)) :
    (finiteChainConjugation hU hN a).symm B =
      star (finiteChainMPOMatrix U N a) * B * finiteChainMPOMatrix U N a := rfl

/-- Actual finite inverse locality derived from the forward standard-form
window formula and outside commutants. Every site outside the retained
region must have its forward window inside the finite chain and disjoint
from the target; these are the only added conditions, and they are purely
geometric. Source: arXiv:1703.09188, eq:appendix-1, lines 2300–2306,
with supplied StandardForm/SF, lines 603–622. -/
theorem finiteChainConjugation_symm_mem_range_of_twoSiteStandardForm_buffers
    {d D ℓ r N : ℕ} {U : MPOTensor d D} (hU : U.IsMPU)
    (k : ℕ) (hk : 0 < k) (hN : 1 < N) (a : ℤ)
    {u : Matrix (Fin ℓ × Fin r)
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ}
    {v : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin r × Fin ℓ) ℂ}
    (S : MPOTensor.TwoSiteStandardFormData
      (MPOTensor.blockTwo (MPOTensor.blockTensor U k)) u v)
    {J K : Finset ℤ} (hJ : J ⊆ finiteChainRegion a N)
    (hK : K ⊆ finiteChainRegion a N)
    (hGeometry : ∀ x ∈ finiteChainRegion a N \ K,
      a ≤ x - (2 * k : ℕ) ∧ x + (4 * k : ℕ) ≤ a + N ∧
        Disjoint (finiteChainRegion (x - (2 * k : ℕ)) (3 * (2 * k))) J)
    (B : LocalAlgebra d J) :
    (finiteChainConjugation hU hN a).symm (localInclusion hJ B) ∈
      Set.range (localInclusion (d := d) hK) := by
  classical
  have hd : d ≠ 0 := by
    intro hd
    have hpos := S.phys_pos
    simp [MPSTensor.blockPhysDim_eq_pow, hd, hk.ne'] at hpos
  let : NeZero d := ⟨hd⟩
  apply inverse_mem_range_localInclusion_of_forward_support hJ hK
    (finiteChainConjugation hU hN a) B
  intro x hx C
  obtain ⟨hleft, hright, hdisjoint⟩ := hGeometry x hx
  let b := x - (2 * k : ℕ)
  let Δ := finiteChainRegion b (3 * (2 * k))
  have hΔ : Δ ⊆ finiteChainRegion a N := by
    intro y hy
    simp only [Δ, finiteChainRegion, Finset.mem_Ico] at *
    dsimp [b] at *
    omega
  let hsingle : ({x} : Finset ℤ) ⊆ finiteChainRegion (b + (2 * k : ℕ)) (2 * k) := by
    intro y hy
    have hyx := Finset.mem_singleton.mp hy
    subst y
    simp only [finiteChainRegion, Finset.mem_Ico]
    dsimp [b]
    omega
  obtain ⟨A, hA⟩ := exists_finiteChainLocalObservable_central_interval hU k b S
    (localInclusion hsingle C)
  let p := (b - a).toNat
  let s := (a + N - (b + (3 * (2 * k) : ℕ))).toNat
  have hb : b - p = a := by dsimp [p, b]; omega
  have hlen : p + (3 * (2 * k) + s) = N := by dsimp [p, s, b]; omega
  have hActual : finiteChainLocalObservable hU hN a
      (Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mp hx).1) C =
      localObservable d Δ A := by
    simpa only [hb, hlen, finiteChainLocalObservable_localInclusion] using
      hA p s (show 1 < p + (3 * (2 * k) + s) by omega)
  refine ⟨Δ, hΔ, hdisjoint, A, ?_⟩
  apply localObservable_injective d (finiteChainRegion a N)
  rw [localObservable_localInclusion]
  exact hActual.symm

/-- The retained finite inverse region consists of a radius-`4k` target
window and the two finite-chain boundary collars. Boundary collars are
recorded explicitly; they are not silently discarded as spectators.
Source context: arXiv:1703.09188, eq:appendix-1, lines 2300–2306. -/
def finiteInverseBufferedRegion (k N : ℕ) (a b : ℤ) (L : ℕ) : Finset ℤ :=
  finiteChainRegion a N ∩
    ((finiteChainRegion (b - (4 * k : ℕ)) (L + 8 * k) ∪ finiteChainRegion a (2 * k)) ∪
      finiteChainRegion (a + N - (4 * k : ℕ)) (4 * k))

/-- The actual inverse finite MPU conjugation is supported in the expanded
target interval together with its explicitly retained boundary collars.
No support, decay, or inverse compatibility is assumed. The boundary-free
periodic propagation statement is not asserted here.
Source: arXiv:1703.09188, eq:appendix-1, lines 2300–2306,
with supplied StandardForm/SF, lines 603–622. -/
theorem finiteChainConjugation_symm_mem_range_bufferedRegion
    {d D ℓ r N : ℕ} {U : MPOTensor d D} (hU : U.IsMPU)
    (k : ℕ) (hk : 0 < k) (hN : 1 < N) (a b : ℤ) (L : ℕ)
    {u : Matrix (Fin ℓ × Fin r)
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ}
    {v : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin r × Fin ℓ) ℂ}
    (S : MPOTensor.TwoSiteStandardFormData
      (MPOTensor.blockTwo (MPOTensor.blockTensor U k)) u v)
    (hJ : finiteChainRegion b L ⊆ finiteChainRegion a N)
    (B : LocalAlgebra d (finiteChainRegion b L)) :
    (finiteChainConjugation hU hN a).symm (localInclusion hJ B) ∈
      Set.range (localInclusion (d := d)
        (show finiteInverseBufferedRegion k N a b L ⊆ finiteChainRegion a N from
          Finset.inter_subset_left)) := by
  apply finiteChainConjugation_symm_mem_range_of_twoSiteStandardForm_buffers
    hU k hk hN a S hJ Finset.inter_subset_left
  intro x hx
  have hxΓ := (Finset.mem_sdiff.mp hx).1
  have hOutside : x ∉
      ((finiteChainRegion (b - (4 * k : ℕ)) (L + 8 * k) ∪ finiteChainRegion a (2 * k)) ∪
        finiteChainRegion (a + N - (4 * k : ℕ)) (4 * k)) := by
    intro hmem
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_inter.mpr ⟨hxΓ, hmem⟩)
  simp only [Finset.mem_union, not_or, finiteChainRegion, Finset.mem_Ico] at hOutside hxΓ
  refine ⟨by omega, by omega, ?_⟩
  rw [Finset.disjoint_left]
  intro y hyW hyJ
  simp only [finiteChainRegion, Finset.mem_Ico] at hyW hyJ
  omega

end SpinChain
