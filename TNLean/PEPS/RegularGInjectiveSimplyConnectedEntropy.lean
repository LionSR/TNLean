/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularGInjectiveTorusRank
import TNLean.PEPS.TorusSimplyConnectedPhysicalDensity

/-!
# Zero-order entropy of regular G-injective torus closures

The local G-injective inverse and the original site map carry actual coherent
closure vectors to and from the regular averaging-projector tensor. Their
Schmidt ranks coincide across every physical cut. For a contiguous simply
connected block, the canonical isometric density theorem determines this rank
by the number of crossing bonds. Normalization preserves the rank of the
original reduced density, and its zero-order Rényi entropy is the logarithm of
that rank. No flat spectrum is claimed for a G-injective tensor.

**Scope restriction (regular native torus):** Both torus periods are at least
three, the occupied nearest-neighbour graph is connected, and its actual
closed-cell realization is simply connected. The coherent family uses
commuting closures and is nonzero before normalization. Spanning trees,
boundary numbering, and complementary paths are derived, and no global Gram
or rank identity is assumed. Identification with the parent-Hamiltonian
ground space remains separate; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807,
Corollary 6.10, local source lines 2074–2090.
-/

open scoped BigOperators Matrix ComplexOrder
namespace TNLean.PEPS

private theorem isGIsometric_relabel_physical
    {G Phys Out V : Type*} [Group G] [Fintype V] [Fintype Phys] [Fintype Out]
    (ρ : Representation ℂ G ((V × V × V × V) → ℂ))
    (a : V → V → V → V → Phys → ℂ)
    (ha : IsGIsometric ρ (siteMap a)) (e : Phys ≃ Out) :
    IsGIsometric ρ (siteMap (fun t r b l s => a t r b l (e.symm s))) := by
  have hmap (x : (V × V × V × V) → ℂ) (s : Out) :
      siteMap (fun t r b l s => a t r b l (e.symm s)) x s =
        siteMap a x (e.symm s) := rfl
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro g
    ext x s
    simpa only [LinearMap.comp_apply, hmap] using
      congrFun (LinearMap.congr_fun (ha.invariant g) x) (e.symm s)
  · intro x hx hzero
    apply ha.injOn_invariants x hx
    funext s
    have h := congrFun hzero (e s)
    simpa only [hmap, Equiv.symm_apply_apply, Pi.zero_apply] using h
  · obtain ⟨c, hc, hinner⟩ := ha.exists_inner_eq
    refine ⟨c, hc, ?_⟩
    intro x hx y hy
    have he : star (siteMap (fun t r b l s => a t r b l (e.symm s)) x) ⬝ᵥ
        siteMap (fun t r b l s => a t r b l (e.symm s)) y =
        star (siteMap a x) ⬝ᵥ siteMap a y := by
      simpa only [dotProduct, Pi.star_apply, hmap] using
        Equiv.sum_comp e.symm (fun s => star (siteMap a x s) * siteMap a y s)
    rw [he]
    exact hinner x hx y hy

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local notation "X" => TorusVertex width height

omit [Fact (2 < width)] [Fact (2 < height)] in
private theorem cut_rank_relabel_physical {Phys Out : Type*}
    [Fintype Phys] [Fintype Out] (e : Phys ≃ Out)
    (a : G → G → G → G → Phys → ℂ)
    (R : Finset X) {I : Type*} [Fintype I] (pairs : I → G × G) (μ : I → ℂ) :
    (physicalCutMatrix (fun v => v ∈ R)
      (∑ i, μ i • torusGClosure (leftRegularMatrix G)
        (fun t r b l s => a t r b l (e.symm s)) (pairs i).1 (pairs i).2)).rank =
    (physicalCutMatrix (fun v => v ∈ R)
      (∑ i, μ i • torusGClosure (leftRegularMatrix G) a (pairs i).1 (pairs i).2)).rank := by
  let eR : ({v : X // v ∈ R} → Out) ≃ ({v : X // v ∈ R} → Phys) :=
    Equiv.piCongrRight (fun _ => e.symm)
  let eS : ({v : X // ¬v ∈ R} → Out) ≃ ({v : X // ¬v ∈ R} → Phys) :=
    Equiv.piCongrRight (fun _ => e.symm)
  have hmat : physicalCutMatrix (fun v => v ∈ R)
      (∑ i, μ i • torusGClosure (leftRegularMatrix G)
        (fun t r b l s => a t r b l (e.symm s)) (pairs i).1 (pairs i).2) =
      (physicalCutMatrix (fun v => v ∈ R)
        (∑ i, μ i • torusGClosure (leftRegularMatrix G) a (pairs i).1 (pairs i).2)).submatrix
        eR eS := by
    ext σ τ
    simp only [physicalCutMatrix, Matrix.submatrix_apply, Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    unfold torusGClosure
    congr 1
    funext v c
    simp only [Equiv.piEquivPiSubtypeProd_symm_apply]
    split_ifs <;> rfl
  rw [hmat, Matrix.rank_submatrix]

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

private theorem rank_canonical_cut_of_isSimplyConnected
    (R : Finset X)
    (hR : ((torusGraph width height).induce (R : Set X)).Connected)
    (hSC : IsSimplyConnected (torusRegionRealization R))
    {I : Type*} [Fintype I] (pairs : I → G × G)
    (hcomm : ∀ i, Commute (pairs i).1 (pairs i).2) (μ : I → ℂ)
    (hne : (∑ i, μ i • torusGClosure (width := width) (height := height)
      (leftRegularMatrix G) (averagingSite (leftRegularMatrix G))
      (pairs i).1 (pairs i).2) ≠ 0) :
    (physicalCutMatrix (fun v => v ∈ R)
      (∑ i, μ i • torusGClosure (leftRegularMatrix G)
        (averagingSite (leftRegularMatrix G)) (pairs i).1 (pairs i).2)).rank =
      Fintype.card G ^ (Fintype.card {f : Edge (torusGraph width height) //
        IsRegionBoundaryEdge R f} - 1) := by
  classical
  let e := Fintype.equivFin (G × G × G × G)
  let b := fun t r d l s => averagingSite (leftRegularMatrix G) t r d l (e.symm s)
  let Ψ := ∑ i, μ i • torusGClosure (width := width) (height := height)
    (leftRegularMatrix G) b (pairs i).1 (pairs i).2
  have hb : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap b) :=
    isGIsometric_relabel_physical _ _ isGIsometric_regularAveragingSite e
  have hΨ : Ψ ≠ 0 := by
    intro hz
    apply hne
    funext σ
    have h := congrFun hz (fun v => e (σ v))
    simpa only [Ψ, b, Finset.sum_apply, Pi.smul_apply, torusGClosure,
      Equiv.symm_apply_apply, Pi.zero_apply] using h
  let K := physicalCutMatrix (fun v => v ∈ R) Ψ
  have hK : K ≠ 0 := by
    intro hz
    apply hΨ
    funext σ
    let π := Equiv.piEquivPiSubtypeProd (fun v : X => v ∈ R)
      (fun _ => Fin (Fintype.card (G × G × G × G)))
    have h := congrFun (congrFun hz (π σ).1) (π σ).2
    simpa only [K, physicalCutMatrix, π, Prod.mk.eta, Equiv.symm_apply_apply,
      Matrix.zero_apply, Pi.zero_apply] using h
  let eD : {v : X // v ∈ Finset.univ \ R} ≃ {v : X // ¬v ∈ R} :=
    Equiv.subtypeEquivRight (fun v => by simp)
  let eS := eD.arrowCongr (Equiv.refl (Fin (Fintype.card (G × G × G × G))))
  let M : Matrix (RegionPhysicalConfig (d := Fintype.card (G × G × G × G)) R)
      (RegionPhysicalConfig (d := Fintype.card (G × G × G × G)) (Finset.univ \ R)) ℂ :=
    fun σ τ => torusClosureSuperpositionCut b pairs μ R (σ, τ)
  have hM : M = K.submatrix (Equiv.refl _) eS := by
    ext σ τ
    rfl
  have hMne : M ≠ 0 := by
    intro hz
    apply hK
    ext σ τ
    have h := congrFun (congrFun hz σ) (eS.symm τ)
    simpa only [hM, Matrix.submatrix_apply, Equiv.refl_apply, Equiv.apply_symm_apply,
      Matrix.zero_apply] using h
  have hcut : torusClosureSuperpositionCut b pairs μ R ≠ 0 := by
    intro hz
    apply hMne
    ext σ τ
    exact congrFun hz (σ, τ)
  obtain ⟨ρ, hρ⟩ := hb.exists_torusPhysicalCut_common_density_of_isSimplyConnected R hR hSC
  obtain ⟨hpos, heq, -, -, hrank, -⟩ := hρ pairs hcomm μ hcut
  change 0 < (M * M.conjTranspose).trace at hpos
  change (M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose) = ρ at heq
  have ht : (M * M.conjTranspose).trace ≠ 0 := ne_of_gt hpos
  have hr : ρ.rank = M.rank := by
    rw [← heq, Matrix.rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_of_ne_zero (inv_ne_zero ht)), Matrix.rank_self_mul_conjTranspose]
  rw [hr, hM, Matrix.rank_submatrix] at hrank
  exact (cut_rank_relabel_physical e (averagingSite (leftRegularMatrix G)) R pairs μ).symm.trans
    hrank

/-- For a regular G-injective tensor, every nonzero coherent superposition of
commuting torus closures has the boundary Schmidt rank on a contiguous simply
connected block. Its normalized reduced density has the same rank, and its
zero-order Rényi entropy is the logarithm of that rank. No isometry or flat
spectrum is asserted for the original tensor.
Source: SCP10, Corollary 6.10, local source lines 2074–2090. -/
theorem IsGInjective.torusPhysicalCut_rank_zeroEntropy_of_isSimplyConnected
    {Phys : Type*} [Fintype Phys] {a : G → G → G → G → Phys → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (R : Finset X)
    (hR : ((torusGraph width height).induce (R : Set X)).Connected)
    (hSC : IsSimplyConnected (torusRegionRealization R))
    {I : Type*} [Fintype I] (pairs : I → G × G)
    (hcomm : ∀ i, Commute (pairs i).1 (pairs i).2) (μ : I → ℂ)
    (hne : (∑ i, μ i • torusGClosure (width := width) (height := height)
      (leftRegularMatrix G) a (pairs i).1 (pairs i).2) ≠ 0) :
    let _ := Classical.decEq Phys
    let b := Fintype.card {f : Edge (torusGraph width height) // IsRegionBoundaryEdge R f}
    let M := physicalCutMatrix (fun v => v ∈ R)
      (∑ i, μ i • torusGClosure (leftRegularMatrix G) a (pairs i).1 (pairs i).2)
    let ρ := (M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose)
    0 < (M * M.conjTranspose).trace ∧ ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ρ.rank = Fintype.card G ^ (b - 1) ∧
      Real.log (ρ.rank : ℝ) = (b - 1 : ℕ) * Real.log (Fintype.card G : ℝ) ∧
      ∃ hρ : ρ.IsHermitian,
        renyiEntropy ρ hρ 0 = (b - 1 : ℕ) * Real.log (Fintype.card G : ℝ) := by
  classical
  let Ψ := ∑ i, μ i • torusGClosure (width := width) (height := height)
    (leftRegularMatrix G) a (pairs i).1 (pairs i).2
  let Ψ₀ := ∑ i, μ i • torusGClosure (width := width) (height := height)
    (leftRegularMatrix G) (averagingSite (leftRegularMatrix G)) (pairs i).1 (pairs i).2
  have hrecover : torusPhysicalMap (LinearMap.toMatrix' (siteMap a)) Ψ₀ = Ψ := by
    simp only [Ψ₀, Ψ, map_sum, map_smul,
      torusPhysicalMap_averagingSite (leftRegularMatrix G) a ha.invariant]
  have hΨ₀ : Ψ₀ ≠ 0 := by
    intro hz
    apply hne
    rw [hz, map_zero] at hrecover
    exact hrecover.symm
  have hrank := (ha.rank_physicalCutMatrix_torusGClosure_sum
    (fun v => v ∈ R) pairs μ).trans
      (rank_canonical_cut_of_isSimplyConnected R hR hSC pairs hcomm μ hΨ₀)
  let M := physicalCutMatrix (fun v => v ∈ R) Ψ
  let ρ := (M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose)
  have hM : M ≠ 0 := by
    intro hz
    apply hne
    let π := Equiv.piEquivPiSubtypeProd (fun v : X => v ∈ R) (fun _ => Phys)
    apply π.symm.surjective.injective_comp_right
    funext p
    exact congrFun (congrFun hz p.1) p.2
  have ht : (M * M.conjTranspose).trace ≠ 0 :=
    mt Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp hM
  have hpos : 0 < (M * M.conjTranspose).trace :=
    lt_of_le_of_ne (Matrix.posSemidef_self_mul_conjTranspose M).trace_nonneg (Ne.symm ht)
  have hρ : ρ.PosSemidef :=
    (Matrix.posSemidef_self_mul_conjTranspose M).smul (inv_nonneg.mpr hpos.le)
  have htr : ρ.trace = 1 := by
    change ((M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose)).trace = 1
    rw [Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ ht]
  have hr : ρ.rank = Fintype.card G ^
      (Fintype.card {f : Edge (torusGraph width height) // IsRegionBoundaryEdge R f} - 1) := by
    change ((M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose)).rank = _
    rw [Matrix.rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_of_ne_zero (inv_ne_zero ht)), Matrix.rank_self_mul_conjTranspose]
    simpa only [Matrix.rank_eq_finrank_span_cols, M, Ψ] using hrank
  have hlog : Real.log (ρ.rank : ℝ) =
      (Fintype.card {f : Edge (torusGraph width height) // IsRegionBoundaryEdge R f} - 1 : ℕ) *
        Real.log (Fintype.card G : ℝ) := by
    rw [hr, Nat.cast_pow, Real.log_pow]
  exact ⟨hpos, hρ, htr, hr, hlog, hρ.isHermitian,
    by simpa only [renyiEntropy, ↓reduceIte] using hlog⟩

end TNLean.PEPS
