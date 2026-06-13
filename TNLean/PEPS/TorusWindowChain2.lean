import TNLean.PEPS.TorusWindowChain
import TNLean.PEPS.RegionBlock.UnionInjectivityGeneral

/-!
# Extending a deformed-window state to a larger region

The two-dimensional strengthening of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, the corollary at lines 2297--2318 of
`Papers/1804.04964/paper_normal.tex`) chains the consecutive-window comparisons of
`TNLean/PEPS/TorusDeformedWindow.lean` across the staircase patch around a lattice
edge.  The chaining needs to read a single window's deformed state as the deformed
state of a larger region carrying the genuine network block on the added vertices:
the *corner-extended* insert.  This file builds that extension and the load-bearing
identity, following the filled-in derivation
(`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Steps 2--3).

## The extension identity

For nested regions `R ⊆ S`, the deformed state on `R` with insert `C` equals the
deformed state on `S` with the *extended* insert `extendInsert R S C`, where the
extended insert pairs `C` with the genuine network block of the added vertices
`S \ R`.  The extension reuses the three-block factorization
`ThreeBlockGeometry.regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical`
of `TNLean/PEPS/RegionBlock/UnionInjectivityGeneral.lean`: with the geometry
`red = R`, `blue = S \ R`, `complement = univ \ S`, the host `univ \ red = univ \ R`
is the complement block of the deformed state on `R`, and the factorization splits its
weight into the blue-coupling combination of the `univ \ S` complement weights.  The
blue-coupling coefficient `threeBlockBlueCoeff`, contracted against `C`, is exactly the
extended insert.  The factorization carries an interior-bond multiplicity factor on the
`univ \ S` block, a nonzero scalar at positive bond dimensions, which cancels.

The deformed state is read as a function of the *full* physical configuration through
`assembleRegionσ`, so the identity is a region-independent equality of functions on
`V → Fin d`; this lets the consecutive-window equalities chain across the patch by
transitivity, the content of Step 2.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, the corollary and proof
  sketch at lines 2296--2445 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964); the
  filled-in derivation in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
  Steps 2--3.
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {A : Tensor G d}

/-! ### The nested-region three-block geometry

For `R ⊆ S` the three blocks `red = R`, `blue = S \ R`, `complement = univ \ S`
partition the vertex set, with host `univ \ red = univ \ R`.  This is the geometry
whose three-block factorization splits the deformed-state complement weight on
`univ \ R` into the `univ \ S` complement weights, the blue coupling carrying the
added vertices `S \ R`. -/

/-- The nested-region three-block geometry for `R ⊆ S`: `red = R`, `blue = S \ R`,
`complement = univ \ S`.  The host `univ \ red` is `univ \ R`, the complement block
of the deformed state on `R`.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 2. -/
def nestedThreeBlockGeometry {R S : Finset V} (hRS : R ⊆ S) : ThreeBlockGeometry V where
  red := R
  blue := S \ R
  complement := Finset.univ \ S
  red_disjoint_blue := by
    rw [Finset.disjoint_left]; intro v hvR hvSR
    exact (Finset.mem_sdiff.mp hvSR).2 hvR
  red_disjoint_complement := by
    rw [Finset.disjoint_left]; intro v hvR hvS
    exact (Finset.mem_sdiff.mp hvS).2 (hRS hvR)
  blue_disjoint_complement := by
    rw [Finset.disjoint_left]; intro v hvSR hvS
    exact (Finset.mem_sdiff.mp hvS).2 (Finset.mem_sdiff.mp hvSR).1
  cover_univ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, iff_true]
    by_cases hvR : v ∈ R
    · exact Or.inl (Or.inl hvR)
    · by_cases hvS : v ∈ S
      · exact Or.inl (Or.inr ⟨hvS, hvR⟩)
      · exact Or.inr hvS

omit [DecidableRel G.Adj] in
@[simp] theorem nestedThreeBlockGeometry_red {R S : Finset V} (hRS : R ⊆ S) :
    (nestedThreeBlockGeometry (V := V) hRS).red = R := rfl

omit [DecidableRel G.Adj] in
@[simp] theorem nestedThreeBlockGeometry_blue {R S : Finset V} (hRS : R ⊆ S) :
    (nestedThreeBlockGeometry (V := V) hRS).blue = S \ R := rfl

omit [DecidableRel G.Adj] in
@[simp] theorem nestedThreeBlockGeometry_complement {R S : Finset V} (hRS : R ⊆ S) :
    (nestedThreeBlockGeometry (V := V) hRS).complement = Finset.univ \ S := rfl

omit [DecidableRel G.Adj] in
/-- The host `univ \ red` of the nested geometry is `univ \ R`. -/
theorem nestedThreeBlockGeometry_sdiff_red {R S : Finset V} (hRS : R ⊆ S) :
    Finset.univ \ (nestedThreeBlockGeometry (V := V) hRS).red = Finset.univ \ R := rfl

/-! ### Restricting a global physical configuration to a region

The deformed state is read as a function of the full physical configuration through
the restriction `restrictRegionσ`, the inverse of `assembleRegionσ`.  Restricting to
the host `univ \ R` factors through the nested geometry's fused leg: the host
restriction is the `complPhysical` of the blue restriction (to `S \ R`) and the
complement restriction (to `univ \ S`). -/

/-- The restriction of a global physical configuration `cfg` to the region `R`. -/
def restrictRegionσ (R : Finset V) (cfg : V → Fin d) :
    RegionPhysicalConfig (V := V) (d := d) R :=
  fun w => cfg w.1

omit [Fintype V] [LinearOrder V] [DecidableRel G.Adj] in
@[simp] theorem restrictRegionσ_apply (R : Finset V) (cfg : V → Fin d)
    (w : {w : V // w ∈ R}) : restrictRegionσ (V := V) (d := d) R cfg w = cfg w.1 := rfl

omit [DecidableRel G.Adj] in
/-- Assembling the region and complement restrictions recovers the global
configuration. -/
theorem assembleRegionσ_restrict (R : Finset V) (cfg : V → Fin d) :
    assembleRegionσ (V := V) (d := d) R (restrictRegionσ (V := V) (d := d) R cfg)
        (restrictRegionσ (V := V) (d := d) (Finset.univ \ R) cfg) = cfg := by
  funext w
  by_cases h : w ∈ R
  · rw [assembleRegionσ_mem (V := V) (d := d) R _ _ ⟨w, h⟩, restrictRegionσ_apply]
  · have hw : w ∈ Finset.univ \ R := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩
    rw [assembleRegionσ_notMem (V := V) (d := d) R _ _ ⟨w, hw⟩, restrictRegionσ_apply]

omit [DecidableRel G.Adj] in
/-- The host `univ \ R` restriction is the nested geometry's fused leg of the blue
restriction (to `S \ R`) and the complement restriction (to `univ \ S`). -/
theorem nestedComplPhysical_restrict {R S : Finset V} (hRS : R ⊆ S) (cfg : V → Fin d) :
    (nestedThreeBlockGeometry (V := V) hRS).complPhysical (d := d)
        (restrictRegionσ (V := V) (d := d) (S \ R) cfg)
        (restrictRegionσ (V := V) (d := d) (Finset.univ \ S) cfg) =
      restrictRegionσ (V := V) (d := d) (Finset.univ \ R) cfg := by
  funext w
  rw [ThreeBlockGeometry.complPhysical]
  by_cases hb : w.1 ∈ (nestedThreeBlockGeometry (V := V) hRS).blue
  · rw [dif_pos hb, restrictRegionσ_apply, restrictRegionσ_apply]
  · rw [dif_neg hb, restrictRegionσ_apply, restrictRegionσ_apply]

/-- The restriction of a physical configuration on `S` to a sub-region `R ⊆ S`. -/
def restrictSubRegionσ {R S : Finset V} (hRS : R ⊆ S)
    (σ : RegionPhysicalConfig (V := V) (d := d) S) :
    RegionPhysicalConfig (V := V) (d := d) R :=
  fun w => σ ⟨w.1, hRS w.2⟩

omit [Fintype V] [LinearOrder V] [DecidableRel G.Adj] in
@[simp] theorem restrictSubRegionσ_restrict {R S : Finset V} (hRS : R ⊆ S) (cfg : V → Fin d) :
    restrictSubRegionσ (V := V) (d := d) hRS (restrictRegionσ (V := V) (d := d) S cfg) =
      restrictRegionσ (V := V) (d := d) R cfg := rfl

/-! ### The corner-extended insert and the extension identity

The corner-extended insert `extendInsert hRS C` pairs the insert `C` on `R` with the
blue-coupling coefficient `threeBlockBlueCoeff` of the nested geometry, contracting `C`
against the genuine network block of the added vertices `S \ R`.  Reading the deformed
state as a function of the full physical configuration, the extension identity says the
deformed state on `R` with `C` equals the deformed state on `S` with `extendInsert
hRS C`. -/

/-- The corner-extended insert on `S` built from an insert `C` on `R ⊆ S`: for a
boundary configuration `ν` on `S` and a physical configuration `σ` on `S`, contract `C`
(read on `R`) against the blue-coupling coefficient `threeBlockBlueCoeff` of the nested
geometry (read on the added vertices `S \ R`) at the complement boundary configuration
`regionComplementBoundaryConfig A S ν` on `univ \ S`, divided by the `univ \ S`
interior-bond multiplicity.  This pairs `C` with the genuine network block of `S \ R`
across the matching boundary configurations; the multiplicity divisor cancels the factor
the three-block factorization introduces, so the deformed state is preserved.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex` (the blue coupling coefficient);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 2. -/
noncomputable def extendInsert {R S : Finset V} (hRS : R ⊆ S)
    (C : RegionInsert (G := G) (d := d) A R) :
    RegionInsert (G := G) (d := d) A S :=
  fun ν σ =>
    (regionInteriorBondProd (G := G) A (Finset.univ \ S) : ℂ)⁻¹ *
      ∑ μ : RegionBoundaryConfig (G := G) A R,
        C μ (restrictSubRegionσ (V := V) (d := d) hRS σ) *
          (nestedThreeBlockGeometry (V := V) hRS).threeBlockBlueCoeff
            (regionComplementBoundaryConfig (G := G) A R μ)
            (restrictSubRegionσ (V := V) (d := d) Finset.sdiff_subset σ)
            (regionComplementBoundaryConfig (G := G) A S ν)

/-- The deformed-window state read as a function of the full physical configuration:
restrict the global configuration to the region and its complement and evaluate the
deformed state. -/
noncomputable def deformedRegionStateAssembled (A : Tensor G d) (R : Finset V)
    (C : RegionInsert (G := G) (d := d) A R) (cfg : V → Fin d) : ℂ :=
  deformedRegionState (G := G) A R C
    (restrictRegionσ (V := V) (d := d) R cfg)
    (restrictRegionσ (V := V) (d := d) (Finset.univ \ R) cfg)

/-! ### The interior-bond multiple of the extension identity

The three-block factorization carries an interior-bond multiplicity factor on the
`univ \ S` block.  The *bare* corner-extended coefficient — the corner-extended insert
without the multiplicity divisor — has deformed state equal to that multiple of the
deformed state on `R`.  Dividing out the multiplicity (a nonzero scalar at positive bond
dimensions) gives the clean extension identity. -/

/-- The bare corner-extended coefficient: the corner-extended insert without the
multiplicity divisor.  Its deformed state on `S` is the `univ \ S` interior-bond multiple
of the deformed state on `R`. -/
noncomputable def bareExtendInsert {R S : Finset V} (hRS : R ⊆ S)
    (C : RegionInsert (G := G) (d := d) A R) :
    RegionInsert (G := G) (d := d) A S :=
  fun ν σ =>
    ∑ μ : RegionBoundaryConfig (G := G) A R,
      C μ (restrictSubRegionσ (V := V) (d := d) hRS σ) *
        (nestedThreeBlockGeometry (V := V) hRS).threeBlockBlueCoeff
          (regionComplementBoundaryConfig (G := G) A R μ)
          (restrictSubRegionσ (V := V) (d := d) Finset.sdiff_subset σ)
          (regionComplementBoundaryConfig (G := G) A S ν)

/-- The corner-extended insert is the bare coefficient scaled by the inverse
multiplicity. -/
theorem extendInsert_eq_smul_bare {R S : Finset V} (hRS : R ⊆ S)
    (C : RegionInsert (G := G) (d := d) A R) :
    extendInsert (G := G) hRS C =
      fun ν σ => (regionInteriorBondProd (G := G) A (Finset.univ \ S) : ℂ)⁻¹ *
        bareExtendInsert (G := G) hRS C ν σ := rfl

open scoped Classical in
/-- The bare corner-extended coefficient has deformed state the `univ \ S` interior-bond
multiple of the deformed state on `R`, read as a function of the full physical
configuration.  Each complement weight on `univ \ R` is split by the nested three-block
factorization into the blue-coupling combination of the `univ \ S` complement weights,
the blue coupling reassembling into the bare coefficient after reindexing the complement
boundary configurations along `regionComplementBoundaryConfigEquiv`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 2. -/
theorem deformedRegionStateAssembled_bareExtend
    {R S : Finset V} (hRS : R ⊆ S) (C : RegionInsert (G := G) (d := d) A R) (cfg : V → Fin d) :
    deformedRegionStateAssembled (G := G) A S (bareExtendInsert (G := G) hRS C) cfg =
      (regionInteriorBondProd (G := G) A (Finset.univ \ S) : ℂ) •
        deformedRegionStateAssembled (G := G) A R C cfg := by
  classical
  set g := nestedThreeBlockGeometry (V := V) hRS with hg
  -- Abbreviate the three restrictions.
  set σR := restrictRegionσ (V := V) (d := d) R cfg with hσR
  set σblue := restrictRegionσ (V := V) (d := d) (S \ R) cfg with hσblue
  set σcompl := restrictRegionσ (V := V) (d := d) (Finset.univ \ S) cfg with hσcompl
  have hcompl : restrictRegionσ (V := V) (d := d) (Finset.univ \ R) cfg =
      g.complPhysical (d := d) σblue σcompl := (nestedComplPhysical_restrict hRS cfg).symm
  -- The right side: distribute the multiplicity into the boundary sum, then split each
  -- `univ \ R` complement weight by the nested three-block factorization.
  have hRHS : (regionInteriorBondProd (G := G) A (Finset.univ \ S) : ℂ) •
        deformedRegionStateAssembled (G := G) A R C cfg =
      ∑ bc' : RegionBoundaryConfig (G := G) A g.complement,
        (∑ μ : RegionBoundaryConfig (G := G) A R,
            C μ σR * g.threeBlockBlueCoeff (regionComplementBoundaryConfig (G := G) A R μ)
              σblue bc') * regionBlockedWeight (G := G) A g.complement bc' σcompl := by
    rw [deformedRegionStateAssembled, deformedRegionState, ← hσR, hcompl, Finset.smul_sum]
    -- Split each `univ \ R` complement weight by the nested three-block factorization.
    rw [show (∑ μ : RegionBoundaryConfig (G := G) A R,
          (regionInteriorBondProd (G := G) A (Finset.univ \ S) : ℂ) •
            (C μ σR * regionBlockedWeight (G := G) A (Finset.univ \ R)
              (regionComplementBoundaryConfig (G := G) A R μ)
              (g.complPhysical (d := d) σblue σcompl))) =
        ∑ μ : RegionBoundaryConfig (G := G) A R,
          ∑ bc' : RegionBoundaryConfig (G := G) A g.complement,
            (C μ σR * g.threeBlockBlueCoeff (regionComplementBoundaryConfig (G := G) A R μ)
              σblue bc') * regionBlockedWeight (G := G) A g.complement bc' σcompl from ?_,
      Finset.sum_comm]
    · refine Finset.sum_congr rfl (fun bc' _ => ?_)
      rw [Finset.sum_mul]
    · refine Finset.sum_congr rfl (fun μ _ => ?_)
      have hfac := g.regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical
        (regionComplementBoundaryConfig (G := G) A R μ) σblue σcompl
      rw [smul_eq_mul, mul_comm (C μ σR), ← mul_assoc,
        show ((regionInteriorBondProd (G := G) A (Finset.univ \ S) : ℂ) *
              regionBlockedWeight (G := G) A (Finset.univ \ R)
                (regionComplementBoundaryConfig (G := G) A R μ)
                (g.complPhysical (d := d) σblue σcompl)) =
            (regionInteriorBondProd (G := G) A g.complement : ℂ) •
              regionBlockedWeight (G := G) A (Finset.univ \ g.red)
                (regionComplementBoundaryConfig (G := G) A R μ)
                (g.complPhysical (d := d) σblue σcompl) from by rw [smul_eq_mul]; rfl,
        hfac, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun bc' _ => ?_)
      rw [smul_eq_mul]; ring
  rw [hRHS, deformedRegionStateAssembled, deformedRegionState]
  -- Reindex the `bc'` sum to the `S`-boundary sum, then match the bare insert termwise.
  refine Eq.trans ?_ (Equiv.sum_comp (regionComplementBoundaryConfigEquiv (G := G) A S)
    (fun bc' : RegionBoundaryConfig (G := G) A g.complement =>
      (∑ μ : RegionBoundaryConfig (G := G) A R,
          C μ σR * g.threeBlockBlueCoeff (regionComplementBoundaryConfig (G := G) A R μ)
            σblue bc') * regionBlockedWeight (G := G) A g.complement bc' σcompl))
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  rw [regionComplementBoundaryConfigEquiv_apply, bareExtendInsert]
  congr 1

/-! ### The clean extension identity

Dividing out the interior-bond multiplicity gives the corner-extension identity: the
deformed state on `R` with `C` equals the deformed state on `S` with the corner-extended
insert, as functions of the full physical configuration.  The multiplicity is a nonzero
scalar at positive bond dimensions. -/

/-- The deformed state is linear in scaling the insert by a constant: scaling the insert
by `c` scales the deformed state by `c`. -/
theorem deformedRegionStateAssembled_const_smul (A : Tensor G d) (R : Finset V) (c : ℂ)
    (C : RegionInsert (G := G) (d := d) A R) (cfg : V → Fin d) :
    deformedRegionStateAssembled (G := G) A R (fun μ σ => c * C μ σ) cfg =
      c * deformedRegionStateAssembled (G := G) A R C cfg := by
  rw [deformedRegionStateAssembled, deformedRegionStateAssembled, deformedRegionState,
    deformedRegionState, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [mul_assoc]

open scoped Classical in
/-- **The corner-extension identity.** For nested regions `R ⊆ S` and positive bond
dimensions, the deformed state on `R` with insert `C` equals the deformed state on `S`
with the corner-extended insert `extendInsert hRS C`, as functions of the full physical
configuration.  The corner-extended insert pairs `C` with the genuine network block of
the added vertices `S \ R`; the three-block factorization
(`deformedRegionStateAssembled_bareExtend`) produces the bare coupling scaled by the
`univ \ S` interior-bond multiplicity, which the corner-extended insert's divisor
cancels.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (the deformed states agree as closed-torus states);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 2. -/
theorem deformedRegionState_extend {R S : Finset V} (hRS : R ⊆ S)
    (hpos : ∀ e : Edge G, 0 < A.bondDim e) (C : RegionInsert (G := G) (d := d) A R)
    (cfg : V → Fin d) :
    deformedRegionStateAssembled (G := G) A R C cfg =
      deformedRegionStateAssembled (G := G) A S (extendInsert (G := G) hRS C) cfg := by
  classical
  have hne : (regionInteriorBondProd (G := G) A (Finset.univ \ S) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (regionInteriorBondProd_pos (G := G) A (Finset.univ \ S) hpos).ne'
  rw [extendInsert_eq_smul_bare, deformedRegionStateAssembled_const_smul,
    deformedRegionStateAssembled_bareExtend, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hne, one_mul]

/-! ### From the assembled state to the curried state

The assembled deformed state, read as a function of the full physical configuration,
determines the curried deformed state, a function of the region and complement physical
configurations: assembling those two configurations and restricting back recovers them.
Two inserts with equal assembled states therefore have equal curried states, the form
the consecutive-window comparison engine consumes. -/

omit [DecidableRel G.Adj] in
/-- Restricting the assembled configuration to the region recovers the region
configuration. -/
theorem restrictRegionσ_assembleRegionσ (R : Finset V)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    restrictRegionσ (V := V) (d := d) R (assembleRegionσ (V := V) (d := d) R σ τ) = σ := by
  funext w
  rw [restrictRegionσ_apply, assembleRegionσ_mem]

omit [DecidableRel G.Adj] in
/-- Restricting the assembled configuration to the set complement recovers the complement
configuration. -/
theorem restrictRegionσ_compl_assembleRegionσ (R : Finset V)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    restrictRegionσ (V := V) (d := d) (Finset.univ \ R)
        (assembleRegionσ (V := V) (d := d) R σ τ) = τ := by
  funext w
  rw [restrictRegionσ_apply, assembleRegionσ_notMem]

/-- Equal assembled deformed states give equal curried deformed states.  Evaluating the
curried states at `(σ, τ)` is evaluating the assembled states at `assembleRegionσ R σ τ`,
where the two restrictions recover `σ` and `τ`. -/
theorem deformedRegionState_eq_of_assembled_eq (A : Tensor G d) (R : Finset V)
    (C₁ C₂ : RegionInsert (G := G) (d := d) A R)
    (h : deformedRegionStateAssembled (G := G) A R C₁ =
      deformedRegionStateAssembled (G := G) A R C₂) :
    deformedRegionState (G := G) A R C₁ = deformedRegionState (G := G) A R C₂ := by
  funext σ τ
  have hcfg := congrFun h (assembleRegionσ (V := V) (d := d) R σ τ)
  simp only [deformedRegionStateAssembled, restrictRegionσ_assembleRegionσ,
    restrictRegionσ_compl_assembleRegionσ] at hcfg
  exact hcfg

/-- Equal curried deformed states give equal assembled deformed states. -/
theorem deformedRegionStateAssembled_eq_of_curried_eq (A : Tensor G d) (R : Finset V)
    (C₁ C₂ : RegionInsert (G := G) (d := d) A R)
    (h : deformedRegionState (G := G) A R C₁ = deformedRegionState (G := G) A R C₂) :
    deformedRegionStateAssembled (G := G) A R C₁ =
      deformedRegionStateAssembled (G := G) A R C₂ := by
  funext cfg
  rw [deformedRegionStateAssembled, deformedRegionStateAssembled, h]

end PEPS
end TNLean
