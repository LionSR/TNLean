import TNLean.PEPS.TorusWindowChain4
import TNLean.PEPS.RegionBlock.UnionInjectivityGeneral2

/-!
# Additivity of the corner extension and the kernel reduction of the cancellation

The two-dimensional strengthening of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, the corollary at lines 2297--2318 of
`Papers/1804.04964/paper_normal.tex`) closes Step 3 of its proof sketch with an
*open-boundary* cancellation: from the open-boundary equality of inserts on the staircase
patch `P` it cancels the shared injective completed corner to leave the equality on the
staircase end pair `S`, never inverting the non-injective torus complement `univ \ S` (the
obstruction recorded in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3).

The cancellation is the injectivity of the corner extension `extendInsert (S ⊆ R)` on
inserts on `S`, where `R = S ⊔ Q` and `Q = R \ S` is the injective completed rectangle.  An
injectivity statement for a linear-in-its-insert map reduces, in the standard way, to a
*kernel* statement: the only insert whose corner extension vanishes is the zero insert.
This file records the linearity of the corner extension in its insert and that kernel
reduction.  The corner extension `extendInsert hRS` and its bare companion `bareExtendInsert
hRS` contract the insert against a fixed blue-coupling coefficient, so each is *additive* in
the insert (on top of the homogeneity `extendInsert_const_smul` of
`TNLean/PEPS/TorusWindowChain3.lean`); subtracting the two extensions of equal-extension
inserts reduces the cancellation to the kernel of the corner extension.

The fiber-gluing engine the cancellation needs — that the corner extension's kernel is
trivial when the added block `R \ S` is blocked-tensor injective, the *shared-corner
cancellation* proper — is the genuinely new content of this file.  Its `Q`-weight span half
(the blue coupling, read on the `Q`-leg, lies in the range of the `Q` block) is combined with
the `S ⊔ Q` assembly bridge (an insert on `R` reads its `S`- and `Q`-legs independently) and
the host-boundary-edge embedding `regionBoundaryLabel_host_eq_hostLabelFrom` of
`TNLean/PEPS/RegionBlock/UnionInjectivityGeneral2.lean` (a global configuration's host residual
is determined by its `Q` and `univ \ R` residuals).  The result is the kernel triviality
`extendInsert_kernel_trivial_of_addedInjective` and the cancellation
`extendInsert_cancel_addedInjective`, needing only injectivity of `Q = R \ S`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, the corollary and proof
  sketch at lines 2296--2445 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964); the
  filled-in derivation in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3.
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {A : Tensor G d}

/-! ### Additivity of the bare and clean corner extensions in the insert

The bare corner-extended coefficient `bareExtendInsert hRS C` contracts the insert `C`
against the fixed blue-coupling coefficient, so it is additive in `C`: extending the sum of
two inserts adds the bare coefficients.  The clean corner extension `extendInsert hRS C` is
the bare coefficient scaled by the fixed inverse multiplicity, so it is additive as well.
With the homogeneity `extendInsert_const_smul` this makes the corner extension linear in its
insert, the algebraic shape the kernel reduction of the cancellation consumes. -/

/-- The bare corner-extended coefficient is additive in its insert: extending the pointwise
sum `C₁ + C₂` is the pointwise sum of the two bare extensions.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 3. -/
theorem bareExtendInsert_add {R S : Finset V} (hRS : R ⊆ S)
    (C₁ C₂ : RegionInsert (G := G) (d := d) A R) :
    bareExtendInsert (G := G) hRS (fun μ σ => C₁ μ σ + C₂ μ σ) =
      fun ν σ => bareExtendInsert (G := G) hRS C₁ ν σ + bareExtendInsert (G := G) hRS C₂ ν σ := by
  funext ν σ
  rw [bareExtendInsert, bareExtendInsert, bareExtendInsert, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [add_mul]

/-- The bare corner-extended coefficient of the zero insert vanishes. -/
theorem bareExtendInsert_zero {R S : Finset V} (hRS : R ⊆ S) :
    bareExtendInsert (G := G) hRS (0 : RegionInsert (G := G) (d := d) A R) = 0 := by
  funext ν σ
  rw [bareExtendInsert]
  refine Finset.sum_eq_zero (fun μ _ => ?_)
  rw [Pi.zero_apply, Pi.zero_apply, zero_mul]

/-- The clean corner extension is additive in its insert: extending the pointwise sum
`C₁ + C₂` is the pointwise sum of the two corner extensions.  The bare coefficient is
additive (`bareExtendInsert_add`) and the inverse multiplicity divisor distributes over the
sum.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 3. -/
theorem extendInsert_add {R S : Finset V} (hRS : R ⊆ S)
    (C₁ C₂ : RegionInsert (G := G) (d := d) A R) :
    extendInsert (G := G) hRS (fun μ σ => C₁ μ σ + C₂ μ σ) =
      fun ν σ => extendInsert (G := G) hRS C₁ ν σ + extendInsert (G := G) hRS C₂ ν σ := by
  rw [extendInsert_eq_smul_bare, extendInsert_eq_smul_bare, extendInsert_eq_smul_bare,
    bareExtendInsert_add]
  funext ν σ
  simp only [mul_add]

/-- The clean corner extension of the zero insert vanishes. -/
theorem extendInsert_zero {R S : Finset V} (hRS : R ⊆ S) :
    extendInsert (G := G) hRS (0 : RegionInsert (G := G) (d := d) A R) = 0 := by
  rw [extendInsert_eq_smul_bare, bareExtendInsert_zero]
  funext ν σ
  simp only [Pi.zero_apply, mul_zero]

/-- The clean corner extension respects pointwise subtraction of inserts: extending the
difference `C₁ - C₂` is the pointwise difference of the two corner extensions.  Combines the
additivity `extendInsert_add` with the homogeneity `extendInsert_const_smul` at the scalar
`-1`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 3. -/
theorem extendInsert_sub {R S : Finset V} (hRS : R ⊆ S)
    (C₁ C₂ : RegionInsert (G := G) (d := d) A R) :
    extendInsert (G := G) hRS (fun μ σ => C₁ μ σ - C₂ μ σ) =
      fun ν σ => extendInsert (G := G) hRS C₁ ν σ - extendInsert (G := G) hRS C₂ ν σ := by
  have hneg : extendInsert (G := G) hRS (fun μ σ => -C₂ μ σ) =
      fun ν σ => -extendInsert (G := G) hRS C₂ ν σ := by
    rw [show (fun μ σ => -C₂ μ σ) = (fun μ σ => (-1 : ℂ) * C₂ μ σ) from by
        funext μ σ; rw [neg_one_mul],
      extendInsert_const_smul]
    funext ν σ; rw [neg_one_mul]
  rw [show (fun μ σ => C₁ μ σ - C₂ μ σ) = (fun μ σ => C₁ μ σ + (-C₂ μ σ)) from by
      funext μ σ; rw [sub_eq_add_neg],
    extendInsert_add, hneg]
  funext ν σ; rw [sub_eq_add_neg]

/-! ### The kernel reduction of the cancellation

Injectivity of the linear-in-its-insert corner extension reduces to the triviality of its
kernel: if the only insert whose corner extension vanishes is the zero insert, then two
inserts with equal corner extensions are equal.  Subtracting the two extensions, the
difference insert has vanishing corner extension (`extendInsert_sub`), hence is the zero
insert, hence the two inserts agree.  This isolates the residual *shared-corner cancellation*
as the single kernel statement the note's Step 3 supplies from injectivity of the added
block. -/

/-- **The kernel reduction of the shared-corner cancellation.**  If the corner extension
`extendInsert hRS` has trivial kernel — the only insert on `R` whose corner extension on `S`
vanishes is the zero insert — then it is injective: two inserts with equal corner extensions
are equal.

Subtracting the two extensions, the difference insert `C₁ - C₂` has corner extension the
difference of the two extensions (`extendInsert_sub`), which vanishes; the kernel hypothesis
forces `C₁ - C₂` to be the zero insert, so `C₁` and `C₂` agree pointwise.  This reduces the
shared-corner cancellation of Step 3 to the kernel statement supplied from injectivity of the
added block `S \ R` (the `Q`-weight span lemma and host-boundary-edge embedding of the note),
never asserting injectivity of `univ \ R`.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (add two-two tensors in the corner and invert);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3. -/
theorem extendInsert_injective_of_kernel_trivial {R S : Finset V} (hRS : R ⊆ S)
    (hker : ∀ D : RegionInsert (G := G) (d := d) A R,
      extendInsert (G := G) hRS D = 0 → D = 0)
    (C₁ C₂ : RegionInsert (G := G) (d := d) A R)
    (h : extendInsert (G := G) hRS C₁ = extendInsert (G := G) hRS C₂) :
    C₁ = C₂ := by
  have hD : (fun μ σ => C₁ μ σ - C₂ μ σ) = 0 := by
    apply hker
    rw [extendInsert_sub]
    funext ν σ
    rw [Pi.zero_apply, Pi.zero_apply, congrFun (congrFun h ν) σ, sub_self]
  funext μ σ
  have := congrFun (congrFun hD μ) σ
  rw [Pi.zero_apply, Pi.zero_apply, sub_eq_zero] at this
  exact this

/-! ### The `Q`-weight span of the blue coupling

The blue coupling `threeBlockBlueCoeff g bdry σblue bc'`, read as a function of the blue
physical leg `σblue`, lies in the range of the blocked-region tensor map of the blue block:
it is a `regionBlockedWeight g.blue`-combination.  This is the *blue mirror* of the
complement-coupling collapse `blueRedCrossingBondProd_smul_threeBlockComplCoeff_eq` of
`TNLean/PEPS/RegionBlock/UnionInjectivityGeneral2.lean`, obtained by reading that lemma at
the geometry with the blue and complement blocks interchanged: the swapped geometry's
*complement* coupling is the original geometry's *blue* coupling, and the swapped lemma reads
it as a `regionBlockedWeight g.blue`-combination scaled by the red/blue crossing bond product.

This is the `Q`-weight span lemma the shared-corner cancellation of Step 3 needs: with the
blue block taken to be the injective completed corner `Q`, it expresses the `σ_Q`-dependence
of the corner extension's coupling as a `Q`-blocked combination, the form `Q` injectivity
inverts. -/

/-- The blue/complement swap of a three-block geometry: the same red block with the blue and
complement blocks interchanged.  Its host `univ \ red` is unchanged, so a host boundary
configuration of `g` is a host boundary configuration of the swap.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 3. -/
def ThreeBlockGeometry.swapBlueComplement (g : ThreeBlockGeometry V) :
    ThreeBlockGeometry V where
  red := g.red
  blue := g.complement
  complement := g.blue
  red_disjoint_blue := g.red_disjoint_complement
  red_disjoint_complement := g.red_disjoint_blue
  blue_disjoint_complement := g.blue_disjoint_complement.symm
  cover_univ := by rw [← g.cover_univ]; ac_rfl

omit [DecidableRel G.Adj] in
@[simp] theorem ThreeBlockGeometry.swapBlueComplement_red (g : ThreeBlockGeometry V) :
    g.swapBlueComplement.red = g.red := rfl

omit [DecidableRel G.Adj] in
@[simp] theorem ThreeBlockGeometry.swapBlueComplement_blue (g : ThreeBlockGeometry V) :
    g.swapBlueComplement.blue = g.complement := rfl

omit [DecidableRel G.Adj] in
@[simp] theorem ThreeBlockGeometry.swapBlueComplement_complement (g : ThreeBlockGeometry V) :
    g.swapBlueComplement.complement = g.blue := rfl

/-- The blue coupling of `g` is the complement coupling of the swapped geometry: both filter
the global configurations on the host label `bdry` and the `g.complement` boundary label
`bc'` and take the product over `g.blue`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 3. -/
theorem ThreeBlockGeometry.threeBlockBlueCoeff_eq_swap_threeBlockComplCoeff
    (g : ThreeBlockGeometry V)
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red))
    (σblue : RegionPhysicalConfig (V := V) (d := d) g.blue)
    (bc' : RegionBoundaryConfig (G := G) A g.complement) :
    g.threeBlockBlueCoeff bdry σblue bc' =
      g.swapBlueComplement.threeBlockComplCoeff bdry σblue bc' := by
  rw [ThreeBlockGeometry.threeBlockBlueCoeff, ThreeBlockGeometry.threeBlockComplCoeff]
  rfl

open scoped Classical in
/-- **The `Q`-weight span of the blue coupling.**  The red/blue crossing bond multiple of the
blue coupling `threeBlockBlueCoeff g bdry σblue bc'`, read as a function of the blue physical
leg `σblue`, is a `regionBlockedWeight g.blue`-combination: the indicator that some global
configuration carries the three boundary labels (host `bdry`, complement `bc'`, blue `bβ`),
contracted against the blue blocked-region weight at `bβ`.

This is the blue mirror of `blueRedCrossingBondProd_smul_threeBlockComplCoeff_eq`, read at the
blue/complement swap `g.swapBlueComplement`: the swapped geometry's complement coupling is
`g`'s blue coupling (`threeBlockBlueCoeff_eq_swap_threeBlockComplCoeff`), and the swapped
collapse reads it as a `regionBlockedWeight g.blue`-combination.  This is the `Q`-weight span
the shared-corner cancellation inverts when the blue block `Q` is injective.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 3. -/
theorem ThreeBlockGeometry.crossingBondProd_smul_threeBlockBlueCoeff_eq
    (g : ThreeBlockGeometry V)
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red))
    (bc' : RegionBoundaryConfig (G := G) A g.complement)
    (σblue : RegionPhysicalConfig (V := V) (d := d) g.blue) :
    (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ) •
        g.threeBlockBlueCoeff bdry σblue bc' =
      ∑ bβ : RegionBoundaryConfig (G := G) A g.blue,
        (if ∃ q : VirtualConfig A,
            regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q = bdry ∧
              regionBoundaryLabel (G := G) A g.complement q = bc' ∧
                regionBoundaryLabel (G := G) A g.blue q = bβ
          then (1 : ℂ) else 0) •
          regionBlockedWeight (G := G) A g.blue bβ σblue := by
  classical
  rw [g.threeBlockBlueCoeff_eq_swap_threeBlockComplCoeff bdry σblue bc',
    g.swapBlueComplement.blueRedCrossingBondProd_smul_threeBlockComplCoeff_eq
      bdry bc' σblue]
  rfl

/-! ### The `S ⊔ Q` assembly bridge

The corner extension `bareExtendInsert (R ⊆ S)` reads the insert's `R`-leg and the added
block's `S \ R`-leg as the two restrictions `restrictSubRegionσ` of a physical configuration on
`S`.  As that configuration ranges over `RegionPhysicalConfig S`, the pair of restricted legs
ranges over all of `RegionPhysicalConfig R × RegionPhysicalConfig (S \ R)`, since `S` is the
disjoint union of `R` and `S \ R`.  The assembly `assembleSubRegionσ` builds the joint
configuration from the two independent legs; restricting it back recovers each leg.  This is
the assembly bridge the kernel triviality consumes: it lets the `R`-leg and the added-block leg
be fixed independently when reading off the corner extension. -/

/-- The physical configuration on `S` assembled from an `R`-leg and a `(S \ R)`-leg, for
`R ⊆ S`: a vertex of `S` lies in `R` (read the `R`-leg) or in `S \ R` (read the added-block
leg).

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 3. -/
def assembleSubRegionσ {R S : Finset V}
    (σR : RegionPhysicalConfig (V := V) (d := d) R)
    (σQ : RegionPhysicalConfig (V := V) (d := d) (S \ R)) :
    RegionPhysicalConfig (V := V) (d := d) S :=
  fun w => if hr : w.1 ∈ R then σR ⟨w.1, hr⟩ else σQ ⟨w.1, Finset.mem_sdiff.mpr ⟨w.2, hr⟩⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- Restricting the assembled configuration to the sub-region `R` recovers the `R`-leg. -/
@[simp] theorem restrictSubRegionσ_assembleSubRegionσ {R S : Finset V} (hRS : R ⊆ S)
    (σR : RegionPhysicalConfig (V := V) (d := d) R)
    (σQ : RegionPhysicalConfig (V := V) (d := d) (S \ R)) :
    restrictSubRegionσ (V := V) (d := d) hRS (assembleSubRegionσ (V := V) σR σQ) = σR := by
  funext w
  rw [restrictSubRegionσ, assembleSubRegionσ, dif_pos w.2]

omit [Fintype V] [DecidableRel G.Adj] in
/-- Restricting the assembled configuration to the added block `S \ R` recovers the
added-block leg.  Stated for an arbitrary `S \ R ⊆ S` subset witness so it matches the witness
the corner extension carries. -/
@[simp] theorem restrictSubRegionσ_sdiff_assembleSubRegionσ {R S : Finset V}
    (hQS : S \ R ⊆ S)
    (σR : RegionPhysicalConfig (V := V) (d := d) R)
    (σQ : RegionPhysicalConfig (V := V) (d := d) (S \ R)) :
    restrictSubRegionσ (V := V) (d := d) hQS
        (assembleSubRegionσ (V := V) σR σQ) = σQ := by
  funext w
  have hnotR : w.1 ∉ R := (Finset.mem_sdiff.mp w.2).2
  rw [restrictSubRegionσ, assembleSubRegionσ, dif_neg hnotR]

/-! ### The kernel triviality of the corner extension from injectivity of the added block

The genuinely new content: when the added block `S \ R = Q` is blocked-tensor injective, the
corner extension `extendInsert (R ⊆ S)` has trivial kernel.  The argument is the source's
two-step inverse application of Lemma `injective_union`, read with the inverted block taken to
be `Q` in the host index, rather than the complement in the complement index.

Fix the `R`-physical leg `σR`.  The kernel hypothesis, read through the assembly bridge at the
joint configuration of `σR` and an arbitrary `Q`-leg `σblue`, makes the `c`-weighted blue
coupling vanish for every `σblue` and every complement boundary configuration `bc'`, where
`c bdry = C ((complement boundary equivalence).symm bdry) σR`.  The `Q`-weight span
`crossingBondProd_smul_threeBlockBlueCoeff_eq` reads the blue coupling, on the `Q`-leg, as a
combination of the `Q` blocked-region weights; injectivity of `Q` (the chosen left inverse of
the `Q` block) then forces the `c`-weighted coupling indicators to vanish for every blue
boundary configuration `bβ` and `bc'`.  Host-label surjectivity at positive bond dimensions and
the host-residual identity `regionBoundaryLabel_host_eq_hostLabelFrom` extract `c bdry = 0` at
every host residual realized by a global configuration, hence `C μ σR = 0` for every `μ`. -/

open scoped Classical in
/-- The kernel hypothesis, read through the assembly bridge at a fixed `R`-leg `σR`, makes the
`c`-weighted blue coupling of the nested geometry vanish for every added-block leg `σblue` and
every complement boundary configuration `bc'`.  Here `c bdry` is the insert coefficient at the
`R`-boundary configuration that the complement boundary equivalence sends to `bdry`.

The nested geometry's host `univ \ R = univ \ g.red` carries `bdry`, and reindexing the insert
sum along the complement boundary equivalence presents the corner extension as the
`c`-combination of the blue coupling.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 3. -/
theorem blueCoeff_combination_eq_zero_of_extendInsert_zero {R S : Finset V} (hRS : R ⊆ S)
    (C : RegionInsert (G := G) (d := d) A R)
    (hker : bareExtendInsert (G := G) hRS C = 0)
    (σR : RegionPhysicalConfig (V := V) (d := d) R)
    (σblue : RegionPhysicalConfig (V := V) (d := d) (S \ R))
    (bc' : RegionBoundaryConfig (G := G) A (Finset.univ \ S)) :
    ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ R),
        C (regionComplementBoundaryConfigEquiv (G := G) A R |>.symm bdry) σR •
          (nestedThreeBlockGeometry (V := V) hRS).threeBlockBlueCoeff bdry σblue bc' = 0 := by
  classical
  -- Read the kernel hypothesis at the assembled configuration and the complement boundary
  -- configuration that the equivalence reaches.
  have hval := congrFun (congrFun hker
    (regionComplementBoundaryConfigEquiv (G := G) A S |>.symm bc'))
    (assembleSubRegionσ (V := V) σR σblue)
  rw [Pi.zero_apply, Pi.zero_apply, bareExtendInsert] at hval
  -- The complement boundary configuration of `S` at the reached argument is `bc'`.
  have hbc : regionComplementBoundaryConfig (G := G) A S
      (regionComplementBoundaryConfigEquiv (G := G) A S |>.symm bc') = bc' := by
    rw [← regionComplementBoundaryConfigEquiv_apply, Equiv.apply_symm_apply]
  -- Reindex the `μ`-sum (over `∂R`) along the complement boundary equivalence to a `bdry`-sum,
  -- then match each summand to the corresponding `hval` summand: the assembled legs restrict
  -- back to `σR` and `σblue`, and the reached complement boundary is `bc'`.
  rw [← Equiv.sum_comp (regionComplementBoundaryConfigEquiv (G := G) A R)
      (fun bdry => C (regionComplementBoundaryConfigEquiv (G := G) A R |>.symm bdry) σR •
        (nestedThreeBlockGeometry (V := V) hRS).threeBlockBlueCoeff bdry σblue bc')]
  rw [← hval]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [Equiv.symm_apply_apply, smul_eq_mul, hbc, regionComplementBoundaryConfigEquiv_apply]
  -- The assembled legs restrict back to `σR` and `σblue`; the boundary residual matches.
  have hlegR : restrictSubRegionσ (V := V) (d := d) hRS
      (assembleSubRegionσ (V := V) σR σblue) = σR :=
    restrictSubRegionσ_assembleSubRegionσ hRS σR σblue
  have hlegQ : ∀ hQS : S \ R ⊆ S,
      restrictSubRegionσ (V := V) (d := d) hQS
        (assembleSubRegionσ (V := V) σR σblue) = σblue := by
    intro hQS; funext w
    have hnotR : w.1 ∉ R := (Finset.mem_sdiff.mp w.2).2
    rw [restrictSubRegionσ, assembleSubRegionσ, dif_neg hnotR]
  rw [hlegR]
  congr 2
  exact (hlegQ _).symm

open scoped Classical in
/-- **The kernel triviality of the corner extension.**  For nested regions `R ⊆ S`, if the
added block `S \ R` is blocked-tensor injective and the bond dimensions are positive, then the
only insert on `R` whose corner extension on `S` vanishes is the zero insert.

Fixing the `R`-leg `σR`, the kernel makes the `c`-weighted blue coupling vanish for every
`Q`-leg and complement boundary configuration
(`blueCoeff_combination_eq_zero_of_extendInsert_zero`).
The `Q`-weight span `crossingBondProd_smul_threeBlockBlueCoeff_eq` reads the blue coupling on
the `Q`-leg as a `Q`-blocked combination; injectivity of `Q = g.blue` forces, for every blue and
complement boundary configuration, the `c`-weighted realization indicator to vanish.  Host-label
surjectivity (`exists_regionBoundaryLabel_host_eq`) and the host-residual identity
(`regionBoundaryLabel_host_eq_hostLabelFrom`) then extract `c bdry = 0` at every realized host
residual, so `C μ σR = 0` for every `μ`.  This needs only injectivity of `Q`, never of
`univ \ R`.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (add two-two tensors in the corner and invert);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3. -/
theorem extendInsert_kernel_trivial_of_addedInjective {R S : Finset V} (hRS : R ⊆ S)
    (hadd : RegionBlockedTensorInjective (G := G) A (S \ R))
    (hpos : ∀ eg : Edge G, 0 < A.bondDim eg)
    (C : RegionInsert (G := G) (d := d) A R)
    (h : extendInsert (G := G) hRS C = 0) :
    C = 0 := by
  classical
  set g := nestedThreeBlockGeometry (V := V) hRS with hg
  -- The corner extension vanishes iff the bare extension vanishes (nonzero divisor).
  have hbare : bareExtendInsert (G := G) hRS C = 0 := by
    have hne : (regionInteriorBondProd (G := G) A (Finset.univ \ S) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (regionInteriorBondProd_pos (G := G) A (Finset.univ \ S) hpos).ne'
    funext ν σ
    have := congrFun (congrFun h ν) σ
    rw [Pi.zero_apply, Pi.zero_apply, extendInsert_eq_smul_bare, mul_eq_zero] at this
    rw [Pi.zero_apply, Pi.zero_apply]
    rcases this with hz | hz
    · exact absurd (inv_eq_zero.mp hz) hne
    · exact hz
  -- Fix the `R`-leg; show the insert coefficient family at that leg is zero.
  funext μ σR
  rw [Pi.zero_apply, Pi.zero_apply]
  -- The `c`-coefficient family indexed by the host residual of `g`.
  set c : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red) → ℂ :=
    fun bdry => C (regionComplementBoundaryConfigEquiv (G := G) A R |>.symm bdry) σR with hc
  -- The blue coupling combination of `c` vanishes for every `Q`-leg and complement boundary.
  have hblue : ∀ (σblue : RegionPhysicalConfig (V := V) (d := d) g.blue)
      (bc' : RegionBoundaryConfig (G := G) A g.complement),
      ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
          c bdry • g.threeBlockBlueCoeff bdry σblue bc' = 0 := fun σblue bc' =>
    blueCoeff_combination_eq_zero_of_extendInsert_zero hRS C hbare σR σblue bc'
  -- The `Q`-weight span strips the blue block: for every blue boundary `bβ` and complement
  -- boundary `bc'`, the `c`-weighted realization indicator vanishes.
  have hrow : ∀ (bβ : RegionBoundaryConfig (G := G) A g.blue)
      (bc' : RegionBoundaryConfig (G := G) A g.complement),
      ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
          c bdry •
            (if ∃ q : VirtualConfig A,
                regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q = bdry ∧
                  regionBoundaryLabel (G := G) A g.complement q = bc' ∧
                    regionBoundaryLabel (G := G) A g.blue q = bβ
              then (1 : ℂ) else 0) = 0 := by
    intro bβ bc'
    -- The `Q`-blocked map of the `c`-weighted indicator row is the crossing multiple of the
    -- `c`-weighted blue coupling, which vanishes.
    have hmap : regionBlockedTensorMap (G := G) A g.blue
        (fun bβ' => ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
          c bdry •
            (if ∃ q : VirtualConfig A,
                regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q = bdry ∧
                  regionBoundaryLabel (G := G) A g.complement q = bc' ∧
                    regionBoundaryLabel (G := G) A g.blue q = bβ'
              then (1 : ℂ) else 0)) = 0 := by
      funext σblue
      rw [regionBlockedTensorMap_apply, Pi.zero_apply]
      -- Distribute each coefficient sum over the weight, then swap the summation order.
      rw [Finset.sum_congr rfl (g := fun bβ' =>
            ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
              (c bdry •
                  (if ∃ q : VirtualConfig A,
                      regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q = bdry ∧
                        regionBoundaryLabel (G := G) A g.complement q = bc' ∧
                          regionBoundaryLabel (G := G) A g.blue q = bβ'
                    then (1 : ℂ) else 0)) •
                regionBlockedWeight (G := G) A g.blue bβ' σblue)
          (fun bβ' _ => Finset.sum_smul)]
      rw [Finset.sum_comm]
      rw [show (∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
            ∑ bβ' : RegionBoundaryConfig (G := G) A g.blue,
              (c bdry •
                  (if ∃ q : VirtualConfig A,
                      regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q = bdry ∧
                        regionBoundaryLabel (G := G) A g.complement q = bc' ∧
                          regionBoundaryLabel (G := G) A g.blue q = bβ'
                    then (1 : ℂ) else 0)) •
                regionBlockedWeight (G := G) A g.blue bβ' σblue) =
          ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
            c bdry •
              ((g.swapBlueComplement.blueRedCrossingBondProd A : ℂ) •
                g.threeBlockBlueCoeff bdry σblue bc') from ?_]
      · -- The `c`-combination of the crossing multiples of the blue coupling vanishes.
        rw [Finset.sum_congr rfl (g := fun bdry =>
              (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ) •
                (c bdry • g.threeBlockBlueCoeff bdry σblue bc'))
            (fun bdry _ => smul_comm _ _ _),
          ← Finset.smul_sum, hblue σblue bc', smul_zero]
      · refine Finset.sum_congr rfl (fun bdry _ => ?_)
        rw [g.crossingBondProd_smul_threeBlockBlueCoeff_eq bdry bc' σblue, Finset.smul_sum]
        refine Finset.sum_congr rfl (fun bβ' _ => ?_)
        rw [smul_assoc]
    have := regionBlockedTensorMap_injective_of_injective (G := G) A g.blue hadd
      (a₁ := fun bβ' => ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
        c bdry •
          (if ∃ q : VirtualConfig A,
              regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q = bdry ∧
                regionBoundaryLabel (G := G) A g.complement q = bc' ∧
                  regionBoundaryLabel (G := G) A g.blue q = bβ'
            then (1 : ℂ) else 0))
      (a₂ := 0) (by rw [hmap, map_zero])
    exact congrFun this bβ
  -- Extract `c` at the host residual realized by a global configuration carrying `μ`.
  have hμ : c (regionComplementBoundaryConfig (G := G) A R μ) = C μ σR := by
    rw [hc, ← regionComplementBoundaryConfigEquiv_apply]
    simp only [Equiv.symm_apply_apply]
  rw [← hμ]
  -- Realize the host residual `complBdry R μ` by a global configuration `q`.
  obtain ⟨q, hq⟩ := g.exists_regionBoundaryLabel_host_eq
    (regionComplementBoundaryConfig (G := G) A R μ) hpos
  -- Apply the vanishing indicator row at the blue and complement labels of `q`.
  have hq0 := hrow (regionBoundaryLabel (G := G) A g.blue q)
    (regionBoundaryLabel (G := G) A g.complement q)
  rw [Finset.sum_eq_single (regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q)] at hq0
  · rw [if_pos ⟨q, rfl, rfl, rfl⟩, smul_eq_mul, mul_one] at hq0
    rw [hq] at hq0; exact hq0
  · intro bdry' _ hne
    -- Any global configuration realizing `q`'s blue and complement labels has host residual
    -- `host q`, so the indicator at `bdry' ≠ host q` is zero.
    rw [if_neg ?_, smul_zero]
    rintro ⟨q', hh', hc', hb'⟩
    apply hne
    have e1 := g.regionBoundaryLabel_host_eq_hostLabelFrom q'
    have e2 := g.regionBoundaryLabel_host_eq_hostLabelFrom q
    rw [hh', hb', hc'] at e1
    rw [e2, ← e1]
  · intro h'; exact absurd (Finset.mem_univ _) h'

/-! ### The shared-corner cancellation

With the kernel triviality and the additivity of the corner extension, two inserts on `R` whose
corner extensions on `S` agree are equal, provided the added block `S \ R` is injective.  This
is the open-boundary cancellation of Step 3 in its reusable generic form: cancel the injective
added block from an equality of corner extensions, needing only that block's injectivity. -/

/-- **The shared-corner cancellation.**  For nested regions `R ⊆ S` with the added block
`S \ R` blocked-tensor injective and positive bond dimensions, two inserts on `R` whose corner
extensions on `S` agree are equal.  The kernel triviality
`extendInsert_kernel_trivial_of_addedInjective` and the difference law `extendInsert_sub` feed
the kernel reduction `extendInsert_injective_of_kernel_trivial`.

This cancels the injective added block `S \ R = Q` from an open-boundary equality of inserts,
needing only injectivity of `Q` and never of `univ \ R`.  It is the reusable engine of Step 3's
shared-corner cancellation, the obstruction recorded in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (add two-two tensors in the corner and invert);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3. -/
theorem extendInsert_cancel_addedInjective {R S : Finset V} (hRS : R ⊆ S)
    (hadd : RegionBlockedTensorInjective (G := G) A (S \ R))
    (hpos : ∀ eg : Edge G, 0 < A.bondDim eg)
    (C₁ C₂ : RegionInsert (G := G) (d := d) A R)
    (h : extendInsert (G := G) hRS C₁ = extendInsert (G := G) hRS C₂) :
    C₁ = C₂ :=
  extendInsert_injective_of_kernel_trivial hRS
    (fun D hD => extendInsert_kernel_trivial_of_addedInjective hRS hadd hpos D hD) C₁ C₂ h

end PEPS
end TNLean
