import TNLean.PEPS.RegionBlock.Recovery2
import TNLean.PEPS.VertexComplement.KernelDescent

/-!
# Region physical-to-virtual recovery: the spanning step and the transfer datum

This file closes the last gating ingredient of the per-edge gauge for the normal
PEPS Fundamental Theorem (remaining obligation 4 of
`docs/paper-gaps/peps_normal_ft_section3_route.tex`). It supplies the region
analogue of the physical-to-virtual recovery `physical_to_virtual_insertion`,
producing the `RegionInsertionTransfer` datum unconditionally from `SameState`
and region injectivity, and assembles the per-edge gauge family.

The conditional recovery `regionTransferMatrix_realizes_of_image` reduces the
realization `hreal` to two facts about the transferred in-region endpoint
operator `O_A := regionInsertionOp A R f hvA M.transpose`: that it preserves the
image of the second tensor's local tensor map at the in-region endpoint vertex
`v` (`himage`), and that its virtual pullback through the second tensor is the
matrix insertion of `(regionTransferMatrix … M)ᵀ` on the boundary edge `f`
(`hform`). At the edge level these are the two consequences
`physical_to_virtual_insertion` extracts from the resonate identity.

At the region level both follow from a single **region spanning** fact: the
state-vector coefficients `stateOpenCoeff B σ τ`, as the physical configurations
`σ, τ` range, span the full local virtual coefficient space at `v`. The pinning
`regionInsertedCoeff_eq_smul_op_regionStateVec`, transferred across `SameState`,
identifies `O_A` with `regionInsertionOp B … N.transpose` on the state vectors;
the spanning then extends this identification to all of the second tensor's local
tensor images, giving `hreal` directly.

The spanning is the dual of injectivity of the blocked complement of `{v}`: the
state-vector coefficient at `v` is a column of the vertex-complement tensor
family of `B`, whose linear independence (`vertexComplementTensorInjective_of_isVertexInjective`)
makes its columns span. This is the region analogue of the blocked-middle
contraction inverse `edgeMiddleLeftInverse` of `physical_to_virtual_insertion`:
where the edge proof inverts the middle block to strip the context, the region
proof uses the dual span of the blocked complement of the endpoint vertex.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Lemma
  `inj_isomorph`, lines 254--582 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Abstract column-spanning from row linear independence

A finite family of vectors in a function space, viewed as the rows of a matrix,
is linearly independent exactly when the columns span the full row-index space.
This is the rank-duality fact underlying the region spanning argument. -/

/-- If a finite family `g : ι → (κ → ℂ)` is linearly independent, then the
"columns" `fun k => fun i => g i k` span the full row-index space `ι → ℂ`. This
is the row-rank–column-rank duality: linear independence of the rows forces the
column span to have full dimension. -/
theorem span_cols_eq_top_of_linearIndependent
    {ι κ : Type*} [Finite ι] [Finite κ]
    (g : ι → (κ → ℂ)) (hg : LinearIndependent ℂ g) :
    Submodule.span ℂ (Set.range (fun k : κ => fun i : ι => g i k)) = ⊤ := by
  classical
  cases nonempty_fintype ι
  cases nonempty_fintype κ
  set M : Matrix ι κ ℂ := fun i k => g i k with hM
  have hrow : M.row = g := by funext i; rfl
  have hrank : M.rank = Fintype.card ι := by
    have hrli : LinearIndependent ℂ M.row := by rw [hrow]; exact hg
    exact hrli.rank_matrix
  have hcols : M.col = (fun k : κ => fun i : ι => g i k) := by funext k i; rfl
  have hspanfr :
      Module.finrank ℂ (Submodule.span ℂ (Set.range M.col)) = Fintype.card ι := by
    rw [← Matrix.rank_eq_finrank_span_cols, hrank]
  have hambient : Module.finrank ℂ (ι → ℂ) = Fintype.card ι := by simp
  rw [← hcols]
  apply Submodule.eq_top_of_finrank_eq
  rw [hspanfr, hambient]

/-! ### The state-vector coefficient as a vertex-complement column

The coefficient `stateOpenCoeff B σ τ` through which the closed state vector at
the in-region endpoint `v` factors is exactly the vertex-complement tensor family
of `B` at `v`, evaluated at the physical configuration assembled from `σ` and
`τ`. This identifies it as a column of that family, so the family's linear
independence makes these coefficients span. -/

/-- The physical configuration on `V\{v}` read off `assembleRegionσ R σ τ` at the
in-region endpoint vertex `v`. -/
noncomputable def regionComplementPhysicalConfig (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    VertexComplementPhysicalConfig (V := V) (d := d)
      (regionBoundaryEdgeInVertex (G := G) R f) :=
  fun w => assembleRegionσ (V := V) (d := d) R σ τ w.1

open scoped Classical in
/-- **The state-vector coefficient is a vertex-complement column.** The
coefficient `stateOpenCoeff B σ τ` equals the vertex-complement tensor family of
`B` at the in-region endpoint `v`, evaluated at the assembled physical
configuration. Both are the blocked contraction of all tensors away from `v` with
`v`'s local virtual configuration left open. -/
theorem stateOpenCoeff_eq_vertexComplementTensorFamily (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    stateOpenCoeff (G := G) B R f σ τ =
      (fun η : LocalVirtualConfig B (regionBoundaryEdgeInVertex (G := G) R f) =>
        vertexComplementTensorFamily (G := G) B (regionBoundaryEdgeInVertex (G := G) R f)
          η (regionComplementPhysicalConfig (G := G) R f σ τ)) := by
  classical
  set v := regionBoundaryEdgeInVertex (G := G) R f with hv
  funext η
  rw [stateOpenCoeff, vertexComplementTensorFamily, vertexComplementWeight]
  -- The two filtered sums agree (the v-star label equals the region vertex
  -- local config), and the products agree under the index reshape `{v}ᶜ`/`≠ v`.
  refine Finset.sum_congr ?_ (fun ζ _ => ?_)
  · ext ζ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  · -- Reshape the product over `({v}ᶜ : Finset V)` to the subtype `{w // w ≠ v}`.
    rw [Finset.prod_subtype (({v} : Finset V)ᶜ)
      (fun x => by rw [Finset.mem_compl, Finset.mem_singleton])
      (fun w => B.component w (fun ie => ζ ie.1)
        (assembleRegionσ (V := V) (d := d) R σ τ w))]
    rfl

omit [DecidableRel G.Adj] in
/-- **The assembled-complement configuration is surjective.** Every physical
configuration on `V\{v}` arises as `regionComplementPhysicalConfig R f σ τ` for
some region and complement physical configurations. Since the in-region endpoint
`v` lies in `R`, any vertex `w ≠ v` is covered by `σ` (if `w ∈ R`) or by `τ` (if
`w ∉ R`), so the assembled configuration can match any prescribed values on
`V\{v}`. -/
theorem regionComplementPhysicalConfig_surjective (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    Function.Surjective
      (fun p : RegionPhysicalConfig (V := V) (d := d) R ×
          RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R) =>
        regionComplementPhysicalConfig (G := G) R f p.1 p.2) := by
  classical
  set v := regionBoundaryEdgeInVertex (G := G) R f with hv
  have hvR : v ∈ R := regionBoundaryEdgeInVertex_mem (G := G) R f
  -- The out-of-region endpoint of `f`: distinct from `v` and outside `R`, it
  -- supplies an inhabitant of `Fin d` through `ρ`.
  set vout : V := if f.1.1.1 ∈ R then f.1.1.2 else f.1.1.1 with hvout
  have hvoutR : vout ∉ R := by
    rw [hvout]; rcases f.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [if_pos h1]; exact h2
    · rw [if_neg h1]; exact h1
  have hvoutv : vout ≠ v := by
    intro hc; rw [hc] at hvoutR; exact hvoutR hvR
  intro ρ
  -- Use `ρ vout` as the (never-read) default value at `v`.
  refine ⟨(fun w : {w : V // w ∈ R} =>
        if h : w.1 = v then ρ ⟨vout, hvoutv⟩ else ρ ⟨w.1, h⟩,
      fun w : {w : V // w ∈ Finset.univ \ R} =>
        ρ ⟨w.1, fun hc => by
          have : w.1 ∈ R := hc ▸ hvR
          exact absurd this (by have := w.2; rw [Finset.mem_sdiff] at this; exact this.2)⟩), ?_⟩
  funext w
  -- Evaluate the assembled config at `w.1 ≠ v`.
  change assembleRegionσ (V := V) (d := d) R _ _ w.1 = ρ w
  by_cases hwR : w.1 ∈ R
  · simp only [assembleRegionσ, dif_pos hwR]
    rw [dif_neg w.2]
  · simp only [assembleRegionσ, dif_neg hwR]

open scoped Classical in
/-- **Region spanning at the in-region endpoint.** The state-vector coefficients
`stateOpenCoeff B σ τ`, as the region and complement physical configurations
range, span the full local virtual coefficient space at the in-region endpoint
`v`, provided `B` is vertex-injective with positive bond dimensions.

This is the region analogue of the blocked-middle contraction inverse of
`physical_to_virtual_insertion`: the state-vector coefficient is a column of the
vertex-complement tensor family of `B` at `v`, whose linear independence
(`vertexComplementTensorInjective_of_isVertexInjective`) forces the columns to
span; the assembled-complement configuration is surjective, so every column is
realized by some `σ, τ`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem span_stateOpenCoeff_eq_top (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hB : IsVertexInjective B) (hposB : ∀ e : Edge G, 0 < B.bondDim e) :
    Submodule.span ℂ
        (Set.range (fun p : RegionPhysicalConfig (V := V) (d := d) R ×
            RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R) =>
          stateOpenCoeff (G := G) B R f p.1 p.2)) = ⊤ := by
  classical
  set v := regionBoundaryEdgeInVertex (G := G) R f with hv
  -- Linear independence of the vertex-complement tensor family of `B` at `v`.
  have hli : LinearIndependent ℂ (vertexComplementTensorFamily (G := G) B v) :=
    vertexComplementTensorInjective_of_isVertexInjective (G := G) (A := B) (v := v) hB hposB
  -- Its columns span the full local virtual coefficient space at `v`.
  have hcols := span_cols_eq_top_of_linearIndependent
    (vertexComplementTensorFamily (G := G) B v) hli
  -- The state-vector coefficients realize every column, by surjectivity of the
  -- assembled-complement configuration.
  have hsurj := regionComplementPhysicalConfig_surjective (G := G) (d := d) R f
  refine le_antisymm le_top ?_
  rw [← hcols]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨ρ, rfl⟩
  obtain ⟨p, hp⟩ := hsurj ρ
  simp only at hp
  have hcol : (fun i : LocalVirtualConfig B v =>
      vertexComplementTensorFamily (G := G) B v i ρ) =
      stateOpenCoeff (G := G) B R f p.1 p.2 := by
    rw [stateOpenCoeff_eq_vertexComplementTensorFamily]
    funext i
    rw [hp]
  change (fun i : LocalVirtualConfig B v =>
      vertexComplementTensorFamily (G := G) B v i ρ) ∈ _
  rw [hcol]
  exact Submodule.subset_span ⟨p, rfl⟩

/-! ### Coincidence of the single-vertex tensor images and image preservation

The region spanning identifies the image of the local tensor map at the in-region
endpoint `v` with the span of the closed state vectors there. Under `SameState`
the closed state vectors of the two tensors coincide, so the two single-vertex
tensor images coincide. Since the transferred endpoint operator
`regionInsertionOp A R f hvA M.transpose` always outputs in the image of the first
tensor's local tensor map, it preserves the (shared) image of the second tensor's
local tensor map. This is the `himage` half of
`regionTransferMatrix_realizes_of_image`. -/

/-- The image of the local tensor map at the in-region endpoint `v` is the span of
the closed state vectors there. The state vectors are local tensor images
(`regionStateVec_eq_localTensorMap`), and their coefficients span the local
virtual coefficient space (`span_stateOpenCoeff_eq_top`), so their span is the
whole image. -/
theorem range_localTensorMap_eq_span_stateVec (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hB : IsVertexInjective B) (hposB : ∀ e : Edge G, 0 < B.bondDim e) :
    LinearMap.range (localTensorMap B (regionBoundaryEdgeInVertex (G := G) R f)) =
      Submodule.span ℂ (Set.range (fun p : RegionPhysicalConfig (V := V) (d := d) R ×
          RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R) =>
        regionStateVec (G := G) B R f p.1 p.2)) := by
  rw [LinearMap.range_eq_map, ← span_stateOpenCoeff_eq_top B R f hB hposB, LinearMap.map_span]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
    exact ⟨p, regionStateVec_eq_localTensorMap B R f p.1 p.2⟩
  · rintro ⟨p, rfl⟩
    exact ⟨stateOpenCoeff (G := G) B R f p.1 p.2, ⟨p, rfl⟩,
      (regionStateVec_eq_localTensorMap B R f p.1 p.2).symm⟩

/-- **Coincidence of the single-vertex tensor images.** Under `SameState`, the
images of the local tensor maps of the two tensors at the in-region endpoint `v`
coincide. Both equal the span of the closed state vectors there
(`range_localTensorMap_eq_span_stateVec`), and the closed state vectors are
`SameState`-invariant (`regionStateVec_sameState`).

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem range_localTensorMap_eq_of_sameState (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hAB : SameState A B) (hA : IsVertexInjective A) (hB : IsVertexInjective B)
    (hposA : ∀ e : Edge G, 0 < A.bondDim e) (hposB : ∀ e : Edge G, 0 < B.bondDim e) :
    LinearMap.range (localTensorMap A (regionBoundaryEdgeInVertex (G := G) R f)) =
      LinearMap.range (localTensorMap B (regionBoundaryEdgeInVertex (G := G) R f)) := by
  rw [range_localTensorMap_eq_span_stateVec A R f hA hposA,
    range_localTensorMap_eq_span_stateVec B R f hB hposB]
  congr 1
  ext x
  simp only [Set.mem_range]
  constructor
  · rintro ⟨p, rfl⟩; exact ⟨p, (regionStateVec_sameState hAB R f p.1 p.2).symm⟩
  · rintro ⟨p, rfl⟩; exact ⟨p, regionStateVec_sameState hAB R f p.1 p.2⟩

/-- **Image preservation (the `himage` half).** The transferred in-region endpoint
operator of the first tensor preserves the image of the second tensor's local
tensor map at `v`: it maps each local tensor image into itself, so the projector
onto that image fixes its output.

The operator `regionInsertionOp A R f hvA M.transpose` always outputs in the image
of the first tensor's local tensor map; under `SameState` that image equals the
second tensor's (`range_localTensorMap_eq_of_sameState`), so the output is a second
tensor image and the projector fixes it. This is the region analogue of the image
preservation `physical_to_virtual_insertion` extracts at the edge level.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertionOp_localProjectorAt_eq (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hAB : SameState A B) (hA : IsVertexInjective A) (hB : IsVertexInjective B)
    (hposA : ∀ e : Edge G, 0 < A.bondDim e) (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (c : LocalVirtualConfig B (regionBoundaryEdgeInVertex (G := G) R f) → ℂ) :
    localProjectorAt B hvB
        (regionInsertionOp (G := G) A R f hvA M.transpose
          (localTensorMap B (regionBoundaryEdgeInVertex (G := G) R f) c)) =
      regionInsertionOp (G := G) A R f hvA M.transpose
        (localTensorMap B (regionBoundaryEdgeInVertex (G := G) R f) c) := by
  have hmem : regionInsertionOp (G := G) A R f hvA M.transpose
      (localTensorMap B (regionBoundaryEdgeInVertex (G := G) R f) c) ∈
      LinearMap.range (localTensorMap B (regionBoundaryEdgeInVertex (G := G) R f)) := by
    rw [← range_localTensorMap_eq_of_sameState A B R f hAB hA hB hposA hposB, regionInsertionOp]
    exact LinearMap.mem_range_self _ _
  obtain ⟨c', hc'⟩ := hmem
  rw [← hc', localProjectorAt_apply_localTensorMap]

/-! ### The region insertion transfer datum from a realized matrix transfer

Given the region physical-to-virtual realization `hreal` in both directions
(`A → B` and `B → A`), the region-inserted coefficients of the two tensors are
matched (`regionInsertedCoeff_transfer_of_realizes`), and the explicit transfer
maps assemble into a `RegionInsertionTransfer` datum. Multiplicativity and
unitality of the forward transfer follow from injectivity of the region-inserted
coefficient (`regionInsertedCoeff_injective`) and the matched coefficients, as at
the edge level (`edgeTransferMatrix_mul`, `edgeTransferMatrix_one`).

The realization `hreal` is the region analogue of the physical-to-virtual
recovery `physical_to_virtual_insertion`; the conditional recovery
`regionTransferMatrix_realizes_of_image` reduces it to the two facts that the
transferred endpoint operator preserves the second tensor's image at the
in-region vertex and that its virtual pullback is of incident-matrix form. -/

/-- The matched-coefficient identity supplied by a realized matrix transfer: with
both the bond-product equality and the realization `hreal`, the region-inserted
coefficient of `M` in the first tensor equals that of `N` in the second. This is
the `RegionInsertionTransfer.fwd_coeff` ingredient, abbreviating
`regionInsertedCoeff_transfer_of_realizes`. -/
theorem regionInsertedCoeff_eq_of_realizes (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hAB : SameState A B)
    (hbond : regionInteriorBondProd (G := G) A R = regionInteriorBondProd (G := G) B R)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (hreal : ∀ c : LocalVirtualConfig B (regionBoundaryEdgeInVertex (G := G) R f) → ℂ,
      regionInsertionOp (G := G) A R f hvA M.transpose
          (localTensorMap B (regionBoundaryEdgeInVertex (G := G) R f) c) =
        localTensorMap B (regionBoundaryEdgeInVertex (G := G) R f)
          (localIncidentMatrixOp B (regionBoundaryEdgeInIncident (G := G) R f) N.transpose c))
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f M σ τ =
      regionInsertedCoeff (G := G) B R f N σ τ :=
  regionInsertedCoeff_transfer_of_realizes A B R f hvA hvB hAB hbond M N hreal σ τ

/-- The realization hypothesis bundle: the region physical-to-virtual realization
of `regionTransferMatrix … M` for every inserted matrix `M`. This is exactly the
per-matrix conclusion of `regionTransferMatrix_realizes_of_image`, the region
analogue of `physical_to_virtual_insertion`. -/
def RegionTransferRealizes (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hposB : ∀ e : Edge G, 0 < B.bondDim e) : Prop :=
  ∀ (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (c : LocalVirtualConfig B (regionBoundaryEdgeInVertex (G := G) R f) → ℂ),
    regionInsertionOp (G := G) A R f hvA M.transpose
        (localTensorMap B (regionBoundaryEdgeInVertex (G := G) R f) c) =
      localTensorMap B (regionBoundaryEdgeInVertex (G := G) R f)
        (localIncidentMatrixOp B (regionBoundaryEdgeInIncident (G := G) R f)
          (regionTransferMatrix (G := G) A B R f hvA hvB hposB M).transpose c)

/-- **Region insertion transfer datum from a realized matrix transfer.** Given the
region physical-to-virtual realization in both directions, matched bond products,
`SameState`, and region/complement injectivity, the explicit transfer maps
`regionTransferMatrix` assemble into a `RegionInsertionTransfer` datum.

The matched coefficients are `regionInsertedCoeff_transfer_of_realizes`; the
forward transfer is multiplicative and unital by injectivity of the
region-inserted coefficient (`regionInsertedCoeff_injective`) together with the
anti-homomorphism of `regionInsertionOp` and the `SameState` identity
coefficient, mirroring `edgeTransferMatrix_mul`/`edgeTransferMatrix_one`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionTransferMatrix_mul_of_realizes (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (hrealAB : RegionTransferRealizes (G := G) A B R f hvA hvB hposB)
    (M M' : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ) :
    regionTransferMatrix (G := G) A B R f hvA hvB hposB (M * M') =
      regionTransferMatrix (G := G) A B R f hvA hvB hposB M *
        regionTransferMatrix (G := G) A B R f hvA hvB hposB M' := by
  classical
  set inc := regionBoundaryEdgeInIncident (G := G) R f with hinc
  set O := regionInsertionOp (G := G) A R f hvA (M * M').transpose with hO
  -- Abbreviate the three transfer matrices.
  set Nmm := regionTransferMatrix (G := G) A B R f hvA hvB hposB (M * M') with hNmm
  set Nm := regionTransferMatrix (G := G) A B R f hvA hvB hposB M with hNm
  set Nm' := regionTransferMatrix (G := G) A B R f hvA hvB hposB M' with hNm'
  -- `O` realizes `Nmm` on `B`'s images (the hypothesis `hrealAB`).
  have hrealmm : ∀ c, O (localTensorMap B (regionBoundaryEdgeInVertex (G := G) R f) c) =
      localTensorMap B (regionBoundaryEdgeInVertex (G := G) R f)
        (localIncidentMatrixOp B inc Nmm.transpose c) := hrealAB (M * M')
  -- `O` also realizes `Nm * Nm'`, by the anti-homomorphism of `regionInsertionOp`
  -- and the composite incident-matrix structure.
  have hrealprod : ∀ c, O (localTensorMap B (regionBoundaryEdgeInVertex (G := G) R f) c) =
      localTensorMap B (regionBoundaryEdgeInVertex (G := G) R f)
        (localIncidentMatrixOp B inc (Nm * Nm').transpose c) := by
    intro c
    have hcomp : localIncidentMatrixOp B inc (Nm * Nm').transpose =
        (localIncidentMatrixOp B inc Nm.transpose).comp
          (localIncidentMatrixOp B inc Nm'.transpose) := by
      rw [Matrix.transpose_mul]
      exact (localIncidentMatrixOp_comp B inc Nm.transpose Nm'.transpose).symm
    rw [hcomp, LinearMap.comp_apply, hO, Matrix.transpose_mul, regionInsertionOp_mul,
      LinearMap.comp_apply, hrealAB M', hrealAB M, ← hNm, ← hNm']
  -- Both incident-matrix operations equal the virtual pullback of `O`; read off.
  have h1 : localIncidentMatrixOp B inc Nmm.transpose =
      localVirtualOpOfPhysicalOpAt B hvB O :=
    (localVirtualOpOfPhysicalOpAt_eq_of_realizes B hvB O _ hrealmm).symm
  have h2 : localIncidentMatrixOp B inc (Nm * Nm').transpose =
      localVirtualOpOfPhysicalOpAt B hvB O :=
    (localVirtualOpOfPhysicalOpAt_eq_of_realizes B hvB O _ hrealprod).symm
  have hops : localIncidentMatrixOp B inc Nmm.transpose =
      localIncidentMatrixOp B inc (Nm * Nm').transpose := h1.trans h2.symm
  have hread := congrArg
    (incidentMatrixOfLocalOp B inc (edgeIncidentReferenceResidual B inc hposB)) hops
  rw [incidentMatrixOfLocalOp_localIncidentMatrixOp,
    incidentMatrixOfLocalOp_localIncidentMatrixOp] at hread
  exact Matrix.transpose_injective hread

/-- The forward transfer is unital under a realized matrix transfer. -/
theorem regionTransferMatrix_one_of_realizes (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hAB : SameState A B)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (hDim : A.bondDim = B.bondDim)
    (hrealAB : RegionTransferRealizes (G := G) A B R f hvA hvB hposB) :
    regionTransferMatrix (G := G) A B R f hvA hvB hposB 1 = 1 := by
  refine regionInsertedCoeff_injective (G := G) B R hRB hCB hposB f _ 1 (fun σ τ => ?_)
  rw [← regionInsertedCoeff_transfer_of_realizes A B R f hvA hvB hAB
      (regionInteriorBondProd_congr A B R hDim) 1 _ (hrealAB 1) σ τ,
    regionInsertedCoeff_one_eq_stateCoeff (G := G) A R f σ τ,
    regionInsertedCoeff_one_eq_stateCoeff (G := G) B R f σ τ,
    regionInteriorBondProd_congr A B R hDim, hAB _]

/-- **Region insertion transfer datum from a realized matrix transfer.** Given the
region physical-to-virtual realization in both directions, matched bond products,
`SameState`, and region/complement injectivity, the explicit transfer maps
`regionTransferMatrix` assemble into a `RegionInsertionTransfer` datum.

The matched coefficients are `regionInsertedCoeff_transfer_of_realizes`; the
forward transfer is multiplicative (`regionTransferMatrix_mul_of_realizes`) and
unital (`regionTransferMatrix_one_of_realizes`), mirroring `edgeTransferMatrix_mul`
and `edgeTransferMatrix_one`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def regionInsertionTransfer_of_realizes (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hAB : SameState A B)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hposA : ∀ e : Edge G, 0 < A.bondDim e)
    (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (hDim : A.bondDim = B.bondDim)
    (hrealAB : RegionTransferRealizes (G := G) A B R f hvA hvB hposB)
    (hrealBA : RegionTransferRealizes (G := G) B A R f hvB hvA hposA) :
    RegionInsertionTransfer (G := G) A B R f where
  fwd M := regionTransferMatrix (G := G) A B R f hvA hvB hposB M
  bwd N := regionTransferMatrix (G := G) B A R f hvB hvA hposA N
  fwd_coeff M σ τ :=
    regionInsertedCoeff_transfer_of_realizes A B R f hvA hvB hAB
      (regionInteriorBondProd_congr A B R hDim) M _ (hrealAB M) σ τ
  bwd_coeff N σ τ :=
    regionInsertedCoeff_transfer_of_realizes B A R f hvB hvA hAB.symm
      (regionInteriorBondProd_congr B A R hDim.symm) N _ (hrealBA N) σ τ
  fwd_mul M M' := regionTransferMatrix_mul_of_realizes A B R f hvA hvB hposB hrealAB M M'
  fwd_one := regionTransferMatrix_one_of_realizes A B R f hvA hvB hAB hRB hCB hposB hDim hrealAB

end PEPS
end TNLean
