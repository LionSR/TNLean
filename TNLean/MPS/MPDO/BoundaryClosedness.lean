/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryTransport
import TNLean.MPS.MPDO.PhysicalClosure
import TNLean.MPS.ParentHamiltonian.GroundSpace

/-!
# Length-independent arbitrary-boundary closedness

The closedness condition of GLM23 has quantifier order
\(\forall X,Y\,\exists Z\,\forall n>0\). Compatibility of an MPO with an
MPS has the same order, with one operator boundary and one state boundary.
The output boundary must work at every positive system size.

The positive-length convention treats a chain as nonempty. The empty chain
has coefficient \(\operatorname{tr}X\); adding it would impose an extra trace
identity not implied by the local fusion or action equations with only a
support projector on the ambient bond space.

Exact biorthogonal decompositions imply the corresponding boundary formulas.
The converse existence and uniqueness of biorthogonal fusion and action
tensors from closedness and block-injectivity is a separate assertion, not
assumed or proved by these results.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `algcond`, lines 321--330;
  `eq:compatible`, lines 431--469; Appendix A, lines 2305 onwards.
-/

open scoped Matrix BigOperators

/-- A simultaneous lift of all matrix units extends linearly, retaining the
same lift across an arbitrarily indexed family of linear maps. -/
private theorem exists_linearMap_comp_of_forall_single
    {m n : Type*} [Finite m] [Finite n] [DecidableEq m] [DecidableEq n]
    {E : Type*} [AddCommMonoid E] [Module ℂ E]
    {κ : Type*} {H : κ → Type*} [∀ k, AddCommMonoid (H k)] [∀ k, Module ℂ (H k)]
    (F : ∀ k : κ, E →ₗ[ℂ] H k)
    (G : ∀ k : κ, Matrix m n ℂ →ₗ[ℂ] H k)
    (h : ∀ i j, ∃ z : E, ∀ k : κ, F k z = G k (Matrix.single i j 1)) :
    ∃ b : Matrix m n ℂ →ₗ[ℂ] E, ∀ k : κ, (F k).comp b = G k := by
  classical
  let := Fintype.ofFinite m
  let := Fintype.ofFinite n
  choose z hz using h
  refine ⟨Matrix.liftLinear ℂ (fun i j ↦ LinearMap.toSpanSingleton ℂ E (z i j)), ?_⟩
  intro k
  apply Matrix.ext_linearMap
  intro i j
  apply LinearMap.ext
  intro c
  change F k (Matrix.liftLinear ℂ
    (fun i j ↦ LinearMap.toSpanSingleton ℂ E (z i j)) (Matrix.single i j c)) =
      G k (Matrix.single i j c)
  rw [Matrix.liftLinear_single]
  change F k (c • z i j) = G k (Matrix.single i j c)
  rw [map_smul, hz, ← map_smul]
  congr 1
  simp [Matrix.smul_single]

namespace MPSTensor

/-- The boundary-weighted vector is the existing ground-space parametrization,
by cyclicity of trace. Source: GLM23, arXiv:2203.12563v3, the space
\(\mathcal S_A^n\) preceding `eq:compatible`. -/
theorem mpvWithBoundary_eq_groundSpaceMap {d D L : ℕ} (A : MPSTensor d D)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    mpvWithBoundary A X = groundSpaceMap A L X := by
  funext σ
  exact Matrix.trace_mul_comm _ _

end MPSTensor

namespace MPOTensor

variable {d D D₁ D₂ : ℕ}

/-- Arbitrary-boundary closedness with one output boundary for all positive
lengths. Source: GLM23, arXiv:2203.12563v3, `algcond`, lines 321--330. -/
def IsBoundaryClosed (T : MPOTensor d D) : Prop :=
  ∀ X Y : Matrix (Fin D) (Fin D) ℂ,
    ∃ Z : Matrix (Fin D) (Fin D) ℂ, ∀ L : ℕ, 0 < L →
      mpoWithBoundary T X L * mpoWithBoundary T Y L = mpoWithBoundary T Z L

/-- Arbitrary-boundary compatibility with one output state boundary for all
positive lengths. Source: GLM23, arXiv:2203.12563v3, `eq:compatible`,
lines 431--469. -/
def IsBoundaryCompatible (T : MPOTensor d D₁) (A : MPSTensor d D₂) : Prop :=
  ∀ (X : Matrix (Fin D₁) (Fin D₁) ℂ) (Y : Matrix (Fin D₂) (Fin D₂) ℂ),
    ∃ Z : Matrix (Fin D₂) (Fin D₂) ℂ, ∀ L : ℕ, 0 < L →
      mpoWithBoundary T X L *ᵥ MPSTensor.mpvWithBoundary A Y =
        (MPSTensor.mpvWithBoundary A Z : (Fin L → Fin d) → ℂ)

/-- The boundary-weighted operator is the existing physical closure, with the
boundary moved to the other side of the trace. -/
theorem mpoWithBoundary_eq_physCloseN (T : MPOTensor d D)
    (X : Matrix (Fin D) (Fin D) ℂ) (L : ℕ) :
    mpoWithBoundary T X L = physCloseN T L X := by
  ext σ τ
  exact Matrix.trace_mul_comm _ _

/-- The existential closedness condition yields a linear boundary transport
on the entire stacked matrix space, with one map for all positive lengths.
Conversely, such a transport gives arbitrary-boundary closedness.

This proves the first assertion of GLM23 Appendix A, lines 2307--2309,
rather than taking linearity of the output-boundary choice as an assumption.
Matrix units are product boundaries and form a basis. No injectivity or
biorthogonal fusion tensors are needed for this assertion. -/
theorem isBoundaryClosed_iff_exists_linearMap (T : MPOTensor d D) :
    IsBoundaryClosed T ↔
      ∃ b : Matrix (Fin (D * D)) (Fin (D * D)) ℂ →ₗ[ℂ]
        Matrix (Fin D) (Fin D) ℂ,
        ∀ (L : ℕ), 0 < L → ∀ C : Matrix (Fin (D * D)) (Fin (D * D)) ℂ,
          mpoWithBoundary (mulTensor T T) C L = mpoWithBoundary T (b C) L := by
  constructor
  · intro h
    have hb := exists_linearMap_comp_of_forall_single
      (fun n : {L : ℕ // 0 < L} ↦ physCloseN T n.val)
      (fun n : {L : ℕ // 0 < L} ↦ physCloseN (mulTensor T T) n.val) ?_
    · obtain ⟨b, hb⟩ := hb
      refine ⟨b, fun L hL C ↦ ?_⟩
      have he := congrArg (fun f ↦ f C) (hb ⟨L, hL⟩)
      simpa only [LinearMap.comp_apply, ← mpoWithBoundary_eq_physCloseN] using he.symm
    · intro i j
      obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective i
      obtain ⟨⟨j₁, j₂⟩, rfl⟩ := finProdFinEquiv.surjective j
      obtain ⟨Z, hZ⟩ := h (Matrix.single i₁ j₁ 1) (Matrix.single i₂ j₂ 1)
      refine ⟨Z, fun n ↦ ?_⟩
      have he := (hZ n.val n.property).symm
      rw [← mpoWithBoundary_mulTensor, productBoundary_single, one_mul] at he
      simpa only [mpoWithBoundary_eq_physCloseN] using he
  · rintro ⟨b, hb⟩ X Y
    refine ⟨b (productBoundary X Y), fun L hL ↦ ?_⟩
    rw [← mpoWithBoundary_mulTensor]
    exact hb L hL (productBoundary X Y)

/-- Compatibility likewise yields a single linear map from the stacked bond
matrices to state boundaries. Source: GLM23, `eq:compatible`, with the
Appendix A argument applied to action tensors as indicated at line 462. -/
theorem isBoundaryCompatible_iff_exists_linearMap (T : MPOTensor d D₁)
    (A : MPSTensor d D₂) :
    IsBoundaryCompatible T A ↔
      ∃ b : Matrix (Fin (D₁ * D₂)) (Fin (D₁ * D₂)) ℂ →ₗ[ℂ]
        Matrix (Fin D₂) (Fin D₂) ℂ,
        ∀ (L : ℕ), 0 < L → ∀ C : Matrix (Fin (D₁ * D₂)) (Fin (D₁ * D₂)) ℂ,
          (MPSTensor.mpvWithBoundary (actTensor T A) C : (Fin L → Fin d) → ℂ) =
            MPSTensor.mpvWithBoundary A (b C) := by
  constructor
  · intro h
    have hb := exists_linearMap_comp_of_forall_single
      (fun n : {L : ℕ // 0 < L} ↦ MPSTensor.groundSpaceMap A n.val)
      (fun n : {L : ℕ // 0 < L} ↦ MPSTensor.groundSpaceMap (actTensor T A) n.val) ?_
    · obtain ⟨b, hb⟩ := hb
      refine ⟨b, fun L hL C ↦ ?_⟩
      have he := congrArg (fun f ↦ f C) (hb ⟨L, hL⟩)
      simpa only [LinearMap.comp_apply, ← MPSTensor.mpvWithBoundary_eq_groundSpaceMap]
        using he.symm
    · intro i j
      obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective i
      obtain ⟨⟨j₁, j₂⟩, rfl⟩ := finProdFinEquiv.surjective j
      obtain ⟨Z, hZ⟩ := h (Matrix.single i₁ j₁ 1) (Matrix.single i₂ j₂ 1)
      refine ⟨Z, fun n ↦ ?_⟩
      have he := (hZ n.val n.property).symm
      rw [mpoWithBoundary_mulVec_mpvWithBoundary, productBoundary_single, one_mul] at he
      simpa only [MPSTensor.mpvWithBoundary_eq_groundSpaceMap] using he
  · rintro ⟨b, hb⟩ X Y
    refine ⟨b (productBoundary X Y), fun L hL ↦ ?_⟩
    rw [mpoWithBoundary_mulVec_mpvWithBoundary]
    exact hb L hL (productBoundary X Y)

/-- Closedness implies closure under products at each fixed positive length.
The converse fixed-length statement alone does not choose a common boundary
for all lengths. Source: GLM23, `algcond`. -/
theorem IsBoundaryClosed.mul_mem_range {T : MPOTensor d D} (h : IsBoundaryClosed T)
    {L : ℕ} (hL : 0 < L) {P Q : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ}
    (hP : P ∈ Set.range (fun X ↦ mpoWithBoundary T X L))
    (hQ : Q ∈ Set.range (fun X ↦ mpoWithBoundary T X L)) :
    P * Q ∈ Set.range (fun X ↦ mpoWithBoundary T X L) := by
  obtain ⟨X, rfl⟩ := hP
  obtain ⟨Y, rfl⟩ := hQ
  obtain ⟨Z, hZ⟩ := h X Y
  exact ⟨Z, (hZ L hL).symm⟩

/-- Compatibility implies invariance of the existing MPS ground space at each
positive length. Source: GLM23, arXiv:2203.12563v3, lines 431--433. -/
theorem IsBoundaryCompatible.mulVec_mem_groundSpace {T : MPOTensor d D₁}
    {A : MPSTensor d D₂} (h : IsBoundaryCompatible T A)
    (X : Matrix (Fin D₁) (Fin D₁) ℂ) {L : ℕ} (hL : 0 < L)
    {ψ : MPSTensor.NSiteSpace d L} (hψ : ψ ∈ MPSTensor.groundSpace A L) :
    mpoWithBoundary T X L *ᵥ ψ ∈ MPSTensor.groundSpace A L := by
  obtain ⟨Y, rfl⟩ := hψ
  obtain ⟨Z, hZ⟩ := h X Y
  refine ⟨Z, ?_⟩
  simpa only [MPSTensor.mpvWithBoundary_eq_groundSpaceMap] using (hZ L hL).symm

/-- Exact fusion decompositions transport arbitrary input boundaries to one
boundary per summand, independent of the positive length. This is the
forward calculation of GLM23 Appendix A and `fusiontensors`; it does not
construct the local decomposition from closedness. -/
theorem mpoWithBoundary_mul_eq_sum_of_biorthogonalDecomposition
    {ι : Type*} [Fintype ι] {δ : ι → ℕ}
    (M : MPOTensor d D₁) (N : MPOTensor d D₂) (T : ∀ c : ι, MPOTensor d (δ c))
    (V : ∀ c : ι, Matrix (Fin (δ c)) (Fin (D₁ * D₂)) ℂ)
    (W : ∀ c : ι, Matrix (Fin (D₁ * D₂)) (Fin (δ c)) ℂ)
    (h : MPSTensor.IsBiorthogonalDecomposition (mulTensor M N).toMPSTensor
      (fun c ↦ (T c).toMPSTensor) V W)
    (X : Matrix (Fin D₁) (Fin D₁) ℂ) (Y : Matrix (Fin D₂) (Fin D₂) ℂ)
    {L : ℕ} (hL : 0 < L) :
    mpoWithBoundary M X L * mpoWithBoundary N Y L =
      ∑ c : ι, mpoWithBoundary (T c) (V c * productBoundary X Y * W c) L := by
  rw [← mpoWithBoundary_mulTensor]
  ext σ τ
  have hh := h.mpvWithBoundary (productBoundary X Y) hL
    (fun k ↦ finProdFinEquiv (σ k, τ k))
  simpa only [MPSTensor.mpvWithBoundary, evalWord_toMPSTensor_pairConfig,
    Matrix.sum_apply, mpoWithBoundary] using hh

/-- Exact action decompositions transport arbitrary boundaries to each target
summand at every positive length. Source: GLM23, `fusiontensors2` and
`eq:compatible`; the reverse construction is not asserted. -/
theorem mpoWithBoundary_mulVec_eq_sum_of_biorthogonalDecomposition
    {ι : Type*} [Fintype ι] {δ : ι → ℕ}
    (T : MPOTensor d D₁) (A : MPSTensor d D₂) (B : ∀ c : ι, MPSTensor d (δ c))
    (V : ∀ c : ι, Matrix (Fin (δ c)) (Fin (D₁ * D₂)) ℂ)
    (W : ∀ c : ι, Matrix (Fin (D₁ * D₂)) (Fin (δ c)) ℂ)
    (h : MPSTensor.IsBiorthogonalDecomposition (actTensor T A) B V W)
    (X : Matrix (Fin D₁) (Fin D₁) ℂ) (Y : Matrix (Fin D₂) (Fin D₂) ℂ)
    {L : ℕ} (hL : 0 < L) :
    mpoWithBoundary T X L *ᵥ MPSTensor.mpvWithBoundary A Y =
      ∑ c : ι, (MPSTensor.mpvWithBoundary (B c)
        (V c * productBoundary X Y * W c) : (Fin L → Fin d) → ℂ) := by
  rw [mpoWithBoundary_mulVec_mpvWithBoundary]
  funext σ
  simpa only [Finset.sum_apply] using h.mpvWithBoundary (productBoundary X Y) hL σ


/-- An exact fusion decomposition into copies of the same tensor supplies
closedness with the explicit length-independent boundary
\(Z=\sum_c V_c(X\otimes Y)W_c\).

This is a sufficient local criterion, not the converse existence theorem of
GLM23 Appendix A. For a tensor with different target blocks, use the preceding
blockwise transport formula before assembling its direct sum. -/
theorem isBoundaryClosed_of_biorthogonalDecomposition
    {ι : Type*} [Fintype ι] (T : MPOTensor d D)
    (V : ι → Matrix (Fin D) (Fin (D * D)) ℂ)
    (W : ι → Matrix (Fin (D * D)) (Fin D) ℂ)
    (h : MPSTensor.IsBiorthogonalDecomposition (mulTensor T T).toMPSTensor
      (fun _ : ι ↦ T.toMPSTensor) V W) :
    IsBoundaryClosed T := by
  intro X Y
  refine ⟨∑ c : ι, V c * productBoundary X Y * W c, fun L hL ↦ ?_⟩
  simpa only [mpoWithBoundary_eq_physCloseN, map_sum] using
    mpoWithBoundary_mul_eq_sum_of_biorthogonalDecomposition T T (fun _ : ι ↦ T)
      V W h X Y hL

/-- An exact action decomposition into copies of the same state tensor
supplies compatibility with \(Z=\sum_c V_c(X\otimes Y)W_c\), independently of
length. This is the sufficient local direction of GLM23 `eq:compatible`. -/
theorem isBoundaryCompatible_of_biorthogonalDecomposition
    {ι : Type*} [Fintype ι] (T : MPOTensor d D₁) (A : MPSTensor d D₂)
    (V : ι → Matrix (Fin D₂) (Fin (D₁ * D₂)) ℂ)
    (W : ι → Matrix (Fin (D₁ * D₂)) (Fin D₂) ℂ)
    (h : MPSTensor.IsBiorthogonalDecomposition (actTensor T A)
      (fun _ : ι ↦ A) V W) :
    IsBoundaryCompatible T A := by
  intro X Y
  refine ⟨∑ c : ι, V c * productBoundary X Y * W c, fun L hL ↦ ?_⟩
  simpa only [MPSTensor.mpvWithBoundary_eq_groundSpaceMap, map_sum] using
    mpoWithBoundary_mulVec_eq_sum_of_biorthogonalDecomposition T A (fun _ : ι ↦ A)
      V W h X Y hL

end MPOTensor
