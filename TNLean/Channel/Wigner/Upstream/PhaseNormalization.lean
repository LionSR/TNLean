/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import TNLean.Channel.Wigner.Upstream.FrameReduction

/-!
# Projective Wigner rigidity: two-level phase normal form and diagonal-phase normalization

This module is adapted from
`CsdLean4/Mathlib/LinearAlgebra/Projectivization/WignerRigidity.lean` in
`zblore/csd-lean4` at commit
`55ac6758832291c8b0fb94d78e10dc47b1cb8a06`, under the Apache License 2.0.
The upstream single source file was split mechanically at semantic section
boundaries, preserving declaration order, to satisfy TNLean's module-size policy.
Ordinary imports and public declarations replace the upstream module-system commands.
Further adaptations are limited to formatting, explicit qualification, documentation, and
style-linter compliance. Declaration order, theorem statements, and proof structure are
preserved.
-/

open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {N : ℕ}
variable {f : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}

/-! ## Stage 2: the two-level phase normal form

For distinct indices `i₀ ≠ i`, the frame-reduced map sends the superposition ray
`mk (b i₀ + b i)` to a ray `mk (b i₀ + ε • b i)` with `ε` unimodular
(`reducedMap_two_level_normal_form`). Stage 1 forces the image rep to be
supported on `{i₀, i}` with equal coordinate moduli there; normalising the ray so
that the `i₀`-coordinate is `1` leaves a single unit phase `ε := d_i / d_{i₀}`.
The genuine content is the support restriction plus the modulus equality; the
phase `ε` is *not* yet pinned to `1` (that is Stage 3, the cocycle). -/

/-- The sum of two distinct basis vectors is nonzero: its squared norm is `2`
(Pythagoras via `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero`, using the
orthogonality `b.orthonormal.2 hij` and the unit norms). -/
lemma add_basis_ne_zero
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {i₀ i : Fin N} (hij : i₀ ≠ i) :
    (b i₀ + b i : EuclideanSpace ℂ (Fin N)) ≠ 0 := by
  intro h
  have h2 : ‖(b i₀ + b i : EuclideanSpace ℂ (Fin N))‖
      * ‖(b i₀ + b i : EuclideanSpace ℂ (Fin N))‖ = 2 := by
    rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (b i₀) (b i)
          (b.orthonormal.2 hij), b.orthonormal.norm_eq_one i₀,
        b.orthonormal.norm_eq_one i]
    norm_num
  rw [h, norm_zero, mul_zero] at h2
  norm_num at h2

/-- **Support reconstruction.** A vector whose coordinates in the basis `b`
vanish outside `{i₀, i}` is the pair sum of its two surviving coordinates.
`OrthonormalBasis.sum_repr` expands `φ`, `Finset.sum_subset` drops the null
coordinates, and `Finset.sum_pair` collapses the two-element sum. -/
lemma repr_eq_pair_of_support
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (φ : EuclideanSpace ℂ (Fin N)) {i₀ i : Fin N} (hij : i₀ ≠ i)
    (hsupp : ∀ j, j ≠ i₀ → j ≠ i → b.repr φ j = 0) :
    φ = b.repr φ i₀ • b i₀ + b.repr φ i • b i := by
  have hvanish : ∀ j ∈ (Finset.univ : Finset (Fin N)),
      j ∉ ({i₀, i} : Finset (Fin N)) → b.repr φ j • b j = 0 := by
    intro j _ hj
    rw [Finset.mem_insert, Finset.mem_singleton] at hj
    push Not at hj
    rw [hsupp j hj.1 hj.2, zero_smul]
  calc φ = ∑ j, b.repr φ j • b j := (b.sum_repr φ).symm
    _ = ∑ j ∈ ({i₀, i} : Finset (Fin N)), b.repr φ j • b j :=
          (Finset.sum_subset (Finset.subset_univ _) hvanish).symm
    _ = b.repr φ i₀ • b i₀ + b.repr φ i • b i := Finset.sum_pair hij

/-- **Profile ⇒ two-level normal form.** A nonzero vector supported on `{i₀, i}`
with equal coordinate moduli there (and nonzero `i₀`-coordinate) spans the ray
`mk (b i₀ + ε • b i)` for the unit phase `ε := (b.repr φ i) / (b.repr φ i₀)`.
Factoring `b.repr φ i₀` out of the pair reconstruction rescales the ray; the
modulus equality gives `‖ε‖ = 1`. -/
lemma mk_eq_two_level_of_profile
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {φ : EuclideanSpace ℂ (Fin N)} (hφ : φ ≠ 0) {i₀ i : Fin N} (hij : i₀ ≠ i)
    (hsupp : ∀ j, j ≠ i₀ → j ≠ i → b.repr φ j = 0)
    (ha : b.repr φ i₀ ≠ 0)
    (hmod : ‖b.repr φ i‖ = ‖b.repr φ i₀‖) :
    ∃ (ε : ℂ) (hne : (b i₀ + ε • b i : EuclideanSpace ℂ (Fin N)) ≠ 0),
      ‖ε‖ = 1 ∧
      Projectivization.mk ℂ φ hφ = Projectivization.mk ℂ (b i₀ + ε • b i) hne := by
  have hrec : φ = b.repr φ i₀ • b i₀ + b.repr φ i • b i :=
    repr_eq_pair_of_support b φ hij hsupp
  set a := b.repr φ i₀ with ha_def
  set c := b.repr φ i with hc_def
  have hfactor : a • (b i₀ + (c / a) • b i) = φ := by
    have hac : a * (c / a) = c := by field_simp
    rw [smul_add, smul_smul, hac, ← hrec]
  have hne : (b i₀ + (c / a) • b i : EuclideanSpace ℂ (Fin N)) ≠ 0 := by
    intro h0
    rw [h0, smul_zero] at hfactor
    exact hφ hfactor.symm
  refine ⟨c / a, hne, ?_, ?_⟩
  · rw [norm_div, hmod, div_self (norm_ne_zero_iff.mpr ha)]
  · exact (Projectivization.mk_eq_mk_iff' ℂ φ (b i₀ + (c / a) • b i) hφ hne).mpr
      ⟨a, hfactor⟩

/-- **Stage 2 (two-level phase normal form).** For distinct `i₀ ≠ i`, the
frame-reduced map sends the superposition ray `mk (b i₀ + b i)` to
`mk (b i₀ + ε • b i)` for a unimodular `ε`. Stage 1 (`reducedMap_coord_modulus`)
forces the image rep to be supported on `{i₀, i}` with equal moduli there;
`mk_eq_two_level_of_profile` packages the ray normal form. This pins the image
ray up to the single phase `ε`; pinning `ε = 1` (globally coherently) is the
Stage 3 cocycle, not proved here. -/
theorem reducedMap_two_level_normal_form
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {i₀ i : Fin N} (hij : i₀ ≠ i) :
    ∃ (ε : ℂ) (hne : (b i₀ + ε • b i : EuclideanSpace ℂ (Fin N)) ≠ 0),
      ‖ε‖ = 1 ∧
      reducedMap hf b
          (Projectivization.mk ℂ (b i₀ + b i) (add_basis_ne_zero b hij))
        = Projectivization.mk ℂ (b i₀ + ε • b i) hne := by
  -- Coordinates of the source superposition `w = b i₀ + b i`.
  have hwj : ∀ j, b.repr (b i₀ + b i) j
      = (if j = i₀ then (1 : ℂ) else 0) + (if j = i then 1 else 0) := by
    intro j
    rw [b.repr_apply_apply, inner_add_right,
        orthonormal_iff_ite.mp b.orthonormal j i₀,
        orthonormal_iff_ite.mp b.orthonormal j i]
  have hwi0 : b.repr (b i₀ + b i) i₀ = 1 := by
    rw [hwj i₀, if_pos rfl, if_neg hij, add_zero]
  have hwi : b.repr (b i₀ + b i) i = 1 := by
    rw [hwj i, if_neg (Ne.symm hij), if_pos rfl, zero_add]
  have hwnorm : ‖(b i₀ + b i : EuclideanSpace ℂ (Fin N))‖ ^ 2 = 2 := by
    rw [sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (b i₀) (b i)
          (b.orthonormal.2 hij), b.orthonormal.norm_eq_one i₀,
        b.orthonormal.norm_eq_one i]
    norm_num
  -- The image rep `φ` and the transported moduli (Stage 1).
  set φ := (reducedMap hf b
      (Projectivization.mk ℂ (b i₀ + b i) (add_basis_ne_zero b hij))).rep
    with hφ_def
  have hφne : φ ≠ 0 := Projectivization.rep_nonzero _
  have hφpos : (0 : ℝ) < ‖φ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hφne) 2
  have hmodj : ∀ j, ‖b.repr φ j‖ ^ 2 / ‖φ‖ ^ 2
      = ‖b.repr (b i₀ + b i) j‖ ^ 2
          / ‖(b i₀ + b i : EuclideanSpace ℂ (Fin N))‖ ^ 2 := by
    intro j
    rw [hφ_def]
    exact reducedMap_coord_modulus hf b (add_basis_ne_zero b hij) j
  -- Support of `φ` is `{i₀, i}`.
  have hsupp : ∀ j, j ≠ i₀ → j ≠ i → b.repr φ j = 0 := by
    intro j hj0 hji
    have hz : ‖b.repr φ j‖ ^ 2 / ‖φ‖ ^ 2 = 0 := by
      rw [hmodj j, hwj j, if_neg hj0, if_neg hji, add_zero, norm_zero]
      norm_num
    have hsq : ‖b.repr φ j‖ ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp hz with h | h
      · exact h
      · exact absurd h (ne_of_gt hφpos)
    rwa [pow_eq_zero_iff (by norm_num), norm_eq_zero] at hsq
  -- The `i₀`-coordinate of `φ` is nonzero (its modulus² is `‖φ‖²/2`).
  have ha : b.repr φ i₀ ≠ 0 := by
    intro h
    have hmj := hmodj i₀
    rw [hwi0, h, norm_zero, hwnorm, norm_one] at hmj
    norm_num at hmj
  -- The `i` and `i₀` coordinate moduli agree.
  have hmod : ‖b.repr φ i‖ = ‖b.repr φ i₀‖ := by
    have hi := hmodj i
    have hi0 := hmodj i₀
    rw [hwi, norm_one, hwnorm] at hi
    rw [hwi0, norm_one, hwnorm] at hi0
    have hd := hi.trans hi0.symm
    rw [div_eq_div_iff (ne_of_gt hφpos) (ne_of_gt hφpos)] at hd
    have heq2 : ‖b.repr φ i‖ ^ 2 = ‖b.repr φ i₀‖ ^ 2 :=
      mul_right_cancel₀ (ne_of_gt hφpos) hd
    rw [← Real.sqrt_sq (norm_nonneg (b.repr φ i)),
        ← Real.sqrt_sq (norm_nonneg (b.repr φ i₀)), heq2]
  -- Assemble via the profile normal form.
  obtain ⟨ε, hne, hεnorm, hmkeq⟩ :=
    mk_eq_two_level_of_profile b hφne hij hsupp ha hmod
  refine ⟨ε, hne, hεnorm, ?_⟩
  rw [← hmkeq]
  exact (Projectivization.mk_rep _).symm

/-! ## Stage 3 piece 1: the diagonal-phase reduction

The first piece of the Stage 3 residual, on the critical path to the dichotomy.
It removes the Stage-2 two-level phases by post-composing the frame-reduced map
`g = reducedMap hf b` with a diagonal isometry `D⁻¹` in the basis `b`.

* **The diagonal isometry.** For a unit-modulus phase family `ε : Fin N → ℂ`
  (`∀ i, ‖ε i‖ = 1`), the scaled family `fun i => ε i • b i` is again an
  orthonormal basis (`scaledBasis`); `diagUnitary b ε hε` is the `≃ₗᵢ[ℂ]`
  carrying `b` to it, so `diagUnitary (b i) = ε i • b i`
  (`diagUnitary_apply_basis`) and `(diagUnitary).symm (b i) = (ε i)⁻¹ • b i`
  (`diagUnitary_symm_apply_basis`). This is diagonal *in the basis `b`*, not in
  the standard basis, so it is built as an `OrthonormalBasis.equiv`, not a
  `Matrix.diagonal`.
* **The extracted phases.** `twoLevelPhase hf b i₀` reads off, per index, the
  Stage-2 phase `εᵢ` from `reducedMap_two_level_normal_form` (anchored at
  `ε i₀ := 1`), with `‖twoLevelPhase hf b i₀ j‖ = 1` for every `j`
  (`twoLevelPhase_norm`).
* **The diagonally-reduced map.** `diagReducedMap hf b i₀ := projMap (D).symm ∘
  reducedMap hf b` with `D := diagUnitary b (twoLevelPhase hf b i₀) …`. It is
  `TransProbPreserving` (`diagReducedMap_transProbPreserving`), still fixes every
  basis ray (`diagReducedMap_fixes_basis`), and additionally **fixes the
  two-level rays** `mk (b i₀ + b i)` for every `i ≠ i₀`
  (`diagReducedMap_fixes_two_level`) — the setup the cocycle step (pieces 2–3)
  consumes. **No ℂ-linearity is assumed:** `D` is constructed *from* the
  extracted phases, not posited of `f`. -/

/-- The scaled family `fun i => ε i • b i` is orthonormal when every phase is
unit modulus (`‖ε i‖ = 1`): the off-diagonals inherit `b`'s orthogonality, and
the diagonal is `conj (ε i) * ε i = ‖ε i‖² = 1` (`RCLike.conj_mul`). -/
lemma scaled_orthonormal
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ε : Fin N → ℂ) (hε : ∀ i, ‖ε i‖ = 1) :
    Orthonormal ℂ (fun i => ε i • b i) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_smul_left, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal i j]
  rcases eq_or_ne i j with h | h
  · subst h
    simp only [if_true, mul_one]
    rw [RCLike.conj_mul, hε i]; norm_num
  · simp [h]

/-- The `ε`-scaled family spans: cardinality `N` linearly independent vectors in
`finrank = N`. Kept a separate `Prop` lemma so `scaledBasis` is a term-mode `def`
(a tactic-mode data `def` would over-include ambient section variables). -/
lemma scaled_span
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ε : Fin N → ℂ) (hε : ∀ i, ‖ε i‖ = 1) :
    ⊤ ≤ Submodule.span ℂ (Set.range (fun i => ε i • b i)) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    intro x _
    exact (Subsingleton.elim x 0) ▸ Submodule.zero_mem _
  · have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    have hcard : Fintype.card (Fin N) = Module.finrank ℂ (EuclideanSpace ℂ (Fin N)) := by
      rw [Fintype.card_fin, finrank_euclideanSpace_fin]
    rw [(scaled_orthonormal b ε hε).linearIndependent.span_eq_top_of_card_eq_finrank hcard]

/-- The `ε`-scaled orthonormal basis (an orthonormal family of cardinality `N`
in `finrank = N`, so `OrthonormalBasis.mk` applies). -/
noncomputable def scaledBasis
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ε : Fin N → ℂ) (hε : ∀ i, ‖ε i‖ = 1) :
    OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)) :=
  OrthonormalBasis.mk (scaled_orthonormal b ε hε) (scaled_span b ε hε)

/-- `scaledBasis` evaluates to the scaled basis vector (`OrthonormalBasis.mk`
apply). -/
lemma scaledBasis_apply
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ε : Fin N → ℂ) (hε : ∀ i, ‖ε i‖ = 1) (i : Fin N) :
    scaledBasis b ε hε i = ε i • b i := by
  unfold scaledBasis; rw [OrthonormalBasis.coe_mk]

/-- The **diagonal isometry in the basis `b`**: the `≃ₗᵢ[ℂ]` carrying `b` to the
`ε`-scaled basis along the identity reindexing. Diagonal in `b`
(`diagUnitary (b i) = ε i • b i`), unit modulus per coordinate. -/
noncomputable def diagUnitary
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ε : Fin N → ℂ) (hε : ∀ i, ‖ε i‖ = 1) :
    EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N) :=
  b.equiv (scaledBasis b ε hε) (Equiv.refl (Fin N))

/-- `diagUnitary` scales the `i`-th basis vector by `ε i`. -/
lemma diagUnitary_apply_basis
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ε : Fin N → ℂ) (hε : ∀ i, ‖ε i‖ = 1) (i : Fin N) :
    diagUnitary b ε hε (b i) = ε i • b i := by
  unfold diagUnitary
  rw [OrthonormalBasis.equiv_apply_basis, Equiv.refl_apply, scaledBasis_apply]

/-- The inverse `diagUnitary` scales the `i`-th basis vector by `(ε i)⁻¹`.
`diagUnitary ((ε i)⁻¹ • b i) = b i` (since `ε i ≠ 0`), then
`symm_apply_apply`. -/
lemma diagUnitary_symm_apply_basis
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ε : Fin N → ℂ) (hε : ∀ i, ‖ε i‖ = 1) (i : Fin N) :
    (diagUnitary b ε hε).symm (b i) = (ε i)⁻¹ • b i := by
  have hεne : ε i ≠ 0 := by rw [← norm_ne_zero_iff, hε i]; norm_num
  have h : diagUnitary b ε hε ((ε i)⁻¹ • b i) = b i := by
    rw [map_smul, diagUnitary_apply_basis, smul_smul, inv_mul_cancel₀ hεne, one_smul]
  conv_lhs => rw [← h]
  rw [LinearIsometryEquiv.symm_apply_apply]

/-- The Stage-2 phase, extracted per index and anchored at `ε i₀ := 1`.
For `j ≠ i₀`, `twoLevelPhase hf b i₀ j` is the unit phase `εⱼ` supplied by
`reducedMap_two_level_normal_form` for the pair `(i₀, j)`. -/
noncomputable def twoLevelPhase
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ j : Fin N) : ℂ :=
  if h : j = i₀ then 1
  else Classical.choose (reducedMap_two_level_normal_form hf b (i₀ := i₀) (i := j) (Ne.symm h))

/-- The anchor phase is `1`: `twoLevelPhase hf b i₀ i₀ = 1`. -/
lemma twoLevelPhase_self
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N) :
    twoLevelPhase hf b i₀ i₀ = 1 := by
  unfold twoLevelPhase; rw [dif_pos rfl]

/-- Every extracted phase is unit modulus: `‖twoLevelPhase hf b i₀ j‖ = 1`
(anchor `‖1‖ = 1`; off-anchor from the Stage-2 `choose_spec`). -/
lemma twoLevelPhase_norm
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ j : Fin N) :
    ‖twoLevelPhase hf b i₀ j‖ = 1 := by
  unfold twoLevelPhase
  rcases eq_or_ne j i₀ with h | h
  · rw [dif_pos h, norm_one]
  · rw [dif_neg h]
    obtain ⟨_, hnorm, _⟩ :=
      Classical.choose_spec
        (reducedMap_two_level_normal_form hf b (i₀ := i₀) (i := j) (Ne.symm h))
    exact hnorm

/-- The **diagonally-reduced map**: `projMap D⁻¹ ∘ reducedMap hf b`, where
`D := diagUnitary b (twoLevelPhase hf b i₀) …` is the diagonal isometry built
from the extracted phases. -/
noncomputable def diagReducedMap
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N) :
    ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N)) :=
  fun p => projMap (diagUnitary b (twoLevelPhase hf b i₀) (twoLevelPhase_norm hf b i₀)).symm
    (reducedMap hf b p)

/-- **`diagReducedMap` is `TransProbPreserving`.** Composition of the
preserving `projMap D⁻¹` and the preserving `reducedMap hf b`. -/
lemma diagReducedMap_transProbPreserving
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N) :
    TransProbPreserving (diagReducedMap hf b i₀) :=
  (projMap_transProbPreserving
    (diagUnitary b (twoLevelPhase hf b i₀) (twoLevelPhase_norm hf b i₀)).symm).comp
    (reducedMap_transProbPreserving hf b)

/-- **`diagReducedMap` still fixes every basis ray.** `reducedMap` fixes
`mk (b i)`, then `projMap D⁻¹` sends it to `mk ((ε i)⁻¹ • b i) = mk (b i)`
(scaling invariance). -/
lemma diagReducedMap_fixes_basis
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ i : Fin N) :
    diagReducedMap hf b i₀ (Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i))
      = Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i) := by
  change projMap (diagUnitary b (twoLevelPhase hf b i₀) (twoLevelPhase_norm hf b i₀)).symm
      (reducedMap hf b _) = _
  rw [reducedMap_fixes_basis hf b i, projMap_mk]
  refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨(twoLevelPhase hf b i₀ i)⁻¹, ?_⟩
  rw [diagUnitary_symm_apply_basis]

/-- **HEADLINE (diagonal-phase reduction).** The diagonally-reduced map fixes
the two-level superposition ray `mk (b i₀ + b i)` for every `i ≠ i₀`.

Proof. Stage 2 (`reducedMap_two_level_normal_form`, extracted through
`twoLevelPhase`) gives `reducedMap hf b (mk (b i₀ + b i)) = mk (b i₀ + c • b i)`
with `c := twoLevelPhase hf b i₀ i` unit modulus. Applying `D⁻¹`:
`D⁻¹ (b i₀) = (ε i₀)⁻¹ • b i₀ = b i₀` (anchor `ε i₀ = 1`) and
`D⁻¹ (b i) = c⁻¹ • b i`, so `D⁻¹ (b i₀ + c • b i) = b i₀ + (c c⁻¹) • b i =
b i₀ + b i`. Hence the ray is fixed. This is the setup consumed by the cocycle
step (pieces 2–3): a `TransProbPreserving` map fixing every basis ray and every
two-level ray `mk (b i₀ + b i)`. **No ℂ-linearity assumed.** -/
theorem diagReducedMap_fixes_two_level
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {i₀ i : Fin N} (hij : i₀ ≠ i) :
    diagReducedMap hf b i₀ (Projectivization.mk ℂ (b i₀ + b i) (add_basis_ne_zero b hij))
      = Projectivization.mk ℂ (b i₀ + b i) (add_basis_ne_zero b hij) := by
  obtain ⟨_, hnorm, heq⟩ :=
    Classical.choose_spec (reducedMap_two_level_normal_form hf b (i₀ := i₀) (i := i) hij)
  have hci : twoLevelPhase hf b i₀ i
      = Classical.choose (reducedMap_two_level_normal_form hf b (i₀ := i₀) (i := i) hij) := by
    rw [twoLevelPhase, dif_neg (Ne.symm hij)]
  set c := Classical.choose
    (reducedMap_two_level_normal_form hf b (i₀ := i₀) (i := i) hij) with hc
  have hcne : c ≠ 0 := by rw [← norm_ne_zero_iff, hnorm]; norm_num
  change projMap (diagUnitary b (twoLevelPhase hf b i₀) (twoLevelPhase_norm hf b i₀)).symm
      (reducedMap hf b _) = _
  rw [heq, projMap_mk]
  have hcomp :
      (diagUnitary b (twoLevelPhase hf b i₀) (twoLevelPhase_norm hf b i₀)).symm
        (b i₀ + c • b i) = b i₀ + b i := by
    rw [map_add, map_smul, diagUnitary_symm_apply_basis, diagUnitary_symm_apply_basis,
        twoLevelPhase_self hf b i₀, hci]
    simp only [inv_one, one_smul, smul_smul]
    rw [mul_inv_cancel₀ hcne, one_smul]
  refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨1, ?_⟩
  rw [one_smul, hcomp]

end Projectivization
