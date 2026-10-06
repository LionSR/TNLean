/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.SharedInfra.JointOneSiteSpan
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointInterpolation
import Mathlib.LinearAlgebra.Pi
import TNLean.Algebra.MatrixCoordinateInclusion

/-!
# The actual mixed block family with shared physical alphabets

For endpoint families \(A_x^0,A_x^1\), the physical space has four phase
summands: the shared alphabet of \(A^0\), the labelled rectangular matrix
units in the \(01\) corner, those in the \(10\) corner, and the shared
alphabet of \(A^1\). The endpoint alphabets occur once, not once per block.

Simultaneous one-site spanning of both endpoint families implies simultaneous
one-site spanning of the enlarged family. The proof retains all physical
overlap between distinct block labels within either endpoint alphabet.

Source: GLM23, arXiv:2203.12563, Section 5, lines 1695–1777.
-/

open scoped Matrix BigOperators

namespace MPSTensor.MPOSymmetry

variable {d₀ d₁ r : ℕ} {D₀ D₁ : Fin r → ℕ}

/-- The four physical phase sectors, retaining the two shared endpoint
alphabets. Source: arXiv:2203.12563, Section 5, lines 1695–1704. -/
abbrev JointMixedPhysical (d₀ d₁ : ℕ) (D₀ D₁ : Fin r → ℕ) :=
  Fin d₀ ⊕ (((x : Fin r) × (Fin (D₀ x) × Fin (D₁ x))) ⊕
    (((x : Fin r) × (Fin (D₁ x) × Fin (D₀ x))) ⊕ Fin d₁))

/-- The physical dimension of the four-summand mixed block construction.
Source: arXiv:2203.12563, Section 5, lines 1695–1704. -/
abbrev jointMixedPhysicalDim (d₀ d₁ : ℕ) (D₀ D₁ : Fin r → ℕ) :=
  Fintype.card (JointMixedPhysical d₀ d₁ D₀ D₁)

/-- Simultaneous letters in direct-sum virtual coordinates. Only the cross
corners carry a physical block label. Source: arXiv:2203.12563,
Section 5, lines 1695–1704. -/
noncomputable def jointMixedEndpointLetter
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (p : JointMixedPhysical d₀ d₁ D₀ D₁) :
    (x : Fin r) → Matrix (Fin (D₀ x) ⊕ Fin (D₁ x))
      (Fin (D₀ x) ⊕ Fin (D₁ x)) ℂ := by
  classical
  exact match p with
  | .inl i => fun x => Matrix.fromBlocks (A₀ x i) 0 0 0
  | .inr (.inl ⟨x, a, b⟩) => Pi.single x (Matrix.single (.inl a) (.inr b) 1)
  | .inr (.inr (.inl ⟨x, a, b⟩)) => Pi.single x (Matrix.single (.inr a) (.inl b) 1)
  | .inr (.inr (.inr i)) => fun x => Matrix.fromBlocks 0 0 0 (A₁ x i)

/-- Both endpoint simultaneous spans and the cross-corner matrix units span
all enlarged block algebras simultaneously. Source: arXiv:2203.12563,
Section 5, lines 1695–1704 and 1777. -/
theorem span_jointMixedEndpointLetter_eq_top
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    Submodule.span ℂ (Set.range (jointMixedEndpointLetter A₀ A₁)) = ⊤ := by
  classical
  let S := Submodule.span ℂ (Set.range (jointMixedEndpointLetter A₀ A₁))
  have hleft (M : (x : Fin r) → Matrix (Fin (D₀ x)) (Fin (D₀ x)) ℂ) :
      (fun x => Matrix.fromBlocks (M x) (0 : Matrix (Fin (D₀ x)) (Fin (D₁ x)) ℂ)
        0 0) ∈ S := by
    have hM : M ∈ Submodule.span ℂ (Set.range fun i => fun x => A₀ x i) := by
      rw [(wordTupleSpanTop_one_iff A₀).mp h₀]
      exact Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem M hM =>
        obtain ⟨i, rfl⟩ := hM
        exact Submodule.subset_span ⟨.inl i, rfl⟩
    | zero => simpa using S.zero_mem
    | add M N _ _ hM hN =>
        simpa only [Pi.add_apply, Matrix.fromBlocks_add, add_zero] using S.add_mem hM hN
    | smul c M _ hM =>
        simpa only [Pi.smul_apply, Matrix.fromBlocks_smul, smul_zero] using S.smul_mem c hM
  have hright (M : (x : Fin r) → Matrix (Fin (D₁ x)) (Fin (D₁ x)) ℂ) :
      (fun x => Matrix.fromBlocks (0 : Matrix (Fin (D₀ x)) (Fin (D₀ x)) ℂ)
        0 0 (M x)) ∈ S := by
    have hM : M ∈ Submodule.span ℂ (Set.range fun i => fun x => A₁ x i) := by
      rw [(wordTupleSpanTop_one_iff A₁).mp h₁]
      exact Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem M hM =>
        obtain ⟨i, rfl⟩ := hM
        exact Submodule.subset_span ⟨.inr (.inr (.inr i)), rfl⟩
    | zero => simpa using S.zero_mem
    | add M N _ _ hM hN =>
        simpa only [Pi.add_apply, Matrix.fromBlocks_add, add_zero] using S.add_mem hM hN
    | smul c M _ hM =>
        simpa only [Pi.smul_apply, Matrix.fromBlocks_smul, smul_zero] using S.smul_mem c hM
  have hsingle (x : Fin r) : ∀ M, Pi.single x M ∈ S := by
    have ht : S.comap (LinearMap.single ℂ _ x) = ⊤ := by
      apply Submodule.eq_top_of_forall_single_mem
      intro i j
      change Pi.single x (Matrix.single i j 1) ∈ S
      cases i with
      | inl a =>
          cases j with
          | inl b =>
              convert hleft (Pi.single x (Matrix.single a b 1)) using 1
              funext y
              by_cases h : y = x
              · subst y
                ext i j
                cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.single_apply]
              · simp [Pi.single_eq_of_ne h]
          | inr b =>
              exact Submodule.subset_span ⟨.inr (.inl ⟨x, a, b⟩), rfl⟩
      | inr a =>
          cases j with
          | inl b =>
              exact Submodule.subset_span ⟨.inr (.inr (.inl ⟨x, a, b⟩)), rfl⟩
          | inr b =>
              convert hright (Pi.single x (Matrix.single a b 1)) using 1
              funext y
              by_cases h : y = x
              · subst y
                ext i j
                cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.single_apply]
              · simp [Pi.single_eq_of_ne h]
    intro M
    exact show M ∈ S.comap (LinearMap.single ℂ _ x) from ht ▸ Submodule.mem_top
  apply top_unique
  intro M _
  rw [← LinearMap.sum_single_apply _ M]
  exact S.sum_mem fun x _ => hsingle x (M x)

/-- The actual mixed block family in finite physical and virtual coordinates.
Source: arXiv:2203.12563, Section 5, lines 1695–1704. -/
noncomputable def jointMixedEndpointBase
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (x : Fin r) : MPSTensor (jointMixedPhysicalDim d₀ d₁ D₀ D₁) (D₀ x + D₁ x) :=
  fun i => Matrix.reindex finSumFinEquiv finSumFinEquiv
    (jointMixedEndpointLetter A₀ A₁ ((Fintype.equivFin _).symm i) x)

/-- The mixed family has simultaneous one-site span, without a physical
orthogonality assumption on endpoint block labels. Source: arXiv:2203.12563,
Section 5, lines 1695–1704 and 1777. -/
theorem wordTupleSpanTop_jointMixedEndpointBase
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    WordTupleSpanTop (jointMixedEndpointBase A₀ A₁) 1 := by
  classical
  rw [wordTupleSpanTop_one_iff]
  let e := LinearEquiv.piCongrRight fun x : Fin r =>
    Matrix.reindexLinearEquiv ℂ ℂ (finSumFinEquiv (m := D₀ x) (n := D₁ x))
      finSumFinEquiv
  have hrange : Set.range (fun i => fun x => jointMixedEndpointBase A₀ A₁ x i) =
      e.toLinearMap '' Set.range (jointMixedEndpointLetter A₀ A₁) := by
    ext M
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨(Fintype.equivFin _).symm i, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
      refine ⟨Fintype.equivFin _ p, ?_⟩
      simp [jointMixedEndpointBase, e]
  rw [hrange, ← Submodule.map_span]
  exact (Submodule.map_eq_top_iff (e := e)).mpr
    (span_jointMixedEndpointLetter_eq_top A₀ A₁ h₀ h₁)

/-- The shared diagonal alphabets contribute only \(d_0+d_1\) physical
letters; the cross corners contribute the rectangular block dimensions.
Source: arXiv:2203.12563, Section 5, lines 1695–1704. -/
theorem jointMixedPhysicalDim_eq :
    jointMixedPhysicalDim d₀ d₁ D₀ D₁ =
      d₀ + ((∑ x, D₀ x * D₁ x) + ((∑ x, D₁ x * D₀ x) + d₁)) := by
  simp [jointMixedPhysicalDim, JointMixedPhysical, Fintype.card_sigma]

/-- The original first family, extended by zero into the other three phase
summands. Source: arXiv:2203.12563, Section 5, lines 1695–1704. -/
noncomputable def jointMixedEndpointLeftTensor
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x)) (d₁ : ℕ) (D₁ : Fin r → ℕ)
    (x : Fin r) : MPSTensor (jointMixedPhysicalDim d₀ d₁ D₀ D₁) (D₀ x) :=
  fun i => match (Fintype.equivFin (JointMixedPhysical d₀ d₁ D₀ D₁)).symm i with
    | .inl j => A₀ x j
    | .inr _ => 0

/-- The actual first virtual compression recovers the first endpoint on its
single shared physical alphabet. Source: arXiv:2203.12563,
Section 5, lines 1695–1704. -/
theorem jointMixedEndpointBase_first_compression
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (x : Fin r) (i : Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁)) :
    (Matrix.coordinateInclusion (Fin.castAddEmb (D₁ x) :
      Fin (D₀ x) ↪ Fin (D₀ x + D₁ x)))ᴴ * jointMixedEndpointBase A₀ A₁ x i *
      Matrix.coordinateInclusion (Fin.castAddEmb (D₁ x)) =
        jointMixedEndpointLeftTensor A₀ d₁ D₁ x i := by
  classical
  rw [Matrix.coordinateInclusion_compression]
  ext a b
  simp only [jointMixedEndpointBase, Matrix.reindex_apply, Matrix.submatrix_apply,
    Fin.castAddEmb_apply, finSumFinEquiv_symm_apply_castAdd]
  unfold jointMixedEndpointLeftTensor
  generalize hp : (Fintype.equivFin (JointMixedPhysical d₀ d₁ D₀ D₁)).symm i = p
  rcases p with j | ⟨y, c, e⟩ | ⟨y, c, e⟩ | j
  · rfl
  · by_cases h : x = y
    · subst y
      simp [jointMixedEndpointLetter, Matrix.single_apply]
    · simp [jointMixedEndpointLetter, Pi.single_eq_of_ne h]
  · by_cases h : x = y
    · subst y
      simp [jointMixedEndpointLetter, Matrix.single_apply]
    · simp [jointMixedEndpointLetter, Pi.single_eq_of_ne h]
  · rfl

/-- The compressed first endpoint still spans all its block algebras
simultaneously. Source: arXiv:2203.12563, Section 5, lines 1695–1704. -/
theorem wordTupleSpanTop_jointMixedEndpointLeftTensor
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    WordTupleSpanTop (jointMixedEndpointLeftTensor A₀ d₁ D₁) 1 := by
  have h := wordTupleSpanTop_one_of_rectangular_compression
    (jointMixedEndpointBase A₀ A₁) (wordTupleSpanTop_jointMixedEndpointBase A₀ A₁ h₀ h₁)
    (fun x => (Matrix.coordinateInclusion (Fin.castAddEmb (D₁ x) :
      Fin (D₀ x) ↪ Fin (D₀ x + D₁ x)))ᴴ)
    (fun x => Matrix.coordinateInclusion (Fin.castAddEmb (D₁ x)))
    (fun x => Matrix.coordinateInclusion_isometry _)
  simpa only [jointMixedEndpointBase_first_compression] using h

/-- The actual path multiplies each mixed block by its prescribed bond
weight. Source: arXiv:2203.12563, Section 5, lines 1695–1704. -/
noncomputable def jointMixedEndpointInterpolation
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (γ : ℝ)
    (x : Fin r) : MPSTensor (jointMixedPhysicalDim d₀ d₁ D₀ D₁) (D₀ x + D₁ x) :=
  fun i => jointMixedEndpointBase A₀ A₁ x i * bondInterpolationMatrix (D₀ x) (D₁ x) γ

/-- The entire mixed block path is continuous. Source: arXiv:2203.12563,
Section 5, lines 1695–1704. -/
theorem continuous_jointMixedEndpointInterpolation
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    Continuous (jointMixedEndpointInterpolation A₀ A₁) := by
  apply continuous_pi
  intro x
  apply continuous_pi
  intro i
  exact continuous_const.matrix_mul (continuous_bondInterpolationMatrix (D₀ x) (D₁ x))

/-- Every interior parameter has simultaneous one-site span across all
blocks. Source: arXiv:2203.12563, Section 5, lines 1695–1704 and 1777. -/
theorem wordTupleSpanTop_jointMixedEndpointInterpolation
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1)
    {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    WordTupleSpanTop (jointMixedEndpointInterpolation A₀ A₁ γ) 1 := by
  classical
  have hunit (x : Fin r) :=
    isUnit_bondInterpolationMatrix_of_mem_Ioo (D₀ := D₀ x) (D₁ := D₁ x) hγ
  choose u hu using hunit
  exact wordTupleSpanTop_one_of_right_inverse (jointMixedEndpointBase A₀ A₁)
    (wordTupleSpanTop_jointMixedEndpointBase A₀ A₁ h₀ h₁)
    (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) γ)
    (fun x => ↑((u x)⁻¹)) (fun x => by rw [← hu x]; exact (u x).inv_mul)

end MPSTensor.MPOSymmetry
