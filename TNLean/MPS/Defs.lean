import Mathlib.Data.Complex.Basic
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Basic definitions for matrix product state tensors

This file contains the core definitions used throughout the MPS development:
`MPSTensor`, word evaluation, MPV coefficients, gauge equivalence, and the
notions of injectivity, block injectivity, and normality. It also proves the
basic gauge-invariance lemmas for `evalWord` and `SameMPV`.
-/

open scoped Matrix

/-- A (periodic, translation-invariant) tensor generating an MPV family:
a family of `D×D` matrices indexed by a physical index in `Fin d`.

The name `MPSTensor` is kept for compatibility with the literature and the
existing Lean development. -/
abbrev MPSTensor (d D : ℕ) := Fin d → Matrix (Fin D) (Fin D) ℂ

namespace MPSTensor

variable {d D : ℕ}

/-- Evaluate a word `w = [i₁, i₂, …, iₙ]` by multiplying the corresponding matrices
`A i₁ * A i₂ * ⋯ * A iₙ`. Returns `1` for the empty word. -/
def evalWord (A : MPSTensor d D) : List (Fin d) → Matrix (Fin D) (Fin D) ℂ
  | [] => 1
  | i :: w => A i * evalWord A w

@[simp] lemma evalWord_nil (A : MPSTensor d D) : evalWord A [] = 1 := rfl

@[simp] lemma evalWord_cons (A : MPSTensor d D) (i : Fin d) (w : List (Fin d)) :
    evalWord A (i :: w) = A i * evalWord A w := rfl

/-- Word evaluation respects concatenation:
`evalWord A (w1 ++ w2) = evalWord A w1 * evalWord A w2`. -/
lemma evalWord_append (A : MPSTensor d D) :
    ∀ w1 w2 : List (Fin d), evalWord A (w1 ++ w2) = evalWord A w1 * evalWord A w2 := by
  intro w1 w2
  induction w1 with
  | nil => simp [evalWord]
  | cons i w1 ih => simp [evalWord, ih, Matrix.mul_assoc]

/-- Scaling every matrix by a scalar `ζ` scales `evalWord` by the factor `ζ ^ w.length`. -/
lemma evalWord_smul (ζ : ℂ) (A : MPSTensor d D) :
    ∀ w : List (Fin d), evalWord (fun i => ζ • A i) w = (ζ ^ w.length) • evalWord A w := by
  intro w
  induction w with
  | nil => simp [evalWord]
  | cons i w ih =>
      simp [evalWord, ih, pow_succ, smul_smul]

/-- The MPV coefficient for a word `w`, given by `trace (evalWord A w)`. -/
def coeff (A : MPSTensor d D) (w : List (Fin d)) : ℂ :=
  Matrix.trace (evalWord A w)

@[simp] lemma coeff_eq (A : MPSTensor d D) (w : List (Fin d)) :
    coeff A w = Matrix.trace (evalWord A w) := rfl

/-- The Matrix Product Vector (MPV) for system size `N`: for each basis state
`σ : Fin N → Fin d`, this returns the coefficient
`trace (A (σ 0) * A (σ 1) * ⋯ * A (σ (N-1)))`. -/
def mpv (A : MPSTensor d D) {N : ℕ} (σ : Fin N → Fin d) : ℂ :=
  coeff A (List.ofFn σ)

@[simp] lemma mpv_eq (A : MPSTensor d D) {N : ℕ} (σ : Fin N → Fin d) :
    mpv A σ = coeff A (List.ofFn σ) := rfl

/-- Gauge equivalence: `A` and `B` are related by simultaneous similarity
`B i = X * A i * X⁻¹` for some `X ∈ GL(D,ℂ)`. -/
def GaugeEquiv (A B : MPSTensor d D) : Prop :=
  ∃ X : GL (Fin D) ℂ, ∀ i : Fin d, B i = X * A i * X⁻¹

/-- Two tensors generate the same MPV family if they produce the same coefficient for every
system size `N` and every basis configuration `σ : Fin N → Fin d`. -/
def SameMPV (A B : MPSTensor d D) : Prop :=
  ∀ (N : ℕ) (σ : Fin N → Fin d), mpv A σ = mpv B σ

/-- MPV equality for possibly different bond dimensions.

This is the heterogeneous version of `SameMPV`, used later when comparing
block decompositions whose summands need not live in the same matrix algebra. -/
def SameMPV₂ {d D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂) : Prop :=
  ∀ (N : ℕ) (σ : Fin N → Fin d), mpv A σ = mpv B σ

/-- Proportionality of MPVs: for each N there exists c_N with V_N(A) = c_N · V_N(B). -/
def ProportionalMPV₂ {d D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂) : Prop :=
  ∀ N : ℕ, ∃ c : ℂ, ∀ σ : Fin N → Fin d, mpv A σ = c * mpv B σ

/-- Gauge equivalence up to a nonzero global scalar (a phase after normalization). -/
def GaugePhaseEquiv {d D : ℕ} (A B : MPSTensor d D) : Prop :=
  ∃ (X : GL (Fin D) ℂ) (ζ : ℂ), ζ ≠ 0 ∧ ∀ i : Fin d,
    B i = ζ • ((X : Matrix (Fin D) (Fin D) ℂ) * A i *
      ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))

/-! ### Injectivity and normality -/

/-- Algebraic injectivity (spanning formulation): the matrices `{A i}` span the full matrix
algebra `Matrix (Fin D) (Fin D) ℂ`. -/
def IsInjective (A : MPSTensor d D) : Prop :=
  Submodule.span ℂ (Set.range A) = (⊤ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ))

/-- Unfolded form of `IsInjective`: the span of the range of `A` equals `⊤`. -/
lemma IsInjective.span_eq_top {A : MPSTensor d D} (hA : IsInjective A) :
    Submodule.span ℂ (Set.range A) = ⊤ := hA

/-- `N`-block injectivity: after blocking `N` sites, the set of all products
`A^{i₁} * ⋯ * A^{i_N}` spans the full matrix algebra.

We index the blocked tensors by `σ : Fin N → Fin d`, i.e. words of length `N`. -/
def IsNBlkInjective (A : MPSTensor d D) (N : ℕ) : Prop :=
  Submodule.span ℂ (Set.range fun σ : Fin N → Fin d => evalWord A (List.ofFn σ))
    = (⊤ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ))

/-- Normality in this project means eventual block injectivity:
there exists some blocking length `N` such that the tensor is `N`-block-injective. -/
def IsNormal (A : MPSTensor d D) : Prop :=
  ∃ N : ℕ, IsNBlkInjective (d := d) (D := D) A N

@[simp] lemma isNormal_iff (A : MPSTensor d D) :
    IsNormal A ↔ ∃ N, IsNBlkInjective A N := Iff.rfl

/-! ### Gauge invariance -/

section GaugeInvariance

variable {A B : MPSTensor d D}

/-- If `B i = X * A i * X⁻¹`, then word evaluation is conjugated:
`evalWord B w = X * evalWord A w * X⁻¹`. -/
lemma evalWord_gauge (X : GL (Fin D) ℂ)
    (hX : ∀ i : Fin d,
        B i = (X : Matrix (Fin D) (Fin D) ℂ) * A i *
          ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) :
    ∀ w : List (Fin d),
      evalWord B w =
        (X : Matrix (Fin D) (Fin D) ℂ) * evalWord A w *
          ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  | [] => by simp [evalWord]
  | i :: w => by simp [evalWord, hX, evalWord_gauge X hX w, Matrix.mul_assoc]

/-- Cyclicity of trace gives invariance under similarity:
`trace (X * M * X⁻¹) = trace M` for `X ∈ GL`. -/
lemma trace_conj_eq (X : GL (Fin D) ℂ) (M : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.trace
        ((X : Matrix (Fin D) (Fin D) ℂ) * M *
          ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) =
      Matrix.trace M := by
  simpa [Matrix.mul_assoc] using Matrix.trace_mul_cycle
      (X : Matrix (Fin D) (Fin D) ℂ) M ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)

/-- Gauge equivalent tensors generate the same MPV family. -/
theorem GaugeEquiv.sameMPV {A B : MPSTensor d D} : GaugeEquiv A B → SameMPV A B := by
  rintro ⟨X, hX⟩ N σ
  simp only [mpv, coeff, evalWord_gauge X hX, trace_conj_eq]

end GaugeInvariance

/-- `GaugeEquiv` is reflexive. -/
theorem GaugeEquiv.refl (A : MPSTensor d D) : GaugeEquiv A A :=
  ⟨1, fun i => by simp⟩

/-- `GaugeEquiv` is symmetric. -/
theorem GaugeEquiv.symm {A B : MPSTensor d D} (h : GaugeEquiv A B) : GaugeEquiv B A := by
  obtain ⟨X, hX⟩ := h
  refine ⟨X⁻¹, fun i => ?_⟩
  rw [hX i]
  simp [Matrix.mul_assoc]

/-- `GaugeEquiv` is transitive. -/
theorem GaugeEquiv.trans {A B C : MPSTensor d D}
    (hAB : GaugeEquiv A B) (hBC : GaugeEquiv B C) :
    GaugeEquiv A C := by
  obtain ⟨X, hX⟩ := hAB
  obtain ⟨Y, hY⟩ := hBC
  refine ⟨Y * X, fun i => ?_⟩
  rw [hY i, hX i]
  simp [Matrix.mul_assoc, mul_inv_rev]

end MPSTensor
