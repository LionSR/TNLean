import Mathlib.Data.Complex.Basic
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Trace

open scoped Matrix

/-- A (periodic, translation-invariant) MPS tensor: a family of `D×D` matrices indexed by a
physical index in `Fin d`. -/
abbrev MPSTensor (d D : ℕ) := Fin d → Matrix (Fin D) (Fin D) ℂ

namespace MPSTensor

variable {d D : ℕ}

/-- Evaluate a word `w = [i₁, i₂, …, iₙ]` by multiplying the corresponding matrices
`A i₁ * A i₂ * ⋯ * A iₙ`. Returns `1` for the empty word. -/
def evalWord (A : MPSTensor d D) : List (Fin d) → Matrix (Fin D) (Fin D) ℂ
  | [] => 1
  | i :: w => A i * evalWord A w

/-- Word evaluation respects concatenation:
`evalWord A (w1 ++ w2) = evalWord A w1 * evalWord A w2`. -/
lemma evalWord_append (A : MPSTensor d D) :
    ∀ w1 w2 : List (Fin d), evalWord A (w1 ++ w2) = evalWord A w1 * evalWord A w2 := by
  intro w1 w2
  induction w1 with
  | nil => simp [evalWord]
  | cons i w1 ih => simp [evalWord, ih, Matrix.mul_assoc]

/-- The MPV coefficient for a word `w`, given by `trace (evalWord A w)`. -/
def coeff (A : MPSTensor d D) (w : List (Fin d)) : ℂ :=
  Matrix.trace (evalWord A w)

/-- The Matrix Product Vector (MPV) for system size `N`: for each basis state
`σ : Fin N → Fin d`, this returns the coefficient
`trace (A (σ 0) * A (σ 1) * ⋯ * A (σ (N-1)))`. -/
def mpv (A : MPSTensor d D) {N : ℕ} (σ : Fin N → Fin d) : ℂ :=
  coeff A (List.ofFn σ)

/-- Gauge equivalence: `A` and `B` are related by simultaneous similarity
`B i = X * A i * X⁻¹` for some `X ∈ GL(D,ℂ)`. -/
def GaugeEquiv (A B : MPSTensor d D) : Prop :=
  ∃ X : GL (Fin D) ℂ, ∀ i : Fin d, B i = X * A i * X⁻¹

/-- Two tensors generate the same MPV family if they produce the same coefficient for every
system size `N` and every basis configuration `σ : Fin N → Fin d`. -/
def SameMPV (A B : MPSTensor d D) : Prop :=
  ∀ (N : ℕ) (σ : Fin N → Fin d), mpv A σ = mpv B σ

/-- MPV equality for possibly different bond dimensions. -/
def SameMPV₂ {d D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂) : Prop :=
  ∀ (N : ℕ) (σ : Fin N → Fin d), mpv A σ = mpv B σ

/-- Proportionality of MPVs: for each N there exists c_N with V_N(A) = c_N · V_N(B). -/
def ProportionalMPV₂ {d D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂) : Prop :=
  ∀ N : ℕ, ∃ c : ℂ, ∀ σ : Fin N → Fin d, mpv A σ = c * mpv B σ

/-- Gauge equivalence up to a global phase. -/
def GaugePhaseEquiv {d D : ℕ} (A B : MPSTensor d D) : Prop :=
  ∃ (X : GL (Fin D) ℂ) (ζ : ℂ), ∀ i : Fin d,
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

/-- Normality (a.k.a. quantum Wielandt property, in this algebraic formulation):
there exists some blocking length `N` such that the tensor is `N`-block-injective. -/
def IsNormal (A : MPSTensor d D) : Prop :=
  ∃ N : ℕ, IsNBlkInjective (d := d) (D := D) A N

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
  simpa [Matrix.mul_assoc] using
    (Matrix.trace_mul_cycle (X : Matrix (Fin D) (Fin D) ℂ) M
      ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))

/-- Gauge equivalent tensors generate the same MPV family. -/
theorem GaugeEquiv.sameMPV {A B : MPSTensor d D} : GaugeEquiv A B → SameMPV A B := by
  rintro ⟨X, hX⟩ N σ
  simp only [mpv, coeff]
  rw [evalWord_gauge (A := A) (B := B) X hX (List.ofFn σ)]
  simpa using (trace_conj_eq X (evalWord A (List.ofFn σ))).symm

end GaugeInvariance

end MPSTensor
