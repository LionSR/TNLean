import TNLean.MPS.FundamentalTheorem.Basic

open scoped Matrix BigOperators

namespace MPSTensor

variable {G : Type*} {d D : ℕ}

/-- Tensor twisted by physical action of `g ∈ G`. -/
noncomputable def twistedTensor (A : MPSTensor d D)
    (U : G → Matrix (Fin d) (Fin d) ℂ) (g : G) : MPSTensor d D :=
  fun i => ∑ j : Fin d, U g i j • A j

/-- MPS is `G`-symmetric under on-site representation `U`. -/
def IsOnSiteSymmetric (A : MPSTensor d D)
    (U : G → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ g : G, SameMPV A (twistedTensor A U g)

lemma twistedTensor_one (A : MPSTensor d D)
    (U : G → Matrix (Fin d) (Fin d) ℂ) [Monoid G] (hU1 : U 1 = 1) :
    twistedTensor A U 1 = A := by
  ext i a b
  simp [twistedTensor, hU1, Matrix.one_apply]

lemma twistedTensor_mul (A : MPSTensor d D)
    (U : G → Matrix (Fin d) (Fin d) ℂ) [Monoid G]
    (hUmul : ∀ g h : G, U (g * h) = U g * U h)
    (g h : G) :
    twistedTensor A U (g * h) = twistedTensor (twistedTensor A U h) U g := by
  ext i a b
  simp only [twistedTensor, hUmul, Matrix.mul_apply]
  calc
    ((∑ x : Fin d, (∑ y : Fin d, U g i y * U h y x) • A x) a b)
        = ∑ x : Fin d, (∑ y : Fin d, U g i y * U h y x) * A x a b := by
            simp [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    _ = ∑ x : Fin d, ∑ y : Fin d, (U g i y * U h y x) * A x a b := by
          simp [Finset.sum_mul]
    _ = ∑ y : Fin d, ∑ x : Fin d, (U g i y * U h y x) * A x a b := by
          simpa using (Finset.sum_comm :
            (∑ x : Fin d, ∑ y : Fin d, (U g i y * U h y x) * A x a b) =
              ∑ y : Fin d, ∑ x : Fin d, (U g i y * U h y x) * A x a b)
    _ = ∑ y : Fin d, U g i y * (∑ x : Fin d, U h y x * A x a b) := by
          simp [Finset.mul_sum, mul_assoc]
    _ = ((∑ y : Fin d, U g i y • ∑ x : Fin d, U h y x • A x) a b) := by
          simp [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

lemma mpv_twistedTensor_eq_trace_evalWord (A : MPSTensor d D)
    (U : G → Matrix (Fin d) (Fin d) ℂ) (g : G) {N : ℕ}
    (σ : Fin N → Fin d) :
    mpv (twistedTensor A U g) σ =
      Matrix.trace (evalWord (twistedTensor A U g) (List.ofFn σ)) := by
  simp [mpv, coeff]

lemma sameMPV_twistedTensor_iff_gaugeEquiv (A : MPSTensor d D)
    (hA : IsInjective A) (U : G → Matrix (Fin d) (Fin d) ℂ) (g : G) :
    SameMPV A (twistedTensor A U g) ↔ GaugeEquiv A (twistedTensor A U g) := by
  constructor
  · intro hSame
    exact fundamentalTheorem_singleBlock hA hSame
  · intro hGauge
    exact GaugeEquiv.sameMPV hGauge

lemma gaugeEquiv_twistedTensor_of_injective (A : MPSTensor d D)
    (hA : IsInjective A) (U : G → Matrix (Fin d) (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) :
    GaugeEquiv A (twistedTensor A U g) := by
  exact (sameMPV_twistedTensor_iff_gaugeEquiv A hA U g).1 (hSymm g)

end MPSTensor
