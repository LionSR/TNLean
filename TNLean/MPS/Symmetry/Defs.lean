import TNLean.MPS.FundamentalTheorem.Basic

open scoped Matrix BigOperators

namespace MPSTensor

variable {G : Type*} [Group G] {d D : ℕ}

/-- Tensor twisted by physical action of `g ∈ G`.

If `U : G →* Matrix (Fin d) (Fin d) ℂ` is an on-site representation, then
`twistedTensor A U g` has components
`(twistedTensor A U g) i = ∑ j, U g i j • A j`. -/
noncomputable def twistedTensor (A : MPSTensor d D)
    (U : G →* Matrix (Fin d) (Fin d) ℂ) (g : G) : MPSTensor d D :=
  fun i => ∑ j : Fin d, U g i j • A j

/-- `A` is on-site symmetric under `U` if each group twist has the same MPV as `A`. -/
def IsOnSiteSymmetric (A : MPSTensor d D)
    (U : G →* Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ g : G, SameMPV A (twistedTensor A U g)

/-- Twisting by the identity group element is trivial. -/
@[simp] lemma twistedTensor_one (A : MPSTensor d D)
    (U : G →* Matrix (Fin d) (Fin d) ℂ) :
    twistedTensor A U 1 = A := by
  funext i
  simp [twistedTensor, Matrix.one_apply]

/-- Functoriality/composition law for twists:

twisting by `g * h` is the same as first twisting by `h` and then by `g`. -/
lemma twistedTensor_mul (A : MPSTensor d D)
    (U : G →* Matrix (Fin d) (Fin d) ℂ) (g h : G) :
    twistedTensor A U (g * h) = twistedTensor (twistedTensor A U h) U g := by
  funext i
  calc
    twistedTensor A U (g * h) i
        = ∑ k : Fin d, (∑ j : Fin d, U g i j * U h j k) • A k := by
            simp [twistedTensor, Matrix.mul_apply]
    _ = ∑ k : Fin d, ∑ j : Fin d, (U g i j * U h j k) • A k := by
          simp_rw [Finset.sum_smul]
    _ = ∑ j : Fin d, ∑ k : Fin d, (U g i j * U h j k) • A k := Finset.sum_comm
    _ = twistedTensor (twistedTensor A U h) U g i := by
          simp [twistedTensor, Finset.smul_sum, smul_smul]

/-- For injective `A`, MPV equality with any `B` is equivalent to gauge equivalence. -/
theorem sameMPV_iff_gaugeEquiv_of_injective {A B : MPSTensor d D}
    (hA : IsInjective A) :
    SameMPV A B ↔ GaugeEquiv A B := by
  constructor
  · intro hAB
    exact fundamentalTheorem_singleBlock hA hAB
  · intro hAB
    exact GaugeEquiv.sameMPV hAB

/-- Twisted specialization of `sameMPV_iff_gaugeEquiv_of_injective`. -/
theorem sameMPV_twistedTensor_iff_gaugeEquiv
    (A : MPSTensor d D) (hA : IsInjective A)
    (U : G →* Matrix (Fin d) (Fin d) ℂ) (g : G) :
    SameMPV A (twistedTensor A U g) ↔ GaugeEquiv A (twistedTensor A U g) :=
  sameMPV_iff_gaugeEquiv_of_injective hA

/-- Injective on-site symmetry implies each twisted tensor is gauge equivalent to `A`. -/
theorem gaugeEquiv_twistedTensor_of_injective
    (A : MPSTensor d D) (hA : IsInjective A)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) :
    ∀ g : G, GaugeEquiv A (twistedTensor A U g) := by
  intro g
  exact (sameMPV_iff_gaugeEquiv_of_injective hA).1 (hSymm g)

end MPSTensor
