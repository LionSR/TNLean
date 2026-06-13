import TNLean.PEPS.TorusWindowChain4

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

The remaining fiber-gluing engine the cancellation needs — that the corner extension's kernel
is trivial when the added block `R \ S` is blocked-tensor injective, the *shared-corner
cancellation* proper — is stated and scoped in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3 (the `Q`-weight span lemma and the
host-boundary-edge embedding).

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

end PEPS
end TNLean
