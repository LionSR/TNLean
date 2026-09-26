/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TwoSiteStandardForm
import TNLean.MPS.MPDO.OperatorCyclicSum

/-!
# Periodic circuit of a two-site standard form

For a tensor with supplied two-site standard-form data, the periodic operator
at every positive length is the product of an unshifted layer of the gate `u`
and a cyclically shifted layer of the gate `v`. Both layers are unitary between
their indicated coordinate spaces. Consequently the periodic operator is
unitary, without assuming that the tensor is already an MPU.

The first factor applied to a physical input is `u`; the second is `v`.
At length one the cyclic successor fixes the single site; the displayed pair
order remains in force. Length zero is excluded because the
empty virtual trace is the bond dimension, independently of the two gates.

Source context: arXiv:1703.09188, equations `uuvv`, `uu`, `vdagger`, and
`StandardForm`, and Definition `SF`, lines 532--543 and 603--622. The closed
positive-length identity is derived here from the supplied open contraction.
-/

open scoped Matrix BigOperators
open Matrix

private noncomputable def rectangularProduct {N : ℕ} {α β : Type*}
    [Fintype α] [Fintype β] (A : Matrix α β ℂ) :
    Matrix (Fin N → α) (Fin N → β) ℂ :=
  fun a b => ∏ x : Fin N, A (a x) (b x)

private theorem rectangularProduct_isIsometry {N : ℕ} {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (A : Matrix α β ℂ) (hA : A.IsIsometry) :
    (rectangularProduct (N := N) A).IsIsometry := by
  change (rectangularProduct (N := N) A)ᴴ * rectangularProduct A = 1
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, rectangularProduct,
    star_prod, ← Finset.prod_mul_distrib]
  rw [(Fintype.prod_sum (fun x c => star (A c (a x)) * A c (b x))).symm]
  simp only [← Matrix.mul_apply, ← Matrix.conjTranspose_apply]
  rw [show Aᴴ * A = 1 from hA]
  simp only [Matrix.one_apply]
  by_cases hab : a = b
  · subst b
    simp
  · obtain ⟨x, hx⟩ := Function.ne_iff.mp hab
    simp only [hab, ↓reduceIte]
    exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp [hx])

private theorem rectangularProduct_conjTranspose {N : ℕ} {α β : Type*}
    [Fintype α] [Fintype β] (A : Matrix α β ℂ) :
    (rectangularProduct (N := N) A)ᴴ = rectangularProduct Aᴴ := by
  ext a b
  simp [rectangularProduct, Matrix.conjTranspose_apply, star_prod]

private theorem rectangularProduct_isUnitaryBetween {N : ℕ} {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (A : Matrix α β ℂ) (hA : A.IsUnitaryBetween) :
    (rectangularProduct (N := N) A).IsUnitaryBetween := by
  refine ⟨rectangularProduct_isIsometry A hA.1, ?_⟩
  have h := rectangularProduct_isIsometry (N := N) Aᴴ (hA.2.conjTranspose A)
  rw [← rectangularProduct_conjTranspose] at h
  simpa using h.conjTranspose _

namespace MPOTensor

variable {d D ℓ r N : ℕ}

/-- The product of the supplied gate $u$ on each unshifted pair. Its entries are
$\prod_x u_{h_x,j_x}$, with row pairs in $(\ell,r)$ order.

Source context: arXiv:1703.09188, equation `StandardForm`, lines 603--617. -/
noncomputable def twoSiteUnshiftedLayer
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ) :
    Matrix (Fin N → Fin ℓ × Fin r) (Fin N → Fin d × Fin d) ℂ :=
  fun h j => ∏ x : Fin N, u (h x) (j x)

/-- The product of the supplied gate $v$ on the cyclic pairs joining adjacent
two-site blocks. Its entry is
$\prod_x v_{(i_{x,2},i_{x+1,1}),(h_{x,2},h_{x+1,1})}$.

Source context: arXiv:1703.09188, equation `StandardForm`, lines 603--617. -/
noncomputable def twoSiteShiftedLayer
    [NeZero N] (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) :
    Matrix (Fin N → Fin d × Fin d) (Fin N → Fin ℓ × Fin r) ℂ :=
  fun i h => ∏ x : Fin N,
    v ((i x).2, (i (x + 1)).1) ((h x).2, (h (x + 1)).1)

/-- Relabel a pair configuration by its second coordinate at site $x$ and
its first coordinate at site $x+1$. The inverse reads the first coordinate
from site $x-1$ and the second from site $x$.

Source context: arXiv:1703.09188, equation `StandardForm`, lines 603--617. -/
def twoSiteShiftedPairEquiv [NeZero N] :
    (Fin N → Fin ℓ × Fin r) ≃ (Fin N → Fin r × Fin ℓ) where
  toFun h x := ((h x).2, (h (x + 1)).1)
  invFun q x := ((q (x - 1)).2, (q x).1)
  left_inv h := by
    funext x
    simp
  right_inv q := by
    funext x
    simp

/-- The unshifted layer is unitary between the physical-pair and
intermediate-pair configuration spaces.

Source context: arXiv:1703.09188, equation `StandardForm`, lines 603--617. -/
theorem twoSiteUnshiftedLayer_isUnitaryBetween
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (hu : u.IsUnitaryBetween) :
    (twoSiteUnshiftedLayer (N := N) u).IsUnitaryBetween :=
  rectangularProduct_isUnitaryBetween (N := N) u hu

/-- The shifted layer is unitary between the intermediate-pair and
physical-pair configuration spaces.

Source context: arXiv:1703.09188, equation `StandardForm`, lines 603--617. -/
theorem twoSiteShiftedLayer_isUnitaryBetween [NeZero N]
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ)
    (hv : v.IsUnitaryBetween) :
    (twoSiteShiftedLayer (N := N) v).IsUnitaryBetween := by
  have h := rectangularProduct_isUnitaryBetween (N := N) v hv
  have h' := h.reindex (rectangularProduct (N := N) v)
    (twoSiteShiftedPairEquiv (N := N) (ℓ := d) (r := d)).symm
    (twoSiteShiftedPairEquiv (N := N) (ℓ := ℓ) (r := r)).symm
  convert h' using 1
  ext i j
  rfl

private theorem cyclic_sum_product [NeZero N]
    (A B : Fin N → Fin D → ℂ) :
    (∑ g : Fin N → Fin D, ∏ x : Fin N, A x (g x) * B x (g (x + 1))) =
      ∏ x : Fin N, ∑ β : Fin D, A x β * B (x - 1) β := by
  have hshift (g : Fin N → Fin D) :
      (∏ x : Fin N, B x (g (x + 1))) =
        ∏ x : Fin N, B (x - 1) (g x) := by
    exact Fintype.prod_equiv (Equiv.addRight 1)
      (fun x : Fin N => B x (g (x + 1)))
      (fun x : Fin N => B (x - 1) (g x)) (by intro x; simp)
  calc
    _ = ∑ g : Fin N → Fin D,
          (∏ x : Fin N, A x (g x)) * (∏ x : Fin N, B x (g (x + 1))) := by
            apply Finset.sum_congr rfl
            intro g _
            rw [Finset.prod_mul_distrib]
    _ = ∑ g : Fin N → Fin D,
          (∏ x : Fin N, A x (g x)) * (∏ x : Fin N, B (x - 1) (g x)) := by
            apply Finset.sum_congr rfl
            intro g _
            rw [hshift g]
    _ = ∑ g : Fin N → Fin D,
          ∏ x : Fin N, A x (g x) * B (x - 1) (g x) := by
            apply Finset.sum_congr rfl
            intro g _
            rw [Finset.prod_mul_distrib]
    _ = _ := (Fintype.prod_sum fun x β => A x β * B (x - 1) β).symm

private theorem cyclic_sum_product_forward [NeZero N]
    (A B : Fin N → Fin D → ℂ) :
    (∑ g : Fin N → Fin D, ∏ x : Fin N, A x (g x) * B x (g (x + 1))) =
      ∏ x : Fin N, ∑ β : Fin D, B x β * A (x + 1) β := by
  rw [cyclic_sum_product A B]
  exact (Fintype.prod_equiv (Equiv.addRight 1)
    (fun x : Fin N => ∑ β : Fin D, B x β * A (x + 1) β)
    (fun x : Fin N => ∑ β : Fin D, A x β * B (x - 1) β)
    (by intro x; simp [mul_comm])).symm

/-- At every positive length, a periodic coefficient is the contraction of
the unshifted $u$ layer with the shifted $v$ layer. The second physical output
of site $x$ joins the first output of site $x+1$, including across the seam.

Source context: arXiv:1703.09188, equations `uuvv` and `StandardForm`,
lines 532--543 and 603--617. -/
theorem TwoSiteStandardFormData.mpo_apply_eq_shifted_mul_unshifted
    [NeZero N] (W : MPOTensor (d * d) D)
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ)
    (S : TwoSiteStandardFormData W u v)
    (i j : Fin N → Fin d × Fin d) :
    mpo W N (fun x => finProdFinEquiv (i x))
        (fun x => finProdFinEquiv (j x)) =
      (twoSiteShiftedLayer (N := N) v * twoSiteUnshiftedLayer (N := N) u) i j := by
  rw [mpo_apply_eq_sum_cyclic, Matrix.mul_apply]
  simp only [S.W_apply, Equiv.symm_apply_apply, twoSiteShiftedLayer,
    twoSiteUnshiftedLayer]
  have hletter (g : Fin N → Fin D) (x : Fin N) :
      (∑ t : Fin ℓ, ∑ s : Fin r,
        S.X₂ (g x, (i x).1) t * u (t, s) (j x) *
          S.X₁ ((i x).2, g (x + 1)) s) =
      ∑ h : Fin ℓ × Fin r,
        (S.X₂ (g x, (i x).1) h.1 *
          S.X₁ ((i x).2, g (x + 1)) h.2) * u h (j x) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro s _
    ring
  simp_rw [hletter]
  simp only [Fintype.prod_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  let A : Fin N → Fin D → ℂ := fun x β => S.X₂ (β, (i x).1) (h x).1
  let B : Fin N → Fin D → ℂ := fun x β => S.X₁ ((i x).2, β) (h x).2
  have hbond :
      (∑ g : Fin N → Fin D, ∏ x : Fin N, A x (g x) * B x (g (x + 1))) =
        ∏ x : Fin N,
          v ((i x).2, (i (x + 1)).1) ((h x).2, (h (x + 1)).1) := by
    rw [cyclic_sum_product_forward]
    apply Finset.prod_congr rfl
    intro x _
    rw [S.v_apply]
  calc
    _ = (∑ g : Fin N → Fin D,
          ∏ x : Fin N, A x (g x) * B x (g (x + 1))) *
          ∏ x : Fin N, u (h x) (j x) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro g _
            rw [Finset.prod_mul_distrib]
    _ = _ := by rw [hbond]

/-- Identify a chain of physical pairs with the alphabet of the two-site MPO
tensor, without changing the order of either physical coordinate.

Source context: arXiv:1703.09188, equation `StandardForm`, lines 603--617. -/
noncomputable def twoSitePairConfigEquiv (d N : ℕ) :
    (Fin N → Fin d × Fin d) ≃ (Fin N → Fin (d * d)) :=
  Equiv.arrowCongr (Equiv.refl (Fin N)) finProdFinEquiv

/-- At every positive length, the periodic operator in pair coordinates is
the shifted $v$ layer after the unshifted $u$ layer.

Source context: arXiv:1703.09188, equations `uuvv` and `StandardForm`,
lines 532--543 and 603--617. -/
theorem TwoSiteStandardFormData.mpo_eq_shifted_mul_unshifted
    [NeZero N] (W : MPOTensor (d * d) D)
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ)
    (S : TwoSiteStandardFormData W u v) :
    Matrix.reindex (twoSitePairConfigEquiv d N).symm
        (twoSitePairConfigEquiv d N).symm (mpo W N) =
      twoSiteShiftedLayer (N := N) v * twoSiteUnshiftedLayer (N := N) u := by
  ext i j
  simpa [Matrix.reindex_apply, twoSitePairConfigEquiv, Equiv.arrowCongr,
    Function.comp_def] using
    TwoSiteStandardFormData.mpo_apply_eq_shifted_mul_unshifted W u v S i j

/-- The periodic operator of a supplied two-site standard form is unitary
at every positive length, including length one.

Source context: arXiv:1703.09188, equation `StandardForm` and Definition
`SF`, lines 603--622. -/
theorem TwoSiteStandardFormData.mpo_mem_unitaryGroup
    [NeZero N] (W : MPOTensor (d * d) D)
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ)
    (S : TwoSiteStandardFormData W u v) :
    mpo W N ∈ Matrix.unitaryGroup (Fin N → Fin (d * d)) ℂ := by
  have hcircuit :
      (Matrix.reindex (twoSitePairConfigEquiv d N).symm
        (twoSitePairConfigEquiv d N).symm
        (mpo W N)).IsUnitaryBetween := by
    rw [TwoSiteStandardFormData.mpo_eq_shifted_mul_unshifted W u v S]
    exact (twoSiteShiftedLayer_isUnitaryBetween v S.v_unitary).mul _ _
      (twoSiteUnshiftedLayer_isUnitaryBetween u S.u_unitary)
  have h := hcircuit.reindex _ (twoSitePairConfigEquiv d N)
    (twoSitePairConfigEquiv d N)
  apply (Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mp
  convert h using 1
  ext i j
  simp [Matrix.reindex_apply]

/-- A supplied two-site standard form generates unitary periodic MPOs at
all lengths required by the MPU predicate.

Source context: arXiv:1703.09188, equation `StandardForm`, Definition `SF`,
and the MPU length convention, lines 319--335 and 603--622. -/
theorem TwoSiteStandardFormData.isMPU
    (W : MPOTensor (d * d) D)
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ)
    (S : TwoSiteStandardFormData W u v) : IsMPU W := by
  intro N hN
  let _ : NeZero N := ⟨by omega⟩
  exact TwoSiteStandardFormData.mpo_mem_unitaryGroup W u v S

end MPOTensor
