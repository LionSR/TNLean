/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TwoSiteStandardForm
import TNLean.Algebra.UnitaryKronecker
import TNLean.Algebra.FinSumPermutation

/-!
# Open words and local observables in a two-site standard form

The two half factors of a supplied two-site standard form expose the virtual
ends of a finite word. At three complete blocks, the two internal half-factor
contractions form the shifted gates. Unitarity of the supplied gates then
intertwines an arbitrary middle input observable with an observable on the
four neighboring output half-sites. The virtual indices remain free in the
main identity. Separate consequences allow arbitrary virtual endpoint
matrices and complete-block words on either side.

This assumes supplied standard-form data, not that the tensor itself is an
MPU. It does not assert stabilization of finite-chain conjugations or
construct a QCA.

## References

* arXiv:1703.09188, equations `uuvv` and `StandardForm`, lines 532--543 and
  603--622.
-/

open scoped Matrix BigOperators Kronecker
open Matrix

namespace MPOTensor

variable {d D ℓ r : ℕ}

/-- The left exposed half factor of one source-standard-form letter.
Source: arXiv:1703.09188, equation `StandardForm`, lines 603--617. -/
noncomputable def twoSiteLeftHalf
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (i : Fin (d * d)) :
    Matrix (Fin D) (Fin ℓ) ℂ :=
  fun α t => S.X₂ (α, (finProdFinEquiv.symm i).1) t

/-- The right exposed half factor of one source-standard-form letter.
Source: arXiv:1703.09188, equation `StandardForm`, lines 603--617. -/
noncomputable def twoSiteRightHalf
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (i : Fin (d * d)) :
    Matrix (Fin r) (Fin D) ℂ :=
  fun s γ => S.X₁ ((finProdFinEquiv.symm i).2, γ) s

/-- The unshifted gate with its physical input pair fixed.
Source: arXiv:1703.09188, equation `uuvv`, lines 532--543. -/
noncomputable def twoSiteInputGate
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ) (j : Fin (d * d)) :
    Matrix (Fin ℓ) (Fin r) ℂ :=
  fun t s => u (t, s) (finProdFinEquiv.symm j)

/-- The shifted gate with its neighboring physical output pair fixed.
Source: arXiv:1703.09188, equation `uuvv`, lines 532--543. -/
noncomputable def twoSiteOutputLink
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ)
    (i i' : Fin (d * d)) : Matrix (Fin r) (Fin ℓ) ℂ :=
  fun s t => v ((finProdFinEquiv.symm i).2, (finProdFinEquiv.symm i').1) (s, t)

/-- A source-standard-form letter factors through its two open half factors
and the unshifted gate. Source: arXiv:1703.09188, equation `StandardForm`,
lines 603--617. -/
theorem twoSite_letter_factorization
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (i j : Fin (d * d)) :
    W i j = twoSiteLeftHalf S i * twoSiteInputGate u j * twoSiteRightHalf S i := by
  ext α γ
  simp only [S.W_apply, Matrix.mul_apply, twoSiteLeftHalf, twoSiteInputGate,
    twoSiteRightHalf]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Adjacent half factors contract to the shifted gate without closing the
virtual ends. Source: arXiv:1703.09188, equation `vdagger`, lines 532--543. -/
theorem twoSite_adjacent_halves
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (i i' : Fin (d * d)) :
    twoSiteRightHalf S i * twoSiteLeftHalf S i' = twoSiteOutputLink v i i' := by
  ext s t
  simp only [Matrix.mul_apply, twoSiteRightHalf, twoSiteLeftHalf,
    twoSiteOutputLink]
  rw [S.v_apply]

/-- The gate product from the first unshifted gate to the open right virtual
end. The list contains all later complete two-site blocks. -/
noncomputable def twoSiteOpenGateTail
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (i j : Fin (d * d)) :
    List (Fin (d * d) × Fin (d * d)) → Matrix (Fin ℓ) (Fin D) ℂ
  | [] => twoSiteInputGate u j * twoSiteRightHalf S i
  | (i', j') :: rest =>
      twoSiteInputGate u j * twoSiteOutputLink v i i' *
        twoSiteOpenGateTail S i' j' rest

/-- Open-word factorization of the supplied standard form. No virtual trace
or cyclic end contraction occurs; the first left half and last right half
remain available for arbitrary residual boundary factors. -/
theorem twoSite_evalWord_open_gate_factorization
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (i j : Fin (d * d))
    (rest : List (Fin (d * d) × Fin (d * d))) :
    evalWord W (i :: rest.map Prod.fst) (j :: rest.map Prod.snd) =
      twoSiteLeftHalf S i * twoSiteOpenGateTail S i j rest := by
  induction rest generalizing i j with
  | nil =>
      simp [evalWord_cons, evalWord_nil, twoSiteOpenGateTail,
        twoSite_letter_factorization S, Matrix.mul_assoc]
  | cons hd tl ih =>
      cases hd with
      | mk i' j' =>
          simp only [List.map_cons, twoSiteOpenGateTail]
          rw [evalWord_cons, ih i' j', twoSite_letter_factorization S i j]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (twoSiteRightHalf S i)
            (twoSiteLeftHalf S i') (twoSiteOpenGateTail S i' j' tl)]
          rw [twoSite_adjacent_halves S i i']

/-- Arbitrary virtual endpoint factors do not alter any internal gate
contraction. In the mixed-block application they are the residual prefix and
suffix products, respectively. -/
theorem twoSite_trace_open_gate_with_endpoints
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v)
    (P Q : Matrix (Fin D) (Fin D) ℂ)
    (i j : Fin (d * d))
    (rest : List (Fin (d * d) × Fin (d * d))) :
    Matrix.trace (P * evalWord W (i :: rest.map Prod.fst) (j :: rest.map Prod.snd) * Q) =
      Matrix.trace (P * twoSiteLeftHalf S i * twoSiteOpenGateTail S i j rest * Q) := by
  rw [twoSite_evalWord_open_gate_factorization S i j]
  simp only [Matrix.mul_assoc]

private theorem unitaryBetween_mul_pullThrough
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (U : Matrix α β ℂ) (hU : U.IsUnitaryBetween)
    (A : Matrix β β ℂ) :
    U * A = (U * A * Uᴴ) * U := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, hU.1]
  simp

private noncomputable def twoLinkMiddleLift
    (C : Matrix (Fin ℓ × Fin r) (Fin ℓ × Fin r) ℂ) :
    Matrix ((Fin r × Fin ℓ) × (Fin r × Fin ℓ))
      ((Fin r × Fin ℓ) × (Fin r × Fin ℓ)) ℂ :=
  fun x y =>
    (1 : Matrix (Fin r) (Fin r) ℂ) x.1.1 y.1.1 *
      C (x.1.2, x.2.1) (y.1.2, y.2.1) *
        (1 : Matrix (Fin ℓ) (Fin ℓ) ℂ) x.2.2 y.2.2

private noncomputable def twoLinkBoundaryInput
    (L : Fin r → ℂ) (R : Fin ℓ → ℂ)
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ) :
    Matrix ((Fin r × Fin ℓ) × (Fin r × Fin ℓ)) (Fin d × Fin d) ℂ :=
  fun x j => L x.1.1 * u (x.1.2, x.2.1) j * R x.2.2

private theorem twoLinkMiddleLift_mul_boundaryInput_apply
    (L : Fin r → ℂ) (R : Fin ℓ → ℂ)
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (C : Matrix (Fin ℓ × Fin r) (Fin ℓ × Fin r) ℂ)
    (x : (Fin r × Fin ℓ) × (Fin r × Fin ℓ))
    (j : Fin d × Fin d) :
    (twoLinkMiddleLift C * twoLinkBoundaryInput L R u) x j =
      L x.1.1 * (C * u) (x.1.2, x.2.1) j * R x.2.2 := by
  simp only [Matrix.mul_apply, twoLinkMiddleLift, twoLinkBoundaryInput,
    Fintype.sum_prod_type, Matrix.one_apply, ite_mul, mul_ite,
    zero_mul, mul_zero, one_mul, mul_one, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x₁ _
  apply Finset.sum_congr rfl
  intro x₂ _
  ring

private theorem twoLink_boundaryInput_pullThrough
    (L : Fin r → ℂ) (R : Fin ℓ → ℂ)
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (hu : u.IsUnitaryBetween)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    twoLinkBoundaryInput L R u * A =
      twoLinkMiddleLift (u * A * uᴴ) * twoLinkBoundaryInput L R u := by
  ext x j
  rw [twoLinkMiddleLift_mul_boundaryInput_apply]
  rw [← unitaryBetween_mul_pullThrough u hu A]
  simp only [Matrix.mul_apply, twoLinkBoundaryInput]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

private noncomputable def twoLinkOutputGate
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) :
    Matrix ((Fin d × Fin d) × (Fin d × Fin d))
      ((Fin r × Fin ℓ) × (Fin r × Fin ℓ)) ℂ :=
  v ⊗ₖ v

/-- The observable on two neighboring shifted output pairs induced by an
observable on the intervening unshifted input pair. In the link order
`(r, ℓ, r, ℓ)`, it is
`(v ⊗ v) (1_r ⊗ (u A uᴴ) ⊗ 1_ℓ) (v ⊗ v)ᴴ`.

Source context: arXiv:1703.09188, equations `uuvv` and `StandardForm`, lines
532--543 and 603--622. -/
noncomputable def twoLinkOutputObservable
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix ((Fin d × Fin d) × (Fin d × Fin d))
      ((Fin d × Fin d) × (Fin d × Fin d)) ℂ :=
  twoLinkOutputGate v * twoLinkMiddleLift (u * A * uᴴ) *
    (twoLinkOutputGate v)ᴴ

/-- The local middle-site pull-through is an operator identity for every
choice of the two exposed boundary coefficients. -/
private theorem twoLink_open_middle_intertwiner
    (L : Fin r → ℂ) (R : Fin ℓ → ℂ)
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ)
    (hu : u.IsUnitaryBetween) (hv : v.IsUnitaryBetween)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (twoLinkOutputGate v * twoLinkBoundaryInput L R u) * A =
      twoLinkOutputObservable u v A *
        (twoLinkOutputGate v * twoLinkBoundaryInput L R u) := by
  let V := twoLinkOutputGate v
  let C := twoLinkMiddleLift (u * A * uᴴ)
  have hV : V.IsUnitaryBetween := by
    dsimp [V, twoLinkOutputGate]
    exact hv.kronecker v v hv
  change (V * twoLinkBoundaryInput L R u) * A =
    (V * C * Vᴴ) * (V * twoLinkBoundaryInput L R u)
  calc
    (V * twoLinkBoundaryInput L R u) * A =
        V * (twoLinkBoundaryInput L R u * A) := by rw [Matrix.mul_assoc]
    _ = V * (C * twoLinkBoundaryInput L R u) := by
      rw [twoLink_boundaryInput_pullThrough L R u hu A]
    _ = (V * C) * twoLinkBoundaryInput L R u := by rw [Matrix.mul_assoc]
    _ = ((V * C * Vᴴ) * V) * twoLinkBoundaryInput L R u := by
      exact congrArg (fun X => X * twoLinkBoundaryInput L R u)
        (unitaryBetween_mul_pullThrough V hV C)
    _ = (V * C * Vᴴ) * (V * twoLinkBoundaryInput L R u) := by
      rw [Matrix.mul_assoc]

private noncomputable def twoLinkOutputSlice
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ)
    (a : Fin d × Fin d) : Matrix (Fin r) (Fin ℓ) ℂ :=
  fun s t => v a (s,t)

private noncomputable def twoLinkInputSlice
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (j : Fin d × Fin d) : Matrix (Fin ℓ) (Fin r) ℂ :=
  fun t s => u (t,s) j

private theorem twoLink_open_coefficient
    (P : Matrix (Fin D) (Fin r) ℂ)
    (Q : Matrix (Fin ℓ) (Fin D) ℂ)
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ)
    (a b : Fin d × Fin d) (j : Fin d × Fin d)
    (α γ : Fin D) :
    (P * twoLinkOutputSlice v a * twoLinkInputSlice u j *
        twoLinkOutputSlice v b * Q) α γ =
      (twoLinkOutputGate v *
        twoLinkBoundaryInput (fun s => P α s) (fun t => Q t γ) u)
          (a,b) j := by
  simp only [Matrix.mul_apply, twoLinkOutputSlice,
    twoLinkInputSlice, twoLinkOutputGate,
    Matrix.kronecker_apply, twoLinkBoundaryInput, Fintype.sum_prod_type]
  simp_rw [Finset.sum_mul]
  rw [Fintype.sum_last_first_four]
  apply Finset.sum_congr₂
  intro s₀ _ t₁ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr₂
  intro s₁ _ t₂ _
  ring

/-- The exact three-block open-word coefficient has two internal output
links. The first and last complete blocks contribute arbitrary boundary
coefficients, while the virtual indices α and γ remain uncontracted. -/
private theorem twoSite_threeBlock_open_coefficient
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v)
    (i₀ i₁ i₂ j₀ j₁ j₂ : Fin (d * d)) (α γ : Fin D) :
    (evalWord W [i₀,i₁,i₂] [j₀,j₁,j₂]) α γ =
      (twoLinkOutputGate v *
        twoLinkBoundaryInput
          (fun s => (twoSiteLeftHalf S i₀ * twoSiteInputGate u j₀) α s)
          (fun t => (twoSiteInputGate u j₂ * twoSiteRightHalf S i₂) t γ) u)
        (((finProdFinEquiv.symm i₀).2, (finProdFinEquiv.symm i₁).1),
          ((finProdFinEquiv.symm i₁).2, (finProdFinEquiv.symm i₂).1))
        (finProdFinEquiv.symm j₁) := by
  have hfac := twoSite_evalWord_open_gate_factorization S i₀ j₀
    [(i₁,j₁),(i₂,j₂)]
  simp only [List.map_cons, List.map_nil, twoSiteOpenGateTail] at hfac
  rw [hfac]
  have hcoeff := twoLink_open_coefficient
    (twoSiteLeftHalf S i₀ * twoSiteInputGate u j₀)
    (twoSiteInputGate u j₂ * twoSiteRightHalf S i₂)
    u v
    ((finProdFinEquiv.symm i₀).2, (finProdFinEquiv.symm i₁).1)
    ((finProdFinEquiv.symm i₁).2, (finProdFinEquiv.symm i₂).1)
    (finProdFinEquiv.symm j₁) α γ
  have hs₀ : twoLinkOutputSlice v
      ((finProdFinEquiv.symm i₀).2, (finProdFinEquiv.symm i₁).1) =
      twoSiteOutputLink v i₀ i₁ := rfl
  have hs₁ : twoLinkOutputSlice v
      ((finProdFinEquiv.symm i₁).2, (finProdFinEquiv.symm i₂).1) =
      twoSiteOutputLink v i₁ i₂ := rfl
  have hu₁ : twoLinkInputSlice u (finProdFinEquiv.symm j₁) =
      twoSiteInputGate u j₁ := rfl
  simpa only [Matrix.mul_assoc, hs₀, hs₁, hu₁] using hcoeff

private noncomputable def twoSiteLeftEdge
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (e : Fin d) :
    Matrix (Fin D) (Fin ℓ) ℂ :=
  fun α t => S.X₂ (α,e) t

private noncomputable def twoSiteRightEdge
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (e : Fin d) :
    Matrix (Fin r) (Fin D) ℂ :=
  fun s γ => S.X₁ (e,γ) s

/-- The open three-letter source word, regarded as a matrix from the middle
input pair to the two neighboring output pairs. The exterior output
half-sites, exterior input pairs, and virtual indices are fixed but arbitrary.

Source context: arXiv:1703.09188, equation `StandardForm`, lines 603--617. -/
noncomputable def twoSiteThreeBlockOpen
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (_S : TwoSiteStandardFormData W u v)
    (eL eR : Fin d) (j₀ j₂ : Fin (d * d))
    (α γ : Fin D) :
    Matrix ((Fin d × Fin d) × (Fin d × Fin d)) (Fin d × Fin d) ℂ :=
  fun x j₁ =>
    (evalWord W
      [finProdFinEquiv (eL,x.1.1), finProdFinEquiv (x.1.2,x.2.1),
        finProdFinEquiv (x.2.2,eR)]
      [j₀,finProdFinEquiv j₁,j₂]) α γ

private theorem twoSiteThreeBlockOpen_eq
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v)
    (eL eR : Fin d) (j₀ j₂ : Fin (d * d))
    (α γ : Fin D) :
    twoSiteThreeBlockOpen S eL eR j₀ j₂ α γ =
      twoLinkOutputGate v *
        twoLinkBoundaryInput
          (fun s => (twoSiteLeftEdge S eL * twoSiteInputGate u j₀) α s)
          (fun t => (twoSiteInputGate u j₂ * twoSiteRightEdge S eR) t γ) u := by
  ext x j₁
  rcases x with ⟨⟨a₀,a₁⟩,⟨b₀,b₁⟩⟩
  have hL : twoSiteLeftHalf S (finProdFinEquiv (eL,a₀)) =
      twoSiteLeftEdge S eL := by
    ext α t
    simp [twoSiteLeftHalf, twoSiteLeftEdge]
  have hR : twoSiteRightHalf S (finProdFinEquiv (b₁,eR)) =
      twoSiteRightEdge S eR := by
    ext s γ
    simp [twoSiteRightHalf, twoSiteRightEdge]
  simpa only [twoSiteThreeBlockOpen, hL, hR, Equiv.symm_apply_apply] using
    (twoSite_threeBlock_open_coefficient S
      (finProdFinEquiv (eL,a₀))
      (finProdFinEquiv (a₁,b₀))
      (finProdFinEquiv (b₁,eR))
      j₀ (finProdFinEquiv j₁) j₂ α γ)

/-- Three complete source blocks intertwine a middle input observable with
an observable on the two neighboring output links, while the first and last
virtual indices and the two exterior output coordinates remain free.

This is an open-word consequence of arXiv:1703.09188, equations `uuvv` and
`StandardForm`, lines 532--543 and 603--622; it does not use a virtual trace. -/
theorem twoSite_threeBlock_open_intertwiner
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v)
    (eL eR : Fin d) (j₀ j₂ : Fin (d * d))
    (α γ : Fin D) (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    twoSiteThreeBlockOpen S eL eR j₀ j₂ α γ * A =
      twoLinkOutputObservable u v A *
        twoSiteThreeBlockOpen S eL eR j₀ j₂ α γ := by
  rw [twoSiteThreeBlockOpen_eq]
  exact twoLink_open_middle_intertwiner _ _ u v S.u_unitary S.v_unitary A

private theorem twoSite_threeBlock_weighted_intertwiner
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v)
    (eL eR : Fin d) (j₀ j₂ : Fin (d * d))
    (c : Fin D → Fin D → ℂ)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (∑ γ, ∑ α, c α γ • twoSiteThreeBlockOpen S eL eR j₀ j₂ α γ) * A =
      twoLinkOutputObservable u v A *
        (∑ γ, ∑ α, c α γ • twoSiteThreeBlockOpen S eL eR j₀ j₂ α γ) := by
  calc
    (∑ γ, ∑ α, c α γ • twoSiteThreeBlockOpen S eL eR j₀ j₂ α γ) * A =
        ∑ γ, ∑ α, c α γ • (twoSiteThreeBlockOpen S eL eR j₀ j₂ α γ * A) := by
      simp only [Matrix.sum_mul, Matrix.smul_mul]
    _ = ∑ γ, ∑ α, c α γ •
        (twoLinkOutputObservable u v A *
          twoSiteThreeBlockOpen S eL eR j₀ j₂ α γ) := by
      simp_rw [twoSite_threeBlock_open_intertwiner S eL eR j₀ j₂]
    _ = twoLinkOutputObservable u v A *
        (∑ γ, ∑ α, c α γ • twoSiteThreeBlockOpen S eL eR j₀ j₂ α γ) := by
      simp only [Matrix.mul_sum, Matrix.mul_smul]

/-- The three-block coefficient with arbitrary matrices at both virtual ends.
Its row and column spaces are the same as for `twoSiteThreeBlockOpen`.
Source context: arXiv:1703.09188, lines 603--622. -/
noncomputable def twoSiteThreeBlockTrace
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (_S : TwoSiteStandardFormData W u v)
    (P Q : Matrix (Fin D) (Fin D) ℂ)
    (eL eR : Fin d) (j₀ j₂ : Fin (d * d)) :
    Matrix ((Fin d × Fin d) × (Fin d × Fin d)) (Fin d × Fin d) ℂ :=
  fun x j₁ =>
    Matrix.trace (P *
      evalWord W
        [finProdFinEquiv (eL,x.1.1), finProdFinEquiv (x.1.2,x.2.1),
          finProdFinEquiv (x.2.2,eR)]
        [j₀,finProdFinEquiv j₁,j₂] * Q)

private theorem twoSiteThreeBlockTrace_eq_weighted
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v)
    (P Q : Matrix (Fin D) (Fin D) ℂ)
    (eL eR : Fin d) (j₀ j₂ : Fin (d * d)) :
    twoSiteThreeBlockTrace S P Q eL eR j₀ j₂ =
      ∑ γ, ∑ α, (Q * P) γ α • twoSiteThreeBlockOpen S eL eR j₀ j₂ α γ := by
  ext x j₁
  simp only [twoSiteThreeBlockTrace]
  rw [Matrix.trace_mul_cycle]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    twoSiteThreeBlockOpen, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

/-- Arbitrary virtual prefix and suffix matrices can be contracted after the
three-block operator identity without changing its support on the two
neighboring output links. This is a consequence of the open identity, not a
replacement for it. Source context: arXiv:1703.09188, lines 603--622. -/
theorem twoSite_threeBlock_trace_intertwiner_with_endpoints
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v)
    (P Q : Matrix (Fin D) (Fin D) ℂ)
    (eL eR : Fin d) (j₀ j₂ : Fin (d * d))
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    twoSiteThreeBlockTrace S P Q eL eR j₀ j₂ * A =
      twoLinkOutputObservable u v A *
        twoSiteThreeBlockTrace S P Q eL eR j₀ j₂ := by
  rw [twoSiteThreeBlockTrace_eq_weighted]
  exact twoSite_threeBlock_weighted_intertwiner S eL eR j₀ j₂
    (fun α γ => (Q * P) γ α) A

/-- The three-block coefficient after arbitrary complete-block prefix and
suffix words have been attached and the virtual trace taken. The prefix and
suffix words remain explicit. Source context: arXiv:1703.09188, lines
603--622. -/
noncomputable def twoSiteBufferedTrace
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (_S : TwoSiteStandardFormData W u v)
    (preI preJ sufI sufJ : List (Fin (d * d)))
    (eL eR : Fin d) (j₀ j₂ : Fin (d * d)) :
    Matrix ((Fin d × Fin d) × (Fin d × Fin d)) (Fin d × Fin d) ℂ :=
  fun x j₁ =>
    Matrix.trace (evalWord W
      (preI ++ ([finProdFinEquiv (eL,x.1.1),
        finProdFinEquiv (x.1.2,x.2.1), finProdFinEquiv (x.2.2,eR)] ++ sufI))
      (preJ ++ ([j₀,finProdFinEquiv j₁,j₂] ++ sufJ)))

private theorem twoSiteBufferedTrace_eq
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v)
    (preI preJ sufI sufJ : List (Fin (d * d)))
    (hpre : preI.length = preJ.length)
    (eL eR : Fin d) (j₀ j₂ : Fin (d * d)) :
    twoSiteBufferedTrace S preI preJ sufI sufJ eL eR j₀ j₂ =
      twoSiteThreeBlockTrace S
        (evalWord W preI preJ) (evalWord W sufI sufJ) eL eR j₀ j₂ := by
  ext x j₁
  simp only [twoSiteBufferedTrace, twoSiteThreeBlockTrace]
  rw [evalWord_append W preI preJ _ _ hpre]
  rw [evalWord_append W
    [finProdFinEquiv (eL,x.1.1), finProdFinEquiv (x.1.2,x.2.1),
      finProdFinEquiv (x.2.2,eR)]
    [j₀,finProdFinEquiv j₁,j₂] sufI sufJ (by simp)]
  rw [Matrix.mul_assoc]

/-- The same local output observable intertwines the three-block word even
after arbitrary complete-block words are attached on both sides. Physical
residual sites enter through the more general virtual-endpoint identity.
Source context: arXiv:1703.09188, lines 603--622. -/
theorem twoSite_threeBlock_buffered_intertwiner
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v)
    (preI preJ sufI sufJ : List (Fin (d * d)))
    (hpre : preI.length = preJ.length)
    (eL eR : Fin d) (j₀ j₂ : Fin (d * d))
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    twoSiteBufferedTrace S preI preJ sufI sufJ eL eR j₀ j₂ * A =
      twoLinkOutputObservable u v A *
        twoSiteBufferedTrace S preI preJ sufI sufJ eL eR j₀ j₂ := by
  rw [twoSiteBufferedTrace_eq S preI preJ sufI sufJ hpre]
  exact twoSite_threeBlock_trace_intertwiner_with_endpoints S _ _ eL eR j₀ j₂ A


end MPOTensor
