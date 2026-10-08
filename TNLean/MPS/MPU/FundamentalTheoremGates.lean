import TNLean.MPS.MPU.TwoSiteStandardFormCircuit

/-!
# The fundamental theorem of matrix product unitaries: gates, sufficiency

Gates related by unitaries on the two internal legs, `u' = (x ⊗ y) u` and
`v' = v (y† ⊗ x†)`, produce the same two-layer circuit, hence the same periodic operators on
rings of even length: in the circuit, the unitary placed on an internal leg by the unshifted
layer meets its adjoint placed on the same leg by the shifted layer.

Source: CPSV17, arXiv:1703.09188, Theorem `FundamentalMPU` (lines 624--648), "if" direction read
for the standard forms. Milestone M-A, Theorem A3 (first assertion).
-/

open scoped Matrix Kronecker BigOperators
open Matrix

namespace MPOTensor

variable {d D ℓ r N : ℕ}

/-- The sitewise product of one matrix on every site of a ring of `N` sites: the entry at the
configurations `a, b` is `∏ x, A (a x) (b x)`. -/
noncomputable def siteProduct (A : Matrix (Fin ℓ × Fin r) (Fin ℓ × Fin r) ℂ) :
    Matrix (Fin N → Fin ℓ × Fin r) (Fin N → Fin ℓ × Fin r) ℂ :=
  fun a b => ∏ x : Fin N, A (a x) (b x)

/-- The sitewise product of a product is the product of the sitewise products. -/
theorem siteProduct_mul (A B : Matrix (Fin ℓ × Fin r) (Fin ℓ × Fin r) ℂ) :
    siteProduct (N := N) (A * B) = siteProduct (N := N) A * siteProduct (N := N) B := by
  ext a c
  simp only [Matrix.mul_apply, siteProduct]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

/-- The sitewise product of the identity is the identity. -/
theorem siteProduct_one :
    siteProduct (N := N) (1 : Matrix (Fin ℓ × Fin r) (Fin ℓ × Fin r) ℂ) = 1 := by
  ext a b
  simp only [siteProduct, Matrix.one_apply]
  by_cases hab : a = b
  · subst b
    simp
  · obtain ⟨x, hx⟩ := Function.ne_iff.mp hab
    simp only [hab, ↓reduceIte]
    exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp [hx])

/-- The sitewise product of a conjugate transpose is the conjugate transpose of the sitewise
product. -/
theorem siteProduct_conjTranspose (A : Matrix (Fin ℓ × Fin r) (Fin ℓ × Fin r) ℂ) :
    siteProduct (N := N) Aᴴ = (siteProduct (N := N) A)ᴴ := by
  ext a b
  simp [siteProduct, Matrix.conjTranspose_apply, star_prod]

/-- The unshifted layer of `G * u` is the sitewise product of `G` times the unshifted layer of
`u`. -/
theorem twoSiteUnshiftedLayer_mul_left (G : Matrix (Fin ℓ × Fin r) (Fin ℓ × Fin r) ℂ)
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ) :
    twoSiteUnshiftedLayer (N := N) (G * u) =
      siteProduct (N := N) G * twoSiteUnshiftedLayer (N := N) u := by
  ext h j
  simp only [Matrix.mul_apply, siteProduct, twoSiteUnshiftedLayer]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

/-- The shifted layer of `v * (yᴴ ⊗ xᴴ)` is the shifted layer of `v` times the sitewise product
of `(x ⊗ y)ᴴ`: the shifted pair relabelling moves the `xᴴ` factor from site `x + 1` back to site
`x`, and a product over a cyclic shift of the sites is unchanged. -/
theorem twoSiteShiftedLayer_mul_kron [NeZero N]
    (x : Matrix (Fin ℓ) (Fin ℓ) ℂ) (y : Matrix (Fin r) (Fin r) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) :
    twoSiteShiftedLayer (N := N) (v * (yᴴ ⊗ₖ xᴴ)) =
      twoSiteShiftedLayer (N := N) v * siteProduct (N := N) (x ⊗ₖ y)ᴴ := by
  ext i h
  simp only [Matrix.mul_apply, twoSiteShiftedLayer, siteProduct]
  rw [Fintype.prod_sum]
  refine Fintype.sum_equiv (twoSiteShiftedPairEquiv (N := N) (ℓ := ℓ) (r := r)).symm _ _ ?_
  intro g
  simp only [twoSiteShiftedPairEquiv, Equiv.coe_fn_symm_mk, add_sub_cancel_right,
    Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply, star_mul', Prod.mk.eta,
    Finset.prod_mul_distrib]
  have hshift : ∏ z : Fin N, star (x (h (z + 1)).1 (g z).2) =
      ∏ z : Fin N, star (x (h z).1 (g (z - 1)).2) :=
    Fintype.prod_equiv (Equiv.addRight 1) _ _ (fun z => by simp)
  rw [hshift]
  ring

/-- Gates related by `(x ⊗ y)` and `(y† ⊗ x†)`, with `x, y` unitary, give the same two-layer
circuit. -/
theorem twoSiteCircuit_eq_of_gate_gauges [NeZero N]
    (x : Matrix.unitaryGroup (Fin ℓ) ℂ) (y : Matrix.unitaryGroup (Fin r) ℂ)
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) :
    twoSiteShiftedLayer (N := N)
        (v * (star (y : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ star (x : Matrix (Fin ℓ) (Fin ℓ) ℂ))) *
      twoSiteUnshiftedLayer (N := N)
        (((x : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y : Matrix (Fin r) (Fin r) ℂ)) * u) =
      twoSiteShiftedLayer (N := N) v * twoSiteUnshiftedLayer (N := N) u := by
  have hxy : ((x : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y : Matrix (Fin r) (Fin r) ℂ))ᴴ *
      ((x : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y : Matrix (Fin r) (Fin r) ℂ)) = 1 := by
    have hx : (x : Matrix (Fin ℓ) (Fin ℓ) ℂ)ᴴ * x = 1 := Matrix.mem_unitaryGroup_iff'.mp x.2
    have hy : (y : Matrix (Fin r) (Fin r) ℂ)ᴴ * y = 1 := Matrix.mem_unitaryGroup_iff'.mp y.2
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hx, hy,
      Matrix.one_kronecker_one]
  rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose, twoSiteShiftedLayer_mul_kron,
    twoSiteUnshiftedLayer_mul_left, Matrix.mul_assoc, ← Matrix.mul_assoc (siteProduct _),
    ← siteProduct_mul, hxy, siteProduct_one, Matrix.one_mul]

/-- **Fundamental theorem, gates, sufficiency.** Two tensors with two-site standard-form data
whose gates are related by `(x ⊗ y)` and `(y† ⊗ x†)` generate the same periodic operators at
every positive length (of the blocked ring, that is on rings of even length of the original one).

Source: CPSV17, arXiv:1703.09188, Theorem `FundamentalMPU`, "if" direction for the standard
forms; Milestone M-A, Theorem A3. -/
theorem TwoSiteStandardFormData.mpo_eq_of_gate_gauges [NeZero N]
    {W W' : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ} {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v)
    (x : Matrix.unitaryGroup (Fin ℓ) ℂ) (y : Matrix.unitaryGroup (Fin r) ℂ)
    (S' : TwoSiteStandardFormData W'
      (((x : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y : Matrix (Fin r) (Fin r) ℂ)) * u)
      (v * (star (y : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ star (x : Matrix (Fin ℓ) (Fin ℓ) ℂ)))) :
    mpo W N = mpo W' N := by
  have h := TwoSiteStandardFormData.mpo_eq_shifted_mul_unshifted (N := N) W u v S
  have h' := TwoSiteStandardFormData.mpo_eq_shifted_mul_unshifted (N := N) W' _ _ S'
  rw [twoSiteCircuit_eq_of_gate_gauges] at h'
  exact (Matrix.reindex _ _).injective (h.trans h'.symm)

end MPOTensor
