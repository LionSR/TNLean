/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.ZMod.Defs
import TNLean.MPS.Examples.GHZQudit
import TNLean.MPS.MPU.GroupCocycleMPO
import TNLean.MPS.Symmetry.GInjective

/-!
# GHZ: the `G`-injective fixed-point tensor

**Source.** Cirac, Pérez-García, Schuch, Verstraete 2021 (arXiv:2011.12127), Section
"Symmetry breaking", paragraph "Virtual symmetries", `Papers/2011.12127/TN-Review-main.tex`
lines 1196–1206, equation `GinjMPS`: for a finite group `G` with left regular representation
`L_g`, the tensor
$A^{ij}=\frac1{|G|}\sum_{g}\sum_{\alpha,\beta}(L_g)_{\alpha i}(\bar L_g)_{\beta j}
\lvert\alpha)(\beta\rvert$, of physical dimension `|G|²` and bond dimension `|G|`, is a
`G`-injective matrix product state and a renormalization fixed point ("all nonzero eigenvalues
of the corresponding transfer matrix are equal to 1"); its physical symmetry is represented by
the regular representation; for `G = ℤ₂`, after a discrete Fourier transform on the physical
and virtual levels and a blocking of two sites, it is the GHZ tensor.

**Formalized here.** For every finite group `G`, with bonds labelled by an enumeration
`e : G ≃ Fin n`:
* the entries of the tensor, $A^{ij}_{\alpha\beta}=|G|^{-1}\,[\beta=\alpha i^{-1}j]$;
* its transfer map, $\mathbb E(X)_{\alpha\beta}=|G|^{-1}\sum_k X_{\alpha k,\beta k}$, which is
  idempotent, so every nonzero eigenvalue of the transfer map equals `1`;
* `G`-injectivity for the representation `L_g ⊗ \bar L_g` on the two virtual legs;
* on-site symmetry under the representation `L_g ⊗ \bar L_g` of `G` on the physical index,
  under which the tensor is invariant letter by letter;
* for `G = ℤ₂`: after the Fourier transform `H ⊗ H` on the physical index and conjugation of
  the bond by the Fourier matrix, the tensor is the two-site blocking of the GHZ tensor.

## Main definitions

* `MPSTensor.gInjEntry`: the entries of equation `GinjMPS` on the group.
* `MPSTensor.gInjTensor`: the tensor of equation `GinjMPS`.
* `MPSTensor.gInjVirtualShift`, `MPSTensor.gInjPhysShift`: the left regular action of `G` on
  a bond label and on a physical label `(i, j)`.

## Main results

* `MPSTensor.gInjEntry_eq`: closed form of the entries.
* `MPSTensor.gInjTensor_transferMap_apply`, `MPSTensor.gInjTensor_isTransferIdempotent`,
  `MPSTensor.gInjTensor_eq_one_of_hasEigenvalue`: the renormalization fixed point.
* `MPSTensor.isGInjective_gInjTensor`: `G`-injectivity.
* `MPSTensor.gInjTensor_isOnSiteSymmetric`: invariance under the regular representation.
* `MPSTensor.z2FourierGInjTensor_eq_blockTensor_ghz`: the `ℤ₂` case is the blocked GHZ tensor.

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- Cirac, Pérez-García, Schuch,
  Verstraete, *Matrix product states and projected entangled pair states: Concepts,
  symmetries, theorems*
- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped Matrix BigOperators
open Matrix MPOTensor.GroupCocycle

namespace MPSTensor

variable {G : Type} [Group G] [Fintype G] [DecidableEq G] {n : ℕ}

/-! ### The tensor -/

variable (G) in
/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 1202–1205,
equation `GinjMPS`. The entry $A^{ij}_{\alpha\beta}=|G|^{-1}\sum_g (L_g)_{\alpha i}
(\bar L_g)_{\beta j}$ of the `G`-injective fixed-point tensor, with the left regular
representation `L_g |k⟩ = |gk⟩`. -/
noncomputable def gInjEntry (i j α β : G) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ g : G, leftShift g α i * star (leftShift g β j)

/-- The entries of equation `GinjMPS`: only `g = αi⁻¹` contributes, so
$A^{ij}_{\alpha\beta}=|G|^{-1}$ if `β = α i⁻¹ j` and `0` otherwise. -/
theorem gInjEntry_eq (i j α β : G) :
    gInjEntry G i j α β = if β = α * i⁻¹ * j then (Fintype.card G : ℂ)⁻¹ else 0 := by
  have hsum : ∑ g : G, leftShift g α i * star (leftShift g β j) =
      if β = α * i⁻¹ * j then 1 else 0 := by
    rw [Finset.sum_eq_single (α * i⁻¹)]
    · simp [leftShift_apply]
    · intro g _ hg
      have hα : α ≠ g * i := fun h => hg (by rw [h, mul_inv_cancel_right])
      simp [leftShift_apply, hα]
    · simp
  rw [gInjEntry, hsum]
  split_ifs <;> simp

/-- The physical label `(i, j) ∈ G × G` as an index of `Fin (n * n)`. -/
def gInjPhysEquiv (e : G ≃ Fin n) : G × G ≃ Fin (n * n) :=
  (e.prodCongr e).trans finProdFinEquiv

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 1200–1206,
equation `GinjMPS`. The `G`-injective fixed-point tensor, with physical dimension `|G|²` and
bond dimension `|G|`; the enumeration `e` labels the group elements by `Fin n`. -/
noncomputable def gInjTensor (e : G ≃ Fin n) : MPSTensor (n * n) n :=
  fun p => Matrix.of fun a b =>
    gInjEntry G ((gInjPhysEquiv e).symm p).1 ((gInjPhysEquiv e).symm p).2 (e.symm a) (e.symm b)

theorem gInjTensor_apply (e : G ≃ Fin n) (i j : G) (a b : Fin n) :
    gInjTensor e (gInjPhysEquiv e (i, j)) a b =
      if b = e (e.symm a * i⁻¹ * j) then (Fintype.card G : ℂ)⁻¹ else 0 := by
  simp only [gInjTensor, of_apply, Equiv.symm_apply_apply, gInjEntry_eq]
  congr 1
  exact propext ⟨fun h => by rw [← h, Equiv.apply_symm_apply], fun h => by simp [h]⟩

/-! ### Renormalization fixed point -/

/-- Project result: the transfer map of the `G`-injective tensor averages over right
translations, $\mathbb E(X)_{\alpha\beta}=|G|^{-1}\sum_k X_{\alpha k,\beta k}$. -/
theorem gInjTensor_transferMap_apply (e : G ≃ Fin n) (X : Matrix (Fin n) (Fin n) ℂ)
    (α β : G) :
    Kraus.transferMap (gInjTensor e) X (e α) (e β) =
      (Fintype.card G : ℂ)⁻¹ * ∑ k : G, X (e (α * k)) (e (β * k)) := by
  rw [Kraus.transferMap_apply, Matrix.sum_apply, ← (gInjPhysEquiv e).sum_comp,
    Fintype.sum_prod_type]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, gInjTensor_apply,
    Equiv.symm_apply_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    apply_ite star, star_zero, mul_ite, mul_zero]
  have hk : star ((Fintype.card G : ℂ)⁻¹) = (Fintype.card G : ℂ)⁻¹ := by simp
  simp only [hk, mul_assoc]
  have hshift : ∀ i : G, ∑ j : G, (Fintype.card G : ℂ)⁻¹ *
      (X (e (α * (i⁻¹ * j))) (e (β * (i⁻¹ * j))) * (Fintype.card G : ℂ)⁻¹) =
      ∑ k : G, (Fintype.card G : ℂ)⁻¹ * (X (e (α * k)) (e (β * k)) * (Fintype.card G : ℂ)⁻¹) :=
    fun i => Equiv.sum_comp (Equiv.mulLeft i⁻¹)
      (fun k => (Fintype.card G : ℂ)⁻¹ * (X (e (α * k)) (e (β * k)) * (Fintype.card G : ℂ)⁻¹))
  simp only [hshift, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum,
    ← Finset.sum_mul]
  have hG : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 1196–1197: the
`G`-injective tensor is a renormalization fixed point, in the transfer-map form
`𝔼 ∘ 𝔼 = 𝔼`. -/
theorem gInjTensor_isTransferIdempotent (e : G ≃ Fin n) :
    IsTransferIdempotent (gInjTensor e) := by
  refine LinearMap.ext fun X => Matrix.ext fun a b => ?_
  obtain ⟨α, rfl⟩ := e.surjective a
  obtain ⟨β, rfl⟩ := e.surjective b
  simp only [LinearMap.comp_apply, gInjTensor_transferMap_apply]
  have hshift : ∀ m : G, ∑ l : G, X (e (α * m * l)) (e (β * m * l)) =
      ∑ l : G, X (e (α * l)) (e (β * l)) := fun m => by
    simpa [mul_assoc] using Equiv.sum_comp (Equiv.mulLeft m) fun l => X (e (α * l)) (e (β * l))
  simp only [← Finset.mul_sum, hshift, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hG : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 1196–1197: every
nonzero eigenvalue of the transfer map of the `G`-injective tensor equals `1`. -/
theorem gInjTensor_eq_one_of_hasEigenvalue (e : G ≃ Fin n) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (Kraus.transferMap (gInjTensor e)) μ) (h0 : μ ≠ 0) :
    μ = 1 :=
  eq_one_of_hasEigenvalue_of_isTransferIdempotent (gInjTensor_isTransferIdempotent e) hμ h0

/-! ### `G`-injectivity -/

/-- The left regular action of `G` on the bond labels. -/
def gInjVirtualShift (e : G ≃ Fin n) : G →* Equiv.Perm (Fin n) :=
  e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G G)

omit [Fintype G] [DecidableEq G] in
theorem gInjVirtualShift_apply (e : G ≃ Fin n) (g : G) (a : Fin n) :
    gInjVirtualShift e g a = e (g * e.symm a) := rfl

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 1196–1202, with the
definition of arXiv:1001.3807, Definition `def:2d-Ug-inj`, `Papers/1001.3807/paper_v3.tex`
lines 1278–1296: the tensor of equation `GinjMPS` is `G`-injective for the representation
`L_g ⊗ \bar L_g` of `G` on its two virtual legs. -/
theorem isGInjective_gInjTensor (e : G ≃ Fin n) :
    TNLean.PEPS.IsGInjective (pairPermRep (gInjVirtualShift e)) (siteMap (gInjTensor e)) where
  invariant := siteMap_comp_pairPermRep _ _ fun g p a b => by
    obtain ⟨⟨i, j⟩, rfl⟩ := (gInjPhysEquiv e).surjective p
    rw [gInjTensor_apply, gInjTensor_apply]
    simp only [gInjVirtualShift_apply, Equiv.symm_apply_apply]
    refine if_congr ?_ rfl rfl
    rw [EmbeddingLike.apply_eq_iff_eq, mul_assoc, mul_assoc, mul_assoc, mul_right_inj,
      Equiv.symm_apply_eq]
  injOn_invariants x hx hTx := by
    have hinv : ∀ (g : G) (a b : Fin n), x (e (g * e.symm a), e (g * e.symm b)) = x (a, b) := by
      intro g a b
      have h := congrFun (hx g⁻¹) (a, b)
      simpa [pairPermRep_apply, gInjVirtualShift_apply] using h
    -- the component of `𝒫(A)x` at the physical label `(1, w)` is `x(e 1, e w)`
    have hcomp : ∀ w : G, x (e 1, e w) = 0 := by
      intro w
      have h := congrFun hTx (gInjPhysEquiv e (1, w))
      rw [siteMap_apply, Fintype.sum_prod_type] at h
      simp only [gInjTensor_apply, inv_one, mul_one, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte, Pi.zero_apply] at h
      have hterm : ∀ a : Fin n, x (a, e (e.symm a * w)) = x (e 1, e w) := by
        intro a
        have := hinv (e.symm a)⁻¹ a (e (e.symm a * w))
        simpa [← mul_assoc] using this.symm
      simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
      have hG : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      have hn : (n : ℂ) ≠ 0 := by
        rw [← Fintype.card_fin n, ← Fintype.card_congr e]
        exact hG
      simpa [hn, hG] using h
    funext ⟨a, b⟩
    have := hinv (e.symm a)⁻¹ a b
    simp only [inv_mul_cancel] at this
    rw [Pi.zero_apply, ← this, hcomp]

/-! ### Physical symmetry -/

/-- The left regular action `(i, j) ↦ (g i, g j)` of `G` on the physical labels. -/
def gInjPhysShift (e : G ≃ Fin n) : G →* Equiv.Perm (Fin (n * n)) :=
  (gInjPhysEquiv e).permCongrHom.toMonoidHom.comp (MulAction.toPermHom G (G × G))

/-- The regular representation `L_g ⊗ \bar L_g` of `G` on the physical index. -/
def gInjPhysRep (e : G ≃ Fin n) : G →* Matrix (Fin (n * n)) (Fin (n * n)) ℂ :=
  Matrix.permMatrixHom.comp (gInjPhysShift e)

/-- The tensor is invariant, letter by letter, under the regular representation on the
physical index. -/
theorem twistedTensor_gInjTensor (e : G ≃ Fin n) (g : G) :
    twistedTensor (gInjTensor e) (gInjPhysRep e) g = gInjTensor e := by
  funext p
  have htw : twistedTensor (gInjTensor e) (gInjPhysRep e) g p =
      gInjTensor e ((gInjPhysShift e g)⁻¹ p) := by
    simp [twistedTensor, gInjPhysRep, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, ite_smul]
  rw [htw]
  obtain ⟨⟨i, j⟩, rfl⟩ := (gInjPhysEquiv e).surjective p
  ext a b
  have hp : (gInjPhysShift e g)⁻¹ (gInjPhysEquiv e (i, j)) =
      gInjPhysEquiv e (g⁻¹ * i, g⁻¹ * j) := by
    simp only [gInjPhysShift, MonoidHom.coe_comp, Function.comp_apply]
    rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
    simp [Equiv.permCongrHom, Equiv.permCongr_apply, Prod.smul_mk]
  rw [hp, gInjTensor_apply, gInjTensor_apply]
  simp [mul_assoc]

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 1197–1198 ("The
physical symmetry action is represented by the regular representation"): the tensor of
equation `GinjMPS` is on-site symmetric under the representation `L_g ⊗ \bar L_g`. -/
theorem gInjTensor_isOnSiteSymmetric (e : G ≃ Fin n) :
    IsOnSiteSymmetric (gInjTensor e) (gInjPhysRep e) := by
  intro g N σ
  rw [twistedTensor_gInjTensor]

/-! ### The case `G = ℤ₂` -/

/-- The labelling of `ℤ₂` by `Fin 2`. -/
def z2Label : Multiplicative (ZMod 2) ≃ Fin 2 := Multiplicative.toAdd

theorem z2Label_apply (x : Multiplicative (ZMod 2)) : z2Label x = Multiplicative.toAdd x := rfl

theorem z2Label_symm_apply (a : Fin 2) : z2Label.symm a = Multiplicative.ofAdd (a : ZMod 2) :=
  rfl

/-- The unnormalized Fourier matrix of `ℤ₂`, `H_{ai} = (-1)^{ai}`. -/
def z2Fourier : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun a i => (-1 : ℂ) ^ (a.val * i.val)

theorem z2Fourier_apply (a i : Fin 2) : z2Fourier a i = (-1 : ℂ) ^ (a.val * i.val) := rfl

/-- The Fourier matrix of `ℤ₂` as a bond gauge; its inverse is `H / 2`. -/
noncomputable def z2FourierGL : GL (Fin 2) ℂ where
  val := z2Fourier
  inv := (1 / 2 : ℂ) • z2Fourier
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [z2Fourier, Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [z2Fourier, Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_z2FourierGL : (z2FourierGL : Matrix (Fin 2) (Fin 2) ℂ) = z2Fourier := rfl

theorem coe_z2FourierGL_inv :
    ((z2FourierGL⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = (1 / 2 : ℂ) • z2Fourier := rfl

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 1205–1206: the
`ℤ₂` tensor of equation `GinjMPS` after the normalized Fourier transform `H ⊗ H` on its
physical label `(i, j)`; the blocked label `(a, b)` is a pair of GHZ sites. -/
noncomputable def z2FourierGInjTensor : MPSTensor (Kraus.blockPhysDim 2 2) 2 := fun I =>
  ∑ i : Fin 2, ∑ j : Fin 2,
    ((1 / 2 : ℂ) * z2Fourier (Kraus.decodeBlock 2 2 I 0) i *
      z2Fourier (Kraus.decodeBlock 2 2 I 1) j) •
      gInjTensor z2Label (gInjPhysEquiv z2Label (z2Label.symm i, z2Label.symm j))

/-- For `ℤ₂` the tensor is `A^{ij} = X^{i+j}/2`: its entry at `(α, β)` is `1/2` if
`β = α + i + j` and `0` otherwise. -/
theorem gInjTensor_z2_apply (i j a b : Fin 2) :
    gInjTensor z2Label (gInjPhysEquiv z2Label (z2Label.symm i, z2Label.symm j)) a b =
      if b = a + i + j then (1 / 2 : ℂ) else 0 := by
  have hcard : (Fintype.card (Multiplicative (ZMod 2)) : ℂ)⁻¹ = 1 / 2 := by
    simp [Fintype.card_multiplicative]
  have hcond : (b = z2Label (z2Label.symm a * (z2Label.symm i)⁻¹ * z2Label.symm j)) ↔
      b = a + i + j := by
    revert a b i j
    decide
  rw [gInjTensor_apply, hcard]
  exact if_congr hcond rfl rfl

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 1205–1206 ("For the
case of `Z₂` symmetry, this can be written in the GHZ form by going to the dual basis (related
by the discrete Fourier transform) both on physical and virtual level and with a blocking of
two sites"): after the Fourier transform on the physical label and conjugation of the bond by
the Fourier matrix, the `ℤ₂` tensor of equation `GinjMPS` is the two-site blocking of the GHZ
tensor. -/
theorem z2FourierGInjTensor_eq_blockTensor_ghz :
    GaugeEquiv z2FourierGInjTensor (Kraus.blockTensor (ghzTensorD 2) 2) := by
  refine ⟨z2FourierGL, fun I => ?_⟩
  obtain ⟨w, rfl⟩ := (Kraus.decodeBlockEquiv 2 2).symm.surjective I
  have hL : Kraus.blockTensor (ghzTensorD 2) 2 ((Kraus.decodeBlockEquiv 2 2).symm w) =
      ghzTensorD 2 (w 0) * ghzTensorD 2 (w 1) := by
    simp [Kraus.blockTensor, Kraus.wordOfBlock, List.ofFn_succ, Kraus.evalWord_cons]
  have hR : z2FourierGInjTensor ((Kraus.decodeBlockEquiv 2 2).symm w) =
      ∑ i : Fin 2, ∑ j : Fin 2, ((1 / 2 : ℂ) * z2Fourier (w 0) i * z2Fourier (w 1) j) •
        gInjTensor z2Label (gInjPhysEquiv z2Label (z2Label.symm i, z2Label.symm j)) := by
    simp [z2FourierGInjTensor]
  rw [hL, hR, coe_z2FourierGL, coe_z2FourierGL_inv]
  generalize w 0 = a
  generalize w 1 = b
  ext α β
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Fin.sum_univ_two, gInjTensor_z2_apply, z2Fourier_apply, ghzTensorD_apply]
  fin_cases a <;> fin_cases b <;> fin_cases α <;> fin_cases β <;>
    simp (config := { decide := true }) <;> norm_num

end MPSTensor
