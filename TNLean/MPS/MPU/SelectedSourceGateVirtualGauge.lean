/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SelectedSourceFactorVirtualGauge

/-!
# Selected source gates under a virtual unitary gauge

The four selected source-factor identities imply the source $u$ relation and
a contracted source $v$ relation. The first gate has output rank coordinates
in the order $\ell\times r$; the second gate has input rank coordinates in the order
$r\times\ell$. The virtual unitary cancels at the contracted virtual leg.
Writing $e_r:r[U]\simeq r[V]$ and $e_\ell:\ell[U]\simeq\ell[V]$ for the
rank identifications, the four factor identities, with these identifications
understood, are
$X_1(V)=(I_d\otimes(z^\dagger)^T)X_1(U)W_1$,
$Y_1(V)=W_1^\dagger Y_1(U)(z^T\otimes I_d)$,
$X_2(V)=(z\otimes I_d)X_2(U)W_2$, and
$Y_2(V)=W_2^\dagger Y_2(U)(I_d\otimes z^\dagger)$.

## References

* CPSV17, arXiv:1703.09188, Theorem `FundamentalMPU` and equations
  `SFuu` and `SFvv` (lines 624–648).
* FBC25, arXiv:2502.20257, equation `eq:uv` (lines 704–760).
-/
open scoped Matrix Kronecker BigOperators
open Matrix

namespace MPOTensor

private def rawU {d D a b : ℕ}
    (Y₁ : Matrix (Fin a) (Fin D × Fin d) ℂ)
    (Y₂ : Matrix (Fin b) (Fin d × Fin D) ℂ) :
    Matrix (Fin b × Fin a) (Fin d × Fin d) ℂ :=
  fun (l, r) (p, q) ↦ ∑ β : Fin D, Y₂ l (p, β) * Y₁ r (β, q)

private theorem source_u_left_rank_gauge
    {d D a b : ℕ}
    (Y₁ : Matrix (Fin a) (Fin D × Fin d) ℂ)
    (Y₂ : Matrix (Fin b) (Fin d × Fin D) ℂ)
    (x : Matrix (Fin b) (Fin b) ℂ)
    (y : Matrix (Fin a) (Fin a) ℂ) :
    rawU (y * Y₁) (x * Y₂) = (x ⊗ₖ y) * rawU Y₁ Y₂ := by
  ext ⟨l, r⟩ ⟨p, q⟩
  simp only [rawU, Matrix.mul_apply, Matrix.kronecker_apply,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  simp only [mul_assoc, mul_left_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext r'; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]

private def rawV {d D a b : ℕ}
    (X₁ : Matrix (Fin d × Fin D) (Fin a) ℂ)
    (X₂ : Matrix (Fin D × Fin d) (Fin b) ℂ) :
    Matrix (Fin d × Fin d) (Fin a × Fin b) ℂ :=
  fun (p, q) (r, l) ↦ ∑ α : Fin D, X₁ (p, α) r * X₂ (α, q) l

private theorem source_v_right_rank_gauge
    {d D a b : ℕ}
    (X₁ : Matrix (Fin d × Fin D) (Fin a) ℂ)
    (X₂ : Matrix (Fin D × Fin d) (Fin b) ℂ)
    (w₁ : Matrix (Fin a) (Fin a) ℂ)
    (w₂ : Matrix (Fin b) (Fin b) ℂ) :
    rawV (X₁ * w₁) (X₂ * w₂) = rawV X₁ X₂ * (w₁ ⊗ₖ w₂) := by
  ext ⟨p, q⟩ ⟨r, l⟩
  simp only [rawV, Matrix.mul_apply, Matrix.kronecker_apply,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  simp only [mul_assoc, mul_left_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext r'; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]

private theorem rawU_reindex
    {d D a b c e : ℕ} (er : Fin a ≃ Fin c) (el : Fin b ≃ Fin e)
    (Y₁ : Matrix (Fin a) (Fin D × Fin d) ℂ)
    (Y₂ : Matrix (Fin b) (Fin d × Fin D) ℂ) :
    rawU (Matrix.reindex er (Equiv.refl _) Y₁)
      (Matrix.reindex el (Equiv.refl _) Y₂) =
      Matrix.reindex (Equiv.prodCongr el er) (Equiv.refl _) (rawU Y₁ Y₂) := by
  rfl

private theorem rawV_reindex
    {d D a b c e : ℕ} (er : Fin a ≃ Fin c) (el : Fin b ≃ Fin e)
    (X₁ : Matrix (Fin d × Fin D) (Fin a) ℂ)
    (X₂ : Matrix (Fin D × Fin d) (Fin b) ℂ) :
    rawV (Matrix.reindex (Equiv.refl _) er X₁)
      (Matrix.reindex (Equiv.refl _) el X₂) =
      Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er el) (rawV X₁ X₂) := by
  rfl

private theorem rawV_virtual_cancel
    {d D a b : ℕ} (z : Matrix.unitaryGroup (Fin D) ℂ)
    (X₁ : Matrix (Fin d × Fin D) (Fin a) ℂ)
    (X₂ : Matrix (Fin D × Fin d) (Fin b) ℂ) :
    rawV
      (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
        (star (z : Matrix (Fin D) (Fin D) ℂ)).transpose) * X₁)
      (((z : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ
        (1 : Matrix (Fin d) (Fin d) ℂ)) * X₂) = rawV X₁ X₂ := by
  ext ⟨p, q⟩ ⟨r, l⟩
  let A : Matrix (Fin a) (Fin D) ℂ := fun r β => X₁ (p, β) r
  let B : Matrix (Fin D) (Fin b) ℂ := fun β l => X₂ (β, q) l
  have hmain : ((A * (z : Matrix (Fin D) (Fin D) ℂ)ᴴ) *
      ((z : Matrix (Fin D) (Fin D) ℂ) * B)) r l = (A * B) r l := by
    have hz : (z : Matrix (Fin D) (Fin D) ℂ)ᴴ *
        (z : Matrix (Fin D) (Fin D) ℂ) = 1 := z.2.1
    calc
      _ = (A * ((z : Matrix (Fin D) (Fin D) ℂ)ᴴ *
          (z : Matrix (Fin D) (Fin D) ℂ)) * B) r l := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hz]; simp
  calc
    _ = ((A * (z : Matrix (Fin D) (Fin D) ℂ)ᴴ) *
        ((z : Matrix (Fin D) (Fin D) ℂ) * B)) r l := by
          simp only [rawV, Matrix.mul_apply, Matrix.kronecker_apply,
            Matrix.one_apply, Matrix.transpose_apply, Fintype.sum_prod_type]
          simp only [Matrix.conjTranspose_apply, A, B]
          simp [star_apply, RCLike.star_def, ite_mul, mul_ite, mul_comm]
    _ = (A * B) r l := hmain
    _ = _ := by change (∑ α, X₁ (p, α) r * X₂ (α, q) l) = _; rfl

private theorem rawU_virtual_cancel
    {d D a b : ℕ} (z : Matrix.unitaryGroup (Fin D) ℂ)
    (Y₁ : Matrix (Fin a) (Fin D × Fin d) ℂ)
    (Y₂ : Matrix (Fin b) (Fin d × Fin D) ℂ) :
    rawU
      (Y₁ * ((z : Matrix (Fin D) (Fin D) ℂ).transpose ⊗ₖ
        (1 : Matrix (Fin d) (Fin d) ℂ)))
      (Y₂ * ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
        star (z : Matrix (Fin D) (Fin D) ℂ))) = rawU Y₁ Y₂ := by
  ext ⟨l, r⟩ ⟨p, q⟩
  let A : Matrix (Fin b) (Fin D) ℂ := fun l β => Y₂ l (p, β)
  let B : Matrix (Fin D) (Fin a) ℂ := fun β r => Y₁ r (β, q)
  have hmain : ((A * (z : Matrix (Fin D) (Fin D) ℂ)ᴴ) *
      ((z : Matrix (Fin D) (Fin D) ℂ) * B)) l r = (A * B) l r := by
    have hz : (z : Matrix (Fin D) (Fin D) ℂ)ᴴ *
        (z : Matrix (Fin D) (Fin D) ℂ) = 1 := z.2.1
    calc
      _ = (A * ((z : Matrix (Fin D) (Fin D) ℂ)ᴴ *
          (z : Matrix (Fin D) (Fin D) ℂ)) * B) l r := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hz]; simp
  calc
    _ = ((A * (z : Matrix (Fin D) (Fin D) ℂ)ᴴ) *
        ((z : Matrix (Fin D) (Fin D) ℂ) * B)) l r := by
          simp only [rawU, Matrix.mul_apply, Matrix.kronecker_apply,
            Matrix.one_apply, Matrix.transpose_apply, Fintype.sum_prod_type]
          simp only [Matrix.conjTranspose_apply, A, B]
          simp [star_apply, RCLike.star_def, ite_mul, mul_ite, mul_comm]
    _ = (A * B) l r := hmain
    _ = _ := by change (∑ β, Y₂ l (p, β) * Y₁ r (β, q)) = _; rfl

private theorem rawU_selected_factor_gauge
    {d D a b c e : ℕ}
    (z : Matrix.unitaryGroup (Fin D) ℂ)
    (er : Fin a ≃ Fin c) (el : Fin b ≃ Fin e)
    (Y₁ : Matrix (Fin a) (Fin D × Fin d) ℂ)
    (Y₂ : Matrix (Fin b) (Fin d × Fin D) ℂ)
    (TY₁ : Matrix (Fin c) (Fin D × Fin d) ℂ)
    (TY₂ : Matrix (Fin e) (Fin d × Fin D) ℂ)
    (W₁ : Matrix (Fin c) (Fin c) ℂ)
    (W₂ : Matrix (Fin e) (Fin e) ℂ)
    (hY₁ : TY₁ = star W₁ *
      Matrix.reindex er (Equiv.refl _)
        (Y₁ * ((z : Matrix (Fin D) (Fin D) ℂ).transpose ⊗ₖ
          (1 : Matrix (Fin d) (Fin d) ℂ))))
    (hY₂ : TY₂ = star W₂ *
      Matrix.reindex el (Equiv.refl _)
        (Y₂ * ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
          star (z : Matrix (Fin D) (Fin D) ℂ)))) :
    rawU TY₁ TY₂ = (star W₂ ⊗ₖ star W₁) *
      Matrix.reindex (Equiv.prodCongr el er) (Equiv.refl _) (rawU Y₁ Y₂) := by
  rw [hY₁, hY₂, source_u_left_rank_gauge]
  rw [rawU_reindex, rawU_virtual_cancel]

private theorem rawV_selected_factor_gauge
    {d D a b c e : ℕ}
    (z : Matrix.unitaryGroup (Fin D) ℂ)
    (er : Fin a ≃ Fin c) (el : Fin b ≃ Fin e)
    (X₁ : Matrix (Fin d × Fin D) (Fin a) ℂ)
    (X₂ : Matrix (Fin D × Fin d) (Fin b) ℂ)
    (TX₁ : Matrix (Fin d × Fin D) (Fin c) ℂ)
    (TX₂ : Matrix (Fin D × Fin d) (Fin e) ℂ)
    (W₁ : Matrix (Fin c) (Fin c) ℂ)
    (W₂ : Matrix (Fin e) (Fin e) ℂ)
    (hX₁ : TX₁ =
      Matrix.reindex (Equiv.refl _) er
        (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
          (star (z : Matrix (Fin D) (Fin D) ℂ)).transpose) * X₁) * W₁)
    (hX₂ : TX₂ =
      Matrix.reindex (Equiv.refl _) el
        (((z : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ
          (1 : Matrix (Fin d) (Fin d) ℂ)) * X₂) * W₂) :
    rawV TX₁ TX₂ =
      Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er el) (rawV X₁ X₂) *
        (W₁ ⊗ₖ W₂) := by
  rw [hX₁, hX₂, source_v_right_rank_gauge]
  rw [rawV_reindex, rawV_virtual_cancel]

private theorem raw_selected_factor_gate_relations
    {d D a b c e : ℕ}
    (z : Matrix.unitaryGroup (Fin D) ℂ)
    (er : Fin a ≃ Fin c) (el : Fin b ≃ Fin e)
    (X₁ : Matrix (Fin d × Fin D) (Fin a) ℂ)
    (Y₁ : Matrix (Fin a) (Fin D × Fin d) ℂ)
    (X₂ : Matrix (Fin D × Fin d) (Fin b) ℂ)
    (Y₂ : Matrix (Fin b) (Fin d × Fin D) ℂ)
    (TX₁ : Matrix (Fin d × Fin D) (Fin c) ℂ)
    (TY₁ : Matrix (Fin c) (Fin D × Fin d) ℂ)
    (TX₂ : Matrix (Fin D × Fin d) (Fin e) ℂ)
    (TY₂ : Matrix (Fin e) (Fin d × Fin D) ℂ)
    (W₁ : Matrix.unitaryGroup (Fin c) ℂ)
    (W₂ : Matrix.unitaryGroup (Fin e) ℂ)
    (hX₁ : TX₁ = Matrix.reindex (Equiv.refl _) er
      (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
        (star (z : Matrix (Fin D) (Fin D) ℂ)).transpose) * X₁) *
          (W₁ : Matrix (Fin c) (Fin c) ℂ))
    (hY₁ : TY₁ = star (W₁ : Matrix (Fin c) (Fin c) ℂ) *
      Matrix.reindex er (Equiv.refl _)
        (Y₁ * ((z : Matrix (Fin D) (Fin D) ℂ).transpose ⊗ₖ
          (1 : Matrix (Fin d) (Fin d) ℂ))))
    (hX₂ : TX₂ = Matrix.reindex (Equiv.refl _) el
      (((z : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ
        (1 : Matrix (Fin d) (Fin d) ℂ)) * X₂) *
          (W₂ : Matrix (Fin e) (Fin e) ℂ))
    (hY₂ : TY₂ = star (W₂ : Matrix (Fin e) (Fin e) ℂ) *
      Matrix.reindex el (Equiv.refl _)
        (Y₂ * ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
          star (z : Matrix (Fin D) (Fin D) ℂ)))) :
    ∃ (x : Matrix.unitaryGroup (Fin e) ℂ)
      (y : Matrix.unitaryGroup (Fin c) ℂ),
      rawU TY₁ TY₂ = ((x : Matrix (Fin e) (Fin e) ℂ) ⊗ₖ
          (y : Matrix (Fin c) (Fin c) ℂ)) *
        Matrix.reindex (Equiv.prodCongr el er) (Equiv.refl _) (rawU Y₁ Y₂) ∧
      rawV TX₁ TX₂ =
        Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er el) (rawV X₁ X₂) *
          (star (y : Matrix (Fin c) (Fin c) ℂ) ⊗ₖ
            star (x : Matrix (Fin e) (Fin e) ℂ)) := by
  refine ⟨W₂⁻¹, W₁⁻¹, ?_, ?_⟩
  · simpa only [Matrix.UnitaryGroup.inv_val] using
      rawU_selected_factor_gauge z er el Y₁ Y₂ TY₁ TY₂ W₁ W₂ hY₁ hY₂
  · simpa only [Matrix.UnitaryGroup.inv_val, star_star] using
      rawV_selected_factor_gauge z er el X₁ X₂ TX₁ TX₂ W₁ W₂ hX₁ hX₂

private theorem supplied_source_factor_gate_relations
    {d D : ℕ} {U V : MPOTensor d D}
    {ρU ρV : Matrix (Fin D) (Fin D) ℂ}
    (S : SourceFactors U ρU) (T : SourceFactors V ρV)
    (z : Matrix.unitaryGroup (Fin D) ℂ)
    (er : Fin r[U] ≃ Fin r[V]) (el : Fin ℓ[U] ≃ Fin ℓ[V])
    (W₁ : Matrix.unitaryGroup (Fin r[V]) ℂ)
    (W₂ : Matrix.unitaryGroup (Fin ℓ[V]) ℂ)
    (hX₁ : T.X₁ = Matrix.reindex (Equiv.refl _) er
      (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
        (star (z : Matrix (Fin D) (Fin D) ℂ)).transpose) * S.X₁) *
          (W₁ : Matrix (Fin r[V]) (Fin r[V]) ℂ))
    (hY₁ : T.Y₁ = star (W₁ : Matrix (Fin r[V]) (Fin r[V]) ℂ) *
      Matrix.reindex er (Equiv.refl _)
        (S.Y₁ * ((z : Matrix (Fin D) (Fin D) ℂ).transpose ⊗ₖ
          (1 : Matrix (Fin d) (Fin d) ℂ))))
    (hX₂ : T.X₂ = Matrix.reindex (Equiv.refl _) el
      (((z : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ
        (1 : Matrix (Fin d) (Fin d) ℂ)) * S.X₂) *
          (W₂ : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ))
    (hY₂ : T.Y₂ = star (W₂ : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) *
      Matrix.reindex el (Equiv.refl _)
        (S.Y₂ * ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
          star (z : Matrix (Fin D) (Fin D) ℂ)))) :
    ∃ (x : Matrix.unitaryGroup (Fin ℓ[V]) ℂ)
      (y : Matrix.unitaryGroup (Fin r[V]) ℂ),
      SourceFactors.sourceU V T = ((x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) ⊗ₖ
          (y : Matrix (Fin r[V]) (Fin r[V]) ℂ)) *
        Matrix.reindex (Equiv.prodCongr el er) (Equiv.refl _)
          (SourceFactors.sourceU U S) ∧
      SourceFactors.sourceV V T =
        Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er el)
          (SourceFactors.sourceV U S) *
          (star (y : Matrix (Fin r[V]) (Fin r[V]) ℂ) ⊗ₖ
            star (x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ)) := by
  exact raw_selected_factor_gate_relations z er el S.X₁ S.Y₁ S.X₂ S.Y₂
    T.X₁ T.Y₁ T.X₂ T.Y₂ W₁ W₂ hX₁ hY₁ hX₂ hY₂

/-- For a supplied virtual unitary conjugation, the selected literal source
gates satisfy the $u$ relation and the contraction of the two $v$ half-factor
relations. If $e_r:r[U]\simeq r[V]$
and $e_\ell:\ell[U]\simeq\ell[V]$ identify the two source ranks, then
\[
  u_V=(x\otimes y)\,\operatorname{reindex}_{e_\ell\times e_r}(u_U),\qquad
  v_V=\operatorname{reindex}_{e_r\times e_\ell}(v_U)
      (y^\dagger\otimes x^\dagger).
\]
Here $x$ acts on the left rank and $y$ on the right rank; the proof takes
$x=W_2^\dagger$ and $y=W_1^\dagger$ from the selected-factor comparison.

The first equation is CPSV17, arXiv:1703.09188, Theorem `FundamentalMPU`,
equation `SFuu` (lines 624–648). The source's `SFvv` diagrams state the two
open half-factor relations involving $z$; the second displayed equation here
follows by contracting those relations. It asserts neither the converse nor
equality of the original odd-length periodic families. -/
theorem IsMPUCanonicalFormII.exists_selected_source_gate_unitary_gauges
    {d D : ℕ} {U : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) (hSimpleU : IsMPUSimple U)
    (z : Matrix.unitaryGroup (Fin D) ℂ)
    (hV : IsMPUCanonicalFormII
      (virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U
        (star (z : Matrix (Fin D) (Fin D) ℂ))))
    (hSimpleV : IsMPUSimple
      (virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U
        (star (z : Matrix (Fin D) (Fin D) ℂ)))) :
    let V := virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U
      (star (z : Matrix (Fin D) (Fin D) ℂ))
    let er : Fin r[U] ≃ Fin r[V] :=
      (finCongr (source_rank_virtual_unitary_sandwich U z).1).symm
    let el : Fin ℓ[U] ≃ Fin ℓ[V] :=
      (finCongr (source_rank_virtual_unitary_sandwich U z).2).symm
    ∃ (x : Matrix.unitaryGroup (Fin ℓ[V]) ℂ)
      (y : Matrix.unitaryGroup (Fin r[V]) ℂ),
      sourceU V hV.ρ hV.ρ_posDef =
        ((x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) ⊗ₖ
          (y : Matrix (Fin r[V]) (Fin r[V]) ℂ)) *
          Matrix.reindex (Equiv.prodCongr el er) (Equiv.refl _)
            (sourceU U hU.ρ hU.ρ_posDef) ∧
      sourceV V hV.ρ hV.ρ_posDef =
        Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er el)
          (sourceV U hU.ρ hU.ρ_posDef) *
          (star (y : Matrix (Fin r[V]) (Fin r[V]) ℂ) ⊗ₖ
            star (x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ)) := by
  let V := virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U
    (star (z : Matrix (Fin D) (Fin D) ℂ))
  let er : Fin r[U] ≃ Fin r[V] :=
    (finCongr (source_rank_virtual_unitary_sandwich U z).1).symm
  let el : Fin ℓ[U] ≃ Fin ℓ[V] :=
    (finCongr (source_rank_virtual_unitary_sandwich U z).2).symm
  let S := sourceFactors U hU.ρ hU.ρ_posDef
  let T := sourceFactors V hV.ρ hV.ρ_posDef
  obtain ⟨W₁, W₂, hX₁, hY₁, hX₂, hY₂⟩ :=
    hU.exists_selected_source_factor_unitary_gauges hSimpleU z hV hSimpleV
  simpa only [sourceFactors_sourceU, sourceFactors_sourceV, S, T, V, er, el] using
    supplied_source_factor_gate_relations S T z er el W₁ W₂
      hX₁ hY₁ hX₂ hY₂


end MPOTensor
