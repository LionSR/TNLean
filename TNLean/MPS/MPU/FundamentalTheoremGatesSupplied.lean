/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.FundamentalTheoremGates
import TNLean.Algebra.UnitaryKronecker

/-!
# The fundamental theorem of matrix product unitaries: gates, necessity

Two pairs of unitary gates `(u, v)` and `(u', v')` of the same shape that give the same two-layer
circuit on rings of two and of three two-site blocks are related by unitaries on the two internal
legs:
`u' = (x ⊗ y) u` and `v' = v (y† ⊗ x†)`.
No canonical form, simplicity or equality of bond dimensions is assumed. Consequently any two
tensors with supplied two-site standard forms that generate the same periodic operators have gates
related in this way.

The argument works directly with the circuits. On a ring of two blocks, the circuit identity
`V' U' = V U` gives `M = u u'†`, with the unshifted product `M ⊗ M` equal to a product of one
matrix on each shifted pair of internal legs. Evaluating at suitable configurations shows that
`M = X ⊗ Y` is a product; unitarity makes `X` and `Y` multiples of unitaries. The relation for `v`
then holds on every ring up to a scalar `ζ` with `ζ^N = 1`; rings of two and of three blocks force
`ζ = 1`.

The lengths count two-site blocks, so the periodic operators compared are those of the blocked
family, on rings of four and six original sites. This is the blocked reading of the Fundamental
Theorem recorded in `docs/paper-gaps/mpu_standard_form_parity_gap.tex`; equality on a ring of two
blocks alone does not determine the gates, since `(u, v)` and `(u, -v)` agree there.

Source: CPSV17, arXiv:1703.09188, Theorem `FundamentalMPU` (lines 640--652), "only if"
direction read for the gates of the standard forms (equations `SFuu` and the contraction of
`SFvv` over the bond).
-/

open scoped Matrix Kronecker BigOperators
open Matrix

namespace MPOTensor

variable {d D D' ℓ r : ℕ}

/-- The adjoint of the shifted layer of `v` times the shifted layer of `w` is the product of
`v† w` over the shifted pairs of internal legs. -/
private theorem twoSiteShiftedLayer_conjTranspose_mul_apply {N : ℕ} [NeZero N]
    (v w : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) (h h' : Fin N → Fin ℓ × Fin r) :
    ((twoSiteShiftedLayer (N := N) v)ᴴ * twoSiteShiftedLayer (N := N) w) h h' =
      ∏ x : Fin N, (vᴴ * w) ((h x).2, (h (x + 1)).1) ((h' x).2, (h' (x + 1)).1) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, twoSiteShiftedLayer, star_prod]
  rw [Fintype.prod_sum]
  refine (Fintype.sum_equiv (twoSiteShiftedPairEquiv (N := N) (ℓ := d) (r := d)) _ _ ?_)
  intro i
  rw [← Finset.prod_mul_distrib]
  rfl

/-- The shifted layer on a ring of `N` blocks, evaluated at configurations whose consecutive
pairs are constant, is the `N`-th power of one entry of the gate. -/
private theorem twoSiteShiftedLayer_apply_const {N : ℕ} [NeZero N]
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) (p : Fin d × Fin d) (q : Fin r × Fin ℓ) :
    twoSiteShiftedLayer (N := N) v (fun _ ↦ (p.2, p.1)) (fun _ ↦ (q.2, q.1)) = v p q ^ N := by
  simp [twoSiteShiftedLayer]

/-- The shifted layer on a ring of two blocks at mixed configurations is a product of two entries
of the gate. -/
private theorem twoSiteShiftedLayer_two_apply
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) (p p' : Fin d × Fin d)
    (q q' : Fin r × Fin ℓ) :
    twoSiteShiftedLayer (N := 2) v ![(p'.2, p.1), (p.2, p'.1)] ![(q'.2, q.1), (q.2, q'.1)] =
      v p q * v p' q' := by
  simp [twoSiteShiftedLayer, Fin.prod_univ_two]

/-- A gate is determined by its shifted layers on rings of two and of three blocks. -/
private theorem eq_of_twoSiteShiftedLayer_two_three_eq
    {v w : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ} (hw : w ≠ 0)
    (h2 : twoSiteShiftedLayer (N := 2) v = twoSiteShiftedLayer (N := 2) w)
    (h3 : twoSiteShiftedLayer (N := 3) v = twoSiteShiftedLayer (N := 3) w) : v = w := by
  obtain ⟨p₀, q₀, hpq⟩ : ∃ p q, w p q ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hw (Matrix.ext hall)
  have hsq : v p₀ q₀ ^ 2 = w p₀ q₀ ^ 2 := by
    have := congrFun (congrFun h2 (fun _ ↦ (p₀.2, p₀.1))) (fun _ ↦ (q₀.2, q₀.1))
    rwa [twoSiteShiftedLayer_apply_const, twoSiteShiftedLayer_apply_const] at this
  have hcube : v p₀ q₀ ^ 3 = w p₀ q₀ ^ 3 := by
    have := congrFun (congrFun h3 (fun _ ↦ (p₀.2, p₀.1))) (fun _ ↦ (q₀.2, q₀.1))
    rwa [twoSiteShiftedLayer_apply_const, twoSiteShiftedLayer_apply_const] at this
  have hpq₀ : v p₀ q₀ = w p₀ q₀ := by
    have hb2 : w p₀ q₀ ^ 2 ≠ 0 := pow_ne_zero 2 hpq
    refine mul_right_cancel₀ hb2 ?_
    linear_combination hcube - v p₀ q₀ * hsq
  ext p q
  have hmix := congrFun (congrFun h2 ![(p₀.2, p.1), (p.2, p₀.1)]) ![(q₀.2, q.1), (q.2, q₀.1)]
  rw [twoSiteShiftedLayer_two_apply, twoSiteShiftedLayer_two_apply, hpq₀] at hmix
  exact mul_right_cancel₀ hpq hmix

/-- If the product of `M` over the two unshifted pairs of a ring of two blocks is a product of
one matrix over the two shifted pairs, then `M` is a Kronecker product. -/
private theorem exists_kronecker_of_prod_two_eq {M : Matrix (Fin ℓ × Fin r) (Fin ℓ × Fin r) ℂ}
    {K : Matrix (Fin r × Fin ℓ) (Fin r × Fin ℓ) ℂ} (hM : M ≠ 0)
    (h : ∀ g g' : Fin 2 → Fin ℓ × Fin r, ∏ x : Fin 2, M (g x) (g' x) =
      ∏ x : Fin 2, K ((g x).2, (g (x + 1)).1) ((g' x).2, (g' (x + 1)).1)) :
    ∃ (X : Matrix (Fin ℓ) (Fin ℓ) ℂ) (Y : Matrix (Fin r) (Fin r) ℂ), M = X ⊗ₖ Y := by
  obtain ⟨⟨c, e⟩, ⟨c', e'⟩, hm⟩ : ∃ p q, M p q ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hM (Matrix.ext hall)
  refine ⟨fun a a' ↦ K (e, a) (e', a') / M (c, e) (c', e'), fun b b' ↦ K (b, c) (b', c'), ?_⟩
  ext ⟨a, b⟩ ⟨a', b'⟩
  have := h ![(a, b), (c, e)] ![(a', b'), (c', e')]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at this
  have h11 : (1 : Fin 2) + 1 = 0 := rfl
  simp only [zero_add, h11, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at this
  change M (a, b) (a', b') = K (e, a) (e', a') / M (c, e) (c', e') * K (b, c) (b', c')
  field_simp
  linear_combination this

/-- A matrix that is unitary between two nonempty coordinate spaces is nonzero. -/
private theorem ne_zero_of_isUnitaryBetween {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [Nonempty n] {A : Matrix m n ℂ}
    (hA : A.IsUnitaryBetween) : A ≠ 0 := by
  intro h0
  have h1 : Aᴴ * A = 1 := hA.1
  rw [h0, Matrix.mul_zero] at h1
  obtain ⟨j⟩ := ‹Nonempty n›
  have := congrFun (congrFun h1 j) j
  simp at this

/-- **Fundamental theorem, gates, necessity.** Two pairs of gates of the same shape, with `u`,
`u'` and `v` unitary, that give the same two-layer circuit on rings of two and of three two-site
blocks are related by unitaries `x, y` on the two internal legs: `u' = (x ⊗ y) u` and
`v' = v (y† ⊗ x†)`.

No canonical form, simplicity or equality of bond dimensions is involved. Rings of three blocks
are needed: on a ring of two blocks the gate pairs `(u, v)` and `(u, -v)` give the same circuit.

Source: CPSV17, arXiv:1703.09188, Theorem `FundamentalMPU` (lines 640--652), "only if"
direction for the gates (equation `SFuu` and the contraction of `SFvv` over the bond). -/
theorem exists_gate_gauges_of_twoSiteCircuit_eq [NeZero ℓ] [NeZero r]
    {u u' : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v v' : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (hu : u.IsUnitaryBetween) (hu' : u'.IsUnitaryBetween) (hv : v.IsUnitaryBetween)
    (h2 : twoSiteShiftedLayer (N := 2) v' * twoSiteUnshiftedLayer (N := 2) u' =
      twoSiteShiftedLayer (N := 2) v * twoSiteUnshiftedLayer (N := 2) u)
    (h3 : twoSiteShiftedLayer (N := 3) v' * twoSiteUnshiftedLayer (N := 3) u' =
      twoSiteShiftedLayer (N := 3) v * twoSiteUnshiftedLayer (N := 3) u) :
    ∃ (x : Matrix.unitaryGroup (Fin ℓ) ℂ) (y : Matrix.unitaryGroup (Fin r) ℂ),
      u' = ((x : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y : Matrix (Fin r) (Fin r) ℂ)) * u ∧
      v' = v * (star (y : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ star (x : Matrix (Fin ℓ) (Fin ℓ) ℂ)) := by
  classical
  -- `M = u u'†` is unitary and `u = M u'`.
  set M : Matrix (Fin ℓ × Fin r) (Fin ℓ × Fin r) ℂ := u * u'ᴴ with hMdef
  have hu'1 : u'ᴴ * u' = 1 := hu'.1
  have hu'2 : u' * u'ᴴ = 1 := hu'.2
  have huM : M * u' = u := by rw [hMdef, Matrix.mul_assoc, hu'1, Matrix.mul_one]
  have hMunit : M.IsUnitaryBetween := hu.mul _ _ hu'.conjTranspose
  -- On every ring, the shifted layer of `v'` is that of `v` followed by the sitewise `M`.
  have hshift : ∀ {N : ℕ} [NeZero N],
      twoSiteShiftedLayer (N := N) v' * twoSiteUnshiftedLayer (N := N) u' =
        twoSiteShiftedLayer (N := N) v * twoSiteUnshiftedLayer (N := N) u →
      twoSiteShiftedLayer (N := N) v' =
        twoSiteShiftedLayer (N := N) v * Matrix.tensorPower N M := by
    intro N _ hN
    have hU' := (twoSiteUnshiftedLayer_isUnitaryBetween (N := N) u' hu').2
    rw [← huM, twoSiteUnshiftedLayer_mul_left, ← Matrix.mul_assoc] at hN
    calc twoSiteShiftedLayer (N := N) v'
        = twoSiteShiftedLayer (N := N) v' * (twoSiteUnshiftedLayer (N := N) u' *
            (twoSiteUnshiftedLayer (N := N) u')ᴴ) := by rw [hU', Matrix.mul_one]
      _ = twoSiteShiftedLayer (N := N) v * Matrix.tensorPower N M := by
          rw [← Matrix.mul_assoc, hN, Matrix.mul_assoc, hU', Matrix.mul_one]
  -- On a ring of two blocks, `M ⊗ M` is a product over the shifted pairs, so `M = X ⊗ Y`.
  have hprod : ∀ g g' : Fin 2 → Fin ℓ × Fin r, ∏ x : Fin 2, M (g x) (g' x) =
      ∏ x : Fin 2, (vᴴ * v') ((g x).2, (g (x + 1)).1) ((g' x).2, (g' (x + 1)).1) := by
    intro g g'
    have hV := (twoSiteShiftedLayer_isUnitaryBetween (N := 2) v hv).1
    have := congrArg (fun A ↦ (twoSiteShiftedLayer (N := 2) v)ᴴ * A) (hshift h2)
    rw [← Matrix.mul_assoc, hV, Matrix.one_mul] at this
    have hc := congrFun (congrFun this g) g'
    rw [twoSiteShiftedLayer_conjTranspose_mul_apply] at hc
    simpa [Matrix.tensorPower_apply] using hc.symm
  have hMne : M ≠ 0 := ne_zero_of_isUnitaryBetween hMunit
  obtain ⟨X, Y, hXY⟩ := exists_kronecker_of_prod_two_eq hMne hprod
  -- Unitarity of `M† = X† ⊗ Y†` makes `X†` and `Y†` multiples of unitaries.
  have hMH : Xᴴ ⊗ₖ Yᴴ ∈ Matrix.unitaryGroup (Fin ℓ × Fin r) ℂ := by
    rw [← Matrix.conjTranspose_kronecker, ← hXY]
    exact (Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mp hMunit.conjTranspose
  obtain ⟨δ, hδ, hxU, hyU⟩ :=
    Matrix.exists_pos_real_rescaling_mem_unitaryGroup_of_kronecker_mem_unitaryGroup hMH
  set xm : Matrix (Fin ℓ) (Fin ℓ) ℂ := ((δ : ℂ)⁻¹) • Xᴴ with hxm
  set ym : Matrix (Fin r) (Fin r) ℂ := (δ : ℂ) • Yᴴ with hym
  have hδ0 : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ.ne'
  have hgauge : xm ⊗ₖ ym = Mᴴ := by
    rw [hXY, Matrix.conjTranspose_kronecker, hxm, hym, Matrix.smul_kronecker,
      Matrix.kronecker_smul, smul_smul, inv_mul_cancel₀ hδ0, one_smul]
  refine ⟨⟨xm, hxU⟩, ⟨ym, hyU⟩, ?_, ?_⟩
  · -- `u' = M† u`.
    change u' = (xm ⊗ₖ ym) * u
    rw [hgauge, hMdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc, hu.1, Matrix.mul_one]
  · -- `v'` and `v (y† ⊗ x†)` have the same shifted layers on rings of two and three blocks.
    change v' = v * (star ym ⊗ₖ star xm)
    have hlayer : ∀ {N : ℕ} [NeZero N],
        twoSiteShiftedLayer (N := N) v' * twoSiteUnshiftedLayer (N := N) u' =
          twoSiteShiftedLayer (N := N) v * twoSiteUnshiftedLayer (N := N) u →
        twoSiteShiftedLayer (N := N) v' =
          twoSiteShiftedLayer (N := N) (v * (star ym ⊗ₖ star xm)) := by
      intro N _ hN
      rw [hshift hN, Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
        twoSiteShiftedLayer_mul_kron, hgauge, Matrix.conjTranspose_conjTranspose]
    have hw : (v * (star ym ⊗ₖ star xm)).IsUnitaryBetween := by
      have hyx : (star ym ⊗ₖ star xm).IsUnitaryBetween :=
        (Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mpr
          (Matrix.kronecker_mem_unitary (Unitary.star_mem hyU) (Unitary.star_mem hxU))
      exact hv.mul _ _ hyx
    exact eq_of_twoSiteShiftedLayer_two_three_eq (ne_zero_of_isUnitaryBetween hw)
      (hlayer h2) (hlayer h3)

/-- **Fundamental theorem for supplied standard forms, necessity.** Two tensors with supplied
two-site standard forms, of arbitrary bond dimensions, that generate the same periodic operators
on every ring of at least two blocks have gates related by unitaries `x, y` on the internal legs.
Only the rings of two and of three blocks are used.

Source: CPSV17, arXiv:1703.09188, Theorem `FundamentalMPU` (lines 640--652), "only if"
direction for the gates; the lengths count two-site blocks, as in
`docs/paper-gaps/mpu_standard_form_parity_gap.tex`. -/
theorem TwoSiteStandardFormData.exists_gate_gauges_of_mpo_eq
    {W : MPOTensor (d * d) D} {W' : MPOTensor (d * d) D'}
    {u u' : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v v' : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (S' : TwoSiteStandardFormData W' u' v')
    (hEq : ∀ N : ℕ, 1 < N → mpo W N = mpo W' N) :
    ∃ (x : Matrix.unitaryGroup (Fin ℓ) ℂ) (y : Matrix.unitaryGroup (Fin r) ℂ),
      u' = ((x : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y : Matrix (Fin r) (Fin r) ℂ)) * u ∧
      v' = v * (star (y : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ star (x : Matrix (Fin ℓ) (Fin ℓ) ℂ)) := by
  have : NeZero ℓ := ⟨S.left_pos.ne'⟩
  have : NeZero r := ⟨S.right_pos.ne'⟩
  have hcirc : ∀ N : ℕ, 1 < N → ∀ _ : NeZero N,
      twoSiteShiftedLayer (N := N) v' * twoSiteUnshiftedLayer (N := N) u' =
        twoSiteShiftedLayer (N := N) v * twoSiteUnshiftedLayer (N := N) u := by
    intro N hN _
    rw [← TwoSiteStandardFormData.mpo_eq_shifted_mul_unshifted W u v S,
      ← TwoSiteStandardFormData.mpo_eq_shifted_mul_unshifted W' u' v' S', hEq N hN]
  exact exists_gate_gauges_of_twoSiteCircuit_eq S.u_unitary S'.u_unitary S.v_unitary
    (hcirc 2 (by decide) inferInstance) (hcirc 3 (by decide) inferInstance)

/-- **Fundamental theorem for supplied standard forms.** Two tensors with supplied two-site
standard forms, of arbitrary bond dimensions, generate the same periodic operators on every ring
of at least two blocks if and only if their gates are related by unitaries `x, y` on the internal
legs, `u' = (x ⊗ y) u` and `v' = v (y† ⊗ x†)`.

Source: CPSV17, arXiv:1703.09188, Theorem `FundamentalMPU` (lines 640--652), read for the gates
of the standard forms; the lengths count two-site blocks, as in
`docs/paper-gaps/mpu_standard_form_parity_gap.tex`. -/
theorem TwoSiteStandardFormData.mpo_eq_iff_exists_gate_gauges
    {W : MPOTensor (d * d) D} {W' : MPOTensor (d * d) D'}
    {u u' : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v v' : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (S' : TwoSiteStandardFormData W' u' v') :
    (∀ N : ℕ, 1 < N → mpo W N = mpo W' N) ↔
      ∃ (x : Matrix.unitaryGroup (Fin ℓ) ℂ) (y : Matrix.unitaryGroup (Fin r) ℂ),
        u' = ((x : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y : Matrix (Fin r) (Fin r) ℂ)) * u ∧
        v' = v * (star (y : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ
          star (x : Matrix (Fin ℓ) (Fin ℓ) ℂ)) := by
  refine ⟨S.exists_gate_gauges_of_mpo_eq S', ?_⟩
  rintro ⟨x, y, hu', hv'⟩ N hN
  have : NeZero N := ⟨by omega⟩
  have h := TwoSiteStandardFormData.mpo_eq_shifted_mul_unshifted (N := N) W u v S
  have h' := TwoSiteStandardFormData.mpo_eq_shifted_mul_unshifted (N := N) W' u' v' S'
  rw [hu', hv', twoSiteCircuit_eq_of_gate_gauges] at h'
  exact (Matrix.reindex _ _).injective (h.trans h'.symm)

end MPOTensor
