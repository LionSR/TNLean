/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.DomainWall

/-!
# Exchange of domain walls: the phase of a symmetry string over a pair of walls

Garre-Rubio and Schuch (arXiv:2405.00439, Section III.F, `Papers/2405.00439/MPU-DW.tex` lines
1427--1672) create domain walls with truncated strings of the symmetry and compare the two
orders of two strings: when the string on `[i₂, j₂]` passes over the pair of walls created by
the string on `[i₁, j₁] ⊂ [i₂, j₂]`, it acts on both walls, and the two orders differ by
`c_{AB} c_{BA} = ω` (`signphysop`, lines 1668--1672). A double exchange of domain walls gives
the same phase (`DWstat`, lines 1660--1663), and since `c_{AB}` can be fixed freely by
rescaling `e_{BA}` (lines 826--832 and 1664--1665), the phases can be chosen equal, `c_{AB} =
c_{BA} = s` with `s² = ω`; for `ω = -1` the exchange of two domain walls is a phase `± i`, the
semionic statistics of the source.

This file formalizes the tensor-level content of these statements:

* the local action of a group element on an open chain containing a pair of domain walls is the
  product of the two phases (`IsDomainWallAction.pair`), which is the phase acquired when a
  symmetry string passes over the pair of walls;
* the square of the exchange phase is one when the symmetry squares to the identity
  (`IsDomainWallAction.mul_sq_eq_one_of_mpo_mul_self_eq_one`, lines 835--839), using that two
  nonzero domain walls between normal blocks give a nonzero state `|ψ(A-B-A)⟩`
  (`exists_twoWallMPV_ne_zero`);
* rescaling a domain wall rescales its phases (`IsDomainWallAction.smul_source`,
  `IsDomainWallAction.smul_target`), so that for an involution the two phases can be made
  equal to any square root of their product (`IsDomainWallAction.exists_eq_of_mul_self`).

**Local fix (nondegenerate domain walls, blocked local action):** the results of this module,
`smul_source`, `smul_target`, `exists_eq_of_mul_self`, `pair` and
`mul_sq_eq_one_of_mpo_mul_self_eq_one`, are stated for
`IsDomainWallAction`, whose walls and phase are nonzero and whose local relation holds against
regions longer than a buffer; documented in `docs/paper-gaps/gs24_domain_wall_nondegenerate.tex`.

The truncated string operators `O^{[i,j]}` of `eq:DWophys`, with the endpoint tensors of
`eq:defEndT` built from left inverses, and the operator identity `signphysop` are formalized in
`TNLean/MPS/Symmetry/MPOSymmetry/DomainWallString.lean`.

## Main results

* `MPOTensor.exists_twoWallMPV_ne_zero`: a nonzero state with two domain walls.
* `MPOTensor.GroupFamily.BlockActionData.IsDomainWallAction.mul_sq_eq_one_of_mpo_mul_self_eq_one`:
  `(c_{AB} c_{BA})² = 1` from `U² = 1`.
* `MPOTensor.GroupFamily.BlockActionData.IsDomainWallAction.pair`: the phase `c c'` of a string
  over a pair of walls.
* `MPOTensor.GroupFamily.BlockActionData.IsDomainWallAction.smul_source`,
  `MPOTensor.GroupFamily.BlockActionData.IsDomainWallAction.smul_target`
* `MPOTensor.GroupFamily.BlockActionData.IsDomainWallAction.exists_eq_of_mul_self`

## References
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- Garre-Rubio, Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*
- [arXiv:1706.07329](https://arxiv.org/abs/1706.07329) -- Molnár, Ge, Schuch, Cirac,
  *A generalization of the injectivity condition for projected entangled pair states*
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D₁ m n : ℕ}

/-- The rectangular action is linear in the domain wall. -/
theorem actRect_smul (T : MPOTensor d D₁) (a : ℂ) (e : Fin d → Matrix (Fin m) (Fin n) ℂ)
    (i : Fin d) : actRect T (fun j ↦ a • e j) i = a • actRect T e i := by
  simp only [actRect, Matrix.kronecker_smul, ← Finset.smul_sum]
  rfl

/-- **Nonvanishing states with two domain walls.** Between normal tensors, two nonzero domain
walls give a nonzero periodic state `|ψ(A-B-A)⟩` with arbitrarily long `A` and `B` regions.

The words of a fixed long length span the full matrix algebras of both blocks, so a vanishing
state would make `tr(X e_i Y f_j)` vanish for all matrices `X`, `Y`, which forces `e_i = 0` or
`f_j = 0`. -/
theorem exists_twoWallMPV_ne_zero {D D' : ℕ} (A : MPSTensor d D)
    (e : Fin d → Matrix (Fin D) (Fin D') ℂ) (B : MPSTensor d D')
    (f : Fin d → Matrix (Fin D') (Fin D) ℂ) (hA : Kraus.IsNormal A) (hB : Kraus.IsNormal B)
    (he : e ≠ 0) (hf : f ≠ 0) (N : ℕ) :
    ∃ k l n : ℕ, N ≤ k ∧ N ≤ l ∧
      ∃ τ : Fin (k + 1 + l + 1 + n) → Fin d, twoWallMPV A e B f τ ≠ 0 := by
  obtain ⟨L, hL, hinj⟩ := hA
  obtain ⟨L', hL', hinj'⟩ := hB
  have hk := MPSTensor.isNBlkInjective_mul_of_isNBlkInjective A (Nat.succ_pos N) hinj
  have hl := MPSTensor.isNBlkInjective_mul_of_isNBlkInjective B (Nat.succ_pos N) hinj'
  obtain ⟨i, hi⟩ := Function.ne_iff.mp he
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hf
  suffices h : ∃ (σ : Fin ((N + 1) * L) → Fin d) (σ' : Fin ((N + 1) * L') → Fin d),
      (Kraus.evalWord A (List.ofFn σ) * e i * Kraus.evalWord B (List.ofFn σ') * f j).trace ≠ 0 by
    obtain ⟨σ, σ', hne⟩ := h
    refine ⟨(N + 1) * L, (N + 1) * L', 0, by nlinarith, by nlinarith,
      Fin.append (Fin.append (Fin.append (Fin.append σ ![i]) σ') ![j]) Fin.elim0, ?_⟩
    rw [twoWallMPV_append]
    simpa using hne
  by_contra hcon
  push Not at hcon
  have h1 : ∀ (X : Matrix (Fin D) (Fin D) ℂ) (σ' : Fin ((N + 1) * L') → Fin d),
      (X * e i * Kraus.evalWord B (List.ofFn σ') * f j).trace = 0 := by
    intro X σ'
    have hmem : X ∈ Submodule.span ℂ
        (Set.range fun σ : Fin ((N + 1) * L) → Fin d ↦ Kraus.evalWord A (List.ofFn σ)) := by
      rw [hk.span_eq_top]
      exact Submodule.mem_top
    refine Submodule.span_induction
      (p := fun M _ ↦ (M * e i * Kraus.evalWord B (List.ofFn σ') * f j).trace = 0)
      (fun M hM ↦ by obtain ⟨σ, rfl⟩ := hM; exact hcon σ σ') (by simp)
      (fun M M' _ _ hM hM' ↦ by simp only [Matrix.add_mul, Matrix.trace_add, hM, hM', add_zero])
      (fun c M _ hM ↦ by simp only [Matrix.smul_mul, Matrix.trace_smul, hM, smul_zero]) hmem
  have h2 : ∀ (X : Matrix (Fin D) (Fin D) ℂ) (Y : Matrix (Fin D') (Fin D') ℂ),
      (X * e i * Y * f j).trace = 0 := by
    intro X Y
    have hmem : Y ∈ Submodule.span ℂ
        (Set.range fun σ' : Fin ((N + 1) * L') → Fin d ↦ Kraus.evalWord B (List.ofFn σ')) := by
      rw [hl.span_eq_top]
      exact Submodule.mem_top
    refine Submodule.span_induction (p := fun M _ ↦ (X * e i * M * f j).trace = 0)
      (fun M hM ↦ by obtain ⟨σ', rfl⟩ := hM; exact h1 X σ') (by simp)
      (fun M M' _ _ hM hM' ↦ by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, hM, hM', add_zero])
      (fun c M _ hM ↦ by
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, hM, smul_zero]) hmem
  obtain ⟨a, b, hab⟩ : ∃ a b, e i a b ≠ 0 := by
    by_contra h0
    push Not at h0
    exact hi (Matrix.ext h0)
  obtain ⟨c, c', hcc⟩ : ∃ c c', f j c c' ≠ 0 := by
    by_contra h0
    push Not at h0
    exact hj (Matrix.ext h0)
  have h3 := h2 (Matrix.single c' a 1) (Matrix.single b c 1)
  rw [Matrix.single_mul_mul_single, Matrix.trace_single_mul] at h3
  exact mul_ne_zero hab hcc (by simpa using h3)

namespace GroupFamily

variable {G X : Type*} [Group G] {F : GroupFamily G d} [MulAction G X] {D : X → ℕ}
  {A : (x : X) → MPSTensor d (D x)}

namespace BlockActionData

variable {ad : BlockActionData F A}

namespace IsDomainWallAction

variable {g : G} {x y x' y' : X} {hx : g • x = x'} {hy : g • y = y'}
  {e : Fin d → Matrix (Fin (D x)) (Fin (D y)) ℂ} {e' : Fin d → Matrix (Fin (D x')) (Fin (D y')) ℂ}
  {c : ℂ}

/-- Rescaling the carried domain wall by a nonzero `a` rescales its phase by `a`.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 826--832 (the choice of
`e_{AB}` and `c_{AB}` fixes `e_{BA}`). -/
theorem smul_source (h : ad.IsDomainWallAction g hx hy e e' c) {a : ℂ} (ha : a ≠ 0) :
    ad.IsDomainWallAction g hx hy (fun i ↦ a • e i) e' (a * c) := by
  obtain ⟨N, hN⟩ := h.eq
  have he : (fun i ↦ a • e i) ≠ 0 := by
    intro h0
    refine h.source_ne_zero (funext fun i ↦ ?_)
    have := congrFun h0 i
    simpa [ha] using this
  refine ⟨he, h.target_ne_zero, mul_ne_zero ha h.phase_ne_zero, N, fun u v i hu hv ↦ ?_⟩
  rw [actRect_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_mul, hN u v i hu hv, smul_smul]

/-- Rescaling the image domain wall by a nonzero `a` divides its phase by `a`.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 826--832 (`e_{BA}` may be
defined through `eq:localcdef` for an arbitrary choice of `c_{AB}`). -/
theorem smul_target (h : ad.IsDomainWallAction g hx hy e e' c) {a : ℂ} (ha : a ≠ 0) :
    ad.IsDomainWallAction g hx hy e (fun i ↦ a • e' i) (c / a) := by
  obtain ⟨N, hN⟩ := h.eq
  have he' : (fun i ↦ a • e' i) ≠ 0 := by
    intro h0
    refine h.target_ne_zero (funext fun i ↦ ?_)
    have := congrFun h0 i
    simpa [ha] using this
  refine ⟨h.source_ne_zero, he', div_ne_zero h.phase_ne_zero ha, N, fun u v i hu hv ↦ ?_⟩
  rw [hN u v i hu hv, Matrix.mul_smul, Matrix.smul_mul, smul_smul, div_mul_cancel₀ _ ha]

/-- **The phases of an involution can be made equal** (arXiv:2405.00439,
`Papers/2405.00439/MPU-DW.tex` line 1664: "we can choose `c_{AB} = c_{BA} = i`"): if `g`
exchanges the domain walls `e_{AB}` and `e_{BA}` with phases `c_{AB}`, `c_{BA}`, then for
every `s` with `s² = c_{AB} c_{BA}` the rescaled wall `(c_{AB} / s) e_{BA}` is exchanged with
`e_{AB}` with both phases equal to `s`. -/
theorem exists_eq_of_mul_self {hxy : g • x = y} {hyx : g • y = x}
    {eAB : Fin d → Matrix (Fin (D x)) (Fin (D y)) ℂ}
    {eBA : Fin d → Matrix (Fin (D y)) (Fin (D x)) ℂ} {cAB cBA : ℂ}
    (hAB : ad.IsDomainWallAction g hxy hyx eAB eBA cAB)
    (hBA : ad.IsDomainWallAction g hyx hxy eBA eAB cBA) {s : ℂ} (hs : s * s = cAB * cBA) :
    ad.IsDomainWallAction g hxy hyx eAB (fun i ↦ (cAB / s) • eBA i) s ∧
      ad.IsDomainWallAction g hyx hxy (fun i ↦ (cAB / s) • eBA i) eAB s := by
  have hc : cAB ≠ 0 := hAB.phase_ne_zero
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hc hBA.phase_ne_zero (by simpa using hs.symm)
  have hcs : cAB / s ≠ 0 := div_ne_zero hc hs0
  refine ⟨?_, ?_⟩
  · have h := hAB.smul_target hcs
    rwa [div_div_cancel₀ hc] at h
  · have h := hBA.smul_source hcs
    convert h using 1
    field_simp
    linear_combination hs

/-- **A symmetry string over a pair of domain walls acquires the product of their phases**
(arXiv:2405.00439, `signphysop`, `Papers/2405.00439/MPU-DW.tex` lines 1667--1672, and `DWstat`,
lines 1660--1663): if `g` carries the domain wall `e` between `x` and `y` to `e'` with phase `c`
and the domain wall `f` between `y` and `z` to `f'` with phase `c'`, then the action tensors of
`g` on the outer regions, applied to `O_g` acting on the open chain `A_x^u e^i A_y^v f^j A_z^w`,
give `c c'` times `A_{gx}^u e'^i A_{gy}^v f'^j A_{gz}^w`, for all words longer than a fixed
buffer. For `ℤ₂` and the pair `e_{AB}`, `e_{BA}` this is `c_{AB} c_{BA} = ω`, the phase between
the two orders of the strings in `signphysop`.

The proof inserts the reduced block of the middle region
(arXiv:1706.07329v2, Lemma `B_expand`, `cornerproblem.tex` lines 3993--4005) and applies the
local action to each wall. -/
theorem pair (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x))) {z z' : X}
    {hz : g • z = z'} {f : Fin d → Matrix (Fin (D y)) (Fin (D z)) ℂ}
    {f' : Fin d → Matrix (Fin (D y')) (Fin (D z')) ℂ} {c' : ℂ}
    (he : ad.IsDomainWallAction g hx hy e e' c) (hf : ad.IsDomainWallAction g hy hz f f' c') :
    ∃ N : ℕ, ∀ (u v w : List (Fin d)) (i j : Fin d), N ≤ u.length → N ≤ v.length →
      N ≤ w.length →
      castIndex D hx * (ad.V g x * (Kraus.evalWord (actTensor (F.tensor g) (A x)) u *
          actRect (F.tensor g) e i * Kraus.evalWord (actTensor (F.tensor g) (A y)) v *
            actRect (F.tensor g) f j * Kraus.evalWord (actTensor (F.tensor g) (A z)) w) *
              ad.W g z) * castIndex D hz.symm =
        (c * c') • (Kraus.evalWord (A x') u * e' i * Kraus.evalWord (A y') v * f' j *
          Kraus.evalWord (A z') w) := by
  subst hx hy hz
  obtain ⟨N₁, H₁⟩ := he.eq
  obtain ⟨N₂, H₂⟩ := hf.eq
  have hBy := (ad.isReduction g y).bondDim_isReductionResidualNilpotencyBound
    ((hperm g y).sameMPV₂Pos_actTensor (MPSTensor.SameMPV₂Pos.refl _))
  set M := N₁ + N₂ + F.bondDim g * D y
  refine ⟨2 * M + 1, fun u v w i j hu hv hw ↦ ?_⟩
  obtain ⟨p, c₁, q, hsplit, hp, hq, hc₁⟩ :=
    v.exists_append_append_of_two_mul_lt (M := M) (by omega)
  have hzB := (ad.isReduction g y).evalWord_mul_reduced_exterior_eq_evalWord_append hBy p c₁ q
    hc₁ (by omega) (by omega)
  have r₁ := H₁ u p i (by omega) (by omega)
  have r₂ := H₂ q w j (by omega) (by omega)
  simp only [castIndex_rfl, Matrix.one_mul, Matrix.mul_one] at r₁ r₂ ⊢
  rw [hsplit, ← hzB]
  calc _ = (ad.V g x * (Kraus.evalWord (actTensor (F.tensor g) (A x)) u *
          actRect (F.tensor g) e i * Kraus.evalWord (actTensor (F.tensor g) (A y)) p) *
            ad.W g y) * Kraus.evalWord (A (g • y)) c₁ *
        (ad.V g y * (Kraus.evalWord (actTensor (F.tensor g) (A y)) q *
          actRect (F.tensor g) f j * Kraus.evalWord (actTensor (F.tensor g) (A z)) w) *
            ad.W g z) := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [r₁, r₂, List.append_assoc, Kraus.evalWord_append, Kraus.evalWord_append]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      rw [mul_comm c' c]

/-- **The square of the exchange phase of an involution** (arXiv:2405.00439,
`Papers/2405.00439/MPU-DW.tex` lines 835--839): if `U = O_g` squares to the identity on every
nonempty chain and `g` exchanges the domain walls `e_{AB}` and `e_{BA}` between the normal
blocks `x` and `y` with phases `c_{AB}`, `c_{BA}`, then `(c_{AB} c_{BA})² = 1`.

As in the source, `U |ψ(A-B-A)⟩ = c_{AB} c_{BA} |ψ(B-A-B)⟩` and
`U |ψ(B-A-B)⟩ = c_{BA} c_{AB} |ψ(A-B-A)⟩`
(`MPOTensor.GroupFamily.BlockActionData.IsDomainWallAction.mpo_mulVec_twoWallMPV`), so applying
`U` twice multiplies `|ψ(A-B-A)⟩` by `(c_{AB} c_{BA})²`; the state is nonzero on a chain with
long regions (`MPOTensor.exists_twoWallMPV_ne_zero`). -/
theorem mul_sq_eq_one_of_mpo_mul_self_eq_one {hxy : g • x = y} {hyx : g • y = x}
    {eAB : Fin d → Matrix (Fin (D x)) (Fin (D y)) ℂ}
    {eBA : Fin d → Matrix (Fin (D y)) (Fin (D x)) ℂ} {cAB cBA : ℂ}
    (hAx : Kraus.IsNormal (A x)) (hAy : Kraus.IsNormal (A y))
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x)))
    (hU : ∀ L, 0 < L → mpo (F.tensor g) L * mpo (F.tensor g) L = 1)
    (hAB : ad.IsDomainWallAction g hxy hyx eAB eBA cAB)
    (hBA : ad.IsDomainWallAction g hyx hxy eBA eAB cBA) :
    (cAB * cBA) ^ 2 = 1 := by
  obtain ⟨N₁, H₁⟩ := mpo_mulVec_twoWallMPV hperm hAB hBA
  obtain ⟨N₂, H₂⟩ := mpo_mulVec_twoWallMPV hperm hBA hAB
  obtain ⟨k, l, n, hk, hl, τ, hτ⟩ := exists_twoWallMPV_ne_zero (A x) eAB (A y) eBA hAx hAy
    hAB.source_ne_zero hBA.source_ne_zero (N₁ + N₂)
  have key : twoWallMPV (A x) eAB (A y) eBA =
      ((cAB * cBA) * (cBA * cAB)) • twoWallMPV (A x) eAB (A y) eBA (k := k) (l := l) (n := n) := by
    calc twoWallMPV (A x) eAB (A y) eBA
        = (mpo (F.tensor g) (k + 1 + l + 1 + n) * mpo (F.tensor g) (k + 1 + l + 1 + n)) *ᵥ
            twoWallMPV (A x) eAB (A y) eBA := by rw [hU _ (by omega), Matrix.one_mulVec]
      _ = _ := by
        rw [← Matrix.mulVec_mulVec, H₁ k l n (by omega) (by omega), Matrix.mulVec_smul,
          H₂ k l n (by omega) (by omega), smul_smul]
  have hτ' := congrFun key τ
  rw [Pi.smul_apply, smul_eq_mul] at hτ'
  refine mul_right_cancel₀ hτ ?_
  linear_combination -hτ'

end IsDomainWallAction

end BlockActionData

end GroupFamily

end MPOTensor
