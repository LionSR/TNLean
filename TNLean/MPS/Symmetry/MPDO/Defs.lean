/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinKronecker
import TNLean.MPS.Symmetry.MPOSymmetry.Defs

/-!
# Strong and weak symmetries of matrix product density operators

**Source.** Sun 2025 (arXiv:2504.16985), "Anomalous matrix product operator symmetries and
1D mixed-state phases", `References/2504.16985/main.tex` line 182: a matrix product density
operator `ρ^{(L)}` is strongly symmetric under a family of matrix product operators `O_a^{(L)}` when
`O_a^{(L)} ρ^{(L)} = λ_a^{(L)} ρ^{(L)}` for all `a` and `L`, and weakly symmetric when
`[O_a^{(L)}, ρ^{(L)}] = 0` for all `a` and `L`; strong symmetry is a special case of weak
symmetry provided each `O_a^{(L)}` has its adjoint `O_{ā}^{(L)}` in the family. The on-site
group case, `[U, ρ] = 0` (weak) and `U ρ = ρ` (strong), is recalled in Garre Rubio, Molnár,
Schuch, Verstraete 2026 (arXiv:2603.28349), `References/2603.28349/main.tex` line 362, from
de Groot, Turzillo, Schuch 2022 (arXiv:2112.04483).

**Formalized here.** The two predicates at one system size and along the whole family of
periodic operators; the implication from strong to weak symmetry under the source's
adjoint-closure proviso; the unit modulus of the eigenvalue of a unitary strong symmetry; the
fusion rules satisfied by strong eigenvalues; and the on-site specialization `U_g^{⊗L}`, where
the eigenvalues form a character of the group at each length.

**Scope restriction (boundary `X = 1`):** the source's density operator
`ρ^{(L)}(X, M) = ∑ tr[X M^{i_1 j_1} ⋯ M^{i_L j_L}] |i⟩⟨j|` carries a boundary matrix `X`
commuting with every `M^{ij}` (`References/2504.16985/main.tex` lines 175–181); the family
predicates of this file are stated for the periodic operators `mpo M L`, the case `X = 1`.
Documented in `docs/paper-gaps/sun25_mpdo_symmetry_boundary_scope.tex`.

## Main definitions

* `Matrix.IsStrongSymmetry`, `Matrix.IsWeakSymmetry`: `O ρ = c ρ` and `[O, ρ] = 0`.
* `MPOTensor.IsStrongMPOSymmetry`, `MPOTensor.IsWeakMPOSymmetry`: the same at every positive
  length along a family of periodic matrix product operators, with length-dependent
  eigenvalues `c a L`.
* `MPOTensor.onSite`: the bond-dimension-one tensor of an on-site operator.
* `MPOTensor.IsStrongOnSiteSymmetry`, `MPOTensor.IsWeakOnSiteSymmetry`: the on-site group case.

## Main results

* `Matrix.IsStrongSymmetry.isWeakSymmetry_of_conjTranspose`,
  `MPOTensor.IsStrongMPOSymmetry.isWeakMPOSymmetry`: strong implies weak under adjoint closure.
* `Matrix.IsStrongSymmetry.norm_eq_one`: a unitary strong symmetry of a nonzero matrix has a
  unimodular eigenvalue.
* `MPOTensor.IsStrongMPOSymmetry.mul_eq_sum`: strong eigenvalues obey the fusion rules.
* `MPOTensor.mpo_onSite`: the periodic operator of `onSite u` is `u^{⊗L}`.
* `MPOTensor.IsStrongOnSiteSymmetry.isWeakOnSiteSymmetry`,
  `MPOTensor.IsStrongOnSiteSymmetry.map_mul`, `MPOTensor.IsStrongOnSiteSymmetry.map_one`.

## References
- [arXiv:2504.16985](https://arxiv.org/abs/2504.16985) -- X.-Q. Sun, *Anomalous matrix
  product operator symmetries and 1D mixed-state phases*
- [arXiv:2112.04483](https://arxiv.org/abs/2112.04483) -- C. de Groot, A. Turzillo,
  N. Schuch, *Symmetry protected topological order in open quantum systems*
- [arXiv:2603.28349](https://arxiv.org/abs/2603.28349) -- J. Garre Rubio, A. Molnár,
  N. Schuch, F. Verstraete, *The local characterization of global tensor network eigenstates*
-/

open scoped Matrix ComplexOrder BigOperators

namespace Matrix

variable {n : Type*} [Fintype n]

/-- **Strong symmetry at one system size.**

Source: arXiv:2504.16985, line 182: `O ρ = λ ρ` for some scalar `λ`. The scalar is not
required to be a phase; `λ = 0` is allowed. -/
def IsStrongSymmetry (O ρ : Matrix n n ℂ) : Prop :=
  ∃ c : ℂ, O * ρ = c • ρ

/-- **Weak symmetry at one system size.**

Source: arXiv:2504.16985, line 182: `[O, ρ] = 0`. -/
def IsWeakSymmetry (O ρ : Matrix n n ℂ) : Prop :=
  Commute O ρ

/-- A Hermitian matrix whose square vanishes is zero. -/
private theorem IsHermitian.mul_self_ne_zero {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (h0 : ρ ≠ 0) : ρ * ρ ≠ 0 := by
  intro h
  apply h0
  refine self_mul_conjTranspose_eq_zero.mp ?_
  rwa [hρ.eq]

/-- **Strong symmetry implies weak symmetry under adjoint closure.**

Source: arXiv:2504.16985, line 182: strong symmetry is a special case of weak symmetry
provided the conjugate operator `O^†` is also a strong symmetry. For Hermitian `ρ`, the two
eigenvalue equations give `ρ O = \bar μ ρ` and `ρ O ρ = λ ρ² = \bar μ ρ²`, so `λ = \bar μ`
unless `ρ = 0`. -/
theorem IsStrongSymmetry.isWeakSymmetry_of_conjTranspose {O ρ : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) (hO : IsStrongSymmetry O ρ) (hOH : IsStrongSymmetry Oᴴ ρ) :
    IsWeakSymmetry O ρ := by
  obtain ⟨c, hc⟩ := hO
  obtain ⟨μ, hμ⟩ := hOH
  have hρO : ρ * O = star μ • ρ := by
    have h := congrArg conjTranspose hμ
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, hρ.eq, conjTranspose_smul, hρ.eq] at h
  by_cases h0 : ρ = 0
  · subst h0
    exact Commute.zero_right O
  have hcμ : c = star μ := by
    have h1 : ρ * (O * ρ) = (ρ * O) * ρ := (Matrix.mul_assoc _ _ _).symm
    rw [hc, hρO, Matrix.mul_smul, Matrix.smul_mul] at h1
    exact smul_left_injective ℂ (IsHermitian.mul_self_ne_zero hρ h0) h1
  change O * ρ = ρ * O
  rw [hc, hρO, hcμ]

/-- A strong symmetry `O` with `O^† O = 1` has its adjoint as a strong symmetry: from
`O ρ = c ρ`, `ρ = O^† O ρ = c O^† ρ`. -/
theorem IsStrongSymmetry.conjTranspose_of_unitary [DecidableEq n] {O ρ : Matrix n n ℂ}
    (hU : Oᴴ * O = 1) (hO : IsStrongSymmetry O ρ) : IsStrongSymmetry Oᴴ ρ := by
  obtain ⟨c, hc⟩ := hO
  have h : ρ = c • (Oᴴ * ρ) := by
    rw [← Matrix.mul_smul, ← hc, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  by_cases hc0 : c = 0
  · refine ⟨0, ?_⟩
    rw [hc0, zero_smul] at h
    rw [h, Matrix.mul_zero, smul_zero]
  · refine ⟨c⁻¹, ?_⟩
    conv_rhs => rw [h, smul_smul, inv_mul_cancel₀ hc0, one_smul]

/-- **Strong implies weak for unitary operators.**

Source: arXiv:2504.16985, line 182, in the unitary case, where the adjoint `O^† = O^{-1}` is a
strong symmetry automatically (`IsStrongSymmetry.conjTranspose_of_unitary`). -/
theorem IsStrongSymmetry.isWeakSymmetry_of_unitary [DecidableEq n] {O ρ : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) (hU : Oᴴ * O = 1) (hO : IsStrongSymmetry O ρ) :
    IsWeakSymmetry O ρ :=
  hO.isWeakSymmetry_of_conjTranspose hρ (hO.conjTranspose_of_unitary hU)

/-- **Unit modulus of a unitary strong eigenvalue.**

Bridge: for `O^† O = 1` and `ρ ≠ 0`, `O ρ = c ρ` forces `|c| = 1`, since
`ρ^† ρ = (O ρ)^† (O ρ) = |c|² ρ^† ρ` and `ρ^† ρ ≠ 0`. This is the modulus of the phase `e^{iθ}`
in the channel-level strong symmetry of arXiv:2112.04483, line 351; the eigenvalue itself
is not determined. -/
theorem IsStrongSymmetry.norm_eq_one [DecidableEq n] {O ρ : Matrix n n ℂ} {c : ℂ}
    (hU : Oᴴ * O = 1) (hc : O * ρ = c • ρ) (h0 : ρ ≠ 0) : ‖c‖ = 1 := by
  have h1 : ρᴴ * ρ = (star c * c) • (ρᴴ * ρ) := by
    calc ρᴴ * ρ = (O * ρ)ᴴ * (O * ρ) := by
          rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Oᴴ, hU, Matrix.one_mul]
      _ = (star c * c) • (ρᴴ * ρ) := by
          rw [hc, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hne : ρᴴ * ρ ≠ 0 := fun h => h0 (conjTranspose_mul_self_eq_zero.mp h)
  have h3 : star c * c = 1 := smul_left_injective ℂ hne (h1.symm.trans (one_smul ℂ _).symm)
  have h4 : (‖c‖ : ℂ) ^ 2 = 1 := by
    rw [← h3, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    push_cast; ring
  have h5 : ‖c‖ ^ 2 = 1 := by exact_mod_cast h4
  nlinarith [norm_nonneg c]

end Matrix

namespace MPOTensor

variable {d D : ℕ}

/-! ### Family predicates -/

section Family

variable {ι : Type*} {χ : ι → ℕ}

/-- **Strong symmetry of a matrix product density operator.**

Source: arXiv:2504.16985, line 182: `O_a^{(L)} ρ^{(L)} = λ_a^{(L)} ρ^{(L)}` for all `a` and
`L`. The eigenvalue `c a L` may depend on the length and is not required to be a phase; system
sizes are positive, as in `IsMPDO`. The definition is more general than the source: there the
`O_a` are normal matrix product operators forming a fusion algebra (lines 125–137) and `ρ` is
a matrix product density operator; here the family and `M` are arbitrary, and the fusion and
positivity hypotheses are added where a result uses them. -/
def IsStrongMPOSymmetry (O : ∀ a, MPOTensor d (χ a)) (M : MPOTensor d D)
    (c : ι → ℕ → ℂ) : Prop :=
  ∀ a L, 0 < L → mpo (O a) L * mpo M L = c a L • mpo M L

/-- **Weak symmetry of a matrix product density operator.**

Source: arXiv:2504.16985, line 182: `[O_a^{(L)}, ρ^{(L)}] = 0` for all `a` and `L`, at positive
system sizes. As for `IsStrongMPOSymmetry`, no fusion structure on the family and no
positivity of `M` is assumed. -/
def IsWeakMPOSymmetry (O : ∀ a, MPOTensor d (χ a)) (M : MPOTensor d D) : Prop :=
  ∀ a L, 0 < L → Commute (mpo (O a) L) (mpo M L)

/-- **Strong symmetry implies weak symmetry under adjoint closure.**

Source: arXiv:2504.16985, line 182: strong symmetry is a special case of weak symmetry
provided the family contains the conjugate `O_{ā}^{(L)} = O_a^{(L)†}` of each operator. -/
theorem IsStrongMPOSymmetry.isWeakMPOSymmetry {O : ∀ a, MPOTensor d (χ a)}
    {M : MPOTensor d D} {c : ι → ℕ → ℂ} (hM : IsMPDO M) (h : IsStrongMPOSymmetry O M c)
    (bar : ι → ι) (hbar : ∀ a L, 0 < L → mpo (O (bar a)) L = (mpo (O a) L)ᴴ) :
    IsWeakMPOSymmetry O M := by
  intro a L hL
  refine Matrix.IsStrongSymmetry.isWeakSymmetry_of_conjTranspose (hM L hL).isHermitian
    ⟨c a L, h a L hL⟩ ⟨c (bar a) L, ?_⟩
  rw [← hbar a L hL]
  exact h (bar a) L hL

/-- **Strong eigenvalues obey the fusion rules.**

Bridge: if the periodic operators satisfy `O_a O_b = ∑_c N_{ab}^c O_c`
(`IsMPOFusionAlgebra`, arXiv:2203.12563 lines 361–362) and `ρ^{(L)} ≠ 0`, the eigenvalues of a
strong symmetry (arXiv:2504.16985, line 182) satisfy `λ_a λ_b = ∑_c N_{ab}^c λ_c` at that
length. -/
theorem IsStrongMPOSymmetry.mul_eq_sum [Fintype ι] {O : ∀ a, MPOTensor d (χ a)}
    {M : MPOTensor d D} {c : ι → ℕ → ℂ} (h : IsStrongMPOSymmetry O M c)
    {Nf : ι → ι → ι → ℕ} (hF : IsMPOFusionAlgebra O Nf) {L : ℕ} (hL : 0 < L)
    (hρ : mpo M L ≠ 0) (a b : ι) :
    c a L * c b L = ∑ e, (Nf a b e : ℂ) * c e L := by
  have h1 : mpo (O a) L * mpo (O b) L * mpo M L = (c a L * c b L) • mpo M L := by
    rw [Matrix.mul_assoc, h b L hL, Matrix.mul_smul, h a L hL, smul_smul, mul_comm]
  have h2 : mpo (O a) L * mpo (O b) L * mpo M L =
      (∑ e, (Nf a b e : ℂ) * c e L) • mpo M L := by
    rw [hF a b L hL, Matrix.sum_mul, Finset.sum_smul]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Matrix.smul_mul, h e L hL, smul_smul]
  exact smul_left_injective ℂ hρ (h1.symm.trans h2)

/-- **Nonzero strong eigenvalues form a fusion character.**

Bridge: under the hypotheses of `IsStrongMPOSymmetry.mul_eq_sum`, if `e` is the unit label of
the fusion ring and its eigenvalue is nonzero, then `a ↦ λ_a^{(L)}` is a fusion character: the
fusion rules give `λ_e² = λ_e`, hence `λ_e = 1`. -/
theorem IsStrongMPOSymmetry.isFusionCharacter [Fintype ι] [DecidableEq ι]
    {O : ∀ a, MPOTensor d (χ a)} {M : MPOTensor d D} {c : ι → ℕ → ℂ}
    (h : IsStrongMPOSymmetry O M c) {Nf : ι → ι → ι → ℕ} (hF : IsMPOFusionAlgebra O Nf)
    {e : ι} (he : IsFusionUnit Nf e) {L : ℕ} (hL : 0 < L) (hρ : mpo M L ≠ 0)
    (hce : c e L ≠ 0) : IsFusionCharacter Nf e fun a => c a L := by
  refine ⟨?_, fun a b => h.mul_eq_sum hF hL hρ a b⟩
  have h1 := h.mul_eq_sum hF hL hρ e e
  simp only [(he e _).1, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h1
  exact mul_left_cancel₀ hce (by rw [h1, mul_one])

end Family

/-! ### On-site operators -/

/-- **The tensor of an on-site operator.** The bond-dimension-one tensor with
`(onSite u)^{ij} = u_{ij}`, whose periodic operator is `u^{⊗L}` (`mpo_onSite`). -/
noncomputable def onSite (u : Matrix (Fin d) (Fin d) ℂ) : MPOTensor d 1 :=
  fun i j => u i j • 1

/-- The periodic operator of an on-site tensor is the Kronecker power `u^{⊗L}`. -/
theorem mpo_onSite (u : Matrix (Fin d) (Fin d) ℂ) (L : ℕ) :
    mpo (onSite u) L = Matrix.finKronecker fun _ : Fin L => u := by
  ext σ τ
  simp only [mpo_apply, mpoMatrixEntry, evalWord_ofFn, onSite, List.prod_ofFn_smul,
    Matrix.finKronecker_apply]
  simp

section OnSite

variable {G : Type*} [Monoid G]

/-- **Strong on-site symmetry.**

Source: arXiv:2504.16985, line 182, for the family `O_g^{(L)} = U_g^{⊗L}` of an on-site
representation; the case `c g L = 1` is the strong symmetry `U ρ = ρ` of arXiv:2603.28349,
line 362. -/
def IsStrongOnSiteSymmetry (M : MPOTensor d D) (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (c : G → ℕ → ℂ) : Prop :=
  IsStrongMPOSymmetry (fun g => onSite (U g)) M c

/-- **Weak on-site symmetry.**

Source: arXiv:2504.16985, line 182, for `O_g^{(L)} = U_g^{⊗L}`; this is the weak symmetry
`[U, ρ] = 0` of arXiv:2603.28349, line 362. -/
def IsWeakOnSiteSymmetry (M : MPOTensor d D) (U : G →* Matrix (Fin d) (Fin d) ℂ) : Prop :=
  IsWeakMPOSymmetry (fun g => onSite (U g)) M

/-- **Strong on-site symmetry implies weak on-site symmetry for unitary representations.**

Source: arXiv:2504.16985, line 182, in the on-site unitary case, where `U_g^{†} = U_{g^{-1}}`
supplies the adjoint-closure proviso. -/
theorem IsStrongOnSiteSymmetry.isWeakOnSiteSymmetry {M : MPOTensor d D}
    {U : G →* Matrix (Fin d) (Fin d) ℂ} {c : G → ℕ → ℂ} (hM : IsMPDO M)
    (hU : ∀ g, (U g)ᴴ * U g = 1) (h : IsStrongOnSiteSymmetry M U c) :
    IsWeakOnSiteSymmetry M U := by
  intro g L hL
  have hL' := h g L hL
  simp only [mpo_onSite] at hL' ⊢
  exact Matrix.IsStrongSymmetry.isWeakSymmetry_of_unitary (hM L hL).isHermitian
    (Matrix.finKronecker_conjTranspose_mul_self (hU g)) ⟨c g L, hL'⟩

/-- **Unit modulus of on-site strong eigenvalues.**

Bridge: for a unitary on-site representation and `ρ^{(L)} ≠ 0`, `|c_g^{(L)}| = 1`. -/
theorem IsStrongOnSiteSymmetry.norm_eq_one {M : MPOTensor d D}
    {U : G →* Matrix (Fin d) (Fin d) ℂ} {c : G → ℕ → ℂ} (h : IsStrongOnSiteSymmetry M U c)
    (hU : ∀ g, (U g)ᴴ * U g = 1) {L : ℕ} (hL : 0 < L) (hρ : mpo M L ≠ 0) (g : G) :
    ‖c g L‖ = 1 := by
  have hL' := h g L hL
  simp only [mpo_onSite] at hL'
  exact Matrix.IsStrongSymmetry.norm_eq_one (Matrix.finKronecker_conjTranspose_mul_self (hU g))
    hL' hρ

/-- **On-site strong eigenvalues are multiplicative.**

Bridge: `U_{gh}^{⊗L} = U_g^{⊗L} U_h^{⊗L}`, so for `ρ^{(L)} ≠ 0` the eigenvalues satisfy
`c_{gh}^{(L)} = c_g^{(L)} c_h^{(L)}`, the group case of `IsStrongMPOSymmetry.mul_eq_sum`. -/
theorem IsStrongOnSiteSymmetry.map_mul {M : MPOTensor d D}
    {U : G →* Matrix (Fin d) (Fin d) ℂ} {c : G → ℕ → ℂ} (h : IsStrongOnSiteSymmetry M U c)
    {L : ℕ} (hL : 0 < L) (hρ : mpo M L ≠ 0) (g k : G) :
    c (g * k) L = c g L * c k L := by
  have hg := h g L hL
  have hk := h k L hL
  have hgk := h (g * k) L hL
  simp only [mpo_onSite] at hg hk hgk
  have hsplit : (Matrix.finKronecker fun _ : Fin L => U (g * k)) =
      (Matrix.finKronecker fun _ : Fin L => U g) * Matrix.finKronecker fun _ : Fin L => U k := by
    rw [Matrix.finKronecker_mul, _root_.map_mul]
  refine smul_left_injective ℂ hρ (hgk.symm.trans ?_)
  change _ = (c g L * c k L) • mpo M L
  rw [hsplit, Matrix.mul_assoc, hk, Matrix.mul_smul, hg, smul_smul, mul_comm (c k L)]

/-- The on-site strong eigenvalue of the identity is `1` when `ρ^{(L)} ≠ 0`. -/
theorem IsStrongOnSiteSymmetry.map_one {M : MPOTensor d D}
    {U : G →* Matrix (Fin d) (Fin d) ℂ} {c : G → ℕ → ℂ} (h : IsStrongOnSiteSymmetry M U c)
    {L : ℕ} (hL : 0 < L) (hρ : mpo M L ≠ 0) : c 1 L = 1 := by
  have h1 := h 1 L hL
  simp only [mpo_onSite, _root_.map_one, Matrix.finKronecker_one, Matrix.one_mul] at h1
  exact smul_left_injective ℂ hρ (h1.symm.trans (one_smul ℂ _).symm)

end OnSite

end MPOTensor
