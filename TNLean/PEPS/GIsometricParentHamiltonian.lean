/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.FrameOperator
import TNLean.PEPS.GIsometric

/-!
# Commuting parent Hamiltonians of G-isometric matrix product states

**Source.** Schuch, Cirac, Pérez-García 2010 (arXiv:1001.3807), Section 6, "Commuting parent
Hamiltonians", `Papers/1001.3807/paper_v3.tex`:

* lines 2092–2096: the parent Hamiltonians of `G`-isometric PEPS are sums of commuting local
  terms; the proof is given for MPS, "the generalization to PEPS is straightforward";
* Lemma 6.11, lines 2098–2125, figures `figs4/ham-proj-from-A.pdf`,
  `figs4/ham-proj-from-A-is-proj.pdf` and `figs4/ham-proj-from-A-pres-subspace.pdf`: for
  `G`-isometric MPS, the local terms `h_i`, which project onto the complement of
  `𝒮_2 = {∑_{ij} tr[A^i A^j X] |ij⟩}`, are of the form of the operator
  `∑ tr[A^i A^j (A^k A^l)†] |ij⟩⟨kl|` (equation `eq:iso:ham-proj-from-A`). The proof shows that
  this operator is a projector, has range in `𝒮_2`, fixes `𝒮_2` and is self-adjoint;
* Theorem 6.12 (commuting parent Hamiltonians), lines 2131–2153, figures
  `figs4/ham-comm-step1.pdf` and `figs4/ham-comm-step2.pdf`: for `G`-isometric PEPS the terms
  `h_i` of the parent Hamiltonian commute. The proof writes the products of the operators on
  sites `1, 2` and `2, 3` as the two sides of `figs4/ham-comm-step1.pdf`, which agree since the
  sum over `g` of `U_g ⊗ U_g⁻¹` on the virtual level moves from one bond to the other.

**Formalized here.** An MPS tensor `A : Fin d → End ℂ[G]` with the left-regular representation
on its bond is `G`-isometric in the sense of `IsGIsometricMPS` (Definition 6.1). The parent
Hamiltonian of the chain is that of the matrix tensor `regularMPSTensor A`, the matrices of the
`A^i` in the basis of group elements, in which `A†` is the conjugate transpose
(`regularBondMatrix_regularAdjoint`). The operator of equation `eq:iso:ham-proj-from-A` is
`MPSTensor.groundSpaceFrame (regularMPSTensor A) 2 = Γ_2 Γ_2†`, with `Γ_2(X) = tr[A^{s₀} A^{s₁} X]`.
Lemma 6.11 is `IsGIsometricMPS.parentInteraction_regularMPSTensor`: up to a positive factor `c`
the operator is idempotent with range `𝒮_2`, and the parent interaction is
`h = 1 - c⁻¹ Γ_2 Γ_2†`; it is self-adjoint by `MPSTensor.groundSpaceFrame_isHermitian`. The
proof uses the stability of `G`-isometry under concatenation (Lemma 6.2,
`IsGIsometricMPS.concatTensor`) for the two-site tensor `A^a A^b`. The factor `c` is the
normalization allowed by `IsGIsometricMPS`, documented in
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

For Theorem 6.12 the key identity is `sum_trace_mul_smul_regularAdjoint`:
`∑_b tr[A^b N] (A^b)† = c N` for `N` commuting with the left-regular representation. Every
product of the `A^i` and `(A^i)†` commutes with it (`commute_leftRegular_regularAdjoint`, from
the unitarity `regularAdjoint_leftRegular`), which is the step at which the sum over `g` of
`figs4/ham-comm-step1.pdf` drops out. The two products of the lifts of `Γ_2 Γ_2†` to sites
`1, 2` and `2, 3` are then both `c Γ_3 Γ_3†`
(`IsGIsometricMPS.pairLift_groundSpaceFrame_regularMPSTensor`), and the parent terms commute on
every ring of `N ≥ 3` sites (`IsGIsometricMPS.isNNCPH_regularMPSTensor`).

**Local fix (projector onto `𝒮_2`):** Lemma 6.11 names the operator of equation
`eq:iso:ham-proj-from-A` the local term `h_i`, which projects onto the complement of `𝒮_2`
(equation `eq:2d:parentham-localterm`, lines 1534–1539), while its proof shows that the operator is
the projector onto `𝒮_2`; it is `1 - h_i`. Documented in
`docs/paper-gaps/scp10_g_isometric_commuting_parent_hamiltonian.tex`.

**Scope restriction (MPS):** Theorem 6.12 is stated for PEPS;
`IsGIsometricMPS.isNNCPH_regularMPSTensor` and
`IsGIsometricMPS.pairLift_groundSpaceFrame_regularMPSTensor` prove it for MPS, the case in which
the source writes the proof, on rings of `N ≥ 3` sites. Documented in
`docs/paper-gaps/scp10_g_isometric_commuting_parent_hamiltonian.tex`.

## Main definitions

* `TNLean.PEPS.regularBondMatrix`: the matrix of an operator on `ℂ[G]` in the basis of group
  elements.
* `TNLean.PEPS.regularMPSTensor`: the matrix tensor of `A : Fin d → End ℂ[G]`.

## Main results

* `TNLean.PEPS.regularAdjoint_leftRegular`: `L_g† = L_{g⁻¹}`.
* `TNLean.PEPS.sum_trace_mul_smul_regularAdjoint`: `∑_b tr[A^b N] (A^b)† = c N` on the commutant.
* `TNLean.PEPS.IsGIsometricMPS.parentInteraction_regularMPSTensor`: Lemma 6.11.
* `TNLean.PEPS.IsGIsometricMPS.pairLift_groundSpaceFrame_regularMPSTensor`,
  `TNLean.PEPS.IsGIsometricMPS.isNNCPH_regularMPSTensor`: Theorem 6.12 for MPS.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open Module LinearMap Representation
open scoped Matrix

namespace TNLean
namespace PEPS

attribute [local instance] Representation.invertibleFintypeCardComplex

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

section Adjoint

/-- The adjoint of `L_g` in the basis of group elements is `L_{g⁻¹}`: the left-regular
representation is unitary. -/
theorem regularAdjoint_leftRegular (g : G) :
    regularAdjoint (leftRegular ℂ G g) = leftRegular ℂ G g⁻¹ := by
  rw [regularAdjoint, AlgEquiv.symm_apply_eq]
  ext k h
  simp only [LinearMap.toMatrixAlgEquiv_apply, Matrix.conjTranspose_apply]
  simp only [MonoidAlgebra.basis, Basis.coe_ofRepr, MonoidAlgebra.coeffLinearEquiv_symm_apply,
    MonoidAlgebra.ofCoeff_single, ofMulAction_single, smul_eq_mul,
    MonoidAlgebra.coeffLinearEquiv_apply, MonoidAlgebra.coeff_single, RCLike.star_def]
  by_cases hk : g * k = h
  · simp [Finsupp.single_apply, hk, inv_mul_eq_iff_eq_mul]
  · simp only [Finsupp.single_apply, hk, ite_false, map_zero]
    split_ifs with h'
    · exact absurd (h' ▸ mul_inv_cancel_left g h) hk
    · rfl

/-- The adjoint of an operator commuting with every `L_g` commutes with every `L_g`. -/
theorem commute_leftRegular_regularAdjoint {X : Module.End ℂ (MonoidAlgebra ℂ G)}
    (hX : ∀ g, Commute (leftRegular ℂ G g) X) (g : G) :
    Commute (leftRegular ℂ G g) (regularAdjoint X) := by
  have h := congrArg regularAdjoint (hX g⁻¹).eq
  rw [regularAdjoint_mul, regularAdjoint_mul, regularAdjoint_leftRegular, inv_inv] at h
  exact h.symm

omit [Fintype G] [DecidableEq G] in
/-- An operator with `L_g X L_g⁻¹ = X` commutes with `L_g`. -/
theorem commute_leftRegular_of_conj {X : Module.End ℂ (MonoidAlgebra ℂ G)} {g : G}
    (h : leftRegular ℂ G g * X * leftRegular ℂ G g⁻¹ = X) : Commute (leftRegular ℂ G g) X := by
  have hg : leftRegular ℂ G g⁻¹ * leftRegular ℂ G g = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  calc leftRegular ℂ G g * X = leftRegular ℂ G g * X * leftRegular ℂ G g⁻¹ * leftRegular ℂ G g := by
        rw [mul_assoc _ (leftRegular ℂ G g⁻¹), hg, mul_one]
    _ = X * leftRegular ℂ G g := by rw [h]

end Adjoint

section Core

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Module.End ℂ (MonoidAlgebra ℂ G)}
  {c : ℂ}

omit [DecidableEq ι] in
/-- Source: arXiv:1001.3807, Definition 6.1, `Papers/1001.3807/paper_v3.tex` lines 1692–1700.
If `𝒫(A†) 𝒫(A) = c σ`, then on an operator `N` commuting with every `L_g`,
`∑_i tr[A^i N] (A^i)† = c N`. -/
theorem sum_trace_mul_smul_regularAdjoint
    (h : mpsAdjointSiteMap A ∘ₗ mpsSiteMap A =
      c • (linHom (leftRegular ℂ G) (leftRegular ℂ G)).averageMap)
    {N : Module.End ℂ (MonoidAlgebra ℂ G)} (hN : ∀ g, Commute (leftRegular ℂ G g) N) :
    ∑ i, LinearMap.trace ℂ _ (A i * N) • regularAdjoint (A i) = c • N := by
  have hinv : N ∈ (linHom (leftRegular ℂ G) (leftRegular ℂ G)).invariants :=
    (mem_invariants_linHom_iff _ N).2 fun g => (hN g).eq
  have := LinearMap.congr_fun h N
  rw [LinearMap.comp_apply, LinearMap.smul_apply, averageMap_id _ N hinv] at this
  rw [← this, mpsAdjointSiteMap]
  simp

omit [DecidableEq ι] in
/-- The trace pairing form of `sum_trace_mul_smul_regularAdjoint`:
`∑_i tr[M (A^i)†] tr[A^i N] = c tr[M N]` for `N` commuting with every `L_g`. -/
theorem sum_trace_mul_regularAdjoint_mul_trace
    (h : mpsAdjointSiteMap A ∘ₗ mpsSiteMap A =
      c • (linHom (leftRegular ℂ G) (leftRegular ℂ G)).averageMap)
    {N : Module.End ℂ (MonoidAlgebra ℂ G)} (hN : ∀ g, Commute (leftRegular ℂ G g) N)
    (M : Module.End ℂ (MonoidAlgebra ℂ G)) :
    ∑ i, LinearMap.trace ℂ _ (M * regularAdjoint (A i)) * LinearMap.trace ℂ _ (A i * N) =
      c * LinearMap.trace ℂ _ (M * N) := by
  have := congrArg (fun Y => LinearMap.trace ℂ _ (M * Y)) (sum_trace_mul_smul_regularAdjoint h hN)
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul] at this
  rw [← this]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end Core

section Matrix

/-- The basis of `ℂ[G]` by the group elements, indexed by `Fin |G|`. -/
noncomputable def regularBondBasis : Basis (Fin (Fintype.card G)) ℂ (MonoidAlgebra ℂ G) :=
  (MonoidAlgebra.basis G ℂ).reindex (Fintype.equivFin G)

/-- The matrix of an operator on `ℂ[G]` in the basis of group elements. -/
noncomputable def regularBondMatrix :
    Module.End ℂ (MonoidAlgebra ℂ G) ≃ₐ[ℂ]
      Matrix (Fin (Fintype.card G)) (Fin (Fintype.card G)) ℂ :=
  LinearMap.toMatrixAlgEquiv regularBondBasis

omit [Group G] in
/-- The matrix of `X†` is the conjugate transpose of the matrix of `X`. -/
theorem regularBondMatrix_regularAdjoint (X : Module.End ℂ (MonoidAlgebra ℂ G)) :
    regularBondMatrix (regularAdjoint X) = (regularBondMatrix X)ᴴ := by
  ext i j
  simp only [regularBondMatrix, LinearMap.toMatrixAlgEquiv_apply, regularBondBasis,
    Basis.reindex_apply, Basis.repr_reindex_apply, Matrix.conjTranspose_apply]
  rw [← LinearMap.toMatrixAlgEquiv_apply, ← LinearMap.toMatrixAlgEquiv_apply, regularAdjoint,
    AlgEquiv.apply_symm_apply, Matrix.conjTranspose_apply]

omit [Group G] [DecidableEq G] in
/-- The trace of the matrix is the trace of the operator. -/
theorem trace_regularBondMatrix (X : Module.End ℂ (MonoidAlgebra ℂ G)) :
    (regularBondMatrix X).trace = LinearMap.trace ℂ _ X :=
  (LinearMap.trace_eq_matrix_trace ℂ regularBondBasis X).symm

variable {d : ℕ}

/-- The MPS tensor of matrices of an MPS tensor `A : Fin d → End ℂ[G]` in the basis of group
elements, on which the parent Hamiltonian of the chain is defined. -/
noncomputable def regularMPSTensor (A : Fin d → Module.End ℂ (MonoidAlgebra ℂ G)) :
    MPSTensor d (Fintype.card G) :=
  fun i => regularBondMatrix (A i)

end Matrix

section ParentHamiltonian

variable {d : ℕ} {A : Fin d → Module.End ℂ (MonoidAlgebra ℂ G)}

/-- Source: arXiv:1001.3807, proof of Lemma 6.11, `Papers/1001.3807/paper_v3.tex`
lines 2112–2120, figure `figs4/ham-proj-from-A-is-proj.pdf`, for the two-site tensor
`C^{ab} = A^a A^b`. If `𝒫(C†) 𝒫(C) = c σ` and `C` is invariant, then
`∑_{ab} tr[A^a A^b X] tr[A^{s₀} A^{s₁} (A^a A^b)†] = c tr[A^{s₀} A^{s₁} X]`. -/
theorem sum_trace_concatTensor_mul_trace_regularAdjoint {c : ℂ}
    (hC : mpsAdjointSiteMap (concatTensor A A) ∘ₗ mpsSiteMap (concatTensor A A) =
      c • (linHom (leftRegular ℂ G) (leftRegular ℂ G)).averageMap)
    (hCinv : ∀ g, mpsSiteMap (concatTensor A A) ∘ₗ linHom (leftRegular ℂ G) (leftRegular ℂ G) g =
      mpsSiteMap (concatTensor A A))
    (X : Module.End ℂ (MonoidAlgebra ℂ G)) (s₀ s₁ : Fin d) :
    ∑ a, ∑ b, LinearMap.trace ℂ _ (A a * A b * X) *
        LinearMap.trace ℂ _ (A s₀ * A s₁ * regularAdjoint (A a * A b)) =
      c * LinearMap.trace ℂ _ (A s₀ * A s₁ * X) := by
  have h := congrArg (fun Y => mpsSiteMap (concatTensor A A) Y (s₀, s₁)) (LinearMap.congr_fun hC X)
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, Pi.smul_apply,
    apply_averageMap_of_forall_comp_eq hCinv, smul_eq_mul] at h
  rw [mpsSiteMap_apply, mpsSiteMap_apply, concatTensor_apply] at h
  rw [← h, mpsAdjointSiteMap]
  simp [Finset.mul_sum, map_sum, Fintype.sum_prod_type]

/-- Source: arXiv:1001.3807, proof of Theorem 6.12, `Papers/1001.3807/paper_v3.tex`
lines 2138–2151, figures `figs4/ham-comm-step1.pdf` and `figs4/ham-comm-step2.pdf`, for the
product `h_1 h_2`: with `𝒫(A†) 𝒫(A) = c σ` and `A` invariant,
`∑_b tr[A^{s₀} A^{s₁} (A^{w₀} A^b)†] tr[A^b A^{s₂} (A^{w₁} A^{w₂})†] =
c tr[A^{s₀} A^{s₁} A^{s₂} (A^{w₀} A^{w₁} A^{w₂})†]`. The twirl `σ` places the sum over `g` of
figure `figs4/ham-comm-step1.pdf` on the virtual bond; it drops out since the remaining
operator commutes with every `L_g`. -/
theorem sum_trace_regularAdjoint_left {c : ℂ}
    (h : mpsAdjointSiteMap A ∘ₗ mpsSiteMap A =
      c • (linHom (leftRegular ℂ G) (leftRegular ℂ G)).averageMap)
    (hinv : ∀ g i, leftRegular ℂ G g * A i * leftRegular ℂ G g⁻¹ = A i)
    (s₀ s₁ s₂ w₀ w₁ w₂ : Fin d) :
    ∑ b, LinearMap.trace ℂ _ (A s₀ * A s₁ * regularAdjoint (A w₀ * A b)) *
        LinearMap.trace ℂ _ (A b * A s₂ * regularAdjoint (A w₁ * A w₂)) =
      c * LinearMap.trace ℂ _ (A s₀ * A s₁ * A s₂ * regularAdjoint (A w₀ * A w₁ * A w₂)) := by
  have hA : ∀ i g, Commute (leftRegular ℂ G g) (A i) := fun i g =>
    commute_leftRegular_of_conj (hinv g i)
  have hA' : ∀ i g, Commute (leftRegular ℂ G g) (regularAdjoint (A i)) := fun i =>
    commute_leftRegular_regularAdjoint (hA i)
  have hN : ∀ g, Commute (leftRegular ℂ G g)
      (A s₂ * regularAdjoint (A w₂) * regularAdjoint (A w₁)) := fun g =>
    ((hA s₂ g).mul_right (hA' w₂ g)).mul_right (hA' w₁ g)
  have key := sum_trace_mul_regularAdjoint_mul_trace h hN
    (regularAdjoint (A w₀) * A s₀ * A s₁)
  simp only [regularAdjoint_mul]
  refine (Finset.sum_congr rfl fun b _ => ?_).trans (key.trans ?_)
  · rw [← mul_assoc (A s₀ * A s₁), LinearMap.trace_mul_comm (g := regularAdjoint (A w₀))]
    simp only [mul_assoc]
  · rw [show regularAdjoint (A w₀) * A s₀ * A s₁ * (A s₂ * regularAdjoint (A w₂) *
        regularAdjoint (A w₁)) = regularAdjoint (A w₀) * (A s₀ * A s₁ * A s₂ *
        regularAdjoint (A w₂) * regularAdjoint (A w₁)) by simp only [mul_assoc],
      LinearMap.trace_mul_comm (f := regularAdjoint (A w₀))]
    simp only [mul_assoc]

/-- Source: arXiv:1001.3807, proof of Theorem 6.12, `Papers/1001.3807/paper_v3.tex`
lines 2138–2151, figures `figs4/ham-comm-step1.pdf` and `figs4/ham-comm-step2.pdf`, for the
product `h_2 h_1` (the right-hand side of figure `figs4/ham-comm-step1.pdf`): with
`𝒫(A†) 𝒫(A) = c σ` and `A` invariant,
`∑_b tr[A^{s₀} A^b (A^{w₀} A^{w₁})†] tr[A^{s₁} A^{s₂} (A^b A^{w₂})†] =
c tr[A^{s₀} A^{s₁} A^{s₂} (A^{w₀} A^{w₁} A^{w₂})†]`. -/
theorem sum_trace_regularAdjoint_right {c : ℂ}
    (h : mpsAdjointSiteMap A ∘ₗ mpsSiteMap A =
      c • (linHom (leftRegular ℂ G) (leftRegular ℂ G)).averageMap)
    (hinv : ∀ g i, leftRegular ℂ G g * A i * leftRegular ℂ G g⁻¹ = A i)
    (s₀ s₁ s₂ w₀ w₁ w₂ : Fin d) :
    ∑ b, LinearMap.trace ℂ _ (A s₀ * A b * regularAdjoint (A w₀ * A w₁)) *
        LinearMap.trace ℂ _ (A s₁ * A s₂ * regularAdjoint (A b * A w₂)) =
      c * LinearMap.trace ℂ _ (A s₀ * A s₁ * A s₂ * regularAdjoint (A w₀ * A w₁ * A w₂)) := by
  have hA : ∀ i g, Commute (leftRegular ℂ G g) (A i) := fun i g =>
    commute_leftRegular_of_conj (hinv g i)
  have hA' : ∀ i g, Commute (leftRegular ℂ G g) (regularAdjoint (A i)) := fun i =>
    commute_leftRegular_regularAdjoint (hA i)
  have hN : ∀ g, Commute (leftRegular ℂ G g)
      (regularAdjoint (A w₁) * regularAdjoint (A w₀) * A s₀) := fun g =>
    ((hA' w₁ g).mul_right (hA' w₀ g)).mul_right (hA s₀ g)
  have key := sum_trace_mul_regularAdjoint_mul_trace h hN
    (A s₁ * A s₂ * regularAdjoint (A w₂))
  simp only [regularAdjoint_mul]
  refine (Finset.sum_congr rfl fun b _ => ?_).trans (key.trans ?_)
  · rw [mul_comm, mul_assoc (A s₀), LinearMap.trace_mul_comm (f := A s₀)]
    simp only [mul_assoc]
  · rw [show A s₁ * A s₂ * regularAdjoint (A w₂) * (regularAdjoint (A w₁) *
        regularAdjoint (A w₀) * A s₀) = (A s₁ * A s₂ * regularAdjoint (A w₂) *
        regularAdjoint (A w₁) * regularAdjoint (A w₀)) * A s₀ by simp only [mul_assoc],
      LinearMap.trace_mul_comm (g := A s₀)]
    simp only [mul_assoc]

end ParentHamiltonian

section Chain

open MPSTensor

variable {d : ℕ} {A : Fin d → Module.End ℂ (MonoidAlgebra ℂ G)}

/-- Source: arXiv:1001.3807, proof of Lemma 6.11, `Papers/1001.3807/paper_v3.tex`
lines 2112–2120, figure `figs4/ham-proj-from-A-is-proj.pdf`. For a `G`-isometric MPS tensor,
`Γ_2 Γ_2† Γ_2 = c Γ_2` for a positive `c`, where `Γ_2(X) = tr[A^{s₀} A^{s₁} X]` parametrizes the
two-site space `𝒮_2`. The two-site tensor is `G`-isometric by Lemma 6.2
(`IsGIsometricMPS.concatTensor`). -/
theorem IsGIsometricMPS.groundSpaceMap_comp_regularMPSTensor (hA : IsGIsometricMPS A) :
    ∃ c : ℝ, 0 < c ∧
      groundSpaceMap (regularMPSTensor A) 2 ∘ₗ groundSpaceMapAdjoint (regularMPSTensor A) 2 ∘ₗ
          groundSpaceMap (regularMPSTensor A) 2 =
        (c : ℂ) • groundSpaceMap (regularMPSTensor A) 2 := by
  have hC := hA.concatTensor hA
  obtain ⟨c, hc, hC'⟩ := hC.exists_adjoint_comp
  refine ⟨c, hc, LinearMap.ext fun X => funext fun σ => ?_⟩
  rw [Matrix.eq_vecCons_fin_two σ]
  obtain ⟨X', rfl⟩ := regularBondMatrix.surjective X
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul,
    groundSpaceMap_apply, groundSpaceMapAdjoint_apply, Matrix.mul_sum, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, sum_cfg_two, evalWord_ofFn_two, regularMPSTensor,
    ← map_mul, ← regularBondMatrix_regularAdjoint, trace_regularBondMatrix]
  exact sum_trace_concatTensor_mul_trace_regularAdjoint hC' hC.isGInjective.invariant X' _ _

/-- Source: arXiv:1001.3807, Lemma 6.11, `Papers/1001.3807/paper_v3.tex` lines 2098–2125,
figures `figs4/ham-proj-from-A.pdf`, `figs4/ham-proj-from-A-is-proj.pdf` and
`figs4/ham-proj-from-A-pres-subspace.pdf`. For a `G`-isometric MPS tensor, the operator
`Γ_2 Γ_2†` of equation `eq:iso:ham-proj-from-A`, with matrix `tr[A^{s₀} A^{s₁} (A^{w₀} A^{w₁})†]`,
is up to a positive factor `c` a projector (`IsIdempotentElem`) with range `𝒮_2`, and the
two-site parent interaction is `h = 1 - c⁻¹ Γ_2 Γ_2†`. Self-adjointness, the last step of the
source's proof, is `MPSTensor.groundSpaceFrame_isHermitian`. -/
theorem IsGIsometricMPS.parentInteraction_regularMPSTensor (hA : IsGIsometricMPS A) :
    ∃ c : ℝ, 0 < c ∧
      IsIdempotentElem ((c : ℂ)⁻¹ • groundSpaceFrame (regularMPSTensor A) 2) ∧
      LinearMap.range (groundSpaceFrame (regularMPSTensor A) 2) =
        groundSpace (regularMPSTensor A) 2 ∧
      parentInteraction (regularMPSTensor A) 2 =
        1 - (c : ℂ)⁻¹ • groundSpaceFrame (regularMPSTensor A) 2 := by
  obtain ⟨c, hc, h⟩ := hA.groundSpaceMap_comp_regularMPSTensor
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  exact ⟨c, hc, isIdempotentElem_smul_groundSpaceFrame hc' h, range_groundSpaceFrame hc' h,
    parentInteraction_eq_one_sub_smul_groundSpaceFrame hc h⟩

/-- Source: arXiv:1001.3807, proof of Theorem 6.12, `Papers/1001.3807/paper_v3.tex`
lines 2138–2151, figures `figs4/ham-comm-step1.pdf` and `figs4/ham-comm-step2.pdf`. For a
`G`-isometric MPS tensor, the products of the operators `Γ_2 Γ_2†` on sites `1, 2` and on
sites `2, 3`, taken in either order, are both `c Γ_3 Γ_3†` for a positive `c`. -/
theorem IsGIsometricMPS.pairLift_groundSpaceFrame_regularMPSTensor (hA : IsGIsometricMPS A) :
    ∃ c : ℝ, 0 < c ∧
      leftPairLift (groundSpaceFrame (regularMPSTensor A) 2) *
          rightPairLift (groundSpaceFrame (regularMPSTensor A) 2) =
        (c : ℂ) • groundSpaceFrame (regularMPSTensor A) 3 ∧
      rightPairLift (groundSpaceFrame (regularMPSTensor A) 2) *
          leftPairLift (groundSpaceFrame (regularMPSTensor A) 2) =
        (c : ℂ) • groundSpaceFrame (regularMPSTensor A) 3 := by
  obtain ⟨c, hc, h⟩ := hA.exists_adjoint_comp
  refine ⟨c, hc, leftPairLift_mul_rightPairLift_groundSpaceFrame _ _ fun s₀ s₁ s₂ w₀ w₁ w₂ => ?_,
    rightPairLift_mul_leftPairLift_groundSpaceFrame _ _ fun s₀ s₁ s₂ w₀ w₁ w₂ => ?_⟩
  · simp only [regularMPSTensor, ← map_mul, ← regularBondMatrix_regularAdjoint,
      trace_regularBondMatrix]
    exact sum_trace_regularAdjoint_left h hA.invariant s₀ s₁ s₂ w₀ w₁ w₂
  · simp only [regularMPSTensor, ← map_mul, ← regularBondMatrix_regularAdjoint,
      trace_regularBondMatrix]
    exact sum_trace_regularAdjoint_right h hA.invariant s₀ s₁ s₂ w₀ w₁ w₂

/-- Source: arXiv:1001.3807, Theorem 6.12 (commuting parent Hamiltonians),
`Papers/1001.3807/paper_v3.tex` lines 2131–2153, for an MPS. For a `G`-isometric MPS tensor, the
two-site terms `h_i` of the parent Hamiltonian commute on every ring of `N ≥ 3` sites. -/
theorem IsGIsometricMPS.isNNCPH_regularMPSTensor (hA : IsGIsometricMPS A) {N : ℕ}
    (hN : 3 ≤ N) : IsNNCPH (regularMPSTensor A) N := by
  obtain ⟨c, hc, h⟩ := hA.groundSpaceMap_comp_regularMPSTensor
  obtain ⟨c', -, h₁, h₂⟩ := hA.pairLift_groundSpaceFrame_regularMPSTensor
  exact isNNCPH_of_pairLift_groundSpaceFrame hc h (h₁.trans h₂.symm) hN

end Chain

end PEPS
end TNLean
