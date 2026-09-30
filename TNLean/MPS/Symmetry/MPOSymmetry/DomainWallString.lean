/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSumPermutation
import TNLean.MPS.Symmetry.MPOSymmetry.DomainWallExchange

/-!
# Domain-wall string operators and their exchange relation

Garre-Rubio and Schuch (arXiv:2405.00439, Section III.E, `Papers/2405.00439/MPU-DW.tex` lines
1341--1425) create a pair of domain walls on a symmetry-broken ground state `|ψ_A⟩` by a
truncated string of the matrix product unitary `U` on sites `i, …, j`, whose open virtual legs
are closed by two endpoint tensors (`eq:DWophys`). The endpoint tensor at the left end is the
sum of two terms (`eq:defEndT`),

`V_B e_{AB} Â + V_A e_{BA} B̂`,

where `Â`, `B̂` are left inverses of the injective tensors `A`, `B` with separated supports and
`(W_B, V_B)`, `(W_A, V_A)` are the action tensors of `U` on `A` and `B` (`eq:Wdef`, where the
left action tensor `V_B` is written as `W_B` with a hat); the right
end is built in the same way from `W_B e_{BA} Â + W_A e_{AB} B̂`. On `|ψ_A⟩` the first terms act
and the string creates the state `|ψ(A-B-A)⟩` of `DWopmps`; on `|ψ_B⟩` the second terms act
and it creates `|ψ(B-A-B)⟩`. For two strings on sites `i₂ < i₁ < j₁ < j₂`, the two orders
differ by `c_{AB} c_{BA} = ω` (`signphysop`, lines 1667--1672): when the outer string acts
second it passes over the two walls created by the inner string and acquires both phases of
`eq:localcdef`, while the inner string acting second meets only the `B` region created by the
outer one.

The string operator of this file acts on the periodic chain of `L = k + 1 + l + 1 + n` sites,
with endpoints at the sites `k` and `k + 1 + l` (counted from zero) and the bulk `U` tensor on
the `l` sites between them. The endpoint tensors act on one site, as in the source at the
renormalization fixed point (lines 1358 and 1422--1425); away from the fixed point the source
blocks sites, which here is the choice of the physical alphabet.

The source prints `signphysop` as `O^{[i₁,j₁]} O^{[i₂,j₂]} |ψ_A⟩ = c_{AB}c_{BA}
O^{[i₂,j₂]} O^{[i₁,j₁]} |ψ_A⟩`; the computation above gives the phase on the other side,
`O^{[i₂,j₂]} O^{[i₁,j₁]} |ψ_A⟩ = c_{AB}c_{BA} O^{[i₁,j₁]} O^{[i₂,j₂]} |ψ_A⟩`. The two agree
when `(c_{AB} c_{BA})² = 1`, which the source derives from `U² = 1` (lines 837--839). The theorem
below is stated in the second form, which holds without that relation.

**Local fix (nondegenerate domain walls, blocked local action):** the exchange relation
`MPOTensor.GroupFamily.BlockActionData.wallString_mul_wallString_mulVec_mpv` is stated for
`IsDomainWallAction`, whose walls and phase are nonzero and whose local relation holds against
regions longer than a buffer, so the regions between the four walls are long; documented in
`docs/paper-gaps/gs24_domain_wall_nondegenerate.tex`.

The half-chain objects `O^{[i]}_x |ψ_A⟩` and the single-endpoint exchange `eq:z2int` (lines
1427--1659) are not formalized.

## Main definitions

* `MPOTensor.physPairing`: the composite `Â ∘ A` of two tensors read as maps between the
  virtual and the physical spaces; `Â` is a left inverse of `A` when it is one.
* `MPOTensor.leftEndpoint`, `MPOTensor.rightEndpoint`: one term of `eq:defEndT`.
* `MPOTensor.stringOperator`: the string operator of an operator tensor with two endpoint tensors
  on a window of the periodic chain.
* `MPOTensor.GroupFamily.IsSeparatingLeftInverse`: left inverses with separated supports.
* `MPOTensor.GroupFamily.BlockActionData.wallString`: the domain-wall string operator
  `O^{[i,j]}` of `eq:DWophys` and `eq:defEndT`.

## Main results

* `MPOTensor.stringOperator_mulVec_trace`: the string operator on a state given by a trace.
* `MPOTensor.GroupFamily.BlockActionData.wallString_mulVec_mpv_left`,
  `MPOTensor.GroupFamily.BlockActionData.wallString_mulVec_mpv_right`: `eq:DWophys`,
  `O^{[i,j]} |ψ_A⟩ = |ψ(A-B-A)⟩` and `O^{[i,j]} |ψ_B⟩ = |ψ(B-A-B)⟩`.
* `MPOTensor.GroupFamily.BlockActionData.wallString_mul_wallString_mulVec_mpv`: `signphysop`.

## References
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- Garre-Rubio, Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D₁ : ℕ}

/-! ### Left inverses and endpoint tensors -/

/-- The physical pairing `(α β, γ δ) ↦ ∑_σ P^σ_{αβ} Q^σ_{γδ}` of two families of matrices: the
composite of `Q`, read as the map `X ↦ (σ ↦ ∑ Q^σ_{γδ} X_{γδ})` from the virtual to the physical
space, with `P`, read as the map back. `P` is a left inverse of `Q` when this is the identity.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 1422--1425 (the left inverses
`Â`, `B̂` of the injective tensors `A`, `B`). -/
def physPairing {a b a' b' : ℕ} (P : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (Q : Fin d → Matrix (Fin a') (Fin b') ℂ) : Matrix (Fin a × Fin b) (Fin a' × Fin b') ℂ :=
  Matrix.of fun αβ γδ ↦ ∑ σ, P σ αβ.1 αβ.2 * Q σ γδ.1 γδ.2

/-- One term of the left endpoint tensor, `(V e Â)^{τσ}_a = ∑_{αβ} Â^σ_{αβ} (e^τ V)_{α,(a,β)}`:
the input leg `σ` is mapped by the left inverse `Â` to a pair of virtual indices, which are
closed by the domain wall `e` and the left action tensor `V`, leaving the output leg `τ` and the
bond `a` of the operator string.

Source: arXiv:2405.00439, `eq:defEndT`, `Papers/2405.00439/MPU-DW.tex` lines 1389--1420. -/
noncomputable def leftEndpoint {D D' : ℕ} (Â : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (e : Fin d → Matrix (Fin D) (Fin D') ℂ) (V : Matrix (Fin D') (Fin (D₁ * D)) ℂ) :
    Fin d → Fin d → Matrix (Fin 1) (Fin D₁) ℂ :=
  fun τ σ ↦ Matrix.of fun _ a ↦ ∑ α, ∑ β, Â σ α β * (e τ * V) α (finProdFinEquiv (a, β))

/-- One term of the right endpoint tensor, `(W f Â)^{τσ}_b = ∑_{αβ} Â^σ_{αβ} (W f^τ)_{(b,α),β}`,
the mirror image of `MPOTensor.leftEndpoint` with the right action tensor `W` and the domain
wall `f`.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` line 1421 ("correspondingly for the
right endpoint"). -/
noncomputable def rightEndpoint {D D' : ℕ} (Â : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (W : Matrix (Fin (D₁ * D)) (Fin D') ℂ) (f : Fin d → Matrix (Fin D') (Fin D) ℂ) :
    Fin d → Fin d → Matrix (Fin D₁) (Fin 1) ℂ :=
  fun τ σ ↦ Matrix.of fun b _ ↦ ∑ α, ∑ β, Â σ α β * (W * f τ) (finProdFinEquiv (b, α)) β

variable {m n n' : ℕ}

/-- The action `∑_{a'} E^{a a'} ⊗ C^{a'}` of a left endpoint tensor on a family of matrices, a
rectangular analogue of `MPOTensor.actRect` with bond dimension one on the left. -/
noncomputable def leftAct (E : Fin d → Fin d → Matrix (Fin 1) (Fin D₁) ℂ)
    (C : Fin d → Matrix (Fin m) (Fin n) ℂ) (a : Fin d) : Matrix (Fin m) (Fin (D₁ * n)) ℂ :=
  (∑ a', E a a' ⊗ₖ C a').submatrix (fun α ↦ (0, α)) finProdFinEquiv.symm

/-- The action `∑_{b'} F^{b b'} ⊗ C^{b'}` of a right endpoint tensor on a family of matrices, with
bond dimension one on the right. -/
noncomputable def rightAct (F : Fin d → Fin d → Matrix (Fin D₁) (Fin 1) ℂ)
    (C : Fin d → Matrix (Fin m) (Fin n) ℂ) (b : Fin d) : Matrix (Fin (D₁ * m)) (Fin n) ℂ :=
  (∑ b', F b b' ⊗ₖ C b').submatrix finProdFinEquiv.symm (fun β ↦ (0, β))

/-- The action of a left endpoint is additive in the endpoint. -/
theorem leftAct_add (E E' : Fin d → Fin d → Matrix (Fin 1) (Fin D₁) ℂ)
    (C : Fin d → Matrix (Fin m) (Fin n) ℂ) (a : Fin d) :
    leftAct (E + E') C a = leftAct E C a + leftAct E' C a := by
  ext α β
  simp [leftAct, Matrix.add_kronecker, Finset.sum_add_distrib]

/-- The action of a right endpoint is additive in the endpoint. -/
theorem rightAct_add (F F' : Fin d → Fin d → Matrix (Fin D₁) (Fin 1) ℂ)
    (C : Fin d → Matrix (Fin m) (Fin n) ℂ) (b : Fin d) :
    rightAct (F + F') C b = rightAct F C b + rightAct F' C b := by
  ext α β
  simp [rightAct, Matrix.add_kronecker, Finset.sum_add_distrib]

variable {D D' : ℕ}

/-- **A left endpoint on its tensor.** If `Â` is a left inverse of `C`, the endpoint term
`V e Â` acting on `C` is `e V`.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 1450--1489 (the endpoint acting
on `|ψ_A⟩` leaves `e_{AB} V_B`). -/
theorem leftAct_leftEndpoint (Â : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (e : Fin d → Matrix (Fin D) (Fin D') ℂ) (V : Matrix (Fin D') (Fin (D₁ * D)) ℂ)
    {C : Fin d → Matrix (Fin D) (Fin D) ℂ} (hC : physPairing Â C = 1) (a : Fin d) :
    leftAct (leftEndpoint Â e V) C a = e a * V := by
  ext γ s
  obtain ⟨⟨s, δ⟩, rfl⟩ := finProdFinEquiv.surjective s
  have h : ∀ α β : Fin D, ∑ σ, Â σ α β * C σ γ δ = if α = γ ∧ β = δ then 1 else 0 :=
    fun α β ↦ by
      simpa [physPairing, Matrix.one_apply] using congrFun (congrFun hC (α, β)) (γ, δ)
  simp only [leftAct, leftEndpoint, Matrix.submatrix_apply, Matrix.sum_apply,
    Matrix.kroneckerMap_apply, Matrix.of_apply, Equiv.symm_apply_apply]
  calc _ = ∑ α, ∑ β, (e a * V) α (finProdFinEquiv (s, β)) * ∑ c, Â c α β * C c γ δ := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun α _ ↦ ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun β _ ↦ Finset.sum_congr rfl fun c _ ↦ by ring
    _ = _ := by simp [h, ite_and]

/-- **A left endpoint on the other tensor.** If `Â ∘ C = 0`, the endpoint term `V e Â` acting on
`C` vanishes.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 1422--1425 (the two terms act
separately on `A` and `B`). -/
theorem leftAct_leftEndpoint_eq_zero (Â : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (e : Fin d → Matrix (Fin D) (Fin D') ℂ) (V : Matrix (Fin D') (Fin (D₁ * D)) ℂ)
    {C : Fin d → Matrix (Fin m) (Fin n) ℂ} (hC : physPairing Â C = 0) (a : Fin d) :
    leftAct (leftEndpoint Â e V) C a = 0 := by
  ext γ s
  obtain ⟨⟨s, δ⟩, rfl⟩ := finProdFinEquiv.surjective s
  have h : ∀ α β : Fin D, ∑ σ, Â σ α β * C σ γ δ = 0 :=
    fun α β ↦ by simpa [physPairing] using congrFun (congrFun hC (α, β)) (γ, δ)
  simp only [leftAct, leftEndpoint, Matrix.submatrix_apply, Matrix.sum_apply,
    Matrix.kroneckerMap_apply, Matrix.of_apply, Equiv.symm_apply_apply]
  calc _ = ∑ α, ∑ β, (e a * V) α (finProdFinEquiv (s, β)) * ∑ c, Â c α β * C c γ δ := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun α _ ↦ ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun β _ ↦ Finset.sum_congr rfl fun c _ ↦ by ring
    _ = _ := by simp [h]

/-- **A right endpoint on its tensor.** If `Â` is a left inverse of `C`, the endpoint term
`W f Â` acting on `C` is `W f`. -/
theorem rightAct_rightEndpoint (Â : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (W : Matrix (Fin (D₁ * D)) (Fin D') ℂ) (f : Fin d → Matrix (Fin D') (Fin D) ℂ)
    {C : Fin d → Matrix (Fin D) (Fin D) ℂ} (hC : physPairing Â C = 1) (b : Fin d) :
    rightAct (rightEndpoint Â W f) C b = W * f b := by
  ext t δ
  obtain ⟨⟨t, γ⟩, rfl⟩ := finProdFinEquiv.surjective t
  have h : ∀ α β : Fin D, ∑ σ, Â σ α β * C σ γ δ = if α = γ ∧ β = δ then 1 else 0 :=
    fun α β ↦ by
      simpa [physPairing, Matrix.one_apply] using congrFun (congrFun hC (α, β)) (γ, δ)
  simp only [rightAct, rightEndpoint, Matrix.submatrix_apply, Matrix.sum_apply,
    Matrix.kroneckerMap_apply, Matrix.of_apply, Equiv.symm_apply_apply]
  calc _ = ∑ α, ∑ β, (W * f b) (finProdFinEquiv (t, α)) β * ∑ c, Â c α β * C c γ δ := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun α _ ↦ ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun β _ ↦ Finset.sum_congr rfl fun c _ ↦ by ring
    _ = _ := by simp [h, ite_and]

/-- **A right endpoint on the other tensor.** If `Â ∘ C = 0`, the endpoint term `W f Â` acting
on `C` vanishes. -/
theorem rightAct_rightEndpoint_eq_zero (Â : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (W : Matrix (Fin (D₁ * D)) (Fin D') ℂ) (f : Fin d → Matrix (Fin D') (Fin D) ℂ)
    {C : Fin d → Matrix (Fin m) (Fin n) ℂ} (hC : physPairing Â C = 0) (b : Fin d) :
    rightAct (rightEndpoint Â W f) C b = 0 := by
  ext t δ
  obtain ⟨⟨t, γ⟩, rfl⟩ := finProdFinEquiv.surjective t
  have h : ∀ α β : Fin D, ∑ σ, Â σ α β * C σ γ δ = 0 :=
    fun α β ↦ by simpa [physPairing] using congrFun (congrFun hC (α, β)) (γ, δ)
  simp only [rightAct, rightEndpoint, Matrix.submatrix_apply, Matrix.sum_apply,
    Matrix.kroneckerMap_apply, Matrix.of_apply, Equiv.symm_apply_apply]
  calc _ = ∑ α, ∑ β, (W * f b) (finProdFinEquiv (t, α)) β * ∑ c, Â c α β * C c γ δ := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun α _ ↦ ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun β _ ↦ Finset.sum_congr rfl fun c _ ↦ by ring
    _ = _ := by simp [h]

/-- A left endpoint, the physical action of the bulk tensor, and a right endpoint compose into
the sum over input configurations of the string coefficients times the input chains. -/
theorem leftAct_mul_physAct_mul_rightAct {l r : ℕ} (E : Fin d → Fin d → Matrix (Fin 1) (Fin D₁) ℂ)
    (T : MPOTensor d D₁) (F : Fin d → Fin d → Matrix (Fin D₁) (Fin 1) ℂ)
    (C : Fin d → Matrix (Fin m) (Fin n) ℂ) (P : (Fin l → Fin d) → Matrix (Fin n) (Fin n') ℂ)
    (C' : Fin d → Matrix (Fin n') (Fin r) ℂ) (a : Fin d) (μ : Fin l → Fin d) (b : Fin d) :
    leftAct E C a * physAct T P μ * rightAct F C' b =
      ∑ a', ∑ μ', ∑ b', (E a a' * evalWord T (List.ofFn μ) (List.ofFn μ') * F b b') 0 0 •
        (C a' * P μ' * C' b') := by
  rw [leftAct, physAct, rightAct, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  simp only [Matrix.sum_mul, Matrix.mul_sum, ← Matrix.mul_kronecker_mul]
  ext α β
  simp only [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.kroneckerMap_apply,
    Matrix.smul_apply, smul_eq_mul]
  exact Fintype.sum_reverse_three _

/-! ### The string operator on a window -/

section StringOperator

variable {k l L : ℕ}

/-- The configurations of a chain of `k + 1 + l + 1 + n` sites, split at the sites `k` and
`k + 1 + l` into a left region, a site, a middle region, a site and a right region. -/
def wallSplit (k l n : ℕ) :
    (Fin k → Fin d) × Fin d × (Fin l → Fin d) × Fin d × (Fin n → Fin d) ≃
      (Fin (k + 1 + l + 1 + n) → Fin d) where
  toFun s := Fin.append (Fin.append (Fin.append (Fin.append s.1 ![s.2.1]) s.2.2.1)
    ![s.2.2.2.1]) s.2.2.2.2
  invFun τ :=
    (fun j : Fin k ↦ τ (Fin.castAdd n (Fin.castAdd 1 (Fin.castAdd l (Fin.castAdd 1 j)))),
      τ (Fin.castAdd n (Fin.castAdd 1 (Fin.castAdd l (Fin.natAdd k 0)))),
      (fun j : Fin l ↦ τ (Fin.castAdd n (Fin.castAdd 1 (Fin.natAdd (k + 1) j)))),
      τ (Fin.castAdd n (Fin.natAdd (k + 1 + l) 0)),
      (fun j : Fin n ↦ τ (Fin.natAdd (k + 1 + l + 1) j)))
  left_inv s := by
    obtain ⟨p, a, μ, b, q⟩ := s
    simp
  right_inv τ := (eq_append_append_append_append τ).symm

/-- The configurations of a chain of `L = k + 1 + l + 1 + n` sites, split at the sites `k` and
`k + 1 + l`. -/
def wallConfig {n : ℕ} (h : k + 1 + l + 1 + n = L) :
    (Fin k → Fin d) × Fin d × (Fin l → Fin d) × Fin d × (Fin n → Fin d) ≃ (Fin L → Fin d) :=
  (wallSplit k l n).trans (Equiv.arrowCongr (finCongr h) (Equiv.refl _))

/-- Reading a split configuration of `L` sites on `k + 1 + l + 1 + n` sites. -/
theorem wallConfig_comp_cast {n : ℕ} (h : k + 1 + l + 1 + n = L) (s) :
    wallConfig (d := d) h s ∘ Fin.cast h = wallSplit k l n s := by
  funext t
  simp [wallConfig, Equiv.arrowCongr_apply]

/-- The word of a split configuration. -/
theorem ofFn_wallConfig {n : ℕ} (h : k + 1 + l + 1 + n = L)
    (s : (Fin k → Fin d) × Fin d × (Fin l → Fin d) × Fin d × (Fin n → Fin d)) :
    List.ofFn (wallConfig h s) =
      List.ofFn s.1 ++ s.2.1 :: (List.ofFn s.2.2.1 ++ s.2.2.2.1 :: List.ofFn s.2.2.2.2) := by
  have : wallConfig h s = wallSplit k l n s ∘ Fin.cast h.symm := by
    funext t
    simp [wallConfig, Equiv.arrowCongr_apply]
  rw [this, Function.comp_def, ← List.ofFn_congr h]
  simp only [wallSplit, Equiv.coe_fn_mk, List.ofFn_fin_append]
  simp

/-- The kernel of the string operator on split configurations: the identity on the two outer
regions times the coefficient `E^{a a'} U^{μ μ'} F^{b b'}` of the string on the window. -/
noncomputable def stringKernel (T : MPOTensor d D₁) (E : Fin d → Fin d → Matrix (Fin 1) (Fin D₁) ℂ)
    (F : Fin d → Fin d → Matrix (Fin D₁) (Fin 1) ℂ) (k l n : ℕ) :
    Matrix ((Fin k → Fin d) × Fin d × (Fin l → Fin d) × Fin d × (Fin n → Fin d))
      ((Fin k → Fin d) × Fin d × (Fin l → Fin d) × Fin d × (Fin n → Fin d)) ℂ :=
  Matrix.of fun s s' ↦ (if s.1 = s'.1 then 1 else 0) * (if s.2.2.2.2 = s'.2.2.2.2 then 1 else 0) *
    (E s.2.1 s'.2.1 * evalWord T (List.ofFn s.2.2.1) (List.ofFn s'.2.2.1) *
      F s.2.2.2.1 s'.2.2.2.1) 0 0

/-- **The string operator** of an operator tensor `T` with a left endpoint tensor `E` and a right
endpoint tensor `F`, on the periodic chain of `L = k + 1 + l + 1 + n` sites: it acts by
`E T ⋯ T F` on the window of sites `k, …, k + 1 + l` and by the identity elsewhere.

Source: arXiv:2405.00439, `eq:DWophys`, `Papers/2405.00439/MPU-DW.tex` lines 1365--1386. -/
noncomputable def stringOperator (T : MPOTensor d D₁)
    (E : Fin d → Fin d → Matrix (Fin 1) (Fin D₁) ℂ) (F : Fin d → Fin d → Matrix (Fin D₁) (Fin 1) ℂ)
    (k l n : ℕ) (h : k + 1 + l + 1 + n = L) : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ :=
  (stringKernel T E F k l n).submatrix (wallConfig h).symm (wallConfig h).symm

/-- The string operator sums over the configurations of the window. -/
theorem stringOperator_mulVec_wallConfig (T : MPOTensor d D₁)
    (E : Fin d → Fin d → Matrix (Fin 1) (Fin D₁) ℂ) (F : Fin d → Fin d → Matrix (Fin D₁) (Fin 1) ℂ)
    {n : ℕ} (h : k + 1 + l + 1 + n = L) (ψ : (Fin L → Fin d) → ℂ) (p : Fin k → Fin d) (a : Fin d)
    (μ : Fin l → Fin d) (b : Fin d) (q : Fin n → Fin d) :
    (stringOperator T E F k l n h *ᵥ ψ) (wallConfig h (p, a, μ, b, q)) =
      ∑ a', ∑ μ', ∑ b', (E a a' * evalWord T (List.ofFn μ) (List.ofFn μ') * F b b') 0 0 *
        ψ (wallConfig h (p, a', μ', b', q)) := by
  rw [stringOperator, Matrix.submatrix_mulVec_equiv, Equiv.symm_symm, Function.comp_apply,
    Equiv.symm_apply_apply]
  simp only [Matrix.mulVec, dotProduct, stringKernel, Matrix.of_apply, Fintype.sum_prod_type,
    ite_mul, one_mul, zero_mul, Function.comp_apply]
  rw [Fintype.sum_eq_single p (fun x hx ↦ by simp [Ne.symm hx])]
  simp [Finset.sum_ite_eq]

/-- **The string operator on a state given by a trace.** If `ψ` is the trace of a chain
`X C P C' Y` split at the two endpoint sites, then the string operator acts on the chain
through the actions of its endpoints on `C` and `C'` and the physical action of its bulk tensor
on `P`. -/
theorem stringOperator_mulVec_trace {r m₁ m₂ m₃ m₄ n : ℕ} (T : MPOTensor d D₁)
    (E : Fin d → Fin d → Matrix (Fin 1) (Fin D₁) ℂ) (F : Fin d → Fin d → Matrix (Fin D₁) (Fin 1) ℂ)
    (h : k + 1 + l + 1 + n = L) (X : (Fin k → Fin d) → Matrix (Fin r) (Fin m₁) ℂ)
    (C : Fin d → Matrix (Fin m₁) (Fin m₂) ℂ) (P : (Fin l → Fin d) → Matrix (Fin m₂) (Fin m₃) ℂ)
    (C' : Fin d → Matrix (Fin m₃) (Fin m₄) ℂ) (Y : (Fin n → Fin d) → Matrix (Fin m₄) (Fin r) ℂ)
    (ψ : (Fin L → Fin d) → ℂ)
    (hψ : ∀ p a μ b q, ψ (wallConfig h (p, a, μ, b, q)) = (X p * C a * P μ * C' b * Y q).trace)
    (p : Fin k → Fin d) (a : Fin d) (μ : Fin l → Fin d) (b : Fin d) (q : Fin n → Fin d) :
    (stringOperator T E F k l n h *ᵥ ψ) (wallConfig h (p, a, μ, b, q)) =
      (X p * leftAct E C a * physAct T P μ * rightAct F C' b * Y q).trace := by
  rw [stringOperator_mulVec_wallConfig]
  simp only [hψ]
  rw [show X p * leftAct E C a * physAct T P μ * rightAct F C' b * Y q =
    X p * (leftAct E C a * physAct T P μ * rightAct F C' b) * Y q by
      simp only [Matrix.mul_assoc], leftAct_mul_physAct_mul_rightAct]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]

/-- The same configuration split at two pairs of sites `i₂ < i₁` and `j₁ < j₂`. -/
theorem wallConfig_resplit {u u' v w' w L : ℕ} (h₁ : u + 1 + u' + 1 + v + 1 + (w' + 1 + w) = L)
    (h₂ : u + 1 + (u' + 1 + v + 1 + w') + 1 + w = L) (p : Fin u → Fin d) (a : Fin d)
    (μ₁ : Fin u' → Fin d) (i : Fin d) (ν : Fin v → Fin d) (j : Fin d) (μ₃ : Fin w' → Fin d)
    (b : Fin d) (q : Fin w → Fin d) :
    wallConfig h₁ (Fin.append (Fin.append p ![a]) μ₁, i, ν, j, Fin.append (Fin.append μ₃ ![b]) q) =
      wallConfig h₂ (p, a, wallSplit u' v w' (μ₁, i, ν, j, μ₃), b, q) := by
  apply List.ofFn_injective
  rw [ofFn_wallConfig, ofFn_wallConfig]
  simp only [wallSplit, Equiv.coe_fn_mk, List.ofFn_fin_append]
  simp

/-- The open chain with two domain walls on an appended configuration. -/
theorem twoWallChain_append {D D' k l n : ℕ} (B : MPSTensor d D)
    (e : Fin d → Matrix (Fin D) (Fin D') ℂ)
    (C : MPSTensor d D') (f : Fin d → Matrix (Fin D') (Fin D) ℂ) (σ : Fin k → Fin d) (i : Fin d)
    (σ' : Fin l → Fin d) (j : Fin d) (σ'' : Fin n → Fin d) :
    twoWallChain B e C f (Fin.append (Fin.append (Fin.append (Fin.append σ ![i]) σ') ![j]) σ'') =
      Kraus.evalWord B (List.ofFn σ) * e i * Kraus.evalWord C (List.ofFn σ') * f j *
        Kraus.evalWord B (List.ofFn σ'') := by
  simp [twoWallChain, wallChain]

/-- The coefficient of a periodic matrix product state on a split configuration. -/
theorem mpv_wallConfig {D' : ℕ} (B : MPSTensor d D') {k l n L : ℕ} (h : k + 1 + l + 1 + n = L)
    (p : Fin k → Fin d) (a : Fin d) (μ : Fin l → Fin d) (b : Fin d) (q : Fin n → Fin d) :
    MPSTensor.mpv B (wallConfig h (p, a, μ, b, q)) =
      (Kraus.evalWord B (List.ofFn p) * B a * Kraus.evalWord B (List.ofFn μ) * B b *
        Kraus.evalWord B (List.ofFn q)).trace := by
  rw [MPSTensor.mpv_eq, MPSTensor.coeff, ofFn_wallConfig]
  simp [Kraus.evalWord_append, Kraus.evalWord_cons, Matrix.mul_assoc]

end StringOperator

/-! ### Domain-wall string operators of a group of matrix product operators -/

namespace GroupFamily

variable {G : Type} {X : Type*} [Group G] {F : GroupFamily G d} [MulAction G X] {D : X → ℕ}
  {A : (x : X) → MPSTensor d (D x)}

/-- **Left inverses with separated supports** (arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex`
lines 1422--1425): `Âx` and `Ây` are left inverses of `A_x` and `A_y`, and each annihilates the
other tensor, so that the two terms of an endpoint tensor act separately on the two ground
states. The source notes that the left inverses exist because the tensors are injective and
have orthogonal support at the renormalization fixed point. -/
structure IsSeparatingLeftInverse {x y : X} (Âx : Fin d → Matrix (Fin (D x)) (Fin (D x)) ℂ)
    (Ây : Fin d → Matrix (Fin (D y)) (Fin (D y)) ℂ) (Ax : MPSTensor d (D x))
    (Ay : MPSTensor d (D y)) : Prop where
  /-- `Âx` is a left inverse of `A_x`. -/
  left_left : physPairing Âx Ax = 1
  /-- `Âx` annihilates `A_y`. -/
  left_right : physPairing Âx Ay = 0
  /-- `Ây` is a left inverse of `A_y`. -/
  right_right : physPairing Ây Ay = 1
  /-- `Ây` annihilates `A_x`. -/
  right_left : physPairing Ây Ax = 0

namespace BlockActionData

variable (ad : BlockActionData F A) (g : G) {x y : X} (hxy : g • x = y) (hyx : g • y = x)
  (Âx : Fin d → Matrix (Fin (D x)) (Fin (D x)) ℂ) (Ây : Fin d → Matrix (Fin (D y)) (Fin (D y)) ℂ)
  (eAB : Fin d → Matrix (Fin (D x)) (Fin (D y)) ℂ) (eBA : Fin d → Matrix (Fin (D y)) (Fin (D x)) ℂ)

/-- **The left endpoint tensor** of a domain-wall string (arXiv:2405.00439, `eq:defEndT`,
`Papers/2405.00439/MPU-DW.tex` lines 1389--1420): `V_B e_{AB} Â + V_A e_{BA} B̂`, with the left
action tensors `V_B = V_{g,x}` of `g` on `A = A_x` and `V_A = V_{g,y}` on `B = A_y`, identified
with the bond spaces of `A_y` and `A_x` along `g • x = y` and `g • y = x`. -/
noncomputable def wallLeftEndpoint : Fin d → Fin d → Matrix (Fin 1) (Fin (F.bondDim g)) ℂ :=
  leftEndpoint Âx eAB (castIndex D hxy * ad.V g x) +
    leftEndpoint Ây eBA (castIndex D hyx * ad.V g y)

/-- **The right endpoint tensor** of a domain-wall string (arXiv:2405.00439,
`Papers/2405.00439/MPU-DW.tex` line 1421): `W_B e_{BA} Â + W_A e_{AB} B̂`, with the right action
tensors `W_B = W_{g,x}` and `W_A = W_{g,y}`. -/
noncomputable def wallRightEndpoint : Fin d → Fin d → Matrix (Fin (F.bondDim g)) (Fin 1) ℂ :=
  rightEndpoint Âx (ad.W g x * castIndex D hxy.symm) eBA +
    rightEndpoint Ây (ad.W g y * castIndex D hyx.symm) eAB

/-- **The domain-wall string operator** `O^{[i,j]}` (arXiv:2405.00439, `eq:DWophys`,
`Papers/2405.00439/MPU-DW.tex` lines 1365--1386): the string of `O_g` on the periodic chain of
`L = k + 1 + l + 1 + n` sites, with the endpoint tensors of `eq:defEndT` at the sites `i = k`
and `j = k + 1 + l`. -/
noncomputable def wallString {L : ℕ} (k l n : ℕ) (h : k + 1 + l + 1 + n = L) :
    Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ :=
  stringOperator (F.tensor g) (ad.wallLeftEndpoint g hxy hyx Âx Ây eAB eBA)
    (ad.wallRightEndpoint g hxy hyx Âx Ây eAB eBA) k l n h

variable {g hxy hyx Âx Ây eAB eBA}

/-- On `A_x` the left endpoint leaves `e_{AB} V_B`. -/
theorem leftAct_wallLeftEndpoint_left (hÂ : IsSeparatingLeftInverse Âx Ây (A x) (A y))
    (a : Fin d) :
    leftAct (ad.wallLeftEndpoint g hxy hyx Âx Ây eAB eBA) (A x) a =
      eAB a * (castIndex D hxy * ad.V g x) := by
  rw [wallLeftEndpoint, leftAct_add, leftAct_leftEndpoint _ _ _ hÂ.left_left,
    leftAct_leftEndpoint_eq_zero _ _ _ hÂ.right_left, add_zero]

/-- On `A_y` the left endpoint leaves `e_{BA} V_A`. -/
theorem leftAct_wallLeftEndpoint_right (hÂ : IsSeparatingLeftInverse Âx Ây (A x) (A y))
    (a : Fin d) :
    leftAct (ad.wallLeftEndpoint g hxy hyx Âx Ây eAB eBA) (A y) a =
      eBA a * (castIndex D hyx * ad.V g y) := by
  rw [wallLeftEndpoint, leftAct_add, leftAct_leftEndpoint _ _ _ hÂ.right_right,
    leftAct_leftEndpoint_eq_zero _ _ _ hÂ.left_right, zero_add]

/-- On `A_x` the right endpoint leaves `W_B e_{BA}`. -/
theorem rightAct_wallRightEndpoint_left (hÂ : IsSeparatingLeftInverse Âx Ây (A x) (A y))
    (b : Fin d) :
    rightAct (ad.wallRightEndpoint g hxy hyx Âx Ây eAB eBA) (A x) b =
      ad.W g x * castIndex D hxy.symm * eBA b := by
  rw [wallRightEndpoint, rightAct_add, rightAct_rightEndpoint _ _ _ hÂ.left_left,
    rightAct_rightEndpoint_eq_zero _ _ _ hÂ.right_left, add_zero]

/-- On `A_y` the right endpoint leaves `W_A e_{AB}`. -/
theorem rightAct_wallRightEndpoint_right (hÂ : IsSeparatingLeftInverse Âx Ây (A x) (A y))
    (b : Fin d) :
    rightAct (ad.wallRightEndpoint g hxy hyx Âx Ây eAB eBA) (A y) b =
      ad.W g y * castIndex D hyx.symm * eAB b := by
  rw [wallRightEndpoint, rightAct_add, rightAct_rightEndpoint _ _ _ hÂ.right_right,
    rightAct_rightEndpoint_eq_zero _ _ _ hÂ.left_right, zero_add]

/-- **The string creates two domain walls on `|ψ_A⟩`** (arXiv:2405.00439, `eq:DWophys`,
`Papers/2405.00439/MPU-DW.tex` lines 1365--1386, and lines 1387--1388): `O^{[i,j]} |ψ_A⟩ =
|ψ(A-B-A)⟩`, the state of `DWopmps` with the domain wall `e_{AB}` at `i` and `e_{BA}` at `j`,
on the periodic chain of every length `L ≥ 2`. The left inverses turn the endpoints into
`e_{AB} V_B` and `W_B e_{BA}`, and the action tensors reduce the string of `O_g · A` between
them to `B`. -/
theorem wallString_mulVec_mpv_left (hÂ : IsSeparatingLeftInverse Âx Ây (A x) (A y))
    {k l n L : ℕ} (h : k + 1 + l + 1 + n = L) :
    ad.wallString g hxy hyx Âx Ây eAB eBA k l n h *ᵥ (fun σ ↦ MPSTensor.mpv (A x) σ) =
      fun τ ↦ twoWallMPV (A x) eAB (A y) eBA (τ ∘ Fin.cast h) := by
  funext τ
  obtain ⟨⟨p, a, μ, b, q⟩, rfl⟩ := (wallConfig h).surjective τ
  rw [wallString, stringOperator_mulVec_trace _ _ _ h (fun p ↦ Kraus.evalWord (A x) (List.ofFn p))
    (A x) (fun μ ↦ Kraus.evalWord (A x) (List.ofFn μ)) (A x)
    (fun q ↦ Kraus.evalWord (A x) (List.ofFn q)) _ (fun p a μ b q ↦ mpv_wallConfig _ h p a μ b q),
    wallConfig_comp_cast, leftAct_wallLeftEndpoint_left ad hÂ,
    rightAct_wallRightEndpoint_left ad hÂ, physAct_evalWord]
  have hr := (isReduction_castIndex (ad.isReduction g x) hxy).evalWord (List.ofFn μ)
  rw [show wallSplit k l n (p, a, μ, b, q) = Fin.append (Fin.append (Fin.append (Fin.append p ![a])
    μ) ![b]) q from rfl, twoWallMPV_append, ← hr]
  simp only [Matrix.mul_assoc]

/-- **The string creates two domain walls on `|ψ_B⟩`** (arXiv:2405.00439,
`Papers/2405.00439/MPU-DW.tex` lines 1387--1388, with `eq:domain-walls-on-B`, lines 696--710):
`O^{[i,j]} |ψ_B⟩ = |ψ(B-A-B)⟩`, with the domain wall `e_{BA}` at `i` and `e_{AB}` at `j`. -/
theorem wallString_mulVec_mpv_right (hÂ : IsSeparatingLeftInverse Âx Ây (A x) (A y))
    {k l n L : ℕ} (h : k + 1 + l + 1 + n = L) :
    ad.wallString g hxy hyx Âx Ây eAB eBA k l n h *ᵥ (fun σ ↦ MPSTensor.mpv (A y) σ) =
      fun τ ↦ twoWallMPV (A y) eBA (A x) eAB (τ ∘ Fin.cast h) := by
  funext τ
  obtain ⟨⟨p, a, μ, b, q⟩, rfl⟩ := (wallConfig h).surjective τ
  rw [wallString, stringOperator_mulVec_trace _ _ _ h (fun p ↦ Kraus.evalWord (A y) (List.ofFn p))
    (A y) (fun μ ↦ Kraus.evalWord (A y) (List.ofFn μ)) (A y)
    (fun q ↦ Kraus.evalWord (A y) (List.ofFn q)) _ (fun p a μ b q ↦ mpv_wallConfig _ h p a μ b q),
    wallConfig_comp_cast, leftAct_wallLeftEndpoint_right ad hÂ,
    rightAct_wallRightEndpoint_right ad hÂ, physAct_evalWord]
  have hr := (isReduction_castIndex (ad.isReduction g y) hyx).evalWord (List.ofFn μ)
  rw [show wallSplit k l n (p, a, μ, b, q) = Fin.append (Fin.append (Fin.append (Fin.append p ![a])
    μ) ![b]) q from rfl, twoWallMPV_append, ← hr]
  simp only [Matrix.mul_assoc]

/-- **Exchange of two domain-wall strings** (arXiv:2405.00439, `signphysop`,
`Papers/2405.00439/MPU-DW.tex` lines 1667--1672): for strings on sites `i₂ < i₁ < j₁ < j₂`,
here `O^{[i₂,j₂]}` with endpoints at `u` and `u + 1 + u' + 1 + v + 1 + w'` and
`O^{[i₁,j₁]}` with endpoints at `u + 1 + u'` and `u + 1 + u' + 1 + v`,

`O^{[i₂,j₂]} O^{[i₁,j₁]} |ψ_A⟩ = c_{AB} c_{BA} O^{[i₁,j₁]} O^{[i₂,j₂]} |ψ_A⟩`

whenever the three regions between the walls are longer than a fixed buffer. Both sides are
multiples of the state with the four domain walls `e_{AB}`, `e_{BA}`, `e_{AB}`, `e_{BA}` at
`i₂, i₁, j₁, j₂`: the outer string acting second passes over the walls of the inner one and
acquires `c_{AB} c_{BA}` (`IsDomainWallAction.pair`), while the inner string acting second meets
only the `B` region. The source prints the phase on the other side. No hypothesis here forces
`g * g = 1` or `(c_{AB} c_{BA})² = 1`, so in general this is the source relation with
`c_{AB} c_{BA}` replaced by its inverse; the two agree exactly when `(c_{AB} c_{BA})² = 1`, as
for the involutive symmetries of lines 837--839. -/
theorem wallString_mul_wallString_mulVec_mpv
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x)))
    (hÂ : IsSeparatingLeftInverse Âx Ây (A x) (A y)) {cAB cBA : ℂ}
    (hAB : ad.IsDomainWallAction g hxy hyx eAB eBA cAB)
    (hBA : ad.IsDomainWallAction g hyx hxy eBA eAB cBA) :
    ∃ N : ℕ, ∀ (u u' v w' w L : ℕ) (h₁ : u + 1 + u' + 1 + v + 1 + (w' + 1 + w) = L)
      (h₂ : u + 1 + (u' + 1 + v + 1 + w') + 1 + w = L), N ≤ u' → N ≤ v → N ≤ w' →
      (ad.wallString g hxy hyx Âx Ây eAB eBA u (u' + 1 + v + 1 + w') w h₂ *
          ad.wallString g hxy hyx Âx Ây eAB eBA (u + 1 + u') v (w' + 1 + w) h₁) *ᵥ
          (fun σ ↦ MPSTensor.mpv (A x) σ) =
        (cAB * cBA) • ((ad.wallString g hxy hyx Âx Ây eAB eBA (u + 1 + u') v (w' + 1 + w) h₁ *
          ad.wallString g hxy hyx Âx Ây eAB eBA u (u' + 1 + v + 1 + w') w h₂) *ᵥ
            (fun σ ↦ MPSTensor.mpv (A x) σ)) := by
  obtain ⟨N, hN⟩ := BlockActionData.IsDomainWallAction.pair hperm hAB hBA
  refine ⟨N, fun u u' v w' w L h₁ h₂ hu' hv hw' ↦ ?_⟩
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, wallString_mulVec_mpv_left ad hÂ h₁,
    wallString_mulVec_mpv_left ad hÂ h₂]
  funext τ
  obtain ⟨⟨p, a, μ, b, q⟩, rfl⟩ := (wallConfig h₂).surjective τ
  obtain ⟨⟨μ₁, i, ν, j, μ₃⟩, rfl⟩ := (wallSplit u' v w').surjective μ
  -- the outer string passes over the two walls created by the inner one
  have hψ₁ : ∀ p a μ b q, twoWallMPV (A x) eAB (A y) eBA (wallConfig h₂ (p, a, μ, b, q) ∘
      Fin.cast h₁) = (Kraus.evalWord (A x) (List.ofFn p) * A x a *
        twoWallChain (A x) eAB (A y) eBA μ * A x b * Kraus.evalWord (A x) (List.ofFn q)).trace := by
    intro p a μ b q
    obtain ⟨⟨μ₁, i, ν, j, μ₃⟩, rfl⟩ := (wallSplit u' v w').surjective μ
    rw [← wallConfig_resplit h₁ h₂, wallConfig_comp_cast]
    rw [show ∀ s, wallSplit (d := d) u' v w' s = Fin.append (Fin.append (Fin.append
      (Fin.append s.1 ![s.2.1]) s.2.2.1) ![s.2.2.2.1]) s.2.2.2.2 from fun _ ↦ rfl,
      show ∀ s, wallSplit (d := d) (u + 1 + u') v (w' + 1 + w) s = Fin.append (Fin.append
        (Fin.append (Fin.append s.1 ![s.2.1]) s.2.2.1) ![s.2.2.2.1]) s.2.2.2.2 from fun _ ↦ rfl,
      twoWallMPV_append, twoWallChain_append]
    simp only [List.ofFn_fin_append]
    simp [Kraus.evalWord_append, Kraus.evalWord_cons, Matrix.mul_assoc]
  rw [wallString, stringOperator_mulVec_trace _ _ _ h₂
    (fun p ↦ Kraus.evalWord (A x) (List.ofFn p)) (A x) (twoWallChain (A x) eAB (A y) eBA) (A x)
    (fun q ↦ Kraus.evalWord (A x) (List.ofFn q)) _ hψ₁, leftAct_wallLeftEndpoint_left ad hÂ,
    rightAct_wallRightEndpoint_left ad hÂ,
    show wallSplit (d := d) u' v w' (μ₁, i, ν, j, μ₃) = Fin.append (Fin.append (Fin.append
      (Fin.append μ₁ ![i]) ν) ![j]) μ₃ from rfl, physAct_twoWallChain]
  have hpair := hN (List.ofFn μ₁) (List.ofFn ν) (List.ofFn μ₃) i j (by simpa using hu')
    (by simpa using hv) (by simpa using hw')
  have key := congrArg (fun M ↦ Kraus.evalWord (A x) (List.ofFn p) * eAB a * M *
    (eBA b * Kraus.evalWord (A x) (List.ofFn q))) hpair
  simp only [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul] at key
  simp only [Matrix.mul_assoc]
  rw [key]
  -- the inner string acts on the `B` region created by the outer one
  have hψ₂ : ∀ P' a' ν' b' Q', twoWallMPV (A x) eAB (A y) eBA
      (wallConfig h₁ (P', a', ν', b', Q') ∘ Fin.cast h₂) =
        (wallChain (A x) eAB (A y) P' * A y a' * Kraus.evalWord (A y) (List.ofFn ν') * A y b' *
          wallChain (A y) eBA (A x) Q').trace := by
    intro P' a' ν' b' Q'
    rw [eq_append_append P', eq_append_append Q', wallConfig_resplit h₁ h₂, wallConfig_comp_cast,
      show ∀ s, wallSplit (d := d) u' v w' s = Fin.append (Fin.append (Fin.append
      (Fin.append s.1 ![s.2.1]) s.2.2.1) ![s.2.2.2.1]) s.2.2.2.2 from fun _ ↦ rfl,
      show ∀ s, wallSplit (d := d) u (u' + 1 + v + 1 + w') w s = Fin.append (Fin.append
        (Fin.append (Fin.append s.1 ![s.2.1]) s.2.2.1) ![s.2.2.2.1]) s.2.2.2.2 from fun _ ↦ rfl,
      twoWallMPV_append, wallChain_append, wallChain_append]
    simp only [List.ofFn_fin_append]
    simp [Kraus.evalWord_append, Kraus.evalWord_cons, Matrix.mul_assoc]
  rw [Pi.smul_apply, show Fin.append (Fin.append (Fin.append (Fin.append μ₁ ![i]) ν) ![j]) μ₃ =
    wallSplit u' v w' (μ₁, i, ν, j, μ₃) from rfl, ← wallConfig_resplit h₁ h₂, wallString,
    stringOperator_mulVec_trace _ _ _ h₁
    (wallChain (A x) eAB (A y)) (A y) (fun ν ↦ Kraus.evalWord (A y) (List.ofFn ν)) (A y)
    (wallChain (A y) eBA (A x)) _ hψ₂, leftAct_wallLeftEndpoint_right ad hÂ,
    rightAct_wallRightEndpoint_right ad hÂ, physAct_evalWord, wallChain_append, wallChain_append]
  have hr := (isReduction_castIndex (ad.isReduction g y) hyx).evalWord (List.ofFn ν)
  rw [← hr]
  simp only [Matrix.mul_assoc, Matrix.trace_smul, smul_eq_mul]

end BlockActionData

end GroupFamily

end MPOTensor
