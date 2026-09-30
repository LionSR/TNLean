/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ScalarThreeCocycleCyclicInvariant
import TNLean.MPS.Symmetry.MPOSymmetry.PermutedBlocks

/-!
# Domain walls between blocks permuted by a group of matrix product operators

Let `g ↦ O_g` be a group of matrix product operators permuting normal matrix product state
tensors `A_x`, with action tensors `(V_{g,x}, W_{g,x})` reducing `O_g · A_x` onto
`A_{g • x}` (`MPOTensor.GroupFamily.BlockActionData`). A domain wall between the blocks `x` and
`y` is a rectangular tensor `e_{xy}` placed between an `A_x` region and an `A_y` region
(arXiv:2405.00439, `SingleDW`, `DWopmps`, lines 643--706, and the finite-group version at lines
1891--1895). The group acts locally on domain walls when

`V_{g,x} (O_g · (A_x^u e_{xy} A_y^v)) W_{g,y} = B^g_{x,y} A_{gx}^u e_{gx,gy} A_{gy}^v`

for all words `u`, `v` longer than a fixed buffer (`eq:localcdef`, lines 714--832, and
`eq:localcdefG`, lines 1896--1921). The source draws this identity at the renormalization fixed
point with one site on each side of the wall; away from the fixed point the buffers are the
blocks of the discussion at line 1358.

The main result is the fractionalization of the group action on domain walls (`PentLB`,
lines 1928--1933):

`B^g_{hx,hy} B^h_{x,y} = (Lˣ_{g,h} / L^y_{g,h}) B^{gh}_{x,y}`,

where `Lˣ_{g,h}` are the L-symbols of `MPOTensor.GroupFamily.BlockActionData.lSymbol`. For an
involution `g` exchanging two blocks `x` and `y = g • x`, the phases `c_{xy} = B^g_{x,y}` and
`c_{yx} = B^g_{y,x}` then satisfy `c_{xy} c_{yx} = ω(g,g,g) ω(g,1,g)`, which is the relation
`c_{AB} c_{BA} = L_A / L_B = ω` of `eq:Lsignrel` and `eq:CC-LL` (lines 895--1121) in the
normalization-free form; in the source normalization, where `ω` is trivial as soon as one
argument is the identity, this is `ω(g,g,g)`.

## Main definitions

* `MPOTensor.actRect`: the action `(O · e)^i = ∑_j O^{ij} ⊗ e^j` on a rectangular tensor.
* `MPOTensor.physAct`: the action of an operator tensor on a family of matrices indexed by
  physical configurations.
* `MPOTensor.wallChain`, `MPOTensor.twoWallChain`: open chains with one and two domain walls.
* `MPOTensor.twoWallMPV`: the periodic state `|ψ(A-B-A)⟩` with two domain walls (`DWopmps`).
* `MPOTensor.GroupFamily.BlockActionData.IsDomainWallAction`: the local action `eq:localcdef`.

## Main results

* `MPOTensor.GroupFamily.BlockActionData.IsDomainWallAction.mul_eq`: `PentLB`.
* `MPOTensor.GroupFamily.BlockActionData.IsDomainWallAction.mpo_mulVec_twoWallMPV`:
  `O_g |ψ(x-y-x)⟩ = c c' |ψ(gx-gy-gx)⟩`.
* `MPOTensor.GroupFamily.BlockActionData.IsDomainWallAction.mul_eq_lSymbol_of_mul_self_eq_one`
  and `...mul_eq_omega_of_mul_self_eq_one`: `c_{AB} c_{BA} = L_A / L_B = ω` for an
  involution, in the normalization-free form `ω(g,g,g) ω(g,1,g)`.
* `MPOTensor.GroupFamily.BlockActionData.IsDomainWallAction.mul_eq_mul_of_mul_self_eq_one`:
  gauge invariance of `c_{AB} c_{BA}`.
* `MPOTensor.GroupFamily.BlockActionData.IsDomainWallAction.mpo_mulVec_twoWallMPV_eq_omega`:
  `U |ψ(A-B-A)⟩ = ω |ψ(B-A-B)⟩`.

The blocks are normal rather than injective, and the phases are not assumed unimodular.

**Local fix (nondegenerate domain walls, blocked local action):** the local action
`IsDomainWallAction` requires both domain walls and the phase to be nonzero (the source's walls
are excitations and `c_{AB}`, `c_{BA}` are phase factors, lines 712 and 1656), and it holds
against regions longer than a buffer rather than at one site of the fixed point; documented in
`docs/paper-gaps/gs24_domain_wall_nondegenerate.tex`.

The group family need not have the bond-one identity tensor of the source, so the
identity element enters through its L-symbols `L_{1,1}` and through `ω(g,1,g)`, which are one in
the source's convention.

## References
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- Garre-Rubio, Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*
- [arXiv:1706.07329](https://arxiv.org/abs/1706.07329) -- Molnár, Ge, Schuch, Cirac,
  *A generalization of the injectivity condition for projected entangled pair states*
-/

open scoped Matrix Kronecker
open TNLean.Algebra

namespace MPOTensor

variable {d D₁ D₂ m n p : ℕ}

/-! ### The action on rectangular tensors and on configuration-indexed families -/

/-- The action of an operator tensor on a rectangular tensor, `(T · e)^i = ∑_j T^{ij} ⊗ e^j`,
with the bond conventions of `MPOTensor.actTensor`.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 774--832 (the MPU tensor
applied to the domain-wall tensor in `eq:localcdef`). -/
noncomputable def actRect (T : MPOTensor d D₁) (e : Fin d → Matrix (Fin m) (Fin n) ℂ)
    (i : Fin d) : Matrix (Fin (D₁ * m)) (Fin (D₁ * n)) ℂ :=
  (∑ j : Fin d, T i j ⊗ₖ e j).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

/-- The action of an operator tensor on a family of matrices indexed by the physical
configurations of a chain of length `L`:
`(T · P)(σ) = ∑_τ T^{σ τ} ⊗ P(τ)`, where `T^{σ τ}` is the operator word. -/
noncomputable def physAct (T : MPOTensor d D₁) {L : ℕ}
    (P : (Fin L → Fin d) → Matrix (Fin m) (Fin n) ℂ) (σ : Fin L → Fin d) :
    Matrix (Fin (D₁ * m)) (Fin (D₁ * n)) ℂ :=
  (∑ τ : Fin L → Fin d, evalWord T (List.ofFn σ) (List.ofFn τ) ⊗ₖ P τ).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm

section PhysAct

variable (T : MPOTensor d D₁) {L M : ℕ}

/-- Boundary matrices pass through the physical action as identity-tensored factors. -/
theorem physAct_mul_mul {m' n' : ℕ} (X : Matrix (Fin m') (Fin m) ℂ)
    (P : (Fin L → Fin d) → Matrix (Fin m) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n') ℂ)
    (σ : Fin L → Fin d) :
    physAct T (fun τ ↦ X * P τ * Y) σ = idKron D₁ X * physAct T P σ * idKron D₁ Y := by
  rw [physAct, physAct, idKron, idKron, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, Matrix.mul_sum, Matrix.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

/-- The physical action is linear in the family. -/
theorem physAct_smul (c : ℂ) (P : (Fin L → Fin d) → Matrix (Fin m) (Fin n) ℂ)
    (σ : Fin L → Fin d) : physAct T (fun τ ↦ c • P τ) σ = c • physAct T P σ := by
  simp only [physAct, Matrix.kronecker_smul, ← Finset.smul_sum]
  rfl

/-- On the word family of a state, the physical action is the word of the action tensor. -/
theorem physAct_evalWord {D : ℕ} (A : MPSTensor d D) (σ : Fin L → Fin d) :
    physAct T (fun τ ↦ Kraus.evalWord A (List.ofFn τ)) σ =
      Kraus.evalWord (actTensor T A) (List.ofFn σ) :=
  (evalWord_actTensor T A σ).symm

/-- On a single site, the physical action is the rectangular action. -/
theorem physAct_single (e : Fin d → Matrix (Fin m) (Fin n) ℂ) (σ : Fin 1 → Fin d) :
    physAct T (fun τ ↦ e (τ 0)) σ = actRect T e (σ 0) := by
  rw [physAct, actRect]
  congr 1
  rw [← (Equiv.funUnique (Fin 1) (Fin d)).symm.sum_comp]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp [List.ofFn_succ, evalWord]

/-- The physical action of a product of families on complementary segments is the product of
the physical actions. -/
theorem physAct_append (P : (Fin L → Fin d) → Matrix (Fin m) (Fin n) ℂ)
    (Q : (Fin M → Fin d) → Matrix (Fin n) (Fin p) ℂ) (σ : Fin L → Fin d)
    (σ' : Fin M → Fin d) :
    physAct T (fun τ ↦ P (fun k ↦ τ (Fin.castAdd M k)) * Q (fun k ↦ τ (Fin.natAdd L k)))
        (Fin.append σ σ') = physAct T P σ * physAct T Q σ' := by
  rw [physAct, physAct, physAct, Matrix.submatrix_mul_equiv, Matrix.sum_mul,
    ← (Fin.appendEquiv L M).sum_comp, ← Finset.univ_product_univ, Finset.sum_product]
  congr 1
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  rw [Matrix.mul_sum]
  refine Finset.sum_congr rfl fun τ' _ ↦ ?_
  rw [show (Fin.appendEquiv L M) (τ, τ') = Fin.append τ τ' from rfl]
  simp only [Fin.append_left, Fin.append_right, List.ofFn_fin_append]
  rw [evalWord_append T _ _ _ _ (by simp), Matrix.mul_kronecker_mul]

/-- **Associativity of the physical action.** The action of the stacked product `M N`,
reindexed by the bond associators, is the action of `M` on the action of `N`. -/
theorem physAct_mulTensor_submatrix (M : MPOTensor d D₁) (N : MPOTensor d D₂)
    (P : (Fin L → Fin d) → Matrix (Fin m) (Fin n) ℂ) (σ : Fin L → Fin d) :
    physAct (mulTensor M N) P σ =
      (physAct M (physAct N P) σ).submatrix (mulTensorAssocEquiv D₁ D₂ m)
        (mulTensorAssocEquiv D₁ D₂ n) := by
  ext x y
  rcases finProdFinEquiv.surjective x with ⟨⟨x₁₂, x₃⟩, rfl⟩
  rcases finProdFinEquiv.surjective x₁₂ with ⟨⟨x₁, x₂⟩, rfl⟩
  rcases finProdFinEquiv.surjective y with ⟨⟨y₁₂, y₃⟩, rfl⟩
  rcases finProdFinEquiv.surjective y₁₂ with ⟨⟨y₁, y₂⟩, rfl⟩
  simp only [physAct, evalWord_mulTensor, Matrix.submatrix_apply, Matrix.sum_apply,
    Matrix.kroneckerMap_apply, mulTensorAssocEquiv, Equiv.trans_apply, Equiv.prodCongr_apply,
    Prod.map_apply, Equiv.refl_apply, Equiv.prodAssoc_apply, Equiv.symm_apply_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ _ ↦ Finset.sum_congr rfl fun τ _ ↦ ?_
  ring

/-- **Associativity of the physical action**, as a conjugation by the bond associators. -/
theorem physAct_mulTensor (M : MPOTensor d D₁) (N : MPOTensor d D₂)
    (P : (Fin L → Fin d) → Matrix (Fin m) (Fin n) ℂ) (σ : Fin L → Fin d) :
    mulTensorAssocInvMatrix D₁ D₂ m * physAct (mulTensor M N) P σ *
        mulTensorAssocMatrix D₁ D₂ n = physAct M (physAct N P) σ := by
  rw [physAct_mulTensor_submatrix, mulTensorAssocInvMatrix, mulTensorAssocMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext a b
  simp

/-- **Fusion inside the physical action.** A reduction `(V, W)` of the operator `X` onto `Y`
reduces the physical action of `X` onto that of `Y`. -/
theorem physAct_kronId {X : MPOTensor d D₂} {Y : MPOTensor d D₁}
    {V : Matrix (Fin D₁) (Fin D₂) ℂ} {W : Matrix (Fin D₂) (Fin D₁) ℂ}
    (h : MPSTensor.IsReduction X.toMPSTensor Y.toMPSTensor V W)
    (P : (Fin L → Fin d) → Matrix (Fin m) (Fin n) ℂ) (σ : Fin L → Fin d) :
    kronId V m * physAct X P σ * kronId W n = physAct Y P σ := by
  rw [physAct, physAct, kronId, kronId, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, Matrix.mul_sum, Matrix.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  have hw := h.evalWord (List.ofFn fun k ↦ finProdFinEquiv (σ k, τ k))
  simp only [evalWord_toMPSTensor_pairConfig] at hw
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hw, Matrix.one_mul,
    Matrix.mul_one]

end PhysAct

/-! ### Chains with one domain wall -/

section WallChain

variable {D D' k l : ℕ}

/-- The open chain `A^u e^i B^v` with one domain wall `e` between an `A` region of `k` sites and
a `B` region of `l` sites, as a family indexed by the configurations of the `k + 1 + l` sites.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 643--667 (`SingleDW`). -/
noncomputable def wallChain (A : MPSTensor d D) (e : Fin d → Matrix (Fin D) (Fin D') ℂ)
    (B : MPSTensor d D') (τ : Fin (k + 1 + l) → Fin d) : Matrix (Fin D) (Fin D') ℂ :=
  Kraus.evalWord A (List.ofFn fun j : Fin k ↦ τ (Fin.castAdd l (Fin.castAdd 1 j))) *
      e (τ (Fin.castAdd l (Fin.natAdd k 0))) *
    Kraus.evalWord B (List.ofFn fun j : Fin l ↦ τ (Fin.natAdd (k + 1) j))

variable (A : MPSTensor d D) (e : Fin d → Matrix (Fin D) (Fin D') ℂ) (B : MPSTensor d D')

theorem wallChain_append (σ : Fin k → Fin d) (i : Fin d) (σ' : Fin l → Fin d) :
    wallChain A e B (Fin.append (Fin.append σ ![i]) σ') =
      Kraus.evalWord A (List.ofFn σ) * e i * Kraus.evalWord B (List.ofFn σ') := by
  simp [wallChain]

/-- Every configuration of `k + 1 + l` sites splits at the domain wall. -/
theorem eq_append_append (τ : Fin (k + 1 + l) → Fin d) :
    τ = Fin.append (Fin.append (fun j : Fin k ↦ τ (Fin.castAdd l (Fin.castAdd 1 j)))
      ![τ (Fin.castAdd l (Fin.natAdd k 0))]) fun j : Fin l ↦ τ (Fin.natAdd (k + 1) j) := by
  conv_lhs => rw [← Fin.append_castAdd_natAdd (f := τ)]
  congr 1
  conv_lhs => rw [← Fin.append_castAdd_natAdd (f := fun j : Fin (k + 1) ↦ τ (Fin.castAdd l j))]
  congr 1
  funext j
  fin_cases j
  rfl

/-- The physical action of an operator on a chain with one domain wall acts site by site: on
the two regions by the action tensors and on the wall by the rectangular action. -/
theorem physAct_wallChain (T : MPOTensor d D₁) (σ : Fin k → Fin d) (i : Fin d)
    (σ' : Fin l → Fin d) :
    physAct T (wallChain A e B) (Fin.append (Fin.append σ ![i]) σ') =
      Kraus.evalWord (actTensor T A) (List.ofFn σ) * actRect T e i *
        Kraus.evalWord (actTensor T B) (List.ofFn σ') := by
  have h := physAct_append T
    (fun ρ : Fin (k + 1) → Fin d ↦ Kraus.evalWord A (List.ofFn fun j ↦ ρ (Fin.castAdd 1 j)) *
      e (ρ (Fin.natAdd k 0)))
    (fun ρ : Fin l → Fin d ↦ Kraus.evalWord B (List.ofFn ρ)) (Fin.append σ ![i]) σ'
  have h' := physAct_append T (fun ρ : Fin k → Fin d ↦ Kraus.evalWord A (List.ofFn ρ))
    (fun ρ : Fin 1 → Fin d ↦ e (ρ 0)) σ ![i]
  rw [physAct_evalWord, physAct_single] at h'
  rw [physAct_evalWord, h'] at h
  exact h

/-- **Nonvanishing domain walls.** Between normal tensors, a nonzero domain wall has a nonzero
chain with arbitrarily long regions on both sides. -/
theorem exists_evalWord_mul_mul_evalWord_ne_zero (hA : Kraus.IsNormal A)
    (hB : Kraus.IsNormal B) (he : e ≠ 0) (N : ℕ) :
    ∃ (k l : ℕ) (σ : Fin k → Fin d) (i : Fin d) (σ' : Fin l → Fin d), N ≤ k ∧ N ≤ l ∧
      Kraus.evalWord A (List.ofFn σ) * e i * Kraus.evalWord B (List.ofFn σ') ≠ 0 := by
  obtain ⟨L, hL, hinj⟩ := hA
  obtain ⟨L', hL', hinj'⟩ := hB
  have hk := MPSTensor.isNBlkInjective_mul_of_isNBlkInjective A (Nat.succ_pos N) hinj
  have hl := MPSTensor.isNBlkInjective_mul_of_isNBlkInjective B (Nat.succ_pos N) hinj'
  obtain ⟨i, hi⟩ := Function.ne_iff.mp he
  by_contra hcon
  push Not at hcon
  have h1 : ∀ σ' : Fin ((N + 1) * L') → Fin d, e i * Kraus.evalWord B (List.ofFn σ') = 0 := by
    intro σ'
    have hmem : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ Submodule.span ℂ
        (Set.range fun σ : Fin ((N + 1) * L) → Fin d ↦ Kraus.evalWord A (List.ofFn σ)) := by
      rw [hk.span_eq_top]
      exact Submodule.mem_top
    have := Submodule.span_induction
      (p := fun M _ ↦ M * e i * Kraus.evalWord B (List.ofFn σ') = 0)
      (fun M hM ↦ by
        obtain ⟨σ, rfl⟩ := hM
        exact hcon _ _ σ i σ' (by nlinarith) (by nlinarith))
      (by simp) (fun M M' _ _ hM hM' ↦ by rw [Matrix.add_mul, Matrix.add_mul, hM, hM', add_zero])
      (fun c M _ hM ↦ by rw [Matrix.smul_mul, Matrix.smul_mul, hM, smul_zero]) hmem
    simpa [Matrix.mul_assoc] using this
  have hmem : (1 : Matrix (Fin D') (Fin D') ℂ) ∈ Submodule.span ℂ
      (Set.range fun σ' : Fin ((N + 1) * L') → Fin d ↦ Kraus.evalWord B (List.ofFn σ')) := by
    rw [hl.span_eq_top]
    exact Submodule.mem_top
  have := Submodule.span_induction (p := fun M _ ↦ e i * M = 0)
    (fun M hM ↦ by obtain ⟨σ', rfl⟩ := hM; exact h1 σ')
    (by simp) (fun M M' _ _ hM hM' ↦ by rw [Matrix.mul_add, hM, hM', add_zero])
    (fun c M _ hM ↦ by rw [Matrix.mul_smul, hM, smul_zero]) hmem
  exact hi (by simpa using this)

end WallChain

/-! ### Periodic states with two domain walls -/

section TwoWalls

variable {D D' k l n : ℕ}

/-- The trace of a physical action is the periodic operator applied to the traces. -/
theorem mpo_mulVec_trace (T : MPOTensor d D₁) {L : ℕ}
    (P : (Fin L → Fin d) → Matrix (Fin m) (Fin m) ℂ) :
    mpo T L *ᵥ (fun τ ↦ (P τ).trace) = fun σ ↦ (physAct T P σ).trace := by
  funext σ
  have htr : ∀ M : Matrix (Fin D₁ × Fin m) (Fin D₁ × Fin m) ℂ,
      (M.submatrix finProdFinEquiv.symm finProdFinEquiv.symm).trace = M.trace := fun M ↦ by
    simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
    exact finProdFinEquiv.symm.sum_comp fun j ↦ M j j
  rw [physAct, htr, Matrix.trace_sum]
  simp only [Matrix.mulVec, dotProduct, mpo_apply, mpoMatrixEntry, Matrix.trace_kronecker]

/-- The open chain `A^u e^i B^v f^j A^w` with two domain walls, on `k + 1 + l + 1 + n` sites. -/
noncomputable def twoWallChain (A : MPSTensor d D) (e : Fin d → Matrix (Fin D) (Fin D') ℂ)
    (B : MPSTensor d D') (f : Fin d → Matrix (Fin D') (Fin D) ℂ)
    (τ : Fin (k + 1 + l + 1 + n) → Fin d) : Matrix (Fin D) (Fin D) ℂ :=
  wallChain A e B (fun j : Fin (k + 1 + l) ↦ τ (Fin.castAdd n (Fin.castAdd 1 j))) *
      f (τ (Fin.castAdd n (Fin.natAdd (k + 1 + l) 0))) *
    Kraus.evalWord A (List.ofFn fun j : Fin n ↦ τ (Fin.natAdd (k + 1 + l + 1) j))

/-- **The periodic state with two domain walls** `|ψ(A-B-A)⟩`: an `A` region of `k` sites, the
domain wall `e`, a `B` region of `l` sites, the domain wall `f`, and an `A` region of `n`
sites, closed by the trace.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 675--706 (`DWopmps`), and the
state `|ψ(x,y)⟩` of lines 1891--1895. -/
noncomputable def twoWallMPV (A : MPSTensor d D) (e : Fin d → Matrix (Fin D) (Fin D') ℂ)
    (B : MPSTensor d D') (f : Fin d → Matrix (Fin D') (Fin D) ℂ)
    (τ : Fin (k + 1 + l + 1 + n) → Fin d) : ℂ :=
  (twoWallChain A e B f τ).trace

variable (A : MPSTensor d D) (e : Fin d → Matrix (Fin D) (Fin D') ℂ) (B : MPSTensor d D')
  (f : Fin d → Matrix (Fin D') (Fin D) ℂ)

/-- Every configuration of `k + 1 + l + 1 + n` sites splits at the two domain walls. -/
theorem eq_append_append_append_append (τ : Fin (k + 1 + l + 1 + n) → Fin d) :
    τ = Fin.append (Fin.append (Fin.append (Fin.append
      (fun j : Fin k ↦ τ (Fin.castAdd n (Fin.castAdd 1 (Fin.castAdd l (Fin.castAdd 1 j)))))
      ![τ (Fin.castAdd n (Fin.castAdd 1 (Fin.castAdd l (Fin.natAdd k 0))))])
      (fun j : Fin l ↦ τ (Fin.castAdd n (Fin.castAdd 1 (Fin.natAdd (k + 1) j)))))
      ![τ (Fin.castAdd n (Fin.natAdd (k + 1 + l) 0))])
      (fun j : Fin n ↦ τ (Fin.natAdd (k + 1 + l + 1) j)) := by
  conv_lhs => rw [← Fin.append_castAdd_natAdd (f := τ)]
  congr 1
  conv_lhs => rw [← Fin.append_castAdd_natAdd (f := fun j : Fin (k + 1 + l + 1) ↦
    τ (Fin.castAdd n j))]
  congr 1
  · exact eq_append_append (fun j : Fin (k + 1 + l) ↦ τ (Fin.castAdd n (Fin.castAdd 1 j)))
  · funext j
    fin_cases j
    rfl

theorem twoWallMPV_append (σ : Fin k → Fin d) (i : Fin d) (σ' : Fin l → Fin d) (j : Fin d)
    (σ'' : Fin n → Fin d) :
    twoWallMPV A e B f (Fin.append (Fin.append (Fin.append (Fin.append σ ![i]) σ') ![j]) σ'') =
      (Kraus.evalWord A (List.ofFn σ) * e i * Kraus.evalWord B (List.ofFn σ') * f j *
        Kraus.evalWord A (List.ofFn σ'')).trace := by
  simp [twoWallMPV, twoWallChain, wallChain]

/-- The physical action on a chain with two domain walls acts site by site. -/
theorem physAct_twoWallChain (T : MPOTensor d D₁) (σ : Fin k → Fin d) (i : Fin d)
    (σ' : Fin l → Fin d) (j : Fin d) (σ'' : Fin n → Fin d) :
    physAct T (twoWallChain A e B f)
        (Fin.append (Fin.append (Fin.append (Fin.append σ ![i]) σ') ![j]) σ'') =
      Kraus.evalWord (actTensor T A) (List.ofFn σ) * actRect T e i *
          Kraus.evalWord (actTensor T B) (List.ofFn σ') * actRect T f j *
        Kraus.evalWord (actTensor T A) (List.ofFn σ'') := by
  have h := physAct_append T
    (fun ρ : Fin (k + 1 + l + 1) → Fin d ↦
      wallChain A e B (fun j : Fin (k + 1 + l) ↦ ρ (Fin.castAdd 1 j)) *
        f (ρ (Fin.natAdd (k + 1 + l) 0)))
    (fun ρ : Fin n → Fin d ↦ Kraus.evalWord A (List.ofFn ρ))
    (Fin.append (Fin.append (Fin.append σ ![i]) σ') ![j]) σ''
  have h' := physAct_append T (wallChain A e B) (fun ρ : Fin 1 → Fin d ↦ f (ρ 0))
    (Fin.append (Fin.append σ ![i]) σ') ![j]
  rw [physAct_single, physAct_wallChain] at h'
  rw [physAct_evalWord, h'] at h
  exact h


/-- A word of length at least `2M + 1` splits into two outer pieces of length `M` and a nonempty
middle. -/
theorem _root_.List.exists_append_append_of_two_mul_lt {α : Type*} (w : List α) {M : ℕ}
    (hw : 2 * M < w.length) :
    ∃ p c q : List α, w = p ++ c ++ q ∧ p.length = M ∧ q.length = M ∧ c ≠ [] := by
  refine ⟨w.take M, (w.drop M).take (w.length - 2 * M), (w.drop M).drop (w.length - 2 * M),
    ?_, ?_, ?_, ?_⟩
  · simp only [List.take_append_drop, List.append_assoc]
  · simp only [List.length_take]; omega
  · simp only [List.length_drop]; omega
  · intro h
    have := congrArg List.length h
    simp only [List.length_take, List.length_drop, List.length_nil] at this
    omega

end TwoWalls

/-! ### The local action of a group on domain walls -/

namespace GroupFamily

variable {G : Type} {X : Type*} [Group G] {F : GroupFamily G d} [MulAction G X] {D : X → ℕ}
  {A : (x : X) → MPSTensor d (D x)}

namespace BlockActionData

variable (fd : FusionData F) (ad : BlockActionData F A)

/-- The right boundary of the reduction of `(O_g O_h) · A_x` onto `A_{g • (h • x)}` by two
successive action tensors, the partner of `MPOTensor.GroupFamily.BlockActionData.actV`.

Source: arXiv:2502.20257, `eq:defL`, `main.tex` lines 1905--1913. -/
noncomputable def actW (g h : G) (x : X) :
    Matrix (Fin (F.bondDim g * F.bondDim h * D x)) (Fin (D (g • h • x))) ℂ :=
  mulTensorAssocMatrix (F.bondDim g) (F.bondDim h) (D x) *
    (idKron (F.bondDim g) (ad.W h x) * ad.W g (h • x))

/-- The right boundary of the reduction of `(O_g O_h) · A_x` onto `A_{g • (h • x)}` through
the fusion tensor of `(g, h)`, the partner of `MPOTensor.GroupFamily.BlockActionData.fuseV`.

Source: arXiv:2502.20257, `eq:defL`, `main.tex` lines 1905--1913. -/
noncomputable def fuseW (g h : G) (x : X) :
    Matrix (Fin (F.bondDim g * F.bondDim h * D x)) (Fin (D (g • h • x))) ℂ :=
  kronId (fd.W g h) (D x) * ad.W (g * h) x * castIndex D (mul_smul g h x).symm

theorem isReduction_actV (g h : G) (x : X) : MPSTensor.IsReduction
    (actTensor (mulTensor (F.tensor g) (F.tensor h)) (A x)) (A (g • h • x)) (ad.actV g h x)
      (ad.actW g h x) :=
  (((ad.isReduction h x).actTensor_idKron (F.tensor g)).trans
    (ad.isReduction g (h • x))).actTensor_assoc_left

theorem isReduction_fuseV (g h : G) (x : X) : MPSTensor.IsReduction
    (actTensor (mulTensor (F.tensor g) (F.tensor h)) (A x)) (A (g • h • x))
      (ad.fuseV fd g h x) (ad.fuseW fd g h x) :=
  isReduction_castIndex (((fd.isReduction g h).actTensor_kronId (A x)).trans
    (ad.isReduction (g * h) x)) (mul_smul g h x)

variable {fd ad}

omit [Group G] [MulAction G X] in
private theorem exists_forall_le_of_forall_lt {P : List (Fin d) → Prop} {M : ℕ}
    (h : ∀ w : List (Fin d), M < w.length → P w) :
    ∃ N : ℕ, ∀ w : List (Fin d), N ≤ w.length → P w :=
  ⟨M + 1, fun w hw ↦ h w (by omega)⟩

/-- **The L-symbols on the right boundaries.** Against long words, the right boundary of two
successive actions is `(Lˣ_{g,h})⁻¹` times the right boundary through the fusion tensor. This
is the right half of the two-sided comparison of reductions onto a normal tensor
(arXiv:1706.07329v2, Theorem 22, `cornerproblem.tex` lines 3156--3162), with the scalar
identified with the L-symbol of `MPOTensor.GroupFamily.BlockActionData.lSymbol`. -/
theorem exists_evalWord_mul_actW_eq (hA : ∀ x, Kraus.IsNormal (A x))
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x))) (g h : G) (x : X)
    (hD : 0 < D (g • h • x)) :
    ∃ N : ℕ, ∀ w : List (Fin d), N ≤ w.length →
      Kraus.evalWord (actTensor (mulTensor (F.tensor g) (F.tensor h)) (A x)) w *
          ad.actW g h x =
        ((ad.lSymbol fd x g h)⁻¹ : ℂˣ) •
          (Kraus.evalWord (actTensor (mulTensor (F.tensor g) (F.tensor h)) (A x)) w *
            ad.fuseW fd g h x) := by
  have hSame : MPSTensor.SameMPV₂Pos (actTensor (mulTensor (F.tensor g) (F.tensor h)) (A x))
      (A (g • h • x)) :=
    ((hperm g _).mulTensor (hperm h x)).sameMPV₂Pos_actTensor (MPSTensor.SameMPV₂Pos.refl _)
  obtain ⟨z, -, hz⟩ :=
    (ad.isReduction_actV g h x).exists_boundary_dressed_proportional_of_nilpotencyLength_le
      (ad.isReduction_fuseV fd g h x) (hA _) hSame (le_max_left _ _) (le_max_right _ _)
  obtain ⟨N, hN⟩ := exists_forall_le_of_forall_lt hz
  have hleft : MPSTensor.IsDressedProportional
      (actTensor (mulTensor (F.tensor g) (F.tensor h)) (A x)) (ad.actV g h x)
        (ad.fuseV fd g h x) z :=
    ⟨N, fun w hw ↦ (hN w hw).1⟩
  have hzL : ((ad.lSymbol fd x g h : ℂˣ) : ℂ) = z :=
    MPSTensor.IsDressedProportional.eq_of_forall_exists_ne_zero
      (isDressedProportional_lSymbol hA hperm x g h) hleft
      ((ad.isReduction_actV g h x).exists_mul_evalWord_ne_zero (hA _) hD)
  refine ⟨N, fun w hw ↦ ?_⟩
  rw [(hN w hw).2, Units.smul_def, Units.val_inv_eq_inv_val, hzL]

variable (ad) in
/-- **The local action of a group element on a domain wall** (arXiv:2405.00439,
`eq:localcdef`, `Papers/2405.00439/MPU-DW.tex` lines 714--832, and `eq:localcdefG`, lines
1896--1921). The action tensors of `g` on the two regions, applied to `O_g` acting on the chain
`A_x^u e^i A_y^v` with one domain wall `e` between `x` and `y`, give `c` times the chain
`A_{x'}^u e'^i A_{y'}^v` with the domain wall `e'` between `x' = g • x` and `y' = g • y`,
for all words `u`, `v` longer than a fixed buffer. The target blocks are identified with
`g • x` and `g • y` along the given equations.

The source draws this identity with one site on each side of the wall (lines 774--832), in the
setting of the renormalization fixed point (lines 1351 and 1358); the buffer here plays the
role of the blocked sites of line 1358. The scalar `c` is `c_{AB}` of `eq:localcdef` for `ℤ₂` and `B^g_{x,y}` of
`eq:localcdefG` for a general group. Both walls and the phase are nonzero, the convention of
the module docstring. -/
structure IsDomainWallAction (g : G) {x y x' y' : X} (hx : g • x = x') (hy : g • y = y')
    (e : Fin d → Matrix (Fin (D x)) (Fin (D y)) ℂ)
    (e' : Fin d → Matrix (Fin (D x')) (Fin (D y')) ℂ) (c : ℂ) : Prop where
  /-- The carried domain wall is nonzero. -/
  source_ne_zero : e ≠ 0
  /-- The image domain wall is nonzero. -/
  target_ne_zero : e' ≠ 0
  /-- The phase is nonzero. -/
  phase_ne_zero : c ≠ 0
  /-- The local relation against long regions. -/
  eq : ∃ N : ℕ, ∀ (u v : List (Fin d)) (i : Fin d), N ≤ u.length → N ≤ v.length →
    castIndex D hx * (ad.V g x * (Kraus.evalWord (actTensor (F.tensor g) (A x)) u *
        actRect (F.tensor g) e i * Kraus.evalWord (actTensor (F.tensor g) (A y)) v) *
          ad.W g y) * castIndex D hy.symm =
      c • (Kraus.evalWord (A x') u * e' i * Kraus.evalWord (A y') v)

namespace IsDomainWallAction

variable {g h : G} {x y x' y' : X} {hx : g • x = x'} {hy : g • y = y'}
  {e : Fin d → Matrix (Fin (D x)) (Fin (D y)) ℂ} {e' : Fin d → Matrix (Fin (D x')) (Fin (D y')) ℂ}
  {c : ℂ}

/-- The local action on domain walls, stated for the configuration-indexed chains. -/
theorem physAct_eq (hg : ad.IsDomainWallAction g hx hy e e' c) :
    ∃ N : ℕ, ∀ k l : ℕ, N ≤ k → N ≤ l → ∀ τ : Fin (k + 1 + l) → Fin d,
      castIndex D hx * (ad.V g x * physAct (F.tensor g) (wallChain (A x) e (A y)) τ *
          ad.W g y) * castIndex D hy.symm = c • wallChain (A x') e' (A y') τ := by
  obtain ⟨N, hN⟩ := hg.eq
  refine ⟨N, fun k l hk hl τ ↦ ?_⟩
  rw [eq_append_append τ, physAct_wallChain, wallChain_append]
  exact hN _ _ _ (by simpa using hk) (by simpa using hl)

/-- The local action on domain walls depends on the group element only through its value. -/
theorem congr_elem (hg : ad.IsDomainWallAction g hx hy e e' c) {g' : G} (hgg' : g = g')
    (hx' : g' • x = x') (hy' : g' • y = y') : ad.IsDomainWallAction g' hx' hy' e e' c := by
  subst hgg'
  exact hg

/-- **The phase of a local action is unique** between normal blocks. -/
theorem phase_eq (hA : ∀ x, Kraus.IsNormal (A x)) {c' : ℂ}
    (h : ad.IsDomainWallAction g hx hy e e' c) (h' : ad.IsDomainWallAction g hx hy e e' c') :
    c = c' := by
  obtain ⟨N, hN⟩ := h.eq
  obtain ⟨N', hN'⟩ := h'.eq
  obtain ⟨k, l, σ, i, σ', hk, hl, hne⟩ := exists_evalWord_mul_mul_evalWord_ne_zero
    (A x') e' (A y') (hA _) (hA _) h.target_ne_zero (N + N')
  have h₁ := hN (List.ofFn σ) (List.ofFn σ') i (by simp only [List.length_ofFn]; omega)
    (by simp only [List.length_ofFn]; omega)
  have h₂ := hN' (List.ofFn σ) (List.ofFn σ') i (by simp only [List.length_ofFn]; omega)
    (by simp only [List.length_ofFn]; omega)
  exact smul_left_injective ℂ hne (h₁.symm.trans h₂)

/-- **Composition of local actions on domain walls** (arXiv:2405.00439,
`Papers/2405.00439/MPU-DW.tex` lines 1926--1929): if `h` carries the domain wall `e₁` between
`x` and `y` to `e₂` with phase `b₁`, and `g` carries `e₂` to `e₃` with phase `b₂`, then `gh`
carries `e₁` to `e₃` with phase `(L^y_{g,h} / Lˣ_{g,h}) b₂ b₁`.

The proof compares the two reductions of `(O_g O_h)` acting on a chain with one domain wall, by
two successive local actions and through the fusion tensor of `(g, h)`; the L-symbols enter on
the two sides of the wall, on the left boundary with `Lˣ_{g,h}` and on the right boundary with
`(L^y_{g,h})⁻¹`. -/
theorem mul (hA : ∀ x, Kraus.IsNormal (A x))
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x))) {x₂ y₂ x₃ y₃ : X}
    {hx₂ : h • x = x₂} {hy₂ : h • y = y₂} {hx₃ : g • x₂ = x₃} {hy₃ : g • y₂ = y₃}
    (hx₃' : (g * h) • x = x₃) (hy₃' : (g * h) • y = y₃)
    {e₁ : Fin d → Matrix (Fin (D x)) (Fin (D y)) ℂ}
    {e₂ : Fin d → Matrix (Fin (D x₂)) (Fin (D y₂)) ℂ}
    {e₃ : Fin d → Matrix (Fin (D x₃)) (Fin (D y₃)) ℂ} {b₁ b₂ : ℂ}
    (h₁ : ad.IsDomainWallAction h hx₂ hy₂ e₁ e₂ b₁)
    (h₂ : ad.IsDomainWallAction g hx₃ hy₃ e₂ e₃ b₂) :
    ad.IsDomainWallAction (g * h) hx₃' hy₃' e₁ e₃
      (((ad.lSymbol fd y g h / ad.lSymbol fd x g h : ℂˣ) : ℂ) * b₂ * b₁) := by
  subst hx₂ hy₂ hx₃ hy₃
  have hDy : 0 < D (g • h • y) := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h₂.target_ne_zero
    rcases Nat.eq_zero_or_pos (D (g • h • y)) with h0 | h0
    · exact absurd (Matrix.ext fun _ b ↦ absurd b.2 (by omega)) hi
    · exact h0
  refine ⟨h₁.source_ne_zero, h₂.target_ne_zero,
    mul_ne_zero (mul_ne_zero (Units.ne_zero _) h₂.phase_ne_zero) h₁.phase_ne_zero, ?_⟩
  obtain ⟨N₁, H₁⟩ := h₁.physAct_eq
  obtain ⟨N₂, H₂⟩ := h₂.physAct_eq
  obtain ⟨N₄, H₄⟩ := isDressedProportional_lSymbol (fd := fd) (ad := ad) hA hperm x g h
  obtain ⟨N₅, H₅⟩ := exists_evalWord_mul_actW_eq (fd := fd) (ad := ad) hA hperm g h y hDy
  refine ⟨N₁ + N₂ + N₄ + N₅, fun u v i hu hv ↦ ?_⟩
  set k := u.length
  set l := v.length
  set σ : Fin k → Fin d := fun j ↦ u.get j
  set σ' : Fin l → Fin d := fun j ↦ v.get j
  have hσ : List.ofFn σ = u := List.ofFn_get u
  have hσ' : List.ofFn σ' = v := List.ofFn_get v
  set τ : Fin (k + 1 + l) → Fin d := Fin.append (Fin.append σ ![i]) σ'
  set P := physAct (mulTensor (F.tensor g) (F.tensor h)) (wallChain (A x) e₁ (A y)) τ
  -- two successive local actions
  have e1 : (fun ρ : Fin (k + 1 + l) → Fin d ↦
      ad.V h x * physAct (F.tensor h) (wallChain (A x) e₁ (A y)) ρ * ad.W h y) =
      fun ρ ↦ b₁ • wallChain (A (h • x)) e₂ (A (h • y)) ρ := by
    funext ρ
    simpa [Matrix.mul_assoc] using H₁ k l (by omega) (by omega) ρ
  have e2 := congrArg (fun Q ↦ physAct (F.tensor g) Q τ) e1
  rw [physAct_mul_mul, physAct_smul, ← physAct_mulTensor] at e2
  have e3 := H₂ k l (by omega) (by omega) τ
  simp only [castIndex_rfl, Matrix.one_mul, Matrix.mul_one] at e3
  have hdouble : ad.actV g h x * P * ad.actW g h y =
      (b₁ * b₂) • wallChain (A (g • h • x)) e₃ (A (g • h • y)) τ := by
    calc ad.actV g h x * P * ad.actW g h y
        = ad.V g (h • x) * (idKron (F.bondDim g) (ad.V h x) *
            (mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h) (D x) * P *
              mulTensorAssocMatrix (F.bondDim g) (F.bondDim h) (D y)) *
            idKron (F.bondDim g) (ad.W h y)) * ad.W g (h • y) := by
          simp only [actV, actW, Matrix.mul_assoc]
      _ = (b₁ * b₂) • wallChain (A (g • h • x)) e₃ (A (g • h • y)) τ := by
          rw [e2, Matrix.mul_smul, Matrix.smul_mul, e3]
          exact smul_smul _ _ _
  -- the fused local action
  have hfused : ad.fuseV fd g h x * P * ad.fuseW fd g h y =
      castIndex D hx₃' * (ad.V (g * h) x *
        (Kraus.evalWord (actTensor (F.tensor (g * h)) (A x)) u *
          actRect (F.tensor (g * h)) e₁ i *
            Kraus.evalWord (actTensor (F.tensor (g * h)) (A y)) v) * ad.W (g * h) y) *
        castIndex D hy₃'.symm := by
    rw [← hσ, ← hσ', ← physAct_wallChain, ← physAct_kronId (fd.isReduction g h)]
    simp only [fuseV, fuseW, P, Matrix.mul_assoc]
    rfl
  -- the L-symbols on the two sides of the wall
  have hL := H₄ u (by omega)
  have hR := H₅ v (by omega)
  have hP : P = Kraus.evalWord (actTensor (mulTensor (F.tensor g) (F.tensor h)) (A x)) u *
      actRect (mulTensor (F.tensor g) (F.tensor h)) e₁ i *
        Kraus.evalWord (actTensor (mulTensor (F.tensor g) (F.tensor h)) (A y)) v := by
    rw [← hσ, ← hσ']
    exact physAct_wallChain _ _ _ _ σ i σ'
  have key : ad.actV g h x * P * ad.actW g h y =
      (((ad.lSymbol fd x g h / ad.lSymbol fd y g h : ℂˣ) : ℂ)) •
        (ad.fuseV fd g h x * P * ad.fuseW fd g h y) := by
    rw [hP]
    calc _ = ad.actV g h x * Kraus.evalWord
            (actTensor (mulTensor (F.tensor g) (F.tensor h)) (A x)) u *
          actRect (mulTensor (F.tensor g) (F.tensor h)) e₁ i *
          (Kraus.evalWord (actTensor (mulTensor (F.tensor g) (F.tensor h)) (A y)) v *
            ad.actW g h y) := by simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hL, hR]
          simp only [Units.smul_def, Units.val_mul, Units.val_inv_eq_inv_val, Matrix.smul_mul,
            Matrix.mul_smul, smul_smul, Matrix.mul_assoc, div_eq_mul_inv]
          rw [mul_comm]
  have hW : wallChain (A (g • h • x)) e₃ (A (g • h • y)) τ =
      Kraus.evalWord (A (g • h • x)) u * e₃ i * Kraus.evalWord (A (g • h • y)) v := by
    rw [← hσ, ← hσ']
    exact wallChain_append _ _ _ σ i σ'
  rw [← hfused]
  rw [hdouble, hW] at key
  have hinv : ((ad.lSymbol fd y g h / ad.lSymbol fd x g h : ℂˣ) : ℂ) *
      ((ad.lSymbol fd x g h / ad.lSymbol fd y g h : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul]
    simp
  calc ad.fuseV fd g h x * P * ad.fuseW fd g h y
      = (((ad.lSymbol fd y g h / ad.lSymbol fd x g h : ℂˣ) : ℂ) *
          ((ad.lSymbol fd x g h / ad.lSymbol fd y g h : ℂˣ) : ℂ)) •
          (ad.fuseV fd g h x * P * ad.fuseW fd g h y) := by rw [hinv, one_smul]
    _ = ((ad.lSymbol fd y g h / ad.lSymbol fd x g h : ℂˣ) : ℂ) • ((b₁ * b₂) •
          (Kraus.evalWord (A (g • h • x)) u * e₃ i * Kraus.evalWord (A (g • h • y)) v)) := by
        rw [← smul_smul, ← key]
    _ = _ := (smul_smul _ _ _).trans (by congr 1; ring)

/-- **Fractionalization of the group action on domain walls** (arXiv:2405.00439, `PentLB`,
`Papers/2405.00439/MPU-DW.tex` lines 1928--1933): if `h` carries the domain wall `e₁` between
`x` and `y` to `e₂` with phase `B^h_{x,y}`, `g` carries `e₂` to `e₃` with phase
`B^g_{hx,hy}`, and `gh` carries `e₁` to `e₃` with phase `B^{gh}_{x,y}`, then
`B^g_{hx,hy} B^h_{x,y} = (Lˣ_{g,h} / L^y_{g,h}) B^{gh}_{x,y}`. -/
theorem mul_eq (hA : ∀ x, Kraus.IsNormal (A x))
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x))) {x₂ y₂ x₃ y₃ : X}
    {hx₂ : h • x = x₂} {hy₂ : h • y = y₂} {hx₃ : g • x₂ = x₃} {hy₃ : g • y₂ = y₃}
    {hx₃' : (g * h) • x = x₃} {hy₃' : (g * h) • y = y₃}
    {e₁ : Fin d → Matrix (Fin (D x)) (Fin (D y)) ℂ}
    {e₂ : Fin d → Matrix (Fin (D x₂)) (Fin (D y₂)) ℂ}
    {e₃ : Fin d → Matrix (Fin (D x₃)) (Fin (D y₃)) ℂ} {b₁ b₂ b₃ : ℂ}
    (h₁ : ad.IsDomainWallAction h hx₂ hy₂ e₁ e₂ b₁)
    (h₂ : ad.IsDomainWallAction g hx₃ hy₃ e₂ e₃ b₂)
    (h₃ : ad.IsDomainWallAction (g * h) hx₃' hy₃' e₁ e₃ b₃) :
    b₂ * b₁ = ((ad.lSymbol fd x g h / ad.lSymbol fd y g h : ℂˣ) : ℂ) * b₃ := by
  have hc := (mul (fd := fd) hA hperm hx₃' hy₃' h₁ h₂).phase_eq hA h₃
  rw [← hc]
  have hLx := (ad.lSymbol fd x g h).ne_zero
  have hLy := (ad.lSymbol fd y g h).ne_zero
  simp only [Units.val_div_eq_div_val]
  field_simp

/-- **The group acts on periodic states with two domain walls by the product of the two
phases** (arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 833--838, and
`U_g |ψ(x,y)⟩ ∝ |ψ(gx,gy)⟩` of line 1894): if `g` carries the domain walls `e` from
`x` to `y` and `f` from `y` to `x` to `e'` and `f'` with phases `c` and `c'`, then
`O_g |ψ(x-y-x)⟩ = c c' |ψ(gx-gy-gx)⟩` on every chain with long enough regions. For `ℤ₂` this is
`U |ψ(A-B-A)⟩ = c_{AB} c_{BA} |ψ(B-A-B)⟩`.

The proof inserts the reduced blocks of both regions into the acted chain
(arXiv:1706.07329v2, Lemma `B_expand`, `cornerproblem.tex` lines 3993--4005) and closes the
trace. -/
theorem mpo_mulVec_twoWallMPV (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x)))
    {f : Fin d → Matrix (Fin (D y)) (Fin (D x)) ℂ} {f' : Fin d → Matrix (Fin (D y')) (Fin (D x')) ℂ}
    {c' : ℂ} (he : ad.IsDomainWallAction g hx hy e e' c)
    (hf : ad.IsDomainWallAction g hy hx f f' c') :
    ∃ N : ℕ, ∀ k l n : ℕ, N ≤ k → N ≤ l →
      mpo (F.tensor g) (k + 1 + l + 1 + n) *ᵥ twoWallMPV (A x) e (A y) f =
        (c * c') • twoWallMPV (A x') e' (A y') f' := by
  subst hx hy
  obtain ⟨N₁, H₁⟩ := he.eq
  obtain ⟨N₂, H₂⟩ := hf.eq
  have hBx := (ad.isReduction g x).bondDim_isReductionResidualNilpotencyBound
    ((hperm g x).sameMPV₂Pos_actTensor (MPSTensor.SameMPV₂Pos.refl _))
  have hBy := (ad.isReduction g y).bondDim_isReductionResidualNilpotencyBound
    ((hperm g y).sameMPV₂Pos_actTensor (MPSTensor.SameMPV₂Pos.refl _))
  set M := N₁ + N₂ + F.bondDim g * D x + F.bondDim g * D y
  refine ⟨2 * M + 1, fun k l n hk hl ↦ ?_⟩
  change mpo (F.tensor g) _ *ᵥ (fun τ ↦ (twoWallChain (A x) e (A y) f τ).trace) = _
  rw [mpo_mulVec_trace]
  funext τ
  rw [Pi.smul_apply, eq_append_append_append_append τ, physAct_twoWallChain, twoWallMPV_append,
    smul_eq_mul]
  generalize (fun j : Fin k ↦ τ _) = σ₁
  generalize (fun j : Fin l ↦ τ _) = σ₂
  generalize (fun j : Fin n ↦ τ _) = σ₃
  generalize τ (Fin.castAdd n (Fin.castAdd 1 (Fin.castAdd l (Fin.natAdd k 0)))) = i
  generalize τ (Fin.castAdd n (Fin.natAdd (k + 1 + l) 0)) = j
  obtain ⟨p, c₀, q, hw, hp, hq, hc₀⟩ :=
    (List.ofFn σ₃ ++ List.ofFn σ₁).exists_append_append_of_two_mul_lt
    (M := M) (by simp only [List.length_append, List.length_ofFn]; omega)
  obtain ⟨p', c₁, q', hv, hp', hq', hc₁⟩ := (List.ofFn σ₂).exists_append_append_of_two_mul_lt
    (M := M) (by simp only [List.length_ofFn]; omega)
  have hzA := (ad.isReduction g x).evalWord_mul_reduced_exterior_eq_evalWord_append hBx p c₀ q hc₀
    (by omega) (by omega)
  have hzB := (ad.isReduction g y).evalWord_mul_reduced_exterior_eq_evalWord_append hBy p' c₁ q'
    hc₁ (by omega) (by omega)
  have r₁ := H₁ q p' i (by omega) (by omega)
  have r₂ := H₂ q' p j (by omega) (by omega)
  simp only [castIndex_rfl, Matrix.one_mul, Matrix.mul_one] at r₁ r₂
  set TA := actTensor (F.tensor g) (A x)
  set TB := actTensor (F.tensor g) (A y)
  -- rotate the last region to the front
  have hrot : ∀ (X : Matrix (Fin (F.bondDim g * D x)) (Fin (F.bondDim g * D x)) ℂ),
      (Kraus.evalWord TA (List.ofFn σ₁) * X * Kraus.evalWord TA (List.ofFn σ₃)).trace =
        (Kraus.evalWord TA (List.ofFn σ₃ ++ List.ofFn σ₁) * X).trace := fun X ↦ by
    rw [Matrix.trace_mul_comm, Kraus.evalWord_append, Matrix.mul_assoc]
  have hrot' : ∀ (X : Matrix (Fin (D (g • x))) (Fin (D (g • x))) ℂ),
      (Kraus.evalWord (A (g • x)) (List.ofFn σ₁) * X * Kraus.evalWord (A (g • x))
        (List.ofFn σ₃)).trace =
        (Kraus.evalWord (A (g • x)) (List.ofFn σ₃ ++ List.ofFn σ₁) * X).trace := fun X ↦ by
    rw [Matrix.trace_mul_comm, Kraus.evalWord_append, Matrix.mul_assoc]
  have lhs := hrot (actRect (F.tensor g) e i * Kraus.evalWord TB (List.ofFn σ₂) *
    actRect (F.tensor g) f j)
  have rhs := hrot' (e' i * Kraus.evalWord (A (g • y)) (List.ofFn σ₂) * f' j)
  simp only [Matrix.mul_assoc] at lhs rhs ⊢
  rw [lhs, rhs, hw, hv, ← hzA, ← hzB]
  -- close the trace around the reduced block of the first region
  have hclose := Matrix.trace_mul_comm (Kraus.evalWord TA p * ad.W g x)
    (Kraus.evalWord (A (g • x)) c₀ * ad.V g x * Kraus.evalWord TA q * actRect (F.tensor g) e i *
      Kraus.evalWord TB p' * ad.W g y * Kraus.evalWord (A (g • y)) c₁ * ad.V g y *
        Kraus.evalWord TB q' * actRect (F.tensor g) f j)
  simp only [Matrix.mul_assoc] at hclose ⊢
  rw [hclose]
  calc _ = (Kraus.evalWord (A (g • x)) c₀ *
        ((ad.V g x * (Kraus.evalWord TA q * actRect (F.tensor g) e i * Kraus.evalWord TB p') *
            ad.W g y) *
          (Kraus.evalWord (A (g • y)) c₁ *
            (ad.V g y * (Kraus.evalWord TB q' * actRect (F.tensor g) f j * Kraus.evalWord TA p) *
              ad.W g x)))).trace := by simp only [Matrix.mul_assoc]
    _ = (Kraus.evalWord (A (g • x)) c₀ *
        (c • (Kraus.evalWord (A (g • x)) q * e' i * Kraus.evalWord (A (g • y)) p') *
          (Kraus.evalWord (A (g • y)) c₁ *
            c' • (Kraus.evalWord (A (g • y)) q' * f' j *
              Kraus.evalWord (A (g • x)) p)))).trace := by
        rw [r₁, r₂]
    _ = _ := by
        simp only [List.append_assoc, Kraus.evalWord_append, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
        rw [Matrix.trace_mul_comm (Kraus.evalWord (A (g • x)) p)]
        simp only [Matrix.mul_assoc]
        ring

/-! ### Involutions: the two domain walls of a `ℤ₂` symmetry -/

section Involution

variable {g : G} {x y : X} {hxy : g • x = y} {hyx : g • y = x}
  {eAB : Fin d → Matrix (Fin (D x)) (Fin (D y)) ℂ} {eBA : Fin d → Matrix (Fin (D y)) (Fin (D x)) ℂ}
  {cAB cBA : ℂ}

/-- **The domain-wall phases of an involution as a ratio of L-symbols** (arXiv:2405.00439,
`eq:CC-LL`, first equality, `Papers/2405.00439/MPU-DW.tex` lines 1020--1121). Let `g` be an
involution exchanging the blocks `x` and `y`, and let the domain walls `e_{AB}` from `x` to
`y` and `e_{BA}` from `y` to `x` be exchanged by `g` with phases `c_{AB}`, `c_{BA}`
(`eq:localcdef`). Then
`c_{AB} c_{BA} = Lˣ_{g,g} Lˣ_{1,1} / (L^y_{g,g} L^y_{1,1})`.

The proof applies `g` twice, which gives the local action of `g² = 1` on `e_{AB}` with phase
`b = (L^y_{g,g} / Lˣ_{g,g}) c_{BA} c_{AB}`
(`MPOTensor.GroupFamily.BlockActionData.IsDomainWallAction.mul`), as in the source's display
before `eq:CC-LL`; composing the identity with itself then forces `b = Lˣ_{1,1} / L^y_{1,1}`.
With the source's trivial identity tensor (line 861) the L-symbols of the identity are one and
the conclusion is `c_{AB} c_{BA} = L_A / L_B`. -/
theorem mul_eq_lSymbol_of_mul_self_eq_one (hA : ∀ x, Kraus.IsNormal (A x))
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x))) (hg : g * g = 1)
    (hAB : ad.IsDomainWallAction g hxy hyx eAB eBA cAB)
    (hBA : ad.IsDomainWallAction g hyx hxy eBA eAB cBA) :
    cAB * cBA = ((ad.lSymbol fd x g g * ad.lSymbol fd x 1 1 /
      (ad.lSymbol fd y g g * ad.lSymbol fd y 1 1) : ℂˣ) : ℂ) := by
  subst hxy
  set b := ((ad.lSymbol fd (g • x) g g / ad.lSymbol fd x g g : ℂˣ) : ℂ) * cBA * cAB
  have h1 : ad.IsDomainWallAction 1 (one_smul G x) (one_smul G (g • x)) eAB eAB b :=
    (mul (fd := fd) hA hperm (by rw [hg, one_smul]) (by rw [hg, one_smul]) hAB hBA).congr_elem
      hg _ _
  have hb : b ≠ 0 := h1.phase_ne_zero
  have h11 : b * b = ((ad.lSymbol fd x 1 1 / ad.lSymbol fd (g • x) 1 1 : ℂˣ) : ℂ) * b :=
    mul_eq (fd := fd) hA hperm h1 h1 (h1.congr_elem (one_mul 1).symm (by rw [one_mul, one_smul])
      (by rw [one_mul, one_smul]))
  have hb' : b = ((ad.lSymbol fd x 1 1 / ad.lSymbol fd (g • x) 1 1 : ℂˣ) : ℂ) :=
    mul_right_cancel₀ hb h11
  have hLx := (ad.lSymbol fd x g g).ne_zero
  have hLy := (ad.lSymbol fd (g • x) g g).ne_zero
  have hLx1 := (ad.lSymbol fd x 1 1).ne_zero
  have hLy1 := (ad.lSymbol fd (g • x) 1 1).ne_zero
  simp only [b, Units.val_div_eq_div_val, Units.val_mul] at hb' ⊢
  field_simp at hb' ⊢
  linear_combination hb'

/-- **The domain-wall phases of an involution detect the anomaly** (arXiv:2405.00439,
`eq:CC-LL`, `Papers/2405.00439/MPU-DW.tex` lines 1020--1121, with `eq:Lsignrel`, lines
895--1017): `c_{AB} c_{BA} = ω(g,g,g) ω(g,1,g)`. For fusion tensors trivial on the identity, as
in the source, `ω(g,1,g) = 1` and this is `c_{AB} c_{BA} = ω`. -/
theorem mul_eq_omega_of_mul_self_eq_one (hF : F.IsNormalRepresentation)
    (hA : ∀ x, Kraus.IsNormal (A x)) (hD : ∀ x, 0 < D x)
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x))) (hg : g * g = 1)
    (hAB : ad.IsDomainWallAction g hxy hyx eAB eBA cAB)
    (hBA : ad.IsDomainWallAction g hyx hxy eBA eAB cBA) :
    cAB * cBA = ((fd.omega g g g * fd.omega g 1 g : ℂˣ) : ℂ) := by
  rw [mul_eq_lSymbol_of_mul_self_eq_one (fd := fd) hA hperm hg hAB hBA]
  subst hxy
  rw [LSymbol.div_eq_mul_of_isCompatible_of_mul_self_eq_one
    (isCompatible_lSymbol (fd := fd) (ad := ad) hF hA hD hperm) x hg]

/-- **The anomaly is observed on states with two domain walls** (arXiv:2405.00439,
`Papers/2405.00439/MPU-DW.tex` lines 833--838 and `eq:CC-LL`):
`U |ψ(A-B-A)⟩ = ω(g,g,g) ω(g,1,g) |ψ(B-A-B)⟩` on every chain with long enough regions. -/
theorem mpo_mulVec_twoWallMPV_eq_omega (hF : F.IsNormalRepresentation)
    (hA : ∀ x, Kraus.IsNormal (A x)) (hD : ∀ x, 0 < D x)
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x))) (hg : g * g = 1)
    (hAB : ad.IsDomainWallAction g hxy hyx eAB eBA cAB)
    (hBA : ad.IsDomainWallAction g hyx hxy eBA eAB cBA) :
    ∃ N : ℕ, ∀ k l n : ℕ, N ≤ k → N ≤ l →
      mpo (F.tensor g) (k + 1 + l + 1 + n) *ᵥ twoWallMPV (A x) eAB (A y) eBA =
        ((fd.omega g g g * fd.omega g 1 g : ℂˣ) : ℂ) • twoWallMPV (A y) eBA (A x) eAB := by
  obtain ⟨N, hN⟩ := mpo_mulVec_twoWallMPV hperm hAB hBA
  refine ⟨N, fun k l n hk hl ↦ ?_⟩
  rw [hN k l n hk hl, mul_eq_omega_of_mul_self_eq_one (fd := fd) hF hA hD hperm hg hAB hBA]

/-- **Gauge invariance of `c_{AB} c_{BA}`** (arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex`
lines 833--838): the product of the two domain-wall phases of an involution does not depend on
the action tensors, the fusion tensors, or the domain-wall tensors. -/
theorem mul_eq_mul_of_mul_self_eq_one (hF : F.IsNormalRepresentation)
    (hA : ∀ x, Kraus.IsNormal (A x)) (hD : ∀ x, 0 < D x)
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x))) (hg : g * g = 1)
    (hAB : ad.IsDomainWallAction g hxy hyx eAB eBA cAB)
    (hBA : ad.IsDomainWallAction g hyx hxy eBA eAB cBA) {ad' : BlockActionData F A}
    {eAB' : Fin d → Matrix (Fin (D x)) (Fin (D y)) ℂ}
    {eBA' : Fin d → Matrix (Fin (D y)) (Fin (D x)) ℂ} {cAB' cBA' : ℂ}
    (hAB' : ad'.IsDomainWallAction g hxy hyx eAB' eBA' cAB')
    (hBA' : ad'.IsDomainWallAction g hyx hxy eBA' eAB' cBA') :
    cAB * cBA = cAB' * cBA' := by
  obtain ⟨fd⟩ := hF.nonempty_fusionData
  rw [mul_eq_omega_of_mul_self_eq_one (fd := fd) hF hA hD hperm hg hAB hBA,
    mul_eq_omega_of_mul_self_eq_one (fd := fd) hF hA hD hperm hg hAB' hBA']

end Involution

end IsDomainWallAction

end BlockActionData

end GroupFamily

end MPOTensor
