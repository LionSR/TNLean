/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalIsometricEmbedding
import TNLean.MPS.MPDO.PhysicalSectorCoordinateTransport
import TNLean.MPS.Symmetry.Defs
import TNLean.MPS.Symmetry.MPDO.Defs

/-!
# Strong and weak on-site symmetry of the vectorized density operator

**Source.** Garre Rubio, Molnár, Schuch, Verstraete 2026 (arXiv:2603.28349),
`References/2603.28349/main.tex` lines 362–368: a density operator is weakly symmetric,
`[U, ρ] = 0`, or strongly symmetric, `U ρ = ρ`; for a matrix product density operator both
conditions are read on the vectorized state `|ρ⟩⟩`, an MPS, where `U ρ U^†` becomes
`(U ⊗ \bar U) |ρ⟩⟩` and `U ρ` becomes `(U ⊗ 1) |ρ⟩⟩`. The strong and weak symmetries of a
family are those of Sun 2025 (arXiv:2504.16985), `References/2504.16985/main.tex` line 182.

**Formalized here.** Bridge: the vectorized state of `ρ^{(L)}(M)` is the matrix product vector
of the doubled-index tensor `toMPSTensor M` (ket index `divNat`, bra index `modNat`). Acting
with `u ⊗ v` on each doubled physical index sends `ρ` to `u^{⊗L} ρ (v^{⊗L})^T`. Consequently,
for a unitary on-site representation, weak on-site symmetry of `M` is on-site symmetry of the
doubled tensor under `g ↦ U_g ⊗ \bar U_g`, and strong on-site symmetry with eigenvalues
`c_g^{(L)}` is proportionality of the matrix product vectors of the doubled tensor and its
twist by `U_g ⊗ 1`.

**Scope restriction (boundary `X = 1`):** as in `TNLean/MPS/Symmetry/MPDO/Defs.lean`, the
density operators are the periodic operators `mpo M L`; documented in
`docs/paper-gaps/sun25_mpdo_symmetry_boundary_scope.tex`.

## Main definitions

* `MPOTensor.pairTwist`: the tensor `∑_{k,l} u_{ik} v_{jl} M^{kl}`.
* `MPOTensor.pairOperator`, `MPOTensor.pairRep`: `u ⊗ v` on the doubled physical index, and
  the representation `g ↦ U_g ⊗ V_g`.
* `MPOTensor.doubledRep`: `g ↦ U_g ⊗ \bar U_g`.

## Main results

* `MPOTensor.mpo_pairTwist`: `ρ^{(L)}(pairTwist u v M) = u^{⊗L} ρ^{(L)}(M) (v^{⊗L})^T`.
* `MPOTensor.pairTwist_map_star`, `MPOTensor.pairOperator_map_star`: for `v = \bar u` the twist
  and the doubled operator are the existing `changePhysicalBasis u` and
  `doubledPhysicalMatrix u`.
* `MPOTensor.twistedTensor_toMPSTensor_pairRep`: twisting the doubled tensor is `pairTwist`.
* `MPOTensor.sameMPV_toMPSTensor_iff`: equal matrix product vectors of doubled tensors are
  equal density operators at every positive length.
* `MPOTensor.isWeakOnSiteSymmetry_iff_isOnSiteSymmetric_toMPSTensor`,
  `MPOTensor.isStrongOnSiteSymmetry_iff_mpv_toMPSTensor`: the vectorized forms.

## References
- [arXiv:2603.28349](https://arxiv.org/abs/2603.28349) -- J. Garre Rubio, A. Molnár,
  N. Schuch, F. Verstraete, *The local characterization of global tensor network eigenstates*
- [arXiv:2504.16985](https://arxiv.org/abs/2504.16985) -- X.-Q. Sun, *Anomalous matrix
  product operator symmetries and 1D mixed-state phases*
-/

open scoped Matrix BigOperators Kronecker

namespace MPOTensor

variable {d D : ℕ}

/-! ### Twisting the ket and bra legs -/

/-- **The ket-bra twist of an MPO tensor.** `(pairTwist u v M)^{ij} = ∑_{k,l} u_{ik} v_{jl}
M^{kl}`: `u` acts on the ket leg and `v` on the bra leg. -/
noncomputable def pairTwist (u v : Matrix (Fin d) (Fin d) ℂ) (M : MPOTensor d D) :
    MPOTensor d D :=
  fun i j => ∑ k, u i k • ∑ l, v j l • M k l

/-- Twisting the ket leg by `u` multiplies the periodic operators by `u^{⊗L}` on the left. -/
theorem mpo_ketTwist (u : Matrix (Fin d) (Fin d) ℂ) (M : MPOTensor d D) (L : ℕ) :
    mpo (fun i j => ∑ k, u i k • M k j) L = (Matrix.finKronecker fun _ : Fin L => u) * mpo M L := by
  ext σ τ
  rw [mpo_apply, mpoMatrixEntry, evalWord_ofFn, Matrix.trace_prod_ofFn_sum_smul, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [Matrix.finKronecker_apply, mpo_apply, mpoMatrixEntry, evalWord_ofFn]

/-- Twisting the bra leg by `v` multiplies the periodic operators by `(v^{⊗L})^T` on the
right. -/
theorem mpo_braTwist (v : Matrix (Fin d) (Fin d) ℂ) (M : MPOTensor d D) (L : ℕ) :
    mpo (fun i j => ∑ l, v j l • M i l) L =
      mpo M L * (Matrix.finKronecker fun _ : Fin L => v)ᵀ := by
  ext σ τ
  rw [mpo_apply, mpoMatrixEntry, evalWord_ofFn, Matrix.trace_prod_ofFn_sum_smul, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [Matrix.transpose_apply, Matrix.finKronecker_apply, mpo_apply, mpoMatrixEntry,
    evalWord_ofFn, mul_comm]

/-- **The periodic operators of a ket-bra twist.**

Bridge: `ρ^{(L)}(pairTwist u v M) = u^{⊗L} ρ^{(L)}(M) (v^{⊗L})^T`, the operator form of acting
with `u ⊗ v` on each doubled physical index of the vectorized state `|ρ⟩⟩`
(arXiv:2603.28349, lines 364–368). -/
theorem mpo_pairTwist (u v : Matrix (Fin d) (Fin d) ℂ) (M : MPOTensor d D) (L : ℕ) :
    mpo (pairTwist u v M) L =
      (Matrix.finKronecker fun _ : Fin L => u) * mpo M L *
        (Matrix.finKronecker fun _ : Fin L => v)ᵀ := by
  rw [Matrix.mul_assoc, ← mpo_braTwist, ← mpo_ketTwist]
  rfl

/-- **The ket-bra twist by `u ⊗ \bar u` is a change of physical coordinates.**

Bridge: `pairTwist u \bar u M = changePhysicalBasis u M`, the conjugation
`M^{αβ} ↦ u M^{αβ} u^†` of every physical slice. -/
theorem pairTwist_map_star (u : Matrix (Fin d) (Fin d) ℂ) (M : MPOTensor d D) :
    pairTwist u (u.map (starRingEnd ℂ)) M =
      PhysicalSectorFactorization.changePhysicalBasis u M := by
  funext i j
  ext β α
  simp only [pairTwist, PhysicalSectorFactorization.changePhysicalBasis, physicalSlice,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [RCLike.star_def]
  ring

/-! ### The doubled physical index -/

/-- **`u ⊗ v` on the doubled physical index**, in the encoding of `toMPSTensor`
(`divNat` = ket, `modNat` = bra). -/
noncomputable def pairOperator (u v : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (d * d)) (Fin (d * d)) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ finProdFinEquiv (u ⊗ₖ v)

theorem pairOperator_apply (u v : Matrix (Fin d) (Fin d) ℂ) (p q : Fin (d * d)) :
    pairOperator u v p q = u p.divNat q.divNat * v p.modNat q.modNat := by
  simp [pairOperator, Matrix.coe_reindexAlgEquiv, Matrix.kroneckerMap_apply]

/-- **The doubled operator of `u ⊗ \bar u`.**

Bridge: `pairOperator u \bar u = doubledPhysicalMatrix u`, the matrix induced by `u` on the
doubled ket-bra index. -/
theorem pairOperator_map_star (u : Matrix (Fin d) (Fin d) ℂ) :
    pairOperator u (u.map (starRingEnd ℂ)) = doubledPhysicalMatrix u := by
  ext p q
  simp [pairOperator_apply, doubledPhysicalMatrix]

section Rep

variable {G : Type*} [Monoid G]

/-- **The representation `g ↦ U_g ⊗ V_g` on the doubled physical index.** -/
noncomputable def pairRep (U V : G →* Matrix (Fin d) (Fin d) ℂ) :
    G →* Matrix (Fin (d * d)) (Fin (d * d)) ℂ where
  toFun g := pairOperator (U g) (V g)
  map_one' := by
    simp only [pairOperator, _root_.map_one, Matrix.one_kronecker_one]
  map_mul' g k := by
    change pairOperator (U (g * k)) (V (g * k)) =
      pairOperator (U g) (V g) * pairOperator (U k) (V k)
    rw [_root_.map_mul U g k, _root_.map_mul V g k, pairOperator, pairOperator, pairOperator,
      ← _root_.map_mul (Matrix.reindexAlgEquiv ℂ ℂ finProdFinEquiv), Matrix.mul_kronecker_mul]

/-- **The doubled representation `g ↦ U_g ⊗ \bar U_g`**, which acts on the vectorized state
`|ρ⟩⟩` as `ρ ↦ U_g ρ U_g^†` (arXiv:2603.28349, lines 364–368). Its matrices are
`doubledPhysicalMatrix (U g)` (`doubledRep_apply`). -/
noncomputable def doubledRep (U : G →* Matrix (Fin d) (Fin d) ℂ) :
    G →* Matrix (Fin (d * d)) (Fin (d * d)) ℂ :=
  pairRep U ((RingHom.mapMatrix (starRingEnd ℂ)).toMonoidHom.comp U)

theorem doubledRep_apply (U : G →* Matrix (Fin d) (Fin d) ℂ) (g : G) :
    doubledRep U g = doubledPhysicalMatrix (U g) :=
  pairOperator_map_star (U g)

/-- Twisting the doubled tensor by `g ↦ U_g ⊗ V_g` is the ket-bra twist. -/
theorem twistedTensor_toMPSTensor_pairRep (U V : G →* Matrix (Fin d) (Fin d) ℂ)
    (M : MPOTensor d D) (g : G) :
    MPSTensor.twistedTensor (toMPSTensor M) (pairRep U V) g =
      toMPSTensor (pairTwist (U g) (V g) M) := by
  funext p
  change ∑ q, pairOperator (U g) (V g) p q • M q.divNat q.modNat = _
  rw [← (finProdFinEquiv : Fin d × Fin d ≃ Fin (d * d)).sum_comp, Fintype.sum_prod_type]
  simp only [pairOperator_apply, MPSTensor.finProdFinEquiv_divNat,
    MPSTensor.finProdFinEquiv_modNat, toMPSTensor, pairTwist, Finset.smul_sum, smul_smul]

end Rep

/-- The matrix product vector of the doubled tensor at a word `w` is the entry of the
periodic operator at the ket and bra configurations of `w`. -/
theorem mpv_toMPSTensor (M : MPOTensor d D) {N : ℕ} (w : Fin N → Fin (d * d)) :
    MPSTensor.mpv (toMPSTensor M) w = mpo M N (fun n => (w n).divNat) fun n => (w n).modNat := by
  rw [MPSTensor.mpv_eq, MPSTensor.coeff_eq, evalWord_toMPSTensor_ofFn, mpo_apply, mpoMatrixEntry]

/-- **Proportional vectorized states are proportional density operators.**

Bridge: at a fixed length, the matrix product vectors of the doubled tensors of `X` and `Y`
are proportional with factor `c` exactly when `ρ^{(N)}(X) = c ρ^{(N)}(Y)`. -/
theorem mpv_toMPSTensor_eq_mul_iff (X Y : MPOTensor d D) (N : ℕ) (c : ℂ) :
    (∀ w : Fin N → Fin (d * d),
        MPSTensor.mpv (toMPSTensor X) w = c * MPSTensor.mpv (toMPSTensor Y) w) ↔
      mpo X N = c • mpo Y N := by
  constructor
  · intro h
    ext σ τ
    have h1 := h fun n => finProdFinEquiv (σ n, τ n)
    simpa only [mpv_toMPSTensor, MPSTensor.finProdFinEquiv_divNat,
      MPSTensor.finProdFinEquiv_modNat, Matrix.smul_apply, smul_eq_mul] using h1
  · intro h w
    rw [mpv_toMPSTensor, mpv_toMPSTensor, h, Matrix.smul_apply, smul_eq_mul]

/-- **Equal vectorized states are equal density operators.**

Bridge: `SameMPV (toMPSTensor X) (toMPSTensor Y)` holds exactly when the periodic operators
agree at every positive length; at length zero both vectors are the bond dimension. -/
theorem sameMPV_toMPSTensor_iff (X Y : MPOTensor d D) :
    MPSTensor.SameMPV (toMPSTensor X) (toMPSTensor Y) ↔ ∀ N, 0 < N → mpo X N = mpo Y N := by
  constructor
  · intro h N _
    rw [← one_smul ℂ (mpo Y N), ← mpv_toMPSTensor_eq_mul_iff]
    intro w
    rw [one_mul]
    exact h N w
  · intro h N w
    rcases N.eq_zero_or_pos with rfl | hN
    · simp
    · have h1 := (mpv_toMPSTensor_eq_mul_iff X Y N 1).mpr (by rw [one_smul]; exact h N hN) w
      rwa [one_mul] at h1

/-! ### Strong and weak symmetry on the vectorized state -/

/-- The transpose of the Kronecker power of the entrywise conjugate is the adjoint of the
Kronecker power. -/
private theorem finKronecker_map_star_transpose (u : Matrix (Fin d) (Fin d) ℂ) (L : ℕ) :
    (Matrix.finKronecker fun _ : Fin L => u.map (starRingEnd ℂ))ᵀ =
      (Matrix.finKronecker fun _ : Fin L => u)ᴴ := by
  rw [Matrix.finKronecker_transpose, Matrix.finKronecker_conjTranspose]
  rfl

/-- For a unitary `a`, `[a, ρ] = 0` is `a ρ a^† = ρ`. -/
private theorem commute_iff_mul_mul_conjTranspose {n : Type*} [Fintype n] [DecidableEq n]
    {a ρ : Matrix n n ℂ} (ha : aᴴ * a = 1) : Commute a ρ ↔ ρ = a * ρ * aᴴ := by
  have ha' : a * aᴴ = 1 := mul_eq_one_comm.mp ha
  constructor
  · intro h
    rw [h.eq, Matrix.mul_assoc, ha', Matrix.mul_one]
  · intro h
    change a * ρ = ρ * a
    conv_rhs => rw [h, Matrix.mul_assoc, ha, Matrix.mul_one]

section Symmetry

variable {G : Type*} [Monoid G]

/-- **Weak on-site symmetry on the vectorized state.**

Bridge: for a unitary on-site representation, the matrix product density operator is weakly
symmetric, `[U_g^{⊗L}, ρ^{(L)}] = 0` at every positive length (arXiv:2504.16985, line 182), if
and only if the doubled tensor `toMPSTensor M` is on-site symmetric under
`g ↦ U_g ⊗ \bar U_g`, i.e. `(U_g ⊗ \bar U_g)^{⊗L} |ρ⟩⟩ = |ρ⟩⟩` (arXiv:2603.28349,
lines 362–368). -/
theorem isWeakOnSiteSymmetry_iff_isOnSiteSymmetric_toMPSTensor (M : MPOTensor d D)
    (U : G →* Matrix (Fin d) (Fin d) ℂ) (hU : ∀ g, (U g)ᴴ * U g = 1) :
    IsWeakOnSiteSymmetry M U ↔ MPSTensor.IsOnSiteSymmetric (toMPSTensor M) (doubledRep U) := by
  unfold IsWeakOnSiteSymmetry IsWeakMPOSymmetry MPSTensor.IsOnSiteSymmetric doubledRep
  refine forall_congr' fun g => ?_
  rw [twistedTensor_toMPSTensor_pairRep, sameMPV_toMPSTensor_iff]
  refine forall_congr' fun L => forall_congr' fun _ => ?_
  rw [mpo_onSite, mpo_pairTwist, MonoidHom.comp_apply]
  change _ ↔ _ = _ * _ * (Matrix.finKronecker fun _ : Fin L => (U g).map (starRingEnd ℂ))ᵀ
  rw [finKronecker_map_star_transpose,
    commute_iff_mul_mul_conjTranspose (Matrix.finKronecker_conjTranspose_mul_self (hU g))]

/-- **Strong on-site symmetry on the vectorized state.**

Bridge: the matrix product density operator is strongly symmetric under `U_g^{⊗L}` with
eigenvalues `c_g^{(L)}` (arXiv:2504.16985, line 182) if and only if, at every positive length,
the twist of the doubled tensor by `g ↦ U_g ⊗ 1` generates `c_g^{(L)}` times the matrix product
vector of the doubled tensor, i.e. `(U_g ⊗ 1)^{⊗L} |ρ⟩⟩ = c_g^{(L)} |ρ⟩⟩` (arXiv:2603.28349,
lines 362–368, where `c = 1`). -/
theorem isStrongOnSiteSymmetry_iff_mpv_toMPSTensor (M : MPOTensor d D)
    (U : G →* Matrix (Fin d) (Fin d) ℂ) (c : G → ℕ → ℂ) :
    IsStrongOnSiteSymmetry M U c ↔
      ∀ g L, 0 < L → ∀ w : Fin L → Fin (d * d),
        MPSTensor.mpv (MPSTensor.twistedTensor (toMPSTensor M) (pairRep U 1) g) w =
          c g L * MPSTensor.mpv (toMPSTensor M) w := by
  unfold IsStrongOnSiteSymmetry IsStrongMPOSymmetry
  refine forall_congr' fun g => forall_congr' fun L => forall_congr' fun _ => ?_
  rw [twistedTensor_toMPSTensor_pairRep, mpv_toMPSTensor_eq_mul_iff, mpo_pairTwist,
    mpo_onSite, MonoidHom.one_apply, Matrix.finKronecker_one, Matrix.transpose_one,
    Matrix.mul_one]

end Symmetry

end MPOTensor
