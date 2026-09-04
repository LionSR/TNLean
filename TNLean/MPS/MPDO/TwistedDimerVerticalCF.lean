/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.TwistedDimerFlagSectors
import TNLean.MPS.MPDO.VerticalSectorCoordinates

/-!
# The vertical canonical form of the $\mathbb Z_2$-twisted quantum dimer

**Scope: the vertical canonical form with the flag sectors as basis.**  The
vertically viewed tensor of the $\mathbb Z_2$-twisted quantum dimer `T` of
`TNLean.MPS.MPDO.TwistedDimer` has letters indexed by the horizontal bond pairs
and acting on the physical space $\mathbb C^8$ of the two qubits $L, R$ and the
flag qubit.  Reordering the physical index $(l, r, f) \mapsto (f, (l, r))$ by a
permutation matrix $U$ splits every vertical letter along the flag value into
the two normalized flag sectors $\widehat M_f$ of
`TNLean.MPS.MPDO.TwistedDimerFlagSectors`, each with the weight $\mu = 5/8$:
$$
  U\,\widetilde T_{ab}\,U^\dagger
    = \mu\,\widehat M_0^{ab} \oplus \mu\,\widehat M_1^{ab}.
$$
This file proves that the two sectors form a basis of normal tensors of the
vertically viewed tensor, so that `T` is in vertical canonical form in the
sense of arXiv:1606.00608, Proposition 4.13, lines 945--959 and 1861--1922,
with two labels, multiplicity one each, and the coefficient $\mu$.  The tensor
is a project example motivated by the length-dependence question after
Theorem 4.14 (lines 995--1010); it is not a tensor stated in that source.

## The argument

* The letters of each flag sector are nonzero multiples of matrix units, one
  for every matrix unit of $M_4(\mathbb C)$, so each sector is injective at one
  site and hence normal.
* The permutation matrix $U$ conjugates the vertical letters onto the weighted
  direct sum of the sector letters, because the letter of `T` between physical
  indices with different flags vanishes and the letter with a common flag is
  $\mu$ times the sector letter (`flagMPO_apply_eq_T`).
* The matrix product vectors of the vertical tensor are therefore the sum over
  the two sectors of $\mu^N$ times the sector matrix product vectors.
* The two sectors are linearly independent at every positive length: on the
  constant word of bond index $(0, 0, 0)$ both sectors evaluate to $(2/5)^N$,
  while on the word with one bond index $(0, 0, 1)$ and the others $(0, 0, 0)$
  they evaluate to $\pm\tfrac{3}{10}(2/5)^{N-1}$ with opposite signs.

## Main definitions

* `sectorCoord` — the identification of a flag value and a two-qubit index
  with a coordinate of the retained vertical space;
* `physCoordEquiv` — the physical index $(l, r, f)$ of the retained coordinate
  $(f, (l, r))$;
* `verticalCoisometry` — the permutation matrix of `physCoordEquiv`.

## Main results

* `flagFamily_isInjective` — each flag sector is injective at one site;
* `verticalCoisometry_conj_verticalTensor` — the conjugated vertical letters
  are the weighted direct sum of the sector letters;
* `mpv_verticalTensor_T` — the vertical matrix product vectors expand along
  the two sectors with the coefficient $\mu^N$;
* `linearIndependent_mpvState_flagFamily` — the sector matrix product vectors
  are linearly independent at every positive length;
* `flagFamily_isBNT` — the flag sectors form a basis of normal tensors of the
  vertically viewed tensor;
* `T_isVerticalCF` — the twisted dimer is in vertical canonical form.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition 4.12 and Proposition 4.13, lines 945--959 and 1861--1922 (the
  vertical canonical form) and lines 995--1010 (the length-dependence question
  motivating this project example)
-/

open scoped BigOperators Matrix ComplexOrder

noncomputable section

namespace MPOTensor.TwistedDimer

/-! ### Coordinates of the retained vertical space -/

/-- The bond dimension four of each flag sector.

Project example; not from CPSV16. -/
abbrev sectorDim : Fin 2 → ℕ := fun _ => 4

/-- Each flag sector occurs with multiplicity one.

Project example; not from CPSV16. -/
abbrev sectorMult : Fin 2 → ℕ := fun _ => 1

/-- The single diagonal entry $\mu = 5/8$ of the positive weight matrix of each
flag sector (arXiv:1606.00608, Proposition 4.13, lines 1863--1870).

Project example; not from CPSV16. -/
def sectorWeight : (f : Fin 2) → Fin (sectorMult f) → ℂ := fun _ _ => ((mu : ℝ) : ℂ)

/-- The retained vertical space of the two flag sectors: two copies of the
two-qubit space, one per flag value. -/
abbrev RetainedCoordinate :=
  Fin (∑ q : Fin (∑ α : Fin 2, sectorMult α), verticalCopyDim sectorDim sectorMult q)

/-- The flag value $f$ and the two-qubit index $q$ of a retained coordinate:
the coordinate of the sector $f$, its single multiplicity copy, and the
two-qubit index $q$. -/
def sectorCoord : Fin 2 × Fin 4 ≃ RetainedCoordinate :=
  ((Equiv.sigmaEquivProd (Fin 2) (Fin 4)).symm.trans
    (Equiv.sigmaCongrRight fun α =>
      (Equiv.uniqueProd (Fin (sectorDim α)) (Fin (sectorMult α))).symm)).trans
    (verticalSectorFinEquiv sectorDim sectorMult)

lemma sectorCoord_apply (f : Fin 2) (q : Fin 4) :
    sectorCoord (f, q) =
      verticalSectorFinEquiv sectorDim sectorMult ⟨f, ((default : Fin 1), q)⟩ :=
  rfl

/-- The physical index $(l, r, f)$ of the retained coordinate $(f, (l, r))$:
the reordering of the physical space $\mathbb C^8 = \bigoplus_f |f\rangle \otimes \mathbb C^4$
by which the flag qubit is moved in front of the two qubits $L, R$. -/
def physCoordEquiv : RetainedCoordinate ≃ Fin 8 :=
  sectorCoord.symm.trans
    ((Equiv.prodCongr (Equiv.refl (Fin 2)) (finProdFinEquiv (m := 2) (n := 2)).symm).trans
      ((Equiv.prodComm (Fin 2) (Fin 2 × Fin 2)).trans
        ((Equiv.prodAssoc (Fin 2) (Fin 2) (Fin 2)).trans physEquiv)))

@[simp] lemma physCoordEquiv_sectorCoord (f l r : Fin 2) :
    physCoordEquiv (sectorCoord (f, finProdFinEquiv (l, r))) = physIdx l r f := by
  simp [physCoordEquiv, physEquiv]

/-! ### The permutation matrix -/

/-- The permutation matrix $(l, r, f) \mapsto (f, (l, r))$ from the physical
space of `T` onto the retained vertical space, the isometry $U$ of the vertical
canonical form (arXiv:1606.00608, Proposition 4.13, lines 1863--1870).

Project example; not from CPSV16. -/
def verticalCoisometry : Matrix RetainedCoordinate (Fin 8) ℂ :=
  Matrix.of fun x i => if physCoordEquiv x = i then 1 else 0

lemma verticalCoisometry_apply (x : RetainedCoordinate) (i : Fin 8) :
    verticalCoisometry x i = if physCoordEquiv x = i then 1 else 0 :=
  rfl

/-- The permutation matrix is a coisometry. -/
theorem verticalCoisometry_mul_conjTranspose :
    verticalCoisometry * verticalCoisometryᴴ =
      (1 : Matrix RetainedCoordinate RetainedCoordinate ℂ) := by
  ext x y
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, verticalCoisometry_apply,
    Matrix.one_apply, physCoordEquiv.injective.eq_iff]

/-- The permutation matrix is an isometry. -/
theorem conjTranspose_mul_verticalCoisometry :
    verticalCoisometryᴴ * verticalCoisometry = (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, verticalCoisometry_apply]
  rw [← physCoordEquiv.symm.sum_comp]
  simp [Matrix.one_apply, eq_comm]

/-- Conjugating by the permutation matrix permutes the matrix entries. -/
theorem verticalCoisometry_conj (M : Matrix (Fin 8) (Fin 8) ℂ) (x y : RetainedCoordinate) :
    (verticalCoisometry * M * verticalCoisometryᴴ) x y =
      M (physCoordEquiv x) (physCoordEquiv y) := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, verticalCoisometry_apply]

/-! ### The conjugated vertical letters -/

/-- The letter of `T` between physical indices with different flags vanishes. -/
lemma T_apply_eq_zero_of_bitF_ne {i j : Fin 8} (h : bitF i ≠ bitF j) : T i j = 0 := by
  simp [T, coef, h]

/-- The letter of a flag sector at an explicitly paired bond index. -/
lemma flagFamily_finProdFinEquiv (f : Fin 2) (a b : Fin 8) :
    flagFamily f (finProdFinEquiv (a, b)) = flagMPO f a b := by
  unfold flagFamily MPOTensor.toMPSTensor
  rw [MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat]

/-- **The conjugated vertical letters.**  Conjugating the vertical letter of
`T` at the bond pair $(a, b)$ by the permutation matrix gives the direct sum,
over the flag value $f$, of $\mu$ times the letter of $\widehat M_f$ at $(a, b)$:
this is the direct-sum identity $U \widetilde M U^\dagger = \bigoplus_\alpha
\mu_\alpha \otimes M_\alpha$ of arXiv:1606.00608, Proposition 4.13, lines
1863--1870, for the displayed tensor.

Project example; not from CPSV16. -/
theorem verticalCoisometry_conj_verticalTensor (v : Fin (8 * 8)) :
    verticalCoisometry * verticalTensor T v * verticalCoisometryᴴ =
      verticalAssembledTensor sectorDim sectorMult sectorWeight flagFamily v := by
  ext x y
  obtain ⟨⟨f, q⟩, rfl⟩ := sectorCoord.surjective x
  obtain ⟨⟨f', q'⟩, rfl⟩ := sectorCoord.surjective y
  obtain ⟨⟨l, r⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 2)).surjective q
  obtain ⟨⟨l', r'⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 2)).surjective q'
  rw [verticalCoisometry_conj, physCoordEquiv_sectorCoord, physCoordEquiv_sectorCoord,
    verticalTensor_apply]
  by_cases hf : f = f'
  · subst hf
    rw [sectorCoord_apply, sectorCoord_apply, verticalAssembledTensor_apply_copy_same]
    have hv : flagFamily f v = flagMPO f v.divNat v.modNat := rfl
    rw [hv, flagMPO_apply_eq_T]
    simp only [sectorWeight]
    have hmu : ((mu : ℝ) : ℂ) ≠ 0 := by norm_num [mu]
    field_simp
  · rw [sectorCoord_apply, sectorCoord_apply, verticalAssembledTensor_apply_copy_ne sectorDim
      sectorMult sectorWeight flagFamily (fun h => hf (congrArg Sigma.fst h))]
    rw [T_apply_eq_zero_of_bitF_ne (by simpa using hf)]
    rfl

/-- **Reconstruction of the vertical letters.**  Every vertical letter of `T`
is recovered from the weighted direct sum of the sector letters through the
permutation matrix (arXiv:1606.00608, Proposition 4.13, lines 1863--1870).

Project example; not from CPSV16. -/
theorem verticalTensor_T_eq_conjTranspose_mul (v : Fin (8 * 8)) :
    verticalTensor T v =
      verticalCoisometryᴴ * verticalAssembledTensor sectorDim sectorMult sectorWeight flagFamily v *
        verticalCoisometry := by
  rw [← verticalCoisometry_conj_verticalTensor v]
  calc verticalTensor T v
      = (verticalCoisometryᴴ * verticalCoisometry) * verticalTensor T v *
          (verticalCoisometryᴴ * verticalCoisometry) := by
        rw [conjTranspose_mul_verticalCoisometry, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

/-! ### Matrix product vectors of the vertical tensor -/

/-- **Sector expansion of the vertical matrix product vectors.**  At every
positive length $N$ the matrix product vector of the vertically viewed tensor
is $\mu^N$ times the sum of the matrix product vectors of the two flag sectors.

Project example; not from CPSV16. -/
theorem mpv_verticalTensor_T {N : ℕ} (hN : 0 < N) (σ : Fin N → Fin (8 * 8)) :
    MPSTensor.mpv (verticalTensor T) σ =
      ∑ f : Fin 2, ((mu : ℝ) : ℂ) ^ N * MPSTensor.mpv (flagFamily f) σ := by
  rw [MPSTensor.sameMPV₂Pos_of_coisometry_reconstruction
      (verticalTensor T)
      (verticalAssembledTensor sectorDim sectorMult sectorWeight flagFamily)
      verticalCoisometry verticalCoisometry_mul_conjTranspose
      verticalTensor_T_eq_conjTranspose_mul N hN σ,
    mpv_verticalAssembledTensor_eq_sum, Fintype.sum_sigma]
  simp [sectorWeight]

/-! ### One-site injectivity of the flag sectors -/

/-- The bond-matrix entries are nonzero. -/
lemma Cmat_ne_zero (k p q : Fin 2) : Cmat k p q ≠ 0 := by
  unfold Cmat
  split_ifs <;> norm_num [cDiag_eq, cOff_eq]

/-- The one-site weight of a bond index of the block $k = 0$ is nonzero. -/
lemma flagWeight_physIdx_zero_ne_zero (f p p' : Fin 2) :
    flagWeight f (physIdx p p' 0) ≠ 0 := by
  rw [flagWeight_physIdx, tau_zero]
  have := Cmat_ne_zero 0 p p'
  norm_num [mu]
  exact this

/-- Every matrix unit of $M_4(\mathbb C)$ is a nonzero multiple of a letter of
each flag sector: the bond pair $((p, q, 0), (p', q', 0))$ gives the matrix
unit at the row $(p, p')$ and the column $(q, q')$. -/
theorem exists_flagFamily_eq_smul_single (f : Fin 2) (p q : Fin 4) :
    ∃ v : Fin (8 * 8), ∃ c : ℂ, c ≠ 0 ∧ flagFamily f v = c • Matrix.single p q 1 := by
  obtain ⟨⟨p₁, p₂⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 2)).surjective p
  obtain ⟨⟨q₁, q₂⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 2)).surjective q
  refine ⟨finProdFinEquiv (physIdx p₁ q₁ 0, physIdx p₂ q₂ 0), flagWeight f (physIdx p₁ q₁ 0),
    flagWeight_physIdx_zero_ne_zero f p₁ q₁, ?_⟩
  rw [flagFamily_finProdFinEquiv, Matrix.smul_single, smul_eq_mul, mul_one]
  simp [flagMPO, unitTensor, flagCoef]

/-- **One-site injectivity of the flag sectors.**  The letters of each flag
sector span the full matrix algebra $M_4(\mathbb C)$.

Project example; not from CPSV16. -/
theorem flagFamily_isInjective (f : Fin 2) : Kraus.IsInjective (flagFamily f) := by
  unfold Kraus.IsInjective
  apply le_antisymm le_top
  rw [← (Matrix.stdBasis ℂ (Fin 4) (Fin 4)).span_eq]
  apply Submodule.span_le.mpr
  rintro M ⟨⟨p, q⟩, rfl⟩
  rw [Matrix.stdBasis_eq_single]
  obtain ⟨v, c, hc, hv⟩ := exists_flagFamily_eq_smul_single f p q
  have hmem : flagFamily f v ∈ Submodule.span ℂ (Set.range (flagFamily f)) :=
    Submodule.subset_span ⟨v, rfl⟩
  rw [hv] at hmem
  have hscaled := Submodule.smul_mem (Submodule.span ℂ (Set.range (flagFamily f))) c⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at hscaled

/-- Each flag sector is normal. -/
theorem flagFamily_isNormal (f : Fin 2) : Kraus.IsNormal (flagFamily f) :=
  (flagFamily_isInjective f).isNormal

/-! ### Linear independence of the two sectors -/

/-- The one-site weight of the bond index $(0, 0, 0)$ is $2/5$ in both sectors. -/
lemma flagWeight_physIdx_zero_zero_zero (f : Fin 2) :
    flagWeight f (physIdx 0 0 0) = (2 / 5 : ℂ) := by
  rw [flagWeight_physIdx, tau_zero]
  norm_num [Cmat, cDiag_eq, mu]

/-- The one-site weight of the bond index $(0, 0, 1)$ is $\tfrac{3}{10}$ times
the flag sign $(\tau_1)_{ff}$. -/
lemma flagWeight_physIdx_zero_zero_one (f : Fin 2) :
    flagWeight f (physIdx 0 0 1) = (3 / 10 : ℂ) * ((tau 1 f : ℝ) : ℂ) := by
  rw [flagWeight_physIdx]
  norm_num [Cmat, cOff_eq, mu]
  ring

/-- The word of bond indices with $(0, 0, 1)$ at the first site and $(0, 0, 0)$
elsewhere. -/
private def signWord (n : ℕ) : Fin (n + 1) → Fin 8 :=
  Fin.cons (physIdx 0 0 1) fun _ => physIdx 0 0 0

private lemma bitL_signWord (n : ℕ) (m : Fin (n + 1)) : bitL (signWord n m) = 0 := by
  refine Fin.cases ?_ (fun m => ?_) m <;> simp [signWord]

private lemma bitR_signWord (n : ℕ) (m : Fin (n + 1)) : bitR (signWord n m) = 0 := by
  refine Fin.cases ?_ (fun m => ?_) m <;> simp [signWord]

private lemma isCyclicBondMatched_signWord (n : ℕ) : IsCyclicBondMatched (n + 1) (signWord n) :=
  fun m => by rw [IsBondMatchedPair, bitR_signWord, bitL_signWord]

private lemma isCyclicBondMatched_const (n : ℕ) :
    IsCyclicBondMatched (n + 1) fun _ : Fin (n + 1) => physIdx 0 0 0 :=
  fun _ => by simp [IsBondMatchedPair]

/-- The sector matrix product vector on the doubled constant word of bond index
$(0, 0, 0)$ is $(2/5)^{N}$. -/
private lemma mpv_flagFamily_const (f : Fin 2) (n : ℕ) :
    MPSTensor.mpv (flagFamily f)
      (fun _ : Fin (n + 1) => finProdFinEquiv (physIdx 0 0 0, physIdx 0 0 0)) =
      (2 / 5 : ℂ) ^ (n + 1) := by
  unfold flagFamily
  rw [MPSTensor.mpv_toMPSTensor_pairConfig, mpo_flagMPO_apply f n.succ_pos,
    ite_eq_left ⟨isCyclicBondMatched_const n, isCyclicBondMatched_const n, fun _ => rfl⟩]
  simp [flagWeight_physIdx_zero_zero_zero, div_pow]

/-- The sector matrix product vector on the doubled word with one bond index
$(0, 0, 1)$ is $\tfrac{3}{10} (\tau_1)_{ff} (2/5)^{N-1}$. -/
private lemma mpv_flagFamily_signWord (f : Fin 2) (n : ℕ) :
    MPSTensor.mpv (flagFamily f) (fun m => finProdFinEquiv (signWord n m, signWord n m)) =
      (3 / 10 : ℂ) * ((tau 1 f : ℝ) : ℂ) * (2 / 5 : ℂ) ^ n := by
  unfold flagFamily
  rw [MPSTensor.mpv_toMPSTensor_pairConfig, mpo_flagMPO_apply f n.succ_pos,
    ite_eq_left ⟨isCyclicBondMatched_signWord n, isCyclicBondMatched_signWord n, fun _ => rfl⟩,
    Fin.prod_univ_succ]
  simp [signWord, flagWeight_physIdx_zero_zero_zero, flagWeight_physIdx_zero_zero_one, div_pow]

/-- **Linear independence of the two sectors.**  At every positive length the
matrix product vectors of the two flag sectors are linearly independent: they
agree on the constant word of bond index $(0, 0, 0)$ and differ by a sign on
the word with one bond index $(0, 0, 1)$.

Project example; not from CPSV16. -/
theorem linearIndependent_mpvState_flagFamily (N : ℕ) (hN : 0 < N) :
    LinearIndependent ℂ fun f : Fin 2 => MPSTensor.mpvState (d := 8 * 8) (flagFamily f) N := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h₁ := congrArg (fun v : MPSTensor.MPVSpace (8 * 8) (n + 1) =>
    v fun _ => finProdFinEquiv (physIdx 0 0 0, physIdx 0 0 0)) hg
  have h₂ := congrArg (fun v : MPSTensor.MPVSpace (8 * 8) (n + 1) =>
    v fun m => finProdFinEquiv (signWord n m, signWord n m)) hg
  simp only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply, PiLp.zero_apply,
    MPSTensor.mpvState_apply, smul_eq_mul, mpv_flagFamily_const, mpv_flagFamily_signWord] at h₁ h₂
  have t0 : tau 1 0 = 1 := by norm_num [tau]
  have t1 : tau 1 1 = -1 := by norm_num [tau]
  rw [t0, t1] at h₂
  push_cast at h₂
  have hc : (2 / 5 : ℂ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hc' : (3 / 10 : ℂ) * (2 / 5 : ℂ) ^ n ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
  have e₁ : g 0 + g 1 = 0 := by
    have : (g 0 + g 1) * (2 / 5 : ℂ) ^ (n + 1) = 0 := by linear_combination h₁
    exact (mul_eq_zero.mp this).resolve_right hc
  have e₂ : g 0 - g 1 = 0 := by
    have : (g 0 - g 1) * ((3 / 10 : ℂ) * (2 / 5 : ℂ) ^ n) = 0 := by linear_combination h₂
    exact (mul_eq_zero.mp this).resolve_right hc'
  rw [Fin.forall_fin_two]
  exact ⟨by linear_combination (e₁ + e₂) / 2, by linear_combination (e₁ - e₂) / 2⟩

/-! ### The vertical canonical form -/

/-- **The flag sectors form a basis of normal tensors of the vertical tensor.**
Each sector is normal, the vertical matrix product vectors expand along the
sectors with the coefficient $\mu^N$, and the sector matrix product vectors are
linearly independent at every positive length.

Project example; not from CPSV16. -/
theorem flagFamily_isBNT : MPSTensor.IsBNT (verticalTensor T) 2 sectorDim flagFamily where
  normal := flagFamily_isNormal
  spans_mpv N hN := ⟨fun _ => ((mu : ℝ) : ℂ) ^ N, mpv_verticalTensor_T hN⟩
  eventually_li := ⟨0, fun N hN => linearIndependent_mpvState_flagFamily N hN⟩

/-- **The twisted quantum dimer is in vertical canonical form.**  The two flag
sectors, each with multiplicity one and weight $\mu = 5/8$, together with the
permutation matrix moving the flag qubit in front of the two qubits, witness
the vertical canonical form of arXiv:1606.00608, Proposition 4.13, lines
945--959 and 1861--1922, for the displayed tensor.  The tensor is a project
example motivated by the length-dependence question after Theorem 4.14 (lines
995--1010); it is not a tensor stated in that source. -/
theorem T_isVerticalCF : IsVerticalCF T :=
  ⟨2, sectorDim, sectorMult, sectorWeight, flagFamily, verticalCoisometry,
    fun _ => Nat.one_pos, fun _ _ => Complex.zero_lt_real.mpr (by norm_num [mu]),
    verticalCoisometry_mul_conjTranspose, flagFamily_isBNT,
    verticalCoisometry_conj_verticalTensor, verticalTensor_T_eq_conjTranspose_mul⟩

end MPOTensor.TwistedDimer
