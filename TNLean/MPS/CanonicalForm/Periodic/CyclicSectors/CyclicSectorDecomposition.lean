/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.Periodic.CyclicSectors.CyclicSectorRelation
import TNLean.MPS.CanonicalForm.Periodic.CyclicSectors.CommonBlockedCyclicSectorFamily
import QICLean.Channel.Peripheral.Spectrum.Conjugation
import TNLean.MPS.CanonicalForm.Periodic.CyclicSectors.HLift
import QICLean.Channel.Peripheral.Irreducible.SectorPrimitivity
import TNLean.MPS.CanonicalForm.Periodic.CyclicSectors.Compression

/-!
# Period removal (cyclic-sector decomposition) after blocking

This file performs the **period-removal step** of the canonical-form
reduction.  In arXiv:1606.00608 the only required input is that after
blocking by the least common multiple of the per-block periods, the
resulting tensor has no nontrivial $p$-periodic vectors (1606.00608,
§2.3).  The non-periodic route then proceeds to the normal/BNT
comparison; there is no standalone ``cyclic-sector theory'' in
1606.00608.

The file therefore
1. derives the channel-level cyclic decomposition from the adjoint
   transfer map (Wolf 2012, Theorem 6.6);
2. feeds it into the blocked-sector infrastructure to obtain the
   MPS-level period-removal decomposition for an irreducible
   trace-preserving tensor;
3. proves that the resulting sector blocks are primitive and
   tensor-irreducible.

The bulk of the projection-multiplicativity and orbit-lift
arguments are internal to the period-removal step; they are not
exposed as independent results of CPSV.

It also contains the following results.

* `MPSTensor.cyclic_projection_ne_zero_of_sum_one`,
  `MPSTensor.compressedTensor_adjointTransferMap_cornerBridge`: corner bridge for compressed cyclic
  sectors.

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, §2.3/App.A]
* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:2011.12127, §IV]
* [Wolf, Quantum Channels & Operations (2012), §6.5–6.6]
-/

open MPTensor

open scoped Matrix BigOperators ComplexOrder MatrixOrder

section CornerBridge

/-!
## Corner bridge for compressed cyclic sectors

This file transports primitivity and irreducibility from the corner restriction
of an ambient adjoint transfer map to the adjoint transfer map of a compressed
tensor. The transport runs along a multiplicative, adjoint-preserving linear
equivalence between the full matrix algebra and the corner `P M_D P` that
intertwines the two transfer maps.

### Main results

* `MPSTensor.cyclic_projection_ne_zero_of_sum_one` — a family summing to the
  identity whose members a linear map permutes cyclically has no zero member.
* `MPSTensor.compressedTensor_adjointTransferMap_cornerBridge` — primitivity and
  irreducibility of the corner restriction pass to the compressed tensor's
  adjoint transfer map.
-/

namespace MPSTensor

/-- If cyclic projections sum to `1`, then none of the summands can vanish. -/
theorem cyclic_projection_ne_zero_of_sum_one
    {m D : ℕ} [NeZero m] [NeZero D]
    {T : MatrixEnd D} {P : Fin m → MatrixAlg D}
    (hPsum : ∑ k : Fin m, P k = 1)
    (hCyclic : ∀ k, T (P (k + 1)) = P k) :
    ∀ k, P k ≠ 0 := by
  by_contra! hzero
  obtain ⟨k₀, hk₀⟩ := hzero
  have hback : ∀ j : Fin m, P (j + 1) = 0 → P j = 0 := by
    intro j hj
    rw [← hCyclic j, hj, map_zero]
  have hall : ∀ j : Fin m, P j = 0 := by
    suffices hs : ∀ n : ℕ, n < m → ∀ j : Fin m,
        (k₀ - j).val = n → P j = 0 by
      intro j
      exact hs _ (k₀ - j).isLt j rfl
    intro n
    induction n with
    | zero =>
        intro _ j hj
        have : k₀ - j = 0 := by
          ext
          simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.val_eq_zero_iff] at hj ⊢
          exact hj
        have : k₀ = j := sub_eq_zero.mp this
        subst this
        exact hk₀
    | succ n ih =>
        intro hd j hj
        apply hback j
        apply ih (by omega) (j + 1)
        have h_eq : k₀ - (j + 1) = (k₀ - j) - 1 := by abel
        rw [h_eq, Fin.val_sub_one_of_ne_zero (by intro h; simp [h] at hj)]
        omega
  exact absurd
    (show (∑ k : Fin m, P k) = 0 from Finset.sum_eq_zero (fun k _ => hall k))
    (by rw [hPsum]; exact one_ne_zero)

/-- **Compression-transfer comparison theorem.**

Given a `∗`-algebra compression equivalence `φ : M_n(ℂ) ≃ₗ[ℂ] cornerSubmodule P`
intertwining the compressed adjoint transfer map (of `C`) with the
`P·B`-adjoint transfer map on the corner (`hIntertwine`), and preserving both
multiplication (`hMul`) and the adjoint (`hStar`), primitivity and
irreducibility of the corner restriction of the ambient `T = Kraus.transferMap Bᴴ`
transport to primitivity and irreducibility of `Kraus.transferMap Cᴴ`.

The proof uses `hMul` / `hStar` to lift orthogonal projections on
`M_n(ℂ)` to corner projections `Q = (φ Q').1 ≤ P`, transports
`PreservesCorner` across `φ` via the intertwining identity, and applies
`IsPrimitive.conj_iff_cross` to move primitivity across the cross-space
conjugation `cornerRestriction P T = φ.conj (Kraus.transferMap Cᴴ)`.
-/
theorem compressedTensor_adjointTransferMap_cornerBridge
    {r D n : ℕ} [NeZero n]
    (B : MPSTensor r D) (C : MPSTensor r n) (P : MatrixAlg D)
    (T : MatrixEnd D)
    (φ : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] cornerSubmodule P)
    (hT :
      Kraus.transferMap (ι := Fin r) (n := Fin D) (fun i => (B i)ᴴ) = T)
    (hPproj : IsOrthogonalProjection P)
    (hIntertwine : ∀ X : Matrix (Fin n) (Fin n) ℂ,
      (φ (Kraus.transferMap (ι := Fin r) (n := Fin n) (fun i => (C i)ᴴ) X)).1 =
        Kraus.transferMap (ι := Fin r) (n := Fin D) (fun i => (P * B i)ᴴ) ((φ X).1))
    (hMul : ∀ X Y : Matrix (Fin n) (Fin n) ℂ,
      (φ (X * Y)).1 = (φ X).1 * (φ Y).1)
    (hStar : ∀ X : Matrix (Fin n) (Fin n) ℂ,
      (φ Xᴴ).1 = ((φ X).1)ᴴ)
    (hInv : PreservesCorner P T)
    (hCornerPrim :
      _root_.IsPrimitive (cornerRestriction P T hInv))
    (hCornerIrr : IsIrreducibleOnCorner P T) :
    _root_.IsPrimitive
      (Kraus.transferMap (ι := Fin r) (n := Fin n) (fun i => (C i)ᴴ)) ∧
      IsIrreducibleMap
        (Kraus.transferMap (ι := Fin r) (n := Fin n) (fun i => (C i)ᴴ)) := by
  classical
  set F_C : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    Kraus.transferMap (ι := Fin r) (n := Fin n) (fun i => (C i)ᴴ) with hF_C_def
  have hPherm : Pᴴ = P := hPproj.1.eq
  -- On the corner, the ambient `T` and the `P*B`-adjoint transfer map agree.
  have hTeq :
      ∀ Y : MatrixAlg D, P * Y * P = Y →
        Kraus.transferMap (ι := Fin r) (n := Fin D) (fun i => (P * B i)ᴴ) Y = T Y := by
    intro Y hY
    have hstep :
        Kraus.transferMap (ι := Fin r) (n := Fin D) (fun i => (P * B i)ᴴ) Y =
          Kraus.transferMap (ι := Fin r) (n := Fin D) (fun i => (B i)ᴴ) Y := by
      simp only [Kraus.transferMap_apply]
      refine Finset.sum_congr rfl ?_
      intro i _
      have hPBi : ((P * B i)ᴴ) = (B i)ᴴ * P := by
        rw [Matrix.conjTranspose_mul, hPherm]
      simp only [Matrix.conjTranspose_conjTranspose]
      rw [hPBi]
      calc
        (B i)ᴴ * P * Y * (P * B i)
            = (B i)ᴴ * (P * Y * P) * B i := by
              simp [Matrix.mul_assoc]
        _ = (B i)ᴴ * Y * B i := by rw [hY]
    rw [hstep, hT]
  -- `cornerRestriction P T hInv = φ.conj F_C`.
  have hConj :
      cornerRestriction P T hInv = φ.conj F_C := by
    refine LinearMap.ext ?_
    intro Y
    refine Subtype.ext ?_
    change T Y.1 = (φ.conj F_C Y).1
    rw [LinearEquiv.conj_apply_apply]
    have hkey := hIntertwine (φ.symm Y)
    have hφsy : (φ (φ.symm Y)).1 = Y.1 :=
      congrArg Subtype.val (LinearEquiv.apply_symm_apply φ Y)
    rw [hφsy] at hkey
    rw [hkey]
    exact (hTeq Y.1 Y.2).symm
  -- Primitivity: transport from the corner via cross-space conjugation.
  have hPrim_F_C : _root_.IsPrimitive F_C :=
    (IsPrimitive.conj_iff_cross (e := φ) (f := F_C)).mp (hConj ▸ hCornerPrim)
  -- Irreducibility: map orthogonal projections `Q'` in `M_n(ℂ)` to corner projections.
  -- `(φ 1).1 = P` since `(φ 1).1` is the identity of `cornerSubmodule P`.
  have hφ1_eq_P : (φ 1).1 = P := by
    have hPcorn : P * P * P = P := by rw [hPproj.2, hPproj.2]
    set Yinv : Matrix (Fin n) (Fin n) ℂ := φ.symm ⟨P, hPcorn⟩
    have hφYinv : (φ Yinv).1 = P :=
      congrArg Subtype.val (LinearEquiv.apply_symm_apply φ ⟨P, hPcorn⟩)
    have hPleft : (φ 1).1 * P = P := by
      have hmul := hMul 1 Yinv
      rw [one_mul, hφYinv] at hmul
      exact hmul.symm
    calc
      (φ 1).1 = P * (φ 1).1 * P := ((φ 1).2).symm
      _ = P * ((φ 1).1 * P) := by simp [Matrix.mul_assoc]
      _ = P * P := by rw [hPleft]
      _ = P := hPproj.2
  have hIrr : IsIrreducibleMap F_C := by
    intro Q' hQ'proj hQ'preserves
    set Q : MatrixAlg D := (φ Q').1 with hQ_def
    have hQ_corner : P * Q * P = Q := (φ Q').2
    have hQherm : Qᴴ = Q := by
      have hstar := hStar Q'
      rw [hQ'proj.1.eq] at hstar
      exact hstar.symm
    have hQidem : Q * Q = Q := by
      have h1 := hMul Q' Q'
      rw [hQ'proj.2] at h1
      exact h1.symm
    have hQP : Q * P = Q := by
      calc Q * P = P * Q * P * P := by rw [hQ_corner]
        _ = P * Q * (P * P) := by simp [Matrix.mul_assoc]
        _ = P * Q * P := by rw [hPproj.2]
        _ = Q := hQ_corner
    have hPQ : P * Q = Q := by
      calc P * Q = P * (P * Q * P) := by rw [hQ_corner]
        _ = (P * P) * Q * P := by simp [Matrix.mul_assoc]
        _ = P * Q * P := by rw [hPproj.2]
        _ = Q := hQ_corner
    have hQproj : IsOrthogonalProjection Q := ⟨hQherm, hQidem⟩
    -- PreservesCorner Q T: use `hIntertwine`, `hMul`, and Q'-invariance of F_C.
    have hQinv : PreservesCorner Q T := by
      intro Y
      set W : MatrixAlg D := P * Y * P with hW_def
      have hW_corner : P * W * P = W := by
        change P * (P * Y * P) * P = P * Y * P
        calc
          P * (P * Y * P) * P = (P * P) * Y * (P * P) := by simp [Matrix.mul_assoc]
          _ = P * Y * P := by rw [hPproj.2]
      have hQYQ_eq : Q * Y * Q = Q * W * Q := by
        calc Q * Y * Q
            = (Q * P) * Y * (P * Q) := by rw [hQP, hPQ]
          _ = Q * (P * Y * P) * Q := by simp [Matrix.mul_assoc]
          _ = Q * W * Q := rfl
      set W' : Matrix (Fin n) (Fin n) ℂ := φ.symm ⟨W, hW_corner⟩
      have hφW' : (φ W').1 = W :=
        congrArg Subtype.val (LinearEquiv.apply_symm_apply φ ⟨W, hW_corner⟩)
      set Z' : Matrix (Fin n) (Fin n) ℂ := Q' * W' * Q' with hZ'_def
      have hQWQ_φZ' : Q * W * Q = (φ Z').1 := by
        have hZ'assoc : Z' = Q' * (W' * Q') := by
          simp [hZ'_def, Matrix.mul_assoc]
        calc
          Q * W * Q = (φ Q').1 * W * (φ Q').1 := rfl
          _ = (φ Q').1 * (φ W').1 * (φ Q').1 := by rw [hφW']
          _ = (φ Q').1 * ((φ W').1 * (φ Q').1) := by simp [Matrix.mul_assoc]
          _ = (φ Q').1 * (φ (W' * Q')).1 := by rw [hMul W' Q']
          _ = (φ (Q' * (W' * Q'))).1 := by rw [hMul Q' (W' * Q')]
          _ = (φ Z').1 := by rw [← hZ'assoc]
      have hQYQ_φZ' : Q * Y * Q = (φ Z').1 := hQYQ_eq.trans hQWQ_φZ'
      -- F_C Z' ∈ corner(Q') by Q'-invariance of F_C.
      have hF_C_fix : Q' * F_C Z' * Q' = F_C Z' := by
        have := hQ'preserves W'
        simpa [hZ'_def, hF_C_def] using this
      -- Transport Q'-invariance of F_C via φ.
      have hφF_C_fix : (φ (F_C Z')).1 = Q * (φ (F_C Z')).1 * Q := by
        have key : (φ (Q' * F_C Z' * Q')).1 = Q * (φ (F_C Z')).1 * Q := by
          calc
            (φ (Q' * F_C Z' * Q')).1
                = (φ (Q' * (F_C Z' * Q'))).1 := by rw [Matrix.mul_assoc]
              _ = (φ Q').1 * (φ (F_C Z' * Q')).1 := hMul _ _
              _ = (φ Q').1 * ((φ (F_C Z')).1 * (φ Q').1) := by rw [hMul (F_C Z') Q']
              _ = Q * (φ (F_C Z')).1 * Q := by simp [hQ_def, Matrix.mul_assoc]
        rw [hF_C_fix] at key
        exact key
      -- `T ((φ Z').1) = (φ (F_C Z')).1`.
      have hTφZ' : T ((φ Z').1) = (φ (F_C Z')).1 := by
        have hZ'corner : P * (φ Z').1 * P = (φ Z').1 := (φ Z').2
        have hIw := (hIntertwine Z').symm
        rw [hTeq _ hZ'corner] at hIw
        exact hIw
      rw [hQYQ_φZ', hTφZ']
      exact hφF_C_fix.symm
    rcases hCornerIrr Q hQproj hQP hPQ hQinv with hQ0 | hQP_eq
    · left
      apply φ.injective
      apply Subtype.ext
      simp only [map_zero, Submodule.coe_zero]
      exact hQ0
    · right
      apply φ.injective
      apply Subtype.ext
      rw [hφ1_eq_P]
      exact hQP_eq
  exact ⟨hPrim_F_C, hIrr⟩

end MPSTensor

end CornerBridge

section CyclicSectorDecomposition

open Filter
open Kraus (blockPhysDim blockTensor)

namespace MPSTensor

variable {d D : ℕ}


section SectorOrbitLift

/-!
## Sector primitivity and irreducibility after period removal

The remaining theorems in this section prove that the cyclic-sector
blocks produced by period removal are primitive and tensor-irreducible.
These are internal lemmas that close the orbit-sum / corner-compression
argument; they are not independent results of CPSV.

The sequence of theorems proceeds through progressively weaker
hypotheses (corner-irreducible → proj-step → fixed-algebra-rigidity
→ scalar-blocked-fixed-points) until the unconditional form
`primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking`
is reached.  Only the unconditional form and the top-level existence theorem
`exists_primitive_irreducible_cyclic_sector_decomp_of_TP_of_isIrreducibleFamily`
are consumed by the downstream canonical-form proof chain.
-/

/-- Transport corner primitivity and corner irreducibility of the blocked adjoint
transfer map to the compressed cyclic-sector tensors.

The only remaining hypothesis beyond the cyclic-sector decomposition data is the
corner irreducibility theorem for `((Kraus.transferMap A†)^m)` on each projection
`P k`. In particular, this theorem isolates the orbit-sum / `hProjStep` part of
the non-periodic proof chain from the subsequent compression-transport
step. -/
private theorem
    primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking_of_cornerIrreducible
    {d D m : ℕ} [NeZero D] [NeZero m]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    {γ : ℂ}
    (hγprim : IsPrimitiveRoot γ m)
    (hperiph :
      peripheralEigenvalues (Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => (A i)ᴴ)) =
        Set.range (fun j : Fin m => γ ^ (j : ℕ)))
    {dim : Fin m → ℕ}
    (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    (P : Fin m → MatrixAlg D)
    (φ : (k : Fin m) →
      Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k))
    (hPproj : ∀ k, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic :
      ∀ k : Fin m,
        Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    (hIntertwine :
      ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k (Kraus.transferMap (ι := Fin (blockPhysDim d m)) (n := Fin (dim k))
            (fun i => (blocks k i)ᴴ) X)).1 =
          Kraus.transferMap (ι := Fin (blockPhysDim d m)) (n := Fin D)
            (fun i => (P k * blockTensor A m i)ᴴ) ((φ k X).1))
    (hMul :
      ∀ k (X Y : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k (X * Y)).1 = (φ k X).1 * (φ k Y).1)
    (hStar :
      ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k Xᴴ).1 = ((φ k X).1)ᴴ)
    (hNondeg : ∀ k, dim k ≠ 0)
    (hCornerIrr :
      ∀ k : Fin m,
        IsIrreducibleOnCorner
          (P k)
          ((Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => (A i)ᴴ)) ^ m)) :
    ∀ u : Fin m,
      _root_.IsPrimitive (Kraus.transferMap (blocks u)) ∧
        Kraus.IsIrreducibleFamily (blocks u) := by
  let T : MatrixEnd D := Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => (A i)ᴴ)
  have hMulLeft := cyclic_projection_mul_left (A := A) (m := m) hTP P hPproj hcyclic
  have hMulRight := cyclic_projection_mul_right (A := A) (m := m) hTP P hPproj hcyclic
  have hPne : ∀ k : Fin m, P k ≠ 0 :=
    cyclic_projection_ne_zero_of_sum_one hPsum hcyclic
  intro u
  have : NeZero (dim u) := ⟨hNondeg u⟩
  let hInv : PreservesCorner (P u) (T ^ m) :=
    preserves_corner_pow_of_cyclic_decomp (T := T) P hPproj hPsum hcyclic hMulLeft hMulRight u
  have hCornerPrim : _root_.IsPrimitive (cornerRestriction (P u) (T ^ m) hInv) :=
    isPrimitive_restriction_of_cyclic_decomp (T := T)
      hγprim hperiph P hPproj hPsum hcyclic hMulLeft hMulRight hPne u
  have hTpow :
      Kraus.transferMap (ι := Fin (blockPhysDim d m)) (n := Fin D)
        (fun i => (blockTensor A m i)ᴴ) = T ^ m := by
    ext X : 1
    exact transferMap_adjoint_blocked_eq_pow A m X
  obtain ⟨hPrimAdj, hIrrAdj⟩ :=
    compressedTensor_adjointTransferMap_cornerBridge
      (B := blockTensor A m) (C := blocks u) (P := P u) (T := T ^ m) (φ := φ u)
      hTpow (hPproj u) (hIntertwine u) (hMul u) (hStar u) hInv hCornerPrim (hCornerIrr u)
  have hM : (1 : Matrix (Fin (dim u)) (Fin (dim u)) ℂ).PosDef := by
    classical
    simpa only using (Matrix.PosDef.one (n := Fin (dim u)) (R := ℂ))
  let : NormedAddCommGroup (Matrix (Fin (dim u)) (Fin (dim u)) ℂ) :=
    Matrix.toMatrixNormedAddCommGroup (n := Fin (dim u)) (𝕜 := ℂ) 1 hM
  let : SeminormedAddCommGroup (Matrix (Fin (dim u)) (Fin (dim u)) ℂ) :=
    Matrix.toMatrixSeminormedAddCommGroup (n := Fin (dim u)) (𝕜 := ℂ) 1 hM.posSemidef
  let : InnerProductSpace ℂ (Matrix (Fin (dim u)) (Fin (dim u)) ℂ) :=
    Matrix.toMatrixInnerProductSpace (n := Fin (dim u)) (𝕜 := ℂ) 1 hM.posSemidef
  have hAdj :
      Kraus.transferMap (ι := Fin (blockPhysDim d m)) (n := Fin (dim u)) (fun i => (blocks u i)ᴴ) =
        (Kraus.transferMap (blocks u)).adjoint := by
    simpa only using
      (Kraus.mapLM_conjTranspose_eq_adjoint (K := blocks u))
  have hPrimAdj' :
      _root_.IsPrimitive
        ((Kraus.transferMap (blocks u)).adjoint) := by
    simpa only [hAdj] using hPrimAdj
  refine ⟨(IsPrimitive.adjoint_iff
    (E := Kraus.transferMap (blocks u))).1 hPrimAdj', ?_⟩
  exact Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM (blocks u)
    ((Kraus.isIrreducibleMap_mapLM_conjTranspose_iff (blocks u)).mp hIrrAdj)

/-- Unconditional: cyclic-sector blocks after period removal are primitive and
tensor-irreducible.

This is the internal lemma that closes the orbit-sum / corner-compression
argument.  It uses `isIrreducibleOnCorner_of_cyclic_decomp_mps` so that no
extra projection-step or fixed-point-algebra hypotheses are needed when the
ambient tensor is irreducible and trace-preserving. -/
theorem primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking
    {d D m : ℕ} [NeZero D] [NeZero m]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : Kraus.IsIrreducibleFamily A)
    {γ : ℂ}
    (hγprim : IsPrimitiveRoot γ m)
    (hperiph :
      peripheralEigenvalues (Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => (A i)ᴴ)) =
        Set.range (fun j : Fin m => γ ^ (j : ℕ)))
    {dim : Fin m → ℕ}
    (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    (P : Fin m → MatrixAlg D)
    (φ : (k : Fin m) →
      Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k))
    (hPproj : ∀ k, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic :
      ∀ k : Fin m,
        Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    (hIntertwine :
      ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k (Kraus.transferMap (ι := Fin (blockPhysDim d m)) (n := Fin (dim k))
            (fun i => (blocks k i)ᴴ) X)).1 =
          Kraus.transferMap (ι := Fin (blockPhysDim d m)) (n := Fin D)
            (fun i => (P k * blockTensor A m i)ᴴ) ((φ k X).1))
    (hMul :
      ∀ k (X Y : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k (X * Y)).1 = (φ k X).1 * (φ k Y).1)
    (hStar :
      ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k Xᴴ).1 = ((φ k X).1)ᴴ)
    (hNondeg : ∀ k, dim k ≠ 0) :
    ∀ u : Fin m,
      _root_.IsPrimitive (Kraus.transferMap (blocks u)) ∧
        Kraus.IsIrreducibleFamily (blocks u) := by
  let T : MatrixEnd D := Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => (A i)ᴴ)
  have hIrrAdj : IsIrreducibleMap T := by
    simpa [T] using
      Kraus.isIrreducibleMap_mapLM_conjTranspose A
        (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hIrr)
  have hMulLeft := cyclic_projection_mul_left (A := A) (m := m) hTP P hPproj hcyclic
  have hMulRight := cyclic_projection_mul_right (A := A) (m := m) hTP P hPproj hcyclic
  have hCornerIrr :
      ∀ k : Fin m, IsIrreducibleOnCorner (P k) (T ^ m) := by
    intro k
    exact isIrreducibleOnCorner_of_cyclic_decomp_mps
      (A := A) (m := m) hIrrAdj hTP P hPproj hPsum hcyclic hMulLeft hMulRight k
  exact primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking_of_cornerIrreducible
    A hTP hγprim hperiph blocks P φ hPproj hPsum hcyclic hIntertwine hMul hStar hNondeg
    hCornerIrr

/-- QPF derivation for period removal.

For an irreducible trace-preserving tensor, there are a positive period `m`, a
primitive `m`th root `γ`, and a cyclic-sector decomposition of `A^[m]`.  The
positive adjoint fixed point and the map-level irreducibility are consequences
of quantum Perron--Frobenius theory, so the only hypotheses are
trace-preservation and tensor irreducibility. -/
private theorem exists_cyclic_sector_decomp_with_peripheral_data_of_TP_of_irreducible
    {d D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : Kraus.IsIrreducibleFamily A) :
    ∃ (m : ℕ) (_ : NeZero m) (_ : 0 < m) (γ : ℂ),
      IsPrimitiveRoot γ m ∧
      peripheralEigenvalues (Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => (A i)ᴴ)) =
        Set.range (fun j : Fin m => γ ^ (j : ℕ)) ∧
      ∃ (dim : Fin m → ℕ)
        (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
        (P : Fin m → MatrixAlg D)
        (φ : (k : Fin m) →
          Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k)),
        (∀ k, ∑ i : Fin (blockPhysDim d m), (blocks k i)ᴴ * blocks k i = 1) ∧
        SameMPV₂ (blockTensor A m)
          (toTensorFromBlocks (α := Fin (blockPhysDim d m)) (μ := fun _ : Fin m => (1 : ℂ))
            blocks) ∧
        (∀ k, IsOrthogonalProjection (P k)) ∧
        (∑ k : Fin m, P k = 1) ∧
        (∀ k, Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => (A i)ᴴ) (P (k + 1)) = P k) ∧
        (∀ k (i : Fin (blockPhysDim d m)),
          P k * (blockTensor A m) i = (blockTensor A m) i * P k) ∧
        (∀ k (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)),
          mpv (blocks k) σ = (P k * Kraus.evalWord (blockTensor A m) (List.ofFn σ)).trace) ∧
        (∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
          (φ k (Kraus.transferMap (ι := Fin (blockPhysDim d m)) (n := Fin (dim k))
              (fun i => (blocks k i)ᴴ) X)).1 =
            Kraus.transferMap (ι := Fin (blockPhysDim d m)) (n := Fin D)
              (fun i => (P k * blockTensor A m i)ᴴ) ((φ k X).1)) ∧
        (∀ k (X Y : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
          (φ k (X * Y)).1 = (φ k X).1 * (φ k Y).1) ∧
        (∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
          (φ k Xᴴ).1 = ((φ k X).1)ᴴ) ∧
        (∀ k, dim k ≠ 0) := by
  obtain ⟨K, h_unitalK, hIrrK, ρ, hρ_pd, h_adjfix, rfl⟩ :=
    conjTranspose_kraus_setup A hTP hIrr
  have hIrrKLM : IsIrreducibleMap (Kraus.mapLM (fun i => (A i)ᴴ)) := by
    exact hIrrK
  obtain ⟨m, γ, hm_pos, hγ_prim, hperiph_set⟩ :=
    PeripheralSpectrum.peripheral_eigenvalues_cyclic_structure _ h_unitalK ρ hρ_pd h_adjfix
      hIrrKLM
  have hperiph_range :
      peripheralEigenvalues (Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => (A i)ᴴ)) =
        Set.range (fun j : Fin m => γ ^ (j : ℕ)) := by
    rw [hperiph_set]
    ext x
    simp [Set.mem_range, eq_comm]
  let hne : NeZero m := ⟨Nat.ne_of_gt hm_pos⟩
  have : NeZero m := hne
  obtain ⟨dim, blocks, P, φ, _V, hTP_blocks, hSame, hPproj, hPsum, hcyclic, hComm,
      hTrace, hIntertwine, hMul, hStar, _hLetter, _hV_iso, _hV_range, _hEmbed, hNondeg⟩ :=
    exists_cyclic_sector_decomp_after_blocking_with_letter_and_isometry A hTP hIrr ρ hρ_pd
      h_adjfix hIrrK hγ_prim hperiph_range
  exact ⟨m, hne, hm_pos, γ, hγ_prim, hperiph_range, dim, blocks, P, φ, hTP_blocks, hSame,
    hPproj, hPsum, hcyclic, hComm, hTrace, hIntertwine, hMul, hStar, hNondeg⟩

/-- **Period removal by blocking.**

For an irreducible trace-preserving tensor `A`, the cyclic-sector decomposition
after period-removing blocking follows from trace-preservation and tensor
irreducibility alone:
the positive adjoint fixed point, primitive peripheral root, and map-level
irreducibility are consequences of quantum Perron--Frobenius theory.

The statement records the period-removal decomposition for irreducible
trace-preserving MPS tensors described in arXiv:1606.00608, lines 227--231. -/
theorem exists_cyclic_sector_decomp_after_blocking_of_TP_of_isIrreducibleFamily
    {d D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : Kraus.IsIrreducibleFamily A) :
    ∃ (m : ℕ) (_ : NeZero m) (_ : 0 < m)
      (dim : Fin m → ℕ)
      (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
      (P : Fin m → MatrixAlg D)
      (φ : (k : Fin m) →
        Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k)),
      (∀ k, ∑ i : Fin (blockPhysDim d m), (blocks k i)ᴴ * blocks k i = 1) ∧
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (α := Fin (blockPhysDim d m)) (μ := fun _ : Fin m => (1 : ℂ))
          blocks) ∧
      (∀ k, IsOrthogonalProjection (P k)) ∧
      (∑ k : Fin m, P k = 1) ∧
      (∀ k, Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => (A i)ᴴ) (P (k + 1)) = P k) ∧
      (∀ k (i : Fin (blockPhysDim d m)),
        P k * (blockTensor A m) i = (blockTensor A m) i * P k) ∧
      (∀ k (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)),
        mpv (blocks k) σ = (P k * Kraus.evalWord (blockTensor A m) (List.ofFn σ)).trace) ∧
      (∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k (Kraus.transferMap (ι := Fin (blockPhysDim d m)) (n := Fin (dim k))
            (fun i => (blocks k i)ᴴ) X)).1 =
          Kraus.transferMap (ι := Fin (blockPhysDim d m)) (n := Fin D)
            (fun i => (P k * blockTensor A m i)ᴴ) ((φ k X).1)) ∧
      (∀ k (X Y : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k (X * Y)).1 = (φ k X).1 * (φ k Y).1) ∧
      (∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k Xᴴ).1 = ((φ k X).1)ᴴ) ∧
      (∀ k, dim k ≠ 0) := by
  obtain ⟨m, hne, hm_pos, _γ, _hγ_prim, _hperiph, hdecomp⟩ :=
    exists_cyclic_sector_decomp_with_peripheral_data_of_TP_of_irreducible
      A hTP hIrr
  have : NeZero m := hne
  obtain ⟨dim, blocks, P, φ, hTP_blocks, hSame, hPproj, hPsum, hcyclic, hComm,
    hTrace, hIntertwine, hMul, hStar, hNondeg⟩ := hdecomp
  exact ⟨m, hne, hm_pos, dim, blocks, P, φ, hTP_blocks, hSame, hPproj, hPsum, hcyclic,
    hComm, hTrace, hIntertwine, hMul, hStar, hNondeg⟩

/-- **Period removal with primitive, irreducible sectors.**

For an irreducible TP tensor `A`, after blocking by the least common
multiple of its periods the blocked tensor is a unit-weight sum of
primitive, tensor-irreducible, trace-preserving sector blocks with
positive bond dimensions.

This encodes the unconditional sector-orbit lift into the single
result consumed by the downstream common-blocking construction.  It is
the period-removal step of arXiv:1606.00608, §2.3, strengthened with
primitivity and irreducibility of the sector blocks. -/
theorem exists_primitive_irreducible_cyclic_sector_decomp_of_TP_of_isIrreducibleFamily
    {d D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : Kraus.IsIrreducibleFamily A) :
    ∃ (m : ℕ) (_ : 0 < m)
      (dim : Fin m → ℕ) (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k)),
      (∀ k, ∑ i : Fin (blockPhysDim d m), (blocks k i)ᴴ * blocks k i = 1) ∧
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (α := Fin (blockPhysDim d m)) (μ := fun _ : Fin m => (1 : ℂ)) blocks) ∧
      (∀ k, _root_.IsPrimitive
        (Kraus.transferMap (ι := Fin (blockPhysDim d m)) (n := Fin (dim k)) (blocks k))) ∧
      (∀ k, Kraus.IsIrreducibleFamily (blocks k)) ∧
      (∀ k, 0 < dim k) := by
  obtain ⟨m, hne, hm_pos, _γ, hγ_prim, hperiph_range, hdecomp⟩ :=
    exists_cyclic_sector_decomp_with_peripheral_data_of_TP_of_irreducible
      A hTP hIrr
  have : NeZero m := hne
  obtain ⟨dim, blocks, P, φ, hTP_blocks, hSame, hPproj, hPsum, hcyclic, _hComm,
      _hTrace, hIntertwine, hMul, hStar, hNondeg⟩ :=
    hdecomp
  have hPrimIrr : ∀ u : Fin m,
      _root_.IsPrimitive (Kraus.transferMap (blocks u)) ∧
        Kraus.IsIrreducibleFamily (blocks u) :=
    primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking
      A hTP hIrr hγ_prim hperiph_range blocks P φ hPproj hPsum hcyclic hIntertwine hMul hStar
      hNondeg
  refine ⟨m, hm_pos, dim, blocks, hTP_blocks, hSame, ?_, ?_, ?_⟩
  · intro k
    exact (hPrimIrr k).1
  · intro k
    exact (hPrimIrr k).2
  · intro k
    exact Nat.pos_of_ne_zero (hNondeg k)

end SectorOrbitLift

end MPSTensor

end CyclicSectorDecomposition
