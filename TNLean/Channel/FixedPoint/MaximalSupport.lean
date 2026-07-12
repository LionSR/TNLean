/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.FixedPoint.WeightedCornerFixedPoints
import TNLean.Channel.FixedPoint.Cesaro

/-!
# A fixed point of maximal support

For a trace-preserving Kraus map $T$ there is a positive semidefinite fixed point
$\rho_0$ whose support carries every fixed point: $Q_0 X Q_0 = X$ for every fixed point
$X$ of $T$, where $Q_0$ is the support projection of $\rho_0$. This is the maximal-support
property of fixed points stated in Section 6.4 of *Quantum Channels & Operations*
(Wolf 2012), there in terms of the fixed point obtained by applying the projection onto
the fixed-point space to the identity; the construction here instead sums the positive
parts of a basis of the fixed-point space, so that every fixed point is a linear
combination of positive fixed points dominated by $\rho_0$, and domination transfers the
support:
$$0 \preceq P \preceq \rho \;\Longrightarrow\; Q\,P = P = P\,Q,$$
for $Q$ the support projection of $\rho$.

Instantiating the weighted corner fixed points at $\rho_0$ removes the corner-support
restriction: conjugation by $\sqrt{\rho_0}$ maps the weighted corner star-algebra
(`Kraus.weightedCornerFixedPointsStarSubalgebra`) onto the full fixed-point set of $T$,
which is the set $\rho_0^{-1/2}\,\{X \mid T(X) = X\}\,\rho_0^{-1/2}$ of Corollary 6.7 of
*Quantum Channels & Operations* (Wolf 2012), with the inverse square root taken on the
support of $\rho_0$.

## Main results

* `Kraus.stationaryProj_absorb_of_le` -- Loewner domination transfers the support: for
  positive semidefinite $P \preceq \rho$, the support projection of $\rho$ absorbs $P$.
* `Kraus.exists_maximalSupport_fixedPoint` -- a positive semidefinite fixed point whose
  support carries every fixed point.
* `Kraus.exists_maximalSupport_weightedCorner_sqrt_eq` -- at such a fixed point,
  conjugation by the square root maps the weighted corner carrier onto the full
  fixed-point set.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

namespace Kraus

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- **Loewner domination transfers the support.** For positive semidefinite matrices
$P \preceq \rho$, the support projection $Q$ of $\rho$ absorbs $P$:
$Q P = P$ and $P Q = P$. From $(\mathbf 1 - Q)\rho = 0$ and
$0 \preceq (\mathbf 1 - Q) P (\mathbf 1 - Q) \preceq (\mathbf 1 - Q) \rho (\mathbf 1 - Q)
= 0$ one gets $(\mathbf 1 - Q)\sqrt{P}\,\bigl((\mathbf 1 - Q)\sqrt{P}\bigr)^{\dagger} = 0$,
hence $(\mathbf 1 - Q)\sqrt{P} = 0$ and $(\mathbf 1 - Q)P = 0$. -/
theorem stationaryProj_absorb_of_le {ρ P : Mat} (hρ_psd : ρ.PosSemidef)
    (hP_psd : P.PosSemidef) (hle : P ≤ ρ) :
    stationaryProj hρ_psd * P = P ∧ P * stationaryProj hρ_psd = P := by
  set Q : Mat := stationaryProj hρ_psd with hQdef
  have hQproj : IsOrthogonalProjection Q := isOrthogonalProjection_stationaryProj hρ_psd
  have hQherm : Qᴴ = Q := hQproj.1.eq
  have h1Q : (1 - Q)ᴴ = 1 - Q := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hQherm]
  have hQρ : Q * ρ = ρ := MPSTensor.supportProj_mul (D := D) (ρ := ρ) hρ_psd
  have hρQ : ρ * Q = ρ := MPSTensor.mul_supportProj (D := D) (ρ := ρ) hρ_psd
  -- The corner of `ρ` on the complement of the support vanishes.
  have hρ0 : (1 - Q) * ρ * (1 - Q) = 0 := by
    have h : (1 - Q) * ρ = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, hQρ, sub_self]
    rw [h, Matrix.zero_mul]
  -- Hence so does the corner of the dominated `P`.
  have hP0 : (1 - Q) * P * (1 - Q) = 0 := by
    have hupper : (1 - Q) * P * (1 - Q) ≤ 0 := by
      have hconj : (1 - Q) * P * (1 - Q) ≤ (1 - Q) * ρ * (1 - Q) := by
        rw [← sub_nonneg] at hle ⊢
        have hpsd : ((1 - Q)ᴴ * (ρ - P) * (1 - Q)).PosSemidef :=
          (hle.posSemidef).conjTranspose_mul_mul_same (1 - Q)
        rw [h1Q] at hpsd
        have heq : (1 - Q) * ρ * (1 - Q) - (1 - Q) * P * (1 - Q) =
            (1 - Q) * (ρ - P) * (1 - Q) := by
          rw [mul_sub (1 - Q) ρ P, sub_mul ((1 - Q) * ρ) ((1 - Q) * P) (1 - Q)]
        rw [heq]
        exact hpsd.nonneg
      calc (1 - Q) * P * (1 - Q) ≤ (1 - Q) * ρ * (1 - Q) := hconj
        _ = 0 := hρ0
    have hlower : (0 : Mat) ≤ (1 - Q) * P * (1 - Q) := by
      have : ((1 - Q)ᴴ * P * (1 - Q)).PosSemidef :=
        hP_psd.conjTranspose_mul_mul_same (1 - Q)
      rw [h1Q] at this
      exact this.nonneg
    exact le_antisymm hupper hlower
  -- Vanishing corner of a positive semidefinite matrix forces the whole row to vanish.
  have hS_herm : (CFC.sqrt P)ᴴ = CFC.sqrt P := MPSTensor.conjTranspose_cfc_sqrt (D := D) P
  have hSS : CFC.sqrt P * CFC.sqrt P = P := CFC.sqrt_mul_sqrt_self P hP_psd.nonneg
  have hM0 : ((1 - Q) * CFC.sqrt P) * ((1 - Q) * CFC.sqrt P)ᴴ = 0 := by
    rw [Matrix.conjTranspose_mul, hS_herm, h1Q]
    calc (1 - Q) * CFC.sqrt P * (CFC.sqrt P * (1 - Q))
        = (1 - Q) * (CFC.sqrt P * CFC.sqrt P) * (1 - Q) := by simp [Matrix.mul_assoc]
      _ = (1 - Q) * P * (1 - Q) := by rw [hSS]
      _ = 0 := hP0
  have hMsqrt : (1 - Q) * CFC.sqrt P = 0 := Matrix.self_mul_conjTranspose_eq_zero.mp hM0
  have hQP : Q * P = P := by
    have h : (1 - Q) * P = 0 := by
      calc (1 - Q) * P = ((1 - Q) * CFC.sqrt P) * CFC.sqrt P := by
            rw [Matrix.mul_assoc, hSS]
        _ = 0 := by rw [hMsqrt, Matrix.zero_mul]
    rw [Matrix.sub_mul, Matrix.one_mul] at h
    exact (sub_eq_zero.mp h).symm
  refine ⟨hQP, ?_⟩
  have h := congrArg Matrix.conjTranspose hQP
  rwa [Matrix.conjTranspose_mul, hQherm, hP_psd.isHermitian.eq] at h

/-- The transfer map of a trace-preserving Kraus family is a quantum channel: it is
completely positive by its Kraus form and trace-preserving because
$\sum_i K_i^\dagger K_i = \mathbf 1$. -/
theorem isChannel_transferMap (K : Fin d → Mat) (h_tp : IsTP K) :
    IsChannel (MPSTensor.transferMap (d := d) (D := D) K) := by
  constructor
  · exact ⟨d, K, fun X => by simp [MPSTensor.transferMap_apply]⟩
  · intro X
    calc Matrix.trace (MPSTensor.transferMap (d := d) (D := D) K X)
        = ∑ i : Fin d, Matrix.trace (K i * X * (K i)ᴴ) := by
          rw [MPSTensor.transferMap_apply, Matrix.trace_sum]
      _ = ∑ i : Fin d, Matrix.trace ((K i)ᴴ * K i * X) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Matrix.trace_mul_cycle]
      _ = Matrix.trace ((∑ i : Fin d, (K i)ᴴ * K i) * X) := by
          rw [Matrix.sum_mul, Matrix.trace_sum]
      _ = Matrix.trace X := by rw [h_tp, Matrix.one_mul]

/-- **A fixed point of maximal support.** For a trace-preserving Kraus map $T$ there is a
positive semidefinite fixed point $\rho_0$ whose support carries every fixed point:
$Q_0 X Q_0 = X$ for every $X$ with $T(X) = X$, where $Q_0$ is the support projection of
$\rho_0$. This is the maximal-support property of fixed points stated in Section 6.4 of
*Quantum Channels & Operations* (Wolf 2012); the reference exhibits the witness as the
image of the identity under the projection onto the fixed-point space, while here
$\rho_0$ is the sum of the positive parts of the Hermitian and anti-Hermitian components
of a basis of the fixed-point space. Every fixed point is then a linear combination of
positive semidefinite fixed points dominated by $\rho_0$ in the Loewner order, and
domination transfers the support (`Kraus.stationaryProj_absorb_of_le`). In particular
$\rho_0$ has maximal rank among the positive semidefinite fixed points, and after
normalization it is a fixed-point density matrix of maximum rank. -/
theorem exists_maximalSupport_fixedPoint (K : Fin d → Mat) (h_tp : IsTP K) :
    ∃ (ρ₀ : Mat) (hρ₀ : ρ₀.PosSemidef), map K ρ₀ = ρ₀ ∧
      ∀ X : Mat, map K X = X →
        stationaryProj hρ₀ * X * stationaryProj hρ₀ = X := by
  classical
  set E : Mat →ₗ[ℂ] Mat := MPSTensor.transferMap (d := d) (D := D) K with hEdef
  have hEK : ∀ X : Mat, E X = map K X := by
    intro X
    simp [hEdef, MPSTensor.transferMap_apply, map]
  have hE : IsChannel E := isChannel_transferMap K h_tp
  -- Positive parts of a Hermitian fixed point are fixed (Proposition 6.8 of the source).
  have hpos : ∀ H : Mat, H.IsHermitian → map K H = H →
      ∃ P₁ P₂ : Mat, P₁.PosSemidef ∧ P₂.PosSemidef ∧ H = P₁ - P₂ ∧
        map K P₁ = P₁ ∧ map K P₂ = P₂ := by
    intro H hH hHfix
    obtain ⟨P₁, P₂, h₁, h₂, hdiff, hf₁, hf₂⟩ :=
      IsChannel.posSemidef_parts_of_hermitian_fixedPoint E hE hH
        (by rw [hEK]; exact hHfix)
    exact ⟨P₁, P₂, h₁, h₂, hdiff, by rw [← hEK]; exact hf₁, by rw [← hEK]; exact hf₂⟩
  -- A basis of the fixed-point space, the eigenspace of the transfer map at one.
  set S : Submodule ℂ Mat := Module.End.eigenspace E 1 with hSdef
  have hSmem : ∀ X : Mat, X ∈ S ↔ map K X = X := by
    intro X
    rw [hSdef, Module.End.mem_eigenspace_iff, one_smul, hEK]
  set m : ℕ := Module.finrank ℂ ↥S with hmdef
  set b : Module.Basis (Fin m) ℂ ↥S := Module.finBasis ℂ ↥S with hbdef
  -- The Hermitian and anti-Hermitian components of the basis vectors are fixed.
  have hbfix : ∀ j : Fin m, map K ((b j : Mat)) = (b j : Mat) := fun j => (hSmem _).mp (b j).2
  have hbHfix : ∀ j : Fin m, map K ((b j : Mat))ᴴ = ((b j : Mat))ᴴ := fun j =>
    conjTranspose_mem_fixedPoints (K := K) (hbfix j)
  set H₁ : Fin m → Mat := fun j => (b j : Mat) + (b j : Mat)ᴴ with hH₁def
  set H₂ : Fin m → Mat := fun j => Complex.I • ((b j : Mat) - (b j : Mat)ᴴ) with hH₂def
  have hH₁herm : ∀ j, (H₁ j).IsHermitian := by
    intro j
    show ((b j : Mat) + (b j : Mat)ᴴ)ᴴ = (b j : Mat) + (b j : Mat)ᴴ
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
    exact add_comm _ _
  have hH₂herm : ∀ j, (H₂ j).IsHermitian := by
    intro j
    show (Complex.I • ((b j : Mat) - (b j : Mat)ᴴ))ᴴ =
      Complex.I • ((b j : Mat) - (b j : Mat)ᴴ)
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose]
    rw [show star Complex.I = -Complex.I by simp]
    rw [neg_smul, ← smul_neg, neg_sub]
  have hH₁fix : ∀ j, map K (H₁ j) = H₁ j := by
    intro j
    show map K ((b j : Mat) + (b j : Mat)ᴴ) = (b j : Mat) + (b j : Mat)ᴴ
    rw [← hEK, E.map_add, hEK, hEK, hbfix j, hbHfix j]
  have hH₂fix : ∀ j, map K (H₂ j) = H₂ j := by
    intro j
    show map K (Complex.I • ((b j : Mat) - (b j : Mat)ᴴ)) =
      Complex.I • ((b j : Mat) - (b j : Mat)ᴴ)
    rw [← hEK, E.map_smul, E.map_sub, hEK, hEK, hbfix j, hbHfix j]
  -- Each basis vector is a combination of its Hermitian and anti-Hermitian components.
  have hXj : ∀ j, (b j : Mat) = (2⁻¹ : ℂ) • H₁ j - ((2⁻¹ : ℂ) * Complex.I) • H₂ j := by
    intro j
    show (b j : Mat) = (2⁻¹ : ℂ) • ((b j : Mat) + (b j : Mat)ᴴ) -
      ((2⁻¹ : ℂ) * Complex.I) • (Complex.I • ((b j : Mat) - (b j : Mat)ᴴ))
    rw [smul_smul,
      show ((2⁻¹ : ℂ) * Complex.I) * Complex.I = -(2⁻¹ : ℂ) by
        rw [mul_assoc, Complex.I_mul_I]; ring]
    module
  -- Positive parts of the components, all of them fixed points.
  choose P₁p P₁m hP₁p hP₁m hH₁eq hf₁p hf₁m using fun j => hpos (H₁ j) (hH₁herm j) (hH₁fix j)
  choose P₂p P₂m hP₂p hP₂m hH₂eq hf₂p hf₂m using fun j => hpos (H₂ j) (hH₂herm j) (hH₂fix j)
  -- The maximal fixed point: the sum of all the positive parts.
  set g : Fin m → Mat := fun j => P₁p j + P₁m j + P₂p j + P₂m j with hgdef
  have hg_nonneg : ∀ j, (0 : Mat) ≤ g j := by
    intro j
    show (0 : Mat) ≤ P₁p j + P₁m j + P₂p j + P₂m j
    exact add_nonneg (add_nonneg (add_nonneg (hP₁p j).nonneg (hP₁m j).nonneg)
      (hP₂p j).nonneg) (hP₂m j).nonneg
  set ρ₀ : Mat := ∑ j : Fin m, g j with hρ₀def
  have hρ₀psd : ρ₀.PosSemidef :=
    (Finset.sum_nonneg fun j _ => hg_nonneg j).posSemidef
  have hρ₀fix : map K ρ₀ = ρ₀ := by
    rw [hρ₀def, ← hEK, _root_.map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show E (P₁p j + P₁m j + P₂p j + P₂m j) = g j
    rw [E.map_add, E.map_add, E.map_add, hEK, hEK, hEK, hEK,
      hf₁p j, hf₁m j, hf₂p j, hf₂m j]
  refine ⟨ρ₀, hρ₀psd, hρ₀fix, ?_⟩
  set Q₀ : Mat := stationaryProj hρ₀psd with hQ₀def
  -- Every positive part is dominated by the sum, so the support projection absorbs it.
  have hg_le : ∀ j, g j ≤ ρ₀ := fun j =>
    Finset.single_le_sum (fun i _ => hg_nonneg i) (Finset.mem_univ j)
  have habsorb : ∀ (P : Mat), P.PosSemidef → P ≤ ρ₀ → Q₀ * P * Q₀ = P := by
    intro P hP hle
    obtain ⟨hQP, hPQ⟩ := stationaryProj_absorb_of_le hρ₀psd hP hle
    rw [Matrix.mul_assoc, hPQ, hQP]
  have hle₁p : ∀ j, P₁p j ≤ ρ₀ := by
    intro j
    refine le_trans (show P₁p j ≤ g j from ?_) (hg_le j)
    calc P₁p j ≤ P₁p j + P₁m j := le_add_of_nonneg_right (hP₁m j).nonneg
      _ ≤ P₁p j + P₁m j + P₂p j := le_add_of_nonneg_right (hP₂p j).nonneg
      _ ≤ P₁p j + P₁m j + P₂p j + P₂m j := le_add_of_nonneg_right (hP₂m j).nonneg
  have hle₁m : ∀ j, P₁m j ≤ ρ₀ := by
    intro j
    refine le_trans (show P₁m j ≤ g j from ?_) (hg_le j)
    calc P₁m j ≤ P₁p j + P₁m j := le_add_of_nonneg_left (hP₁p j).nonneg
      _ ≤ P₁p j + P₁m j + P₂p j := le_add_of_nonneg_right (hP₂p j).nonneg
      _ ≤ P₁p j + P₁m j + P₂p j + P₂m j := le_add_of_nonneg_right (hP₂m j).nonneg
  have hle₂p : ∀ j, P₂p j ≤ ρ₀ := by
    intro j
    refine le_trans (show P₂p j ≤ g j from ?_) (hg_le j)
    calc P₂p j ≤ P₁p j + P₁m j + P₂p j := le_add_of_nonneg_left
          (add_nonneg (hP₁p j).nonneg (hP₁m j).nonneg)
      _ ≤ P₁p j + P₁m j + P₂p j + P₂m j := le_add_of_nonneg_right (hP₂m j).nonneg
  have hle₂m : ∀ j, P₂m j ≤ ρ₀ := by
    intro j
    refine le_trans (show P₂m j ≤ g j from ?_) (hg_le j)
    exact le_add_of_nonneg_left (add_nonneg (add_nonneg (hP₁p j).nonneg (hP₁m j).nonneg)
      (hP₂p j).nonneg)
  -- The support projection absorbs the components, hence the basis vectors.
  have habsorbH₁ : ∀ j, Q₀ * H₁ j * Q₀ = H₁ j := by
    intro j
    rw [hH₁eq j, Matrix.mul_sub, Matrix.sub_mul,
      habsorb _ (hP₁p j) (hle₁p j), habsorb _ (hP₁m j) (hle₁m j)]
  have habsorbH₂ : ∀ j, Q₀ * H₂ j * Q₀ = H₂ j := by
    intro j
    rw [hH₂eq j, Matrix.mul_sub, Matrix.sub_mul,
      habsorb _ (hP₂p j) (hle₂p j), habsorb _ (hP₂m j) (hle₂m j)]
  have hQb : ∀ j, Q₀ * (b j : Mat) * Q₀ = (b j : Mat) := by
    intro j
    conv_lhs => rw [hXj j]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul, habsorbH₁ j, habsorbH₂ j, ← hXj j]
  -- Every fixed point is a combination of the basis vectors, all carried by the support.
  intro X hX
  have hXS : X ∈ S := (hSmem X).mpr hX
  have hrepr : ∑ j : Fin m, b.repr ⟨X, hXS⟩ j • (b j : Mat) = X := by
    have h := congrArg (Subtype.val) (b.sum_repr ⟨X, hXS⟩)
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
    exact h
  calc Q₀ * X * Q₀
      = ∑ j : Fin m, b.repr ⟨X, hXS⟩ j • (Q₀ * (b j : Mat) * Q₀) := by
        conv_lhs => rw [← hrepr]
        rw [Matrix.mul_sum, Matrix.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by
          rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = ∑ j : Fin m, b.repr ⟨X, hXS⟩ j • (b j : Mat) := by
        exact Finset.sum_congr rfl fun j _ => by rw [hQb j]
    _ = X := hrepr

/-- **Conjugation by the square root at a fixed point of maximal support.** For a
trace-preserving Kraus map $T$ there is a positive semidefinite fixed point $\rho_0$ such
that every fixed point $X$ of $T$ arises as $X = \sqrt{\rho_0}\, Y \sqrt{\rho_0}$ for a
corner-supported $Y$ with $\sqrt{\rho_0}\, Y \sqrt{\rho_0}$ fixed by $T$: conjugation by
$\sqrt{\rho_0}$ maps the carrier of the weighted corner star-subalgebra
(`Kraus.weightedCornerFixedPointsStarSubalgebra`) onto the full fixed-point set, so that
set realizes
$$\rho_0^{-1/2}\,\{X \mid T(X) = X\}\,\rho_0^{-1/2},$$
with the inverse square root taken on the support of $\rho_0$. This is the conjugated
fixed-point set of Corollary 6.7 of *Quantum Channels & Operations* (Wolf 2012), at a
fixed point of maximal support; after normalization $\rho_0$ is a fixed-point density
matrix of maximum rank, as in the corollary. -/
theorem exists_maximalSupport_weightedCorner_sqrt_eq (K : Fin d → Mat) (h_tp : IsTP K) :
    ∃ (ρ₀ : Mat) (hρ₀ : ρ₀.PosSemidef), map K ρ₀ = ρ₀ ∧
      ∀ X : Mat, map K X = X →
        ∃ Y : Mat, stationaryProj hρ₀ * Y * stationaryProj hρ₀ = Y ∧
          map K (CFC.sqrt ρ₀ * Y * CFC.sqrt ρ₀) = CFC.sqrt ρ₀ * Y * CFC.sqrt ρ₀ ∧
          CFC.sqrt ρ₀ * Y * CFC.sqrt ρ₀ = X := by
  obtain ⟨ρ₀, hρ₀, hfix, hmax⟩ := exists_maximalSupport_fixedPoint K h_tp
  exact ⟨ρ₀, hρ₀, hfix, fun X hX =>
    exists_weightedCorner_sqrt_eq_of_fixedPoint K h_tp hρ₀ hfix hX (hmax X hX)⟩

end Kraus
