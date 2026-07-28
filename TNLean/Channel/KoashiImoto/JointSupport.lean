/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.SupportInvariance
import TNLean.Channel.KoashiImoto.PreservingBlockAction
import TNLean.Channel.Spectral.Support

/-!
# Joint-support compression for invariant state families

This file formalizes the support reduction at the start of the operator-algebraic
Koashi--Imoto argument in Hayden, Jozsa, Petz and Winter,
arXiv:quant-ph/0304007v2, Appendix A, lines 761--763.

For a finite nonempty family of density matrices, the support of their common
average is their minimum joint supporting subspace.  Compression to that
subspace makes the common average positive definite, preserves the density
normalization of every family member, and restricts every channel preserving
the family to a trace-preserving channel on the support.

## Main declarations

* `Kraus.commonAverage_posSemidef`: the common average of a positive family is
  positive semidefinite.
* `Kraus.commonAverage_trace`: the common average of a trace-one family has
  trace one.
* `Kraus.supportCompressedFamily`: compression of a state family along an
  isometry.
* `Kraus.supportCompressedKraus`: compression of a Kraus family along the same
  isometry.
* `Kraus.map_supportCompressedKraus_intertwines`: the compressed Kraus map
  intertwines with the ambient map on the joint support.
* `Kraus.exists_commonAverageSupportCompression`: the source-faithful
  joint-support reduction for an arbitrary finite density family.
* `Kraus.exists_commonInvariant_normalizedStateBlockForm_preservingBlockAction_jointSupport`:
  the unrestricted invariant-family block form and support-space channel
  action.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators Kronecker
open Matrix Finset Complex

namespace Kraus

variable {D : ℕ}
variable {Kidx : Type*} [Fintype Kidx] [Nonempty Kidx]

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- The common average of a positive-semidefinite family is positive
semidefinite.

This is the positive-matrix part of HJPW, arXiv:quant-ph/0304007v2,
lines 761--763. -/
theorem commonAverage_posSemidef (ρ : Kidx → Mat)
    (hρpos : ∀ x, (ρ x).PosSemidef) :
    (commonAverage ρ).PosSemidef := by
  unfold commonAverage
  exact (Matrix.posSemidef_sum Finset.univ fun x _ ↦ hρpos x).smul (by positivity)

/-- The common average of a trace-one family has trace one. -/
theorem commonAverage_trace (ρ : Kidx → Mat)
    (hρtrace : ∀ x, (ρ x).trace = 1) :
    (commonAverage ρ).trace = 1 := by
  unfold commonAverage
  rw [Matrix.trace_smul, Matrix.trace_sum]
  simp [hρtrace, Fintype.card_ne_zero]

/-- Compress every member of a matrix family along an isometry `V`. -/
noncomputable def supportCompressedFamily {n : ℕ}
    (V : Matrix (Fin D) (Fin n) ℂ) (ρ : Kidx → Mat) :
    Kidx → Matrix (Fin n) (Fin n) ℂ :=
  fun x ↦ Vᴴ * ρ x * V

/-- Compress every Kraus operator along an isometry `V`. -/
noncomputable def supportCompressedKraus {n r : ℕ}
    (V : Matrix (Fin D) (Fin n) ℂ) (Kfam : Fin r → Mat) :
    Fin r → Matrix (Fin n) (Fin n) ℂ :=
  fun i ↦ Vᴴ * Kfam i * V

/-- Compression intertwines a support-preserving Kraus map with its ambient
action.

This is the operation-transport step in HJPW,
arXiv:quant-ph/0304007v2, Appendix A, lines 761--763. -/
theorem map_supportCompressedKraus_intertwines {n r : ℕ}
    (V : Matrix (Fin D) (Fin n) ℂ) (Kfam : Fin r → Mat) (Q : Mat)
    (hV : Vᴴ * V = 1) (hVrange : V * Vᴴ = Q)
    (hQproj : IsOrthogonalProjection Q)
    (hLower : ∀ i, (1 - Q) * Kfam i * Q = 0) :
    ∀ X, map Kfam (V * X * Vᴴ) =
      V * map (supportCompressedKraus V Kfam) X * Vᴴ := by
  intro X
  have hsupported : Q * (V * X * Vᴴ) * Q = V * X * Vᴴ := by
    calc
      Q * (V * X * Vᴴ) * Q =
          (V * Vᴴ) * (V * X * Vᴴ) * (V * Vᴴ) := by rw [hVrange]
      _ = V * (Vᴴ * V) * X * (Vᴴ * V) * Vᴴ := by
        simp only [Matrix.mul_assoc]
      _ = V * X * Vᴴ := by rw [hV]; simp
  have hinvariant :=
    lowerZero_implies_invariance Kfam Q hQproj hLower (V * X * Vᴴ)
  rw [hsupported] at hinvariant
  rw [← hinvariant]
  unfold map supportCompressedKraus
  rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← hVrange]
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Every member of a positive family is supported on the support of its
common average.

This identifies the support of the common average with the minimum joint
support used by HJPW, arXiv:quant-ph/0304007v2, lines 761--763. -/
theorem commonAverage_supports_family (ρ : Kidx → Mat)
    (hρpos : ∀ x, (ρ x).PosSemidef) :
    let hρbar := commonAverage_posSemidef ρ hρpos
    ∀ x, hρbar.supportProj * ρ x * hρbar.supportProj = ρ x := by
  classical
  dsimp only
  let hρbar := commonAverage_posSemidef ρ hρpos
  intro x
  have hker : ∀ v : Fin D → ℂ,
      commonAverage ρ *ᵥ v = 0 → ρ x *ᵥ v = 0 := by
    intro v hv
    have hsum : (∑ y, ρ y) *ᵥ v = 0 := by
      have hcard : ((Fintype.card Kidx : ℂ)⁻¹) ≠ 0 :=
        inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero)
      change (((Fintype.card Kidx : ℂ)⁻¹) • (∑ y, ρ y)) *ᵥ v = 0 at hv
      rw [Matrix.smul_mulVec] at hv
      exact (smul_eq_zero.mp hv).resolve_left hcard
    exact Matrix.PosSemidef.mulVec_eq_zero_of_sum_mulVec_eq_zero hρpos hsum x
  have hright : ρ x * hρbar.supportProj = ρ x :=
    hρbar.isHermitian.mul_supportProj_eq_self_of_mulVec_kernel_le hker
  have hleft : hρbar.supportProj * ρ x = ρ x := by
    have h := congrArg Matrix.conjTranspose hright
    simpa [Matrix.conjTranspose_mul, hρbar.supportProj_isHermitian.eq,
      (hρpos x).isHermitian.eq] using h
  rw [hleft, hright]

/-- **Joint-support reduction for a finite invariant-state family.**

For positive-semidefinite trace-one states `ρ x`, there are support coordinates
`V : Fin n → Fin D` in which the common average is positive definite.  Every
state reconstructs exactly from its compression, and every ambient CPTP Kraus
family preserving `ρ` compresses to a CPTP Kraus family preserving the
compressed states.

This is HJPW, arXiv:quant-ph/0304007v2, Appendix A, lines 761--763.  It is the
support-transport prerequisite for applying
`exists_commonInvariant_normalizedStateBlockForm_preservingBlockAction`
without a full-support hypothesis on the original ambient space. -/
theorem exists_commonAverageSupportCompression
    (ρ : Kidx → Mat)
    (hρpos : ∀ x, (ρ x).PosSemidef)
    (hρtrace : ∀ x, (ρ x).trace = 1) :
    ∃ (n : ℕ) (V : Matrix (Fin D) (Fin n) ℂ),
      Vᴴ * V = 1 ∧
      V * Vᴴ = (commonAverage_posSemidef ρ hρpos).supportProj ∧
      (∀ x, (supportCompressedFamily V ρ x).PosSemidef) ∧
      (∀ x, (supportCompressedFamily V ρ x).trace = 1) ∧
      (commonAverage (supportCompressedFamily V ρ)).PosDef ∧
      (∀ x, V * supportCompressedFamily V ρ x * Vᴴ = ρ x) ∧
      ∀ F : PreservingKrausFamily ρ,
        IsPreserving (supportCompressedFamily V ρ)
            (supportCompressedKraus V F.Kfam) ∧
          ∀ X, map F.Kfam (V * X * Vᴴ) =
            V * map (supportCompressedKraus V F.Kfam) X * Vᴴ := by
  classical
  let hρbar := commonAverage_posSemidef ρ hρpos
  obtain ⟨n, V, hV, hVrange⟩ :=
    hρbar.isOrthogonalProjection_supportProj.exists_range_isometry
  refine ⟨n, V, hV, hVrange, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simpa only [supportCompressedFamily, Matrix.conjTranspose_conjTranspose] using
      (hρpos x).mul_mul_conjTranspose_same Vᴴ
  · intro x
    rw [supportCompressedFamily, Matrix.trace_mul_cycle, hVrange]
    have hsupp := commonAverage_supports_family ρ hρpos x
    have hQρ : hρbar.supportProj * ρ x = ρ x := by
      calc
        hρbar.supportProj * ρ x =
            hρbar.supportProj * (hρbar.supportProj * ρ x * hρbar.supportProj) := by
              rw [hsupp]
        _ = (hρbar.supportProj * hρbar.supportProj) *
              ρ x * hρbar.supportProj := by simp [Matrix.mul_assoc]
        _ = ρ x := by rw [hρbar.supportProj_idem, hsupp]
    rw [hQρ]
    exact hρtrace x
  · have hcompression :=
      hρbar.compression_on_support_posDef (V := Vᴴ)
        (by simpa [Matrix.conjTranspose_conjTranspose] using hV)
        (by simpa [Matrix.conjTranspose_conjTranspose] using hVrange)
    have havg :
        commonAverage (supportCompressedFamily V ρ) =
          Vᴴ * commonAverage ρ * V := by
      unfold commonAverage supportCompressedFamily
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]
    rw [havg]
    simpa only [Matrix.conjTranspose_conjTranspose] using hcompression
  · intro x
    change V * (Vᴴ * ρ x * V) * Vᴴ = ρ x
    calc
      V * (Vᴴ * ρ x * V) * Vᴴ =
          (V * Vᴴ) * ρ x * (V * Vᴴ) := by simp [Matrix.mul_assoc]
      _ = ρ x := by
        rw [hVrange]
        exact commonAverage_supports_family ρ hρpos x
  · intro F
    have hQproj := hρbar.isOrthogonalProjection_supportProj
    have hInv : ∀ i : Fin F.numKraus,
        (1 - hρbar.supportProj) * F.Kfam i * hρbar.supportProj = 0 := by
      simpa only [stationaryProj] using
        (lowerZero_of_posSemidef_fixedPoint F.Kfam (commonAverage ρ)
          hρbar F.map_commonAverage).2
    constructor
    · constructor
      · have hQV : hρbar.supportProj * V = V := by
          rw [← hVrange]
          simp [Matrix.mul_assoc, hV]
        have hKV : ∀ i : Fin F.numKraus,
            hρbar.supportProj * F.Kfam i * V = F.Kfam i * V := by
          intro i
          have h := hInv i
          rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
          calc
            hρbar.supportProj * F.Kfam i * V =
                hρbar.supportProj * F.Kfam i * (hρbar.supportProj * V) := by
                  rw [hQV]
            _ = (hρbar.supportProj * F.Kfam i * hρbar.supportProj) * V := by
              simp [Matrix.mul_assoc]
            _ = (F.Kfam i * hρbar.supportProj) * V := by rw [← h]
            _ = F.Kfam i * V := by rw [Matrix.mul_assoc, hQV]
        calc
          ∑ i : Fin F.numKraus,
              (supportCompressedKraus V F.Kfam i)ᴴ *
                supportCompressedKraus V F.Kfam i
              = Vᴴ * (∑ i : Fin F.numKraus, (F.Kfam i)ᴴ * F.Kfam i) * V := by
                  rw [Matrix.mul_sum, Matrix.sum_mul]
                  refine Finset.sum_congr rfl fun i _ ↦ ?_
                  simp only [supportCompressedKraus, Matrix.conjTranspose_mul,
                    Matrix.conjTranspose_conjTranspose]
                  calc
                    Vᴴ * ((F.Kfam i)ᴴ * V) * (Vᴴ * F.Kfam i * V) =
                        Vᴴ * (F.Kfam i)ᴴ *
                          ((V * Vᴴ) * F.Kfam i * V) := by
                            simp [Matrix.mul_assoc]
                    _ = Vᴴ * ((F.Kfam i)ᴴ * F.Kfam i) * V := by
                      rw [hVrange, hKV]
                      simp [Matrix.mul_assoc]
          _ = 1 := by rw [F.isPreserving.1, Matrix.mul_one, hV]
      · intro x
        have hsupp := commonAverage_supports_family ρ hρpos x
        have hmap :
            map (supportCompressedKraus V F.Kfam)
                (supportCompressedFamily V ρ x) =
              Vᴴ * map F.Kfam (ρ x) * V := by
          unfold map supportCompressedKraus supportCompressedFamily
          rw [Matrix.mul_sum, Matrix.sum_mul]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
          calc
            Vᴴ * F.Kfam i * V * (Vᴴ * ρ x * V) *
                  (Vᴴ * ((F.Kfam i)ᴴ * V)) =
                Vᴴ * (F.Kfam i * ((V * Vᴴ) * ρ x * (V * Vᴴ)) *
                  (F.Kfam i)ᴴ) * V := by
                    simp [Matrix.mul_assoc]
            _ = Vᴴ * (F.Kfam i * ρ x * (F.Kfam i)ᴴ) * V := by
              rw [hVrange, hsupp]
        rw [hmap, F.isPreserving.2 x]
        rfl
    · exact map_supportCompressedKraus_intertwines V F.Kfam hρbar.supportProj
        hV hVrange hQproj hInv

/-- **Unrestricted Koashi--Imoto state and preserving-operation block form.**

Every finite density family admits support coordinates in which the normalized
state decomposition and the action of every preserving operation on the
compressed family have the full-support form proved in
`exists_commonInvariant_normalizedStateBlockForm_preservingBlockAction`.

The isometry `V` reconstructs the original family from the support coordinates.
Every ambient preserving operation restricts to this family, and its ambient
action intertwines with the compressed action.  The block equation itself is
stated on the minimum joint support, so no artificial zero-weight density
block is added on its orthogonal complement.

Source: HJPW, arXiv:quant-ph/0304007v2, Appendix A, lines 761--816 and
853--882.  TNLean uses the reverse tensor-factor order from HJPW. -/
theorem exists_commonInvariant_normalizedStateBlockForm_preservingBlockAction_jointSupport
    (ρ : Kidx → Mat)
    (hρpos : ∀ x, (ρ x).PosSemidef)
    (hρtrace : ∀ x, (ρ x).trace = 1) :
    ∃ (n : ℕ) (V : Matrix (Fin D) (Fin n) ℂ),
      Vᴴ * V = 1 ∧
      V * Vᴴ = (commonAverage_posSemidef ρ hρpos).supportProj ∧
      (∀ x, V * supportCompressedFamily V ρ x * Vᴴ = ρ x) ∧
      ∃ (K : ℕ) (d m : Fin K → ℕ)
        (e : ((j : Fin K) × (Fin (m j) × Fin (d j))) ≃ Fin n)
        (U : Matrix (Fin n) (Fin n) ℂ)
        (σ : ∀ j, Matrix (Fin (m j)) (Fin (m j)) ℂ)
        (q : Kidx → Fin K → ℝ)
        (τ : Kidx → ∀ j, Matrix (Fin (d j)) (Fin (d j)) ℂ),
        U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
          (∀ j, 0 < d j) ∧ (∀ j, 0 < m j) ∧
          (∀ j, (σ j).PosSemidef) ∧ (∀ j, (σ j).trace = 1) ∧
          (∀ x j, 0 ≤ q x j) ∧ (∀ x, ∑ j, q x j = 1) ∧
          (∀ x j, (τ x j).PosSemidef) ∧ (∀ x j, (τ x j).trace = 1) ∧
          (∀ x, star U * supportCompressedFamily V ρ x * U =
            Matrix.reindex e e
              (Matrix.blockDiagonal' fun j ↦
                (q x j : ℂ) • (σ j ⊗ₖ τ x j))) ∧
          (∀ F : PreservingKrausFamily ρ,
            IsPreserving (supportCompressedFamily V ρ)
                (supportCompressedKraus V F.Kfam) ∧
              ∀ X, map F.Kfam (V * X * Vᴴ) =
                V * map (supportCompressedKraus V F.Kfam) X * Vᴴ) ∧
          ∀ G : PreservingKrausFamily (supportCompressedFamily V ρ),
            ∃ C : (i : Fin G.numKraus) → ∀ j,
                Matrix (Fin (m j)) (Fin (m j)) ℂ,
              (∀ i,
                Matrix.reindex e.symm e.symm
                    (star U * G.Kfam i * U) =
                  Matrix.blockDiagonal' fun j ↦
                    C i j ⊗ₖ (1 : Matrix (Fin (d j)) (Fin (d j)) ℂ)) ∧
              (∀ j, IsTP (fun i ↦ C i j)) ∧
              (∀ j, map (fun i ↦ C i j) (σ j) = σ j) ∧
              ∀ j (A : Matrix (Fin (m j)) (Fin (m j)) ℂ)
                  (B : Matrix (Fin (d j)) (Fin (d j)) ℂ),
                Matrix.reindex e.symm e.symm
                    (star U * map G.Kfam
                      (U * Matrix.reindex e e
                        (Matrix.directSumBlockEmbedding (m := m) (d := d) j
                          (A ⊗ₖ B)) * star U) * U) =
                  Matrix.directSumBlockEmbedding (m := m) (d := d) j
                    (map (fun i ↦ C i j) A ⊗ₖ B) := by
  classical
  obtain ⟨n, V, hV, hVrange, hρspos, hρstrace, hρsbar, hrec, hpres⟩ :=
    exists_commonAverageSupportCompression ρ hρpos hρtrace
  obtain ⟨K, d, m, e, U, σ, q, τ, hU, hd, hm, hσpos, hσtrace,
      hqnonneg, hqsum, hτpos, hτtrace, hfamily, haction⟩ :=
    exists_commonInvariant_normalizedStateBlockForm_preservingBlockAction
      hρspos hρstrace hρsbar
  refine ⟨n, V, hV, hVrange, hrec, K, d, m, e, U, σ, q, τ, hU, hd, hm,
    hσpos, hσtrace, hqnonneg, hqsum, hτpos, hτtrace, hfamily, hpres, haction⟩

end Kraus
