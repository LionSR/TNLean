/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalIntervalTransport
import QICLean.ManyBody.Sites.PlaceAlong
import QICLean.Analysis.PrincipalSubmatrixNorm

/-!
# Native restriction of a supported operator approximation

A fixed configuration outside an interval restricts an actual operator chain
to its native site coordinates. The virtual dimension is unchanged and
placing the restricted operator back on the original chain preserves the
approximation error. The source operator is genuinely supported on the
interval, rather than supplied with a native representation.

This is operator algebra for ALVV, arXiv:1602.08828v2,
`lem:exp-approx-eff`, lines 1262–1268.
-/

open ManyBody (interval mem_interval)

open Matrix
open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- Restricting an actual Hermitian operator chain to a supported interval
preserves its approximation error after native placement. The same actual
site tensors and closing matrix are retained. Supporting ALVV,
arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268. -/
theorem exists_native_interval_slice_of_mpo_approximation {N q l r D : ℕ}
    (hq : 0 < q) (hlr : l ≤ r) (hrL : r ≤ N + 1)
    (P : Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hPs : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
      P (interval (N + 1) l r))
    (Aglobal : Fin (N + 1) → MPOTensor q D)
    (hA : (MPOTensor.traceChainOperator Aglobal 1).IsHermitian)
    (xi : ℝ) (herr : ‖P - MPOTensor.traceChainOperator Aglobal 1‖ ≤ xi) :
    let sigma0 : Fin (N + 1) → Fin q := fun _ ↦ ⟨0, hq⟩
    let insert := insertInterval (L := r - l) l sigma0
    let eJ := intervalShiftOrderIso hlr hrL
    let e : Fin (r - l) ↪ Fin (N + 1) :=
      eJ.toEquiv.toEmbedding.trans (Function.Embedding.subtype _)
    ∃ (Acore : Fin (r - l) → MPOTensor q D)
      (C0 : Matrix (Fin D) (Fin D) ℂ),
      let Z := MPOTensor.traceChainOperator Acore C0
      let Zphys := ManyBody.placeAlong (X := fun _ ↦ Fin q) e Z
      Z.IsHermitian ∧ Zphys.IsHermitian ∧
        P = ManyBody.placeAlong (X := fun _ ↦ Fin q) e (P.submatrix insert insert) ∧
        ‖P.submatrix insert insert - Z‖ ≤ xi ∧ ‖P - Zphys‖ ≤ xi := by
  classical
  intro sigma0 insert eJ e
  have hmap : Finset.univ.map e = interval (N + 1) l r := by
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨u, rfl⟩
      exact (eJ u).property
    · intro hi
      exact ⟨eJ.symm ⟨i, hi⟩, congrArg Subtype.val (eJ.apply_symm_apply ⟨i, hi⟩)⟩
  have hs : P ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) (Finset.univ.map e) := by
    rw [hmap]
    exact hPs
  obtain ⟨M, hM⟩ := ManyBody.exists_eq_placeAlong_of_mem_supportedOperators e hs
  have hread (sigma : Fin (r - l) → Fin q) : insert sigma ∘ e = sigma := by
    funext u
    change insert sigma (eJ u).val = sigma u
    simp [insert, insertInterval, eJ, intervalShiftOrderIso, u.isLt]
  have hgoff (sigma tau : Fin (r - l) → Fin q) :
      ∀ v, (∀ u, e u ≠ v) → insert sigma v = insert tau v := by
    intro v hv
    have hout : ¬(l ≤ v.val ∧ v.val < l + (r - l)) := by
      intro hvin
      have hvJ : v ∈ interval (N + 1) l r := mem_interval.mpr (by omega)
      rw [← hmap] at hvJ
      obtain ⟨u, -, hu⟩ := Finset.mem_map.mp hvJ
      exact hv u hu
    simp only [insert, insertInterval, dite_eq_right hout]
  have hsliceP : P.submatrix insert insert = M := by
    ext sigma tau
    rw [Matrix.submatrix_apply, hM, ManyBody.placeAlong_apply,
      ite_eq_left (hgoff sigma tau)]
    exact congrArg₂ M (hread sigma) (hread tau)
  have hbound : l + (r - l) ≤ N + 1 := by omega
  let C0 := MPOTensor.actualRetainedIntervalClosing (L := r - l)
    Aglobal 1 l hbound (fun v ↦ sigma0 v.val) (fun v ↦ sigma0 v.val)
  let Acore : Fin (r - l) → MPOTensor q D := fun u ↦ Aglobal ⟨l + u.val, by omega⟩
  have hcore : (MPOTensor.traceChainOperator Aglobal 1).submatrix insert insert =
      MPOTensor.traceChainOperator Acore C0 := by
    ext sigma tau
    exact MPOTensor.trace_actual_retainedInterval_eq Aglobal 1 l hbound
      (fun v ↦ sigma0 v.val) (fun v ↦ sigma0 v.val) sigma tau
  have hNativeError :
      ‖P.submatrix insert insert - MPOTensor.traceChainOperator Acore C0‖ ≤ xi := by
    have hinj : Function.Injective insert :=
      (show Function.LeftInverse (fun x : Fin (N + 1) → Fin q ↦ x ∘ e) insert
        from hread).injective
    rw [← hcore]
    change ‖(P - MPOTensor.traceChainOperator Aglobal 1).submatrix insert insert‖ ≤ xi
    exact (Matrix.l2_opNorm_principal_submatrix_le _ _ hinj).trans herr
  exact
    let Z := MPOTensor.traceChainOperator Acore C0
    let hZ : Z.IsHermitian :=
      (congrArg Matrix.IsHermitian hcore).mp (hA.submatrix insert)
    let hMError : ‖M - Z‖ ≤ xi :=
      (congrArg (fun X : Matrix (Fin (r - l) → Fin q) (Fin (r - l) → Fin q) ℂ ↦
        ‖X - Z‖ ≤ xi) hsliceP).mp hNativeError
    let hDifference : P - ManyBody.placeAlong (X := fun _ ↦ Fin q) e Z =
        ManyBody.placeAlong (X := fun _ ↦ Fin q) e (M - Z) :=
      (congrArg (fun K ↦ K - ManyBody.placeAlong (X := fun _ ↦ Fin q) e Z) hM).trans
        (ManyBody.placeAlong_sub (X := fun _ ↦ Fin q) e M Z).symm
    ⟨Acore, C0, hZ,
      ManyBody.isHermitian_placeAlong (X := fun _ ↦ Fin q) e hZ,
      hM.trans (congrArg (ManyBody.placeAlong (X := fun _ ↦ Fin q) e) hsliceP.symm),
      hNativeError,
      (congrArg norm hDifference).le.trans
        ((ManyBody.norm_placeAlong_le (X := fun _ ↦ Fin q) e _).trans hMError)⟩

end TNLean.MPS.AreaLaw
