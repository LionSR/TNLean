/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Defs
import TNLean.Kraus.Blocking

/-!
# Matrix-product-vector bridge for physical blocking

The word-evaluation content of physical blocking (`blockPhysDim`, `wordOfBlock`,
`blockTensor`, `blockKron`, `evalWord_blockTensor`, canonical-normalization
propagation, `leftCanonical_blockTensor`) now lives in
`TNLean/Kraus/Blocking.lean`. This file keeps
the surviving matrix-product-vector bridge lemmas that transport `mpv`/`SameMPV`
through physical blocking. `mpv_blockTensor_eq_mpv` was also a bridge lemma
here; it had zero call sites (repo-wide, including generalized field notation)
and was deleted rather than carried across the split — the actually-used
flattened-word `mpv` bridge lives in `TNLean/MPS/Core/BlockingInfrastructure.lean`.

## Main results

* `mpv_blockTensor_one` transports MPVs through single-site blocking.
* `SameMPV.blockTensor` transports the `SameMPV` relation through blocking.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

@[simp] lemma mpv_blockTensor_one (A : MPSTensor d D) {N : ℕ}
    (σ : Fin N → Fin (blockPhysDim d 1)) :
    mpv (blockTensor (d := d) (D := D) A 1) σ =
      mpv A (fun n => singleBlockEquiv d (σ n)) := by
  simp [mpv, coeff, evalWord_blockTensor, List.map_ofFn]
  rfl

/-- Physical blocking preserves the `SameMPV` relation. -/
theorem SameMPV.blockTensor {A B : MPSTensor d D} (hSame : SameMPV A B) (L : ℕ) :
    SameMPV (MPSTensor.blockTensor (d := d) (D := D) A L)
      (MPSTensor.blockTensor (d := d) (D := D) B L) := by
  intro N σ
  classical
  -- Use the same flattened configuration for both tensors.
  set flat : List (Fin d) := flattenBlockedWord d L (List.ofFn σ) with flat_def
  have hlen : flat.length = N * L := by
    simpa [flat_def] using (length_flattenBlockedWord (d := d) (L := L) (List.ofFn σ))
  set σflat : Fin (N * L) → Fin d :=
    fun i => flat.get (Fin.cast hlen.symm i) with σflat_def
  have hofFn : List.ofFn σflat = flat := by
    rw [σflat_def]
    conv_rhs => rw [← List.ofFn_get flat]
    have hcongr :=
      (List.ofFn_congr (m := N * L) (n := flat.length) hlen.symm
        (fun i : Fin (N * L) => flat.get (Fin.cast hlen.symm i)))
    simpa [Function.comp, Fin.cast_cast] using hcongr
  have hblock (T : MPSTensor d D) :
      mpv (MPSTensor.blockTensor (d := d) (D := D) T L) σ = mpv T σflat := by
    simp [mpv, coeff, hofFn, flat_def, evalWord_blockTensor]
  calc
    mpv (MPSTensor.blockTensor (d := d) (D := D) A L) σ = mpv A σflat := hblock A
    _ = mpv B σflat := hSame (N * L) σflat
    _ = mpv (MPSTensor.blockTensor (d := d) (D := D) B L) σ := (hblock B).symm

end MPSTensor
