/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.Z3Anomalous.Z3AnomalousTensor

/-!
# Fusion-tree data of the `ℤ₃` representation

Integer data over `ℤ[ω]` for the anomaly computation of
`Z3Anomalous.family` (`TNLean.MPS.Examples.Z3Anomalous.Z3AnomalyClass`):
the two fusion trees of the triples `(g,g,g)` and `(g,g²,g)` and the letters of the two
triple products. The finitely many identities between them are checked by
`decide +kernel` in `Z3AnomalyTreeUUU` and `Z3AnomalyTreeUDU`.
-/

open scoped Matrix Kronecker
open MPSTensor EisensteinInt

namespace Z3Anomalous

/-! ### Eisenstein data of the two nontrivial triples -/

/-- The recorded left fusion tensor of `U ⊗ U → U†` over `ℤ[ω]`. -/
def uuLeftEis : Matrix (Fin 2) (Fin 4) EisensteinInt :=
  !![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩; ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]

/-- The recorded left fusion tensor of `U ⊗ U† → 1` and of `U† ⊗ U → 1` over `ℤ[ω]`. -/
def scalarLeftEis : Matrix (Fin 1) (Fin 4) EisensteinInt :=
  !![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]

/-- `X ⊗ 1` over `ℤ[ω]`, in the bond order of `MPOTensor.kronId`. -/
def kronIdEis {m n : ℕ} (X : Matrix (Fin m) (Fin n) EisensteinInt) (D : ℕ) :
    Matrix (Fin (m * D)) (Fin (n * D)) EisensteinInt :=
  (X ⊗ₖ (1 : Matrix (Fin D) (Fin D) EisensteinInt)).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm

/-- `1 ⊗ X` over `ℤ[ω]`, in the bond order of `MPOTensor.idKron`. -/
def idKronEis {m n : ℕ} (D : ℕ) (X : Matrix (Fin m) (Fin n) EisensteinInt) :
    Matrix (Fin (D * m)) (Fin (D * n)) EisensteinInt :=
  ((1 : Matrix (Fin D) (Fin D) EisensteinInt) ⊗ₖ X).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm

/-- The letters of the triple product `(U U) U` over `ℤ[ω]`. -/
def tripleUUUEis (a : Fin 9) : Matrix (Fin 8) (Fin 8) EisensteinInt :=
  mulTensorR (mulTensorR uEis uEis) uEis (Fin.divNat (m := 3) (n := 3) a)
    (Fin.modNat (m := 3) (n := 3) a)

/-- The letters of the triple product `(U U†) U` over `ℤ[ω]`. -/
def tripleUDUEis (a : Fin 9) : Matrix (Fin 8) (Fin 8) EisensteinInt :=
  mulTensorR (mulTensorR uEis uDagEis) uEis (Fin.divNat (m := 3) (n := 3) a)
    (Fin.modNat (m := 3) (n := 3) a)

/-- The tree of `(g,g,g)` fusing the first two factors first. -/
def leftUUUEis : Matrix (Fin 1) (Fin 8) EisensteinInt := scalarLeftEis * kronIdEis uuLeftEis 2

/-- The tree of `(g,g,g)` fusing the last two factors first. -/
def rightUUUEis : Matrix (Fin 1) (Fin 8) EisensteinInt := scalarLeftEis * idKronEis 2 uuLeftEis

/-- The tree of `(g,g²,g)` fusing the first two factors first. -/
def leftUDUEis : Matrix (Fin 2) (Fin 8) EisensteinInt := kronIdEis scalarLeftEis 2

/-- The tree of `(g,g²,g)` fusing the last two factors first. -/
def rightUDUEis : Matrix (Fin 2) (Fin 8) EisensteinInt := idKronEis 2 scalarLeftEis

/-- The letters of the triple product, as explicit matrices over `ℤ[ω]`. -/
def tripleUUUTable : Fin 9 → Matrix (Fin 8) (Fin 8) EisensteinInt
  | 0 =>
    !![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 =>
    !![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 =>
    !![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]

/-- The letters of the triple product, as explicit matrices over `ℤ[ω]`. -/
def tripleUDUTable : Fin 9 → Matrix (Fin 8) (Fin 8) EisensteinInt
  | 0 => 0
  | 1 => 0
  | 2 =>
    !![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]
  | 3 =>
    !![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
       ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 =>
    !![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩;
       ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]
  | 8 => 0

set_option maxRecDepth 8000 in
/-- The letters of `(U U) U` are the explicit table `tripleUUUTable`. -/
theorem tripleUUUEis_eq_table : ∀ a, tripleUUUEis a = tripleUUUTable a := by
  decide +kernel

set_option maxRecDepth 8000 in
/-- The letters of `(U U†) U` are the explicit table `tripleUDUTable`. -/
theorem tripleUDUEis_eq_table : ∀ a, tripleUDUEis a = tripleUDUTable a := by
  decide +kernel

end Z3Anomalous
