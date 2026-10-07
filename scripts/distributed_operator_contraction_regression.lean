import TNLean.PEPS.Approximation.DistributedOperatorContraction
import Mathlib.Tactic.NormNum

/-!
Focused regression checks for actual star/sample operator evaluation. These tests
exercise the constructed contraction, including zero labels/samples, a gate with
no virtual edges, complex bra conjugation, and repeated gate occurrences with
parallel star/sample links. No actual circuit expansion is assumed.
-/

open scoped BigOperators
open TNLean.PEPS TNLean.PEPS.Approximation
open TNLean.PEPS.Approximation.DistributedOperatorContraction

noncomputable section

private abbrev oneGate : Finset (Fin 1) := Finset.univ
private abbrev twoParties (_ : Fin 1) : Finset (Fin 2) := Finset.univ
private abbrev oneParty (_ : Fin 1) : Finset (Fin 1) := Finset.univ

-- An empty circuit gives the exact heterogeneous rectangular product matrix, even
-- when every branch alphabet and the sample alphabet is empty.
example (F : (p : Fin 2) → Matrix (Fin (p.1 + 2)) (Fin (p.1 + 3)) ℂ) :
    contractedOperator (∅ : Finset (Fin 1)) twoParties (fun _ => 0)
      (by simp) (fun _ => Fin 0) 0 (fun _ z => Fin.elim0 z)
      (fun p _ _ => F p) = dependentPhysicalProductFamilyMatrix F := by
  classical
  apply Matrix.ext
  intro x y
  rw [contractedOperator_eq_branchSampleSum]
  simp [GateLabels, ActiveGate, Sample, dependentPhysicalProductFamilyMatrix]

-- A singleton gate still sums its branch label locally: an empty label alphabet
-- gives the zero operator, despite there being no star or sample links.
example (T : (p : Fin 1) → GateLabelsAt oneGate oneParty (fun _ => Fin 0) p →
    (SampleAt oneGate oneParty p → Fin 0) → Matrix (Fin 2) (Fin 3) ℂ) :
    contractedOperator oneGate oneParty (fun _ => 0) (fun _ _ => Finset.mem_univ 0)
      (fun _ => Fin 0) 0 (fun _ z => Fin.elim0 z) T = 0 := by
  classical
  let : IsEmpty (GateLabels oneGate (fun _ => Fin 0)) :=
    ⟨fun ξ => Fin.elim0 (ξ ⟨0, by simp [oneGate]⟩)⟩
  apply Matrix.ext
  intro x y
  rw [contractedOperator_eq_branchSampleSum]
  simp

-- k = 0 makes the evaluation zero when a sample position really exists.
example (T : (p : Fin 2) → GateLabelsAt oneGate twoParties (fun _ => Fin 2) p →
    (SampleAt oneGate twoParties p → Fin 0) → Matrix (Fin 2) (Fin 3) ℂ) :
    contractedOperator oneGate twoParties (fun _ => 0) (fun _ _ => Finset.mem_univ 0)
      (fun _ => Fin 2) 0 (fun _ _ => 1) T = 0 := by
  classical
  let s : Sample oneGate twoParties :=
    ⟨⟨0, by simp [oneGate]⟩, ⟨Sym2.mk 0 1, by
      simp [twoParties]⟩⟩
  let : IsEmpty (Sample oneGate twoParties → Fin 0) :=
    ⟨fun j => Fin.elim0 (j s)⟩
  apply Matrix.ext
  intro x y
  rw [contractedOperator_eq_branchSampleSum]
  simp

-- The complete ket/bra label has dimension 2 * 3 and is summed even though a
-- singleton gate has no star edge. Physical input/output dimensions may differ.
example (x : Fin 1 → Fin 2) (y : Fin 1 → Fin 3) :
    contractedOperator oneGate oneParty (fun _ => 0) (fun _ _ => Finset.mem_univ 0)
      (fun _ => Fin 2 × Fin 3) 0 (fun _ _ => 1) (fun _ _ _ => Matrix.of (fun _ _ => 1)) x y = 6 := by
  classical
  rw [contractedOperator_eq_branchSampleSum]
  norm_num [GateLabels, ActiveGate, Sample, oneGate, oneParty, Fintype.card_pi, Matrix.of_apply]

-- The bra coefficient is conjugated, and a root-only gate weight appears once.
-- I * conjugate(I) = 1, so the genuine constructed operator entry is 1/2.
example (x : Fin 1 → Fin 2) (y : Fin 1 → Fin 3) :
    contractedOperator oneGate oneParty (fun _ => 0) (fun _ _ => Finset.mem_univ 0)
      (fun _ => Fin 1 × Fin 1) 0
      (densityPairCoefficient (fun _ => Fin 1) (fun _ => Fin 1)
        (fun _ _ => Complex.I) (fun _ _ => Complex.I) (fun _ => 1 / 2))
      (fun _ _ _ => Matrix.of (fun _ _ => 1)) x y = 1 / 2 := by
  classical
  rw [contractedOperator_eq_branchSampleSum]
  norm_num [GateLabels, ActiveGate, Sample, oneGate, oneParty,
    densityPairCoefficient, Fintype.card_pi, Matrix.of_apply]
  rw [mul_assoc, Complex.I_mul_I]
  norm_num

private abbrev repeatedGates : Finset Bool := Finset.univ
private abbrev repeatedParties (_ : Bool) : Finset (Fin 2) := Finset.univ

-- Two repeated gate occurrences have separate star and sample links. There are
-- 6^2 branch assignments and 2^2 sample assignments. The factor 1/2 is inserted
-- once per gate, so the exact averaged operator entry is 36, not 9 or 6.
example (x : Fin 2 → Fin 2) (y : Fin 2 → Fin 3) :
    contractedOperator repeatedGates repeatedParties (fun _ => 0)
      (fun _ _ => Finset.mem_univ 0) (fun _ => Fin 2 × Fin 3) 2
      (fun _ _ => 1 / 2) (fun _ _ _ => Matrix.of (fun _ _ => 1)) x y = 36 := by
  classical
  have hsample : Fintype.card (Sample repeatedGates repeatedParties) = 2 := by
    calc
      Fintype.card (Sample repeatedGates repeatedParties) =
          ∑ g : ActiveGate repeatedGates, (pairSampleLabels (repeatedParties g.1)).card := by
        simp only [Sample, Fintype.card_sigma, Fintype.card_coe]
      _ = 2 := by norm_num [card_pairSampleLabels, repeatedParties, ActiveGate]
  rw [contractedOperator_eq_branchSampleSum]
  norm_num [GateLabels, ActiveGate, repeatedGates, Fintype.card_pi, hsample, Matrix.of_apply]

-- Each actual star link carries the complete 2-by-3 density branch pair.
example (g : ActiveGate repeatedGates)
    (q : {p // p ∈ (repeatedParties g.1).erase (0 : Fin 2)}) :
    Fintype.card (alphabet repeatedGates repeatedParties (fun _ => 0)
      (fun _ => Fin 2 × Fin 3) 2
      (starLink repeatedGates repeatedParties (fun _ => 0) g q)) = 6 := by
  rw [card_alphabet]
  norm_num [starLink]

-- A sample link carries exactly k, regardless of the branch-pair alphabet.
example (s : Sample repeatedGates repeatedParties) :
    Fintype.card (alphabet repeatedGates repeatedParties (fun _ => 0)
      (fun _ => Fin 2 × Fin 3) 2
      (sampleLink repeatedGates repeatedParties (fun _ => 0) s)) = 2 := by
  rw [card_alphabet]
  rfl
