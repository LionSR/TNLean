/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.RegisterLayout
import TNLean.MPS.MPU.TreeAmplificationGateBounds
import TNLean.Circuit.SelectedZeroRegisterReflectionPool

/-!
# Uniform resource bounds for the exact interval construction

The register allocation and the actual reversible zero-register reflections give
uniform bounds for the numerical cost at every node. Substitution in the cost
on the constructed midpoint tree yields an explicit power of the physical
length, with coefficients depending only on the bond bound and local dimension.

These results bound numerical costs of the stated operations. The existence of
the complete recursively assembled circuit is a separate theorem. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

namespace MPUCircuit

open QuantumCircuit

/-- The ceiling-logarithmic bond width has a polynomial bound in the bond
dimension. Source: the register allocation in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem bondRegisterWidth_le_bondDim {d D : ℕ} (hd : 2 ≤ d) :
    bondRegisterWidth d D ≤ D :=
  Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self (n := D) (by omega : 1 < d)))

/-- One common bound for a routed leaf or a joining dilation followed by
attenuation. Source: the small-packet construction in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def uniformPacketGateCount (d D N : ℕ) : ℕ :=
  (76 * (d ^ 4 * D ^ 2) ^ 6 + 8 * (D + 1)) * globalSiteCount d D N

/-- Reserve an additive quadratic cost for conjugating child calls into
the coordinate order of a joining packet. Child gate counts are retained;
their individual gates are not routed again. Source: the interval circuit
assembly in Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def uniformNodeGateCount (d D N : ℕ) : ℕ :=
  uniformPacketGateCount d D N + 16 * (globalSiteCount d D N) ^ 2

/-- The placed leaf synthesis budget fits the common packet budget.
Source: the exact leaf synthesis in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem placedLeafGateCount_le_uniform (d D N : ℕ) :
    (38 * (d ^ 4 * D ^ 2) ^ 6) * (2 * globalSiteCount d D N) ≤
      uniformPacketGateCount d D N := by
  calc
    _ = (76 * (d ^ 4 * D ^ 2) ^ 6) * globalSiteCount d D N := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)

/-- The stated circuit for the complete joining packet, including routing
of its local attenuation decomposition, fits the common packet budget.
Source: the encoded joining construction in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem joiningPacketGateCount_le_uniform {d D : ℕ} (hd : 2 ≤ d)
    (hD : 0 < D) (N : ℕ) :
    (2 * (2 * bondRegisterWidth d D + 2) +
        38 * (d ^ (2 * bondRegisterWidth d D + 2)) ^ 6) *
        (2 * globalSiteCount d D N) ≤ uniformPacketGateCount d D N := by
  have hwidth := bondRegisterWidth_le_bondDim (D := D) hd
  have hdim : d ^ (2 * bondRegisterWidth d D + 2) ≤ d ^ 4 * D ^ 2 := by
    calc
      _ = (d ^ bondRegisterWidth d D) ^ 2 * d ^ 2 := by
        rw [show 2 * bondRegisterWidth d D + 2 = bondRegisterWidth d D * 2 + 2 by omega,
          pow_add, pow_mul]
      _ ≤ (d * D) ^ 2 * d ^ 2 := Nat.mul_le_mul_right _
        (Nat.pow_le_pow_left (registerCapacity_le_mul_bondDim hd hD) 2)
      _ = _ := by ring
  have hlocal := Nat.add_le_add
    (by omega : 2 * (2 * bondRegisterWidth d D + 2) ≤ 4 * (D + 1))
    (Nat.mul_le_mul_left 38 (Nat.pow_le_pow_left hdim 6))
  calc
    _ ≤ (4 * (D + 1) + 38 * (d ^ 4 * D ^ 2) ^ 6) *
        (2 * globalSiteCount d D N) := Nat.mul_le_mul_right _ hlocal
    _ = _ := by dsimp [uniformPacketGateCount]; ring

/-- A bound including the one-gate phase for an empty selected register.
Source: the initialized-register reflections in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def uniformReflectionGateCount (d D N : ℕ) : ℕ :=
  1 + zeroRegisterReflectionGateCount d (auxiliarySiteCount d D N) *
    (2 * globalSiteCount d D N)

/-- Testing any subset of the allocated logical auxiliaries has the common
reflection budget. Source: the shared-workspace reflections in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem selectedZeroRegisterReflectionPoolGateCount_le_uniform
    (d D N a : ℕ) (ha : a ≤ auxiliarySiteCount d D N) :
    selectedZeroRegisterReflectionPoolGateCount d (logicalSiteCount d D N) a
        (auxiliarySiteCount d D N) ≤ uniformReflectionGateCount d D N := by
  rw [selectedZeroRegisterReflectionPoolGateCount]
  split_ifs
  · simp [uniformReflectionGateCount]
  · have hmono : zeroRegisterReflectionGateCount d a ≤
        zeroRegisterReflectionGateCount d (auxiliarySiteCount d D N) := by
      rw [zeroRegisterReflectionGateCount_eq, zeroRegisterReflectionGateCount_eq]
      exact Nat.add_le_add
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ha 2))
        (Nat.mul_le_mul_left 4 ha)
    exact (Nat.mul_le_mul_right _ hmono).trans (by
      simp only [uniformReflectionGateCount, globalSiteCount]
      omega)

/-- The common reflection budget grows cubically in the physical length
times the bond-register width. Source: the conservative routed reflection
bound in Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem uniformReflectionGateCount_le_cubic (d D N : ℕ) (hN : 0 < N) :
    uniformReflectionGateCount d D N ≤
      (400 * (38 * (d ^ 3) ^ 6 + 1) + 1) *
        (N * (bondRegisterWidth d D + 1)) ^ 3 := by
  let H := N * (bondRegisterWidth d D + 1)
  let c := 38 * (d ^ 3) ^ 6 + 1
  have hH : 1 ≤ H := Nat.mul_pos hN (by omega)
  have hc : 1 ≤ c := by dsimp [c]; omega
  have hA : auxiliarySiteCount d D N ≤ 2 * H := by
    dsimp [auxiliarySiteCount, H]
    simpa only [Nat.mul_assoc] using
      Nat.mul_le_mul_right (bondRegisterWidth d D + 1)
        (Nat.mul_le_mul_left 2 (Nat.sub_le N 1))
  have hn : globalSiteCount d D N ≤ 5 * H := by
    simpa only [H, Nat.mul_assoc] using globalSiteCount_le d D N
  have href : zeroRegisterReflectionGateCount d (auxiliarySiteCount d D N) ≤
      32 * c * H ^ 2 + 8 * H := by
    rw [zeroRegisterReflectionGateCount_eq]
    calc
      _ ≤ 8 * c * (2 * H) ^ 2 + 4 * (2 * H) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hA 2))
          (Nat.mul_le_mul_left 4 hA)
      _ = _ := by ring
  change 1 + zeroRegisterReflectionGateCount d (auxiliarySiteCount d D N) *
      (2 * globalSiteCount d D N) ≤ (400 * c + 1) * H ^ 3
  calc
    _ ≤ 1 + (32 * c * H ^ 2 + 8 * H) * (2 * (5 * H)) :=
      Nat.add_le_add_left (Nat.mul_le_mul href (Nat.mul_le_mul_left 2 hn)) 1
    _ ≤ (400 * c + 1) * H ^ 3 := by
      have hH2 : H ^ 2 ≤ H ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
      have hH3 : 1 ≤ H ^ 3 := one_le_pow₀ hH
      have hsmall : 80 * H ^ 2 ≤ 80 * c * H ^ 3 := by
        exact (Nat.mul_le_mul_left 80 hH2).trans (by
          simpa only [Nat.mul_one] using
            Nat.mul_le_mul_right (H ^ 3) (Nat.mul_le_mul_left 80 hc))
      calc
        _ = 1 + (320 * c * H ^ 3 + 80 * H ^ 2) := by ring
        _ ≤ H ^ 3 + (320 * c * H ^ 3 + 80 * c * H ^ 3) :=
          Nat.add_le_add hH3 (Nat.add_le_add_left hsmall _)
        _ = _ := by ring

/-- The coefficient in the final numerical tree estimate. Source: the
resource recurrence in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def uniformCircuitResourceCoefficient (d D : ℕ) : ℕ :=
  (2 * D + 2) * (5 * (76 * (d ^ 4 * D ^ 2) ^ 6 + 8 * (D + 1)) + 400) +
    D * (1 + 2 * (400 * (38 * (d ^ 3) ^ 6 + 1) + 1))

/-- The actual numerical midpoint recursion with the common packet and
reflection bounds. Source: the exact amplification recurrence in Section 5
of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def uniformCircuitTreeGateCount (d D N : ℕ) (rounds : ℕ → ℕ) : ℕ :=
  amplificationTreeGateCount (uniformNodeGateCount d D N)
    (uniformNodeGateCount d D N) (uniformReflectionGateCount d D N)
    (uniformReflectionGateCount d D N) rounds (balancedIntervalTree 0 N)

/-- Substituting the routed primitive bounds gives an explicit polynomial
in the length at fixed bond bound. This is a bound on the stated numerical
construction, not an assumption of complete circuit existence. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem uniformCircuitTreeGateCount_le_polynomial (d D N : ℕ) (hN : 0 < N)
    (rounds : ℕ → ℕ) (hrounds : ∀ cut, rounds cut ≤ D) :
    uniformCircuitTreeGateCount d D N rounds ≤
      uniformCircuitResourceCoefficient d D * (bondRegisterWidth d D + 1) ^ 3 *
        (2 * N) ^ (Nat.clog 2 (4 * D + 2) + 3) := by
  let H := N * (bondRegisterWidth d D + 1)
  let m := 76 * (d ^ 4 * D ^ 2) ^ 6 + 8 * (D + 1)
  let f := 400 * (38 * (d ^ 3) ^ 6 + 1) + 1
  have hH : 1 ≤ H := Nat.mul_pos hN (by omega)
  have hH3 : 1 ≤ H ^ 3 := one_le_pow₀ hH
  have hHle : H ≤ H ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < H) (by omega : 1 ≤ 3)
  have hH2 : H ^ 2 ≤ H ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hn : globalSiteCount d D N ≤ 5 * H := by
    simpa only [H, Nat.mul_assoc] using globalSiteCount_le d D N
  have hpacket : uniformPacketGateCount d D N ≤ 5 * m * H := by
    change m * globalSiteCount d D N ≤ 5 * m * H
    calc
      _ ≤ m * (5 * H) := Nat.mul_le_mul_left m hn
      _ = _ := by ring
  have hm : uniformNodeGateCount d D N ≤ (5 * m + 400) * H ^ 3 := by
    rw [uniformNodeGateCount]
    calc
      _ ≤ 5 * m * H + 16 * (5 * H) ^ 2 := Nat.add_le_add hpacket
        (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hn 2))
      _ = 5 * m * H + 400 * H ^ 2 := by ring
      _ ≤ 5 * m * H ^ 3 + 400 * H ^ 3 := Nat.add_le_add
        (Nat.mul_le_mul_left _ hHle) (Nat.mul_le_mul_left 400 hH2)
      _ = _ := by ring
  have hf : uniformReflectionGateCount d D N ≤ f * H ^ 3 :=
    uniformReflectionGateCount_le_cubic d D N hN
  have hreserve : uniformNodeGateCount d D N +
      amplificationTreeOverhead D (uniformNodeGateCount d D N)
        (uniformReflectionGateCount d D N) (uniformReflectionGateCount d D N) ≤
      uniformCircuitResourceCoefficient d D * H ^ 3 := by
    rw [amplificationTreeOverhead]
    calc
      _ = (2 * D + 2) * uniformNodeGateCount d D N +
          D * (1 + 2 * uniformReflectionGateCount d D N) := by ring
      _ ≤ (2 * D + 2) * ((5 * m + 400) * H ^ 3) +
          D * (H ^ 3 + 2 * (f * H ^ 3)) :=
        Nat.add_le_add
          (Nat.mul_le_mul_left _ hm)
          (Nat.mul_le_mul_left D (Nat.add_le_add hH3 (Nat.mul_le_mul_left 2 hf)))
      _ = _ := by dsimp [uniformCircuitResourceCoefficient, m, f]; ring
  have htree := amplificationTreeGateCount_balanced_le_polynomial
    (uniformNodeGateCount d D N) (uniformNodeGateCount d D N)
    (uniformReflectionGateCount d D N) (uniformReflectionGateCount d D N)
    D 0 N hN rounds hrounds
  change uniformCircuitTreeGateCount d D N rounds ≤ _ at htree
  refine htree.trans ((Nat.mul_le_mul_right _ hreserve).trans ?_)
  rw [pow_add]
  dsimp [H]
  rw [mul_pow]
  calc
    _ = uniformCircuitResourceCoefficient d D * (bondRegisterWidth d D + 1) ^ 3 *
        (2 * N) ^ Nat.clog 2 (4 * D + 2) * N ^ 3 := by ring
    _ ≤ _ := by
      have hmul := Nat.mul_le_mul_left
        (uniformCircuitResourceCoefficient d D * (bondRegisterWidth d D + 1) ^ 3 *
          (2 * N) ^ Nat.clog 2 (4 * D + 2))
        (Nat.pow_le_pow_left (by omega : N ≤ 2 * N) 3)
      convert hmul using 1
      ring

/-- The explicit coefficient is polynomial in the bond dimension, while
the exponent of the physical length grows only logarithmically. Source:
the resource bound in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem uniformCircuitTreeGateCount_le_polynomial_bond {d D N : ℕ}
    (hd : 2 ≤ d) (hD : 0 < D) (hN : 0 < N)
    (rounds : ℕ → ℕ) (hrounds : ∀ cut, rounds cut ≤ D) :
    uniformCircuitTreeGateCount d D N rounds ≤
      uniformCircuitResourceCoefficient d D * (D + 1) ^ 3 *
        (2 * N) ^ (Nat.clog 2 D + 6) := by
  have hcoeff := Nat.mul_le_mul_left (uniformCircuitResourceCoefficient d D)
    (Nat.pow_le_pow_left
      (Nat.add_le_add_right (bondRegisterWidth_le_bondDim (D := D) hd) 1) 3)
  have hexp : Nat.clog 2 (4 * D + 2) + 3 ≤ Nat.clog 2 D + 6 := by
    have := amplification_branching_exponent_le hD
    omega
  exact (uniformCircuitTreeGateCount_le_polynomial d D N hN rounds hrounds).trans
    (Nat.mul_le_mul hcoeff (Nat.pow_le_pow_right (by omega : 0 < 2 * N) hexp))

end MPUCircuit
