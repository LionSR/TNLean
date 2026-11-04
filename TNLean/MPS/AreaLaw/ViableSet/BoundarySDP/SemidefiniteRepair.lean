/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.GramMeshes

/-!
# Semidefinite minimization and density repair

This is part of the finite-precision analysis of the boundary optimization in
Landau, Vazirani and Vidick, arXiv:1307.5143v1, equation `eq:conv`.
-/

open Matrix
open scoped Kronecker ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw
/-- A canonical factor-grid spacing for a prescribed entrywise Gram error `ζ`.
The denominator includes `ζ` itself so that the spacing is at most one without
requiring an upper bound on the requested error. -/
noncomputable def gramCertificateMesh
    (ι : Type*) [Fintype ι] (C ζ : ℝ) : ℝ :=
  ζ / ((Fintype.card ι : ℝ) * (2 * √C + 1) + ζ)

/-- A strictly positive relaxation of any real entry-square bound. -/
noncomputable def gramCertificateBound (x : ℝ) : ℝ := 1 + |x|

/-- An explicit entry bound for the approximate density variable, obtained from its
bounded shifted Gram factor. -/
noncomputable def approxSDPDensityEntryBound (n : ℕ) (κ ε : ℝ) : ℝ :=
  n * gramCertificateBound (1 + κ + n * ε) + ε

/-- An explicit entry bound for either approximate auxiliary variable. -/
noncomputable def approxSDPAuxEntryBound (r : ℕ) (η εb : ℝ) : ℝ :=
  r * gramCertificateBound (η + 2 * r * εb) + εb

/-- The cardinality bound for the canonical finite Gram-certificate grid. -/
noncomputable def gramCertificateNetCard
    (ι : Type*) [Fintype ι] (C ζ : ℝ) : ℕ :=
  (2 * ⌈(Fintype.card ι : ℝ) ^ 2 /
    (gramCertificateMesh ι C ζ / ((Fintype.card ι : ℝ) ^ 2 * √C))⌉₊ + 1) ^
      (2 * Fintype.card ι ^ 2)

/-- The integer coordinate-grid order needed to attain the canonical Gram mesh. -/
noncomputable def gramCertificateGridOrder
    (ι : Type*) [Fintype ι] (C ζ : ℝ) : ℕ :=
  ⌈√C / gramCertificateMesh ι C ζ⌉₊

/-- The concrete coordinate grid used for bounded Gram certificates. -/
noncomputable def gramCertificateGrid
    (ι : Type*) [Fintype ι] (C ζ : ℝ) : Finset (Matrix ι ι ℂ) :=
  complexMatrixGrid ι (gramCertificateGridOrder ι C ζ) √C

/-- The relaxed Gram-factor bound is strictly positive. -/
theorem gramCertificateBound_pos (x : ℝ) : 0 < gramCertificateBound x := by
  rw [gramCertificateBound]
  positivity

/-- Every real number is at most its relaxed Gram-factor bound. -/
theorem le_gramCertificateBound (x : ℝ) : x ≤ gramCertificateBound x := by
  rw [gramCertificateBound]
  linarith [le_abs_self x]

/-- The density-variable entry bound is positive in positive dimension for a
nonnegative spectral tolerance. -/
theorem approxSDPDensityEntryBound_pos {n : ℕ} (hn : 0 < n) {κ ε : ℝ}
    (hε : 0 ≤ ε) : 0 < approxSDPDensityEntryBound n κ ε := by
  rw [approxSDPDensityEntryBound]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp := mul_pos hn' (gramCertificateBound_pos (1 + κ + n * ε))
  linarith

/-- The auxiliary-variable entry bound is positive in positive dimension for a
nonnegative spectral tolerance. -/
theorem approxSDPAuxEntryBound_pos {r : ℕ} (hr : 0 < r) {η εb : ℝ}
    (hεb : 0 ≤ εb) : 0 < approxSDPAuxEntryBound r η εb := by
  rw [approxSDPAuxEntryBound]
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hp := mul_pos hr' (gramCertificateBound_pos (η + 2 * r * εb))
  linarith

/-- The canonical Gram-certificate mesh is positive. -/
theorem gramCertificateMesh_pos
    {ι : Type*} [Fintype ι] [Nonempty ι] {C ζ : ℝ} (hζ : 0 < ζ) :
    0 < gramCertificateMesh ι C ζ := by
  apply div_pos hζ
  have hcard : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  positivity

/-- The canonical factor mesh makes the induced Gram error no larger than the
prescribed tolerance. -/
theorem gramCertificateMesh_error_le
    {ι : Type*} [Fintype ι] [Nonempty ι] {C ζ : ℝ} (hζ : 0 < ζ) :
    Fintype.card ι * gramCertificateMesh ι C ζ *
        (2 * √C + gramCertificateMesh ι C ζ) ≤ ζ := by
  have hcard : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hbase : 0 < (Fintype.card ι : ℝ) * (2 * √C + 1) := by positivity
  have hden : 0 < (Fintype.card ι : ℝ) * (2 * √C + 1) + ζ := add_pos hbase hζ
  have hmesh : 0 ≤ gramCertificateMesh ι C ζ :=
    (gramCertificateMesh_pos hζ).le
  have hmeshOne : gramCertificateMesh ι C ζ ≤ 1 := by
    rw [gramCertificateMesh, div_le_one hden]
    linarith [hbase]
  have hidentity : gramCertificateMesh ι C ζ *
      ((Fintype.card ι : ℝ) * (2 * √C + 1) + ζ) = ζ := by
    rw [gramCertificateMesh]
    exact div_mul_cancel₀ ζ hden.ne'
  calc
    Fintype.card ι * gramCertificateMesh ι C ζ *
        (2 * √C + gramCertificateMesh ι C ζ) ≤
        Fintype.card ι * gramCertificateMesh ι C ζ * (2 * √C + 1) := by
      gcongr
    _ = gramCertificateMesh ι C ζ *
        ((Fintype.card ι : ℝ) * (2 * √C + 1)) := by ring
    _ ≤ ζ := by nlinarith

/-- The canonical Gram coordinate-grid order is positive. -/
theorem gramCertificateGridOrder_pos
    {ι : Type*} [Fintype ι] [Nonempty ι] {C ζ : ℝ}
    (hC : 0 < C) (hζ : 0 < ζ) :
    0 < gramCertificateGridOrder ι C ζ := by
  rw [gramCertificateGridOrder]
  exact Nat.ceil_pos.mpr (div_pos (Real.sqrt_pos.2 hC) (gramCertificateMesh_pos hζ))

/-- The concrete Gram grid has the expected coordinate-count cardinality. -/
theorem gramCertificateGrid_card_le
    {ι : Type*} [Fintype ι] (C ζ : ℝ) :
    (gramCertificateGrid ι C ζ).card ≤
      (2 * gramCertificateGridOrder ι C ζ + 1) ^
        (2 * Fintype.card ι ^ 2) := by
  exact complexMatrixGrid_card_le _ _

/-- Every factor with squared entries bounded by `C` has a representative in the
concrete Gram grid whose Gram matrix is entrywise `ζ`-close. -/
theorem exists_mem_gramCertificateGrid
    {ι : Type*} [Fintype ι] [Nonempty ι] {C ζ : ℝ}
    (hC : 0 < C) (hζ : 0 < ζ) (R : Matrix ι ι ℂ)
    (hR : ∀ i j, ‖R i j‖ ^ 2 ≤ C) :
    ∃ Q ∈ gramCertificateGrid ι C ζ,
      ∀ i j, ‖(R * Rᴴ - Q * Qᴴ) i j‖ ≤ ζ := by
  let M := gramCertificateGridOrder ι C ζ
  have hM : 0 < M := gramCertificateGridOrder_pos hC hζ
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hmesh : 0 < gramCertificateMesh ι C ζ := gramCertificateMesh_pos hζ
  have hentry : ∀ i j, ‖R i j‖ ≤ √C := by
    intro i j
    nlinarith [hR i j, Real.sq_sqrt hC.le, norm_nonneg (R i j), Real.sqrt_nonneg C]
  have hratio : √C / gramCertificateMesh ι C ζ ≤ M := by
    exact Nat.le_ceil _
  have hround : √C / M ≤ gramCertificateMesh ι C ζ := by
    rw [div_le_iff₀ hMreal]
    have := (div_le_iff₀ hmesh).mp hratio
    nlinarith
  obtain ⟨Q, hQ, hclose⟩ :=
    exists_mem_complexMatrixGrid hM (Real.sqrt_pos.2 hC) R hentry
  refine ⟨Q, hQ, fun i j ↦ ?_⟩
  exact (norm_gram_sub_apply_le_of_entry_norm_le R Q (Real.sqrt_nonneg C)
    hmesh.le hentry (fun i j ↦ (hclose i j).trans hround) i j).trans
      (gramCertificateMesh_error_le hζ)

/-- Bounded Gram factors admit an explicit finite certificate net at any prescribed
positive entrywise Gram tolerance.  The canonical mesh absorbs the quadratic rounding
error, so the statement has no additional grid parameter. -/
theorem exists_finset_bounded_gram_certificate_net_at_error
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {C ζ : ℝ} (hC : 0 < C) (hζ : 0 < ζ) :
    ∃ N : Finset (Matrix ι ι ℂ),
      N.card ≤ gramCertificateNetCard ι C ζ ∧
      ∀ R : Matrix ι ι ℂ, (∀ i j, ‖R i j‖ ^ 2 ≤ C) →
        ∃ Q ∈ N, ∀ i j, ‖(R * Rᴴ - Q * Qᴴ) i j‖ ≤ ζ := by
  classical
  obtain ⟨N, hNcard, hNcover⟩ :=
    exists_finset_bounded_gram_certificate_net (ι := ι) (C := C)
      (δ := gramCertificateMesh ι C ζ) hC (gramCertificateMesh_pos hζ)
  refine ⟨N, ?_, ?_⟩
  · simpa only [gramCertificateNetCard] using hNcard
  intro R hR
  obtain ⟨Q, hQN, hclose⟩ := hNcover R hR
  exact ⟨Q, hQN, fun i j ↦ (hclose i j).trans (gramCertificateMesh_error_le hζ)⟩

/-- The density matrices have a finite trace-norm net whose centers are themselves exact
density matrices.  It is obtained by retaining the unit-ball grid cells which meet the
density matrices and choosing one density representative in each retained cell.  The
covering radius is doubled, while the ambient grid cardinality is unchanged. -/
theorem exists_finset_density_rectangularTraceNorm_net
    {ι : Type*} [Fintype ι] [DecidableEq ι] {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : Finset (Matrix ι ι ℂ),
      N.card ≤
        (2 * ⌈(Fintype.card ι : ℝ) ^ 2 / δ⌉₊ + 1) ^
          (2 * Fintype.card ι ^ 2) ∧
      (∀ ρ ∈ N, ρ.PosSemidef ∧ ρ.trace = 1) ∧
      ∀ σ : Matrix ι ι ℂ, σ.PosSemidef → σ.trace = 1 →
        ∃ ρ ∈ N, rectangularTraceNorm (σ - ρ) ≤ 2 * δ := by
  classical
  obtain ⟨G, hGcard, hGcover⟩ :=
    Matrix.exists_finset_rectangularTraceNorm_net (n := ι) (η := δ) hδ
  let Good : Matrix ι ι ℂ → Prop := fun X ↦
    ∃ ρ : Matrix ι ι ℂ,
      ρ.PosSemidef ∧ ρ.trace = 1 ∧ rectangularTraceNorm (ρ - X) ≤ δ
  let rep : Matrix ι ι ℂ → Matrix ι ι ℂ := fun X ↦
    if h : Good X then Classical.choose h else 0
  let N := (G.filter Good).image rep
  have hNcard : N.card ≤ G.card := by
    exact Finset.card_image_le.trans (Finset.card_filter_le _ _)
  refine ⟨N, hNcard.trans hGcard, ?_, ?_⟩
  · intro ρ hρ
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hρ
    have hgood : Good X := (Finset.mem_filter.mp hX).2
    dsimp only [rep]
    rw [dite_eq_left hgood]
    exact ⟨(Classical.choose_spec hgood).1, (Classical.choose_spec hgood).2.1⟩
  · intro σ hσ hσtrace
    have hσnorm : rectangularTraceNorm σ ≤ 1 := by
      rw [rectangularTraceNorm_eq_re_trace_of_posSemidef hσ, hσtrace]
      norm_num
    obtain ⟨X, hXG, hσX⟩ := hGcover σ hσnorm
    have hgood : Good X := ⟨σ, hσ, hσtrace, hσX⟩
    refine ⟨rep X, Finset.mem_image.mpr
      ⟨X, Finset.mem_filter.mpr ⟨hXG, hgood⟩, rfl⟩, ?_⟩
    have hrep := (Classical.choose_spec hgood).2.2
    have hrepdef : rep X = Classical.choose hgood := by
      dsimp only [rep]
      rw [dite_eq_left hgood]
    have hrev : rectangularTraceNorm (X - rep X) ≤ δ := by
      rw [hrepdef]
      have heq : X - Classical.choose hgood =
          (-1 : ℂ) • (Classical.choose hgood - X) := by module
      rw [heq, rectangularTraceNorm_smul]
      norm_num
      exact hrep
    calc
      rectangularTraceNorm (σ - rep X) =
          rectangularTraceNorm ((σ - X) + (X - rep X)) := by congr 1; abel
      _ ≤ rectangularTraceNorm (σ - X) + rectangularTraceNorm (X - rep X) :=
        rectangularTraceNorm_add_le _ _
      _ ≤ 2 * δ := by linarith

/-- The number of real scalar coordinates needed to specify the three Hermitian matrix
variables in the compressed boundary semidefinite program.  A Hermitian matrix of order
`d` has `d ^ 2` real coordinates; the variables have orders `n`, `r`, and `r`.

This is the finite-dimensional size count implicit in LVV13, equation `eq:conv`,
`algo53.tex`, lines 472--476.  It does not assert a running-time bound for a particular
semidefinite-program solver. -/
def compressedBoundarySDPRealCoordinateCount (n r : ℕ) : ℕ :=
  n ^ 2 + 2 * r ^ 2

/-- The sum of the orders of the three positive-semidefinite cones in the compressed
boundary program. -/
def compressedBoundarySDPTotalConeOrder (n r : ℕ) : ℕ :=
  n + 2 * r

/-- The scalar-coordinate count is monotone in the density and boundary orders. -/
theorem compressedBoundarySDPRealCoordinateCount_le
    {n r nMax rMax : ℕ} (hn : n ≤ nMax) (hr : r ≤ rMax) :
    compressedBoundarySDPRealCoordinateCount n r ≤
      compressedBoundarySDPRealCoordinateCount nMax rMax := by
  exact Nat.add_le_add (Nat.pow_le_pow_left hn 2)
    (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hr 2))

/-- The total positive-semidefinite cone order is monotone in the two matrix orders. -/
theorem compressedBoundarySDPTotalConeOrder_le
    {n r nMax rMax : ℕ} (hn : n ≤ nMax) (hr : r ≤ rMax) :
    compressedBoundarySDPTotalConeOrder n r ≤
      compressedBoundarySDPTotalConeOrder nMax rMax := by
  exact Nat.add_le_add hn (Nat.mul_le_mul_left 2 hr)

/-- For the LVV support compression at a chain cut, the semidefinite program has at most
`(|S| m)² + 2 (q m)²` real scalar coordinates and total cone order at most
`|S| m + 2 q m`.  Thus its matrix dimensions are polynomial in the retained support size,
the local dimension, and the actual bond dimension. -/
theorem chain_compressedBoundarySDP_size_le
    {L q k m n : ℕ} (S : Finset (LeftBlockVector L q k)) (hq : 1 ≤ q)
    (hn : n ≤ S.card * m) :
    let r := Fintype.card (CutSite L q k × Fin m)
    compressedBoundarySDPRealCoordinateCount n r ≤
        compressedBoundarySDPRealCoordinateCount (S.card * m) (q * m) ∧
      compressedBoundarySDPTotalConeOrder n r ≤
        compressedBoundarySDPTotalConeOrder (S.card * m) (q * m) := by
  classical
  intro r
  have hr : r ≤ q * m := by
    simpa only [r, Fintype.card_prod, Fintype.card_fin] using
      Nat.mul_le_mul (card_cutSite_le (L := L) (k := k) hq) (Nat.le_refl m)
  exact ⟨compressedBoundarySDPRealCoordinateCount_le hn hr,
    compressedBoundarySDPTotalConeOrder_le hn hr⟩

/-- The compressed LVV density problem at energy threshold `E` is feasible if and only
if its explicit semidefinite system is feasible.  Thus all nonlinear-looking content of
the trace-norm boundary condition has been replaced by two auxiliary positive-semidefinite
variables.  This is LVV13, equation `eq:conv`, `algo53.tex`, lines 472--476, after support
compression. -/
theorem exists_compressed_boundary_density_iff_exists_sdp_feasible_at_energy
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    (hX : X.IsHermitian) (η E : ℝ) :
    (∃ σ : Matrix (Fin n) (Fin n) ℂ,
      σ.PosSemidef ∧ σ.trace = 1 ∧
      rectangularTraceNorm (compressedBoundaryLM Z σ - X) ≤ η ∧
      (σ * K).trace.re ≤ E) ↔
    ∃ σ : Matrix (Fin n) (Fin n) ℂ,
      ∃ P N : Matrix (s × b) (s × b) ℂ,
        IsCompressedBoundarySDPFeasibleAtEnergy Z K X η E σ P N := by
  constructor
  · rintro ⟨σ, hσ, htrace, hboundary, henergy⟩
    obtain ⟨P, N, hP, hN, hsub, htraces⟩ :=
      (compressedBoundary_rectangularTraceNorm_le_iff_exists_posSemidef_sub
        Z hσ.isHermitian X hX η).mp hboundary
    exact ⟨σ, P, N, hσ, htrace, hP, hN, hsub, htraces, henergy⟩
  · rintro ⟨σ, P, N, hσ, htrace, hP, hN, hsub, htraces, henergy⟩
    refine ⟨σ, hσ, htrace, ?_, henergy⟩
    exact (compressedBoundary_rectangularTraceNorm_le_iff_exists_posSemidef_sub
      Z hσ.isHermitian X hX η).mpr ⟨P, N, hP, hN, hsub, htraces⟩

/-- A nonempty compressed LVV boundary problem attains its minimum energy, and the
minimizer admits an explicit semidefinite certificate.  This is the attained-minimum
part of LVV13, equation `eq:conv`, `algo53.tex`, lines 472--476, after support
compression. -/
theorem exists_compressed_boundary_sdp_minimizer_of_nonempty
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    (hX : X.IsHermitian) (η : ℝ)
    (hne : ∃ τ : Matrix (Fin n) (Fin n) ℂ,
      τ.PosSemidef ∧ τ.trace = 1 ∧
        rectangularTraceNorm (compressedBoundaryLM Z τ - X) ≤ η) :
    ∃ σ : Matrix (Fin n) (Fin n) ℂ,
      ∃ P N : Matrix (s × b) (s × b) ℂ,
        IsCompressedBoundarySDPFeasibleAtEnergy Z K X η
          (σ * K).trace.re σ P N ∧
        ∀ τ : Matrix (Fin n) (Fin n) ℂ,
          τ.PosSemidef → τ.trace = 1 →
          rectangularTraceNorm (compressedBoundaryLM Z τ - X) ≤ η →
          (σ * K).trace.re ≤ (τ * K).trace.re := by
  classical
  let F := {τ : Matrix (Fin n) (Fin n) ℂ |
    τ.PosSemidef ∧ τ.trace = 1 ∧
      rectangularTraceNorm (compressedBoundaryLM Z τ - X) ≤ η}
  have hboundary : IsClosed {τ : Matrix (Fin n) (Fin n) ℂ |
      rectangularTraceNorm (compressedBoundaryLM Z τ - X) ≤ η} :=
    (Matrix.isClosed_setOf_rectangularTraceNorm_le η).preimage
      ((compressedBoundaryLM Z).continuous_of_finiteDimensional.sub continuous_const)
  have hcompact : IsCompact F := by
    simpa only [F, Set.ofPred_and, Set.inter_assoc] using
      Matrix.isCompact_setOf_posSemidef_trace_eq_one.inter_right hboundary
  have henergy : Continuous fun τ : Matrix (Fin n) (Fin n) ℂ ↦ (τ * K).trace.re :=
    Complex.continuous_re.comp ((continuous_id.mul continuous_const).matrix_trace)
  obtain ⟨σ, hσ, hmin⟩ := hcompact.exists_isMinOn hne henergy.continuousOn
  obtain ⟨P, N, hP, hN, hsub, htraces⟩ :=
    (compressedBoundary_rectangularTraceNorm_le_iff_exists_posSemidef_sub
      Z hσ.1.isHermitian X hX η).mp hσ.2.2
  refine ⟨σ, P, N, ⟨hσ.1, hσ.2.1, hP, hN, hsub, htraces, le_rfl⟩, ?_⟩
  intro τ hτ hτtrace hτboundary
  exact hmin ⟨hτ, hτtrace, hτboundary⟩

/-- A finite exact-density net contains an approximate solution of every nonempty
compressed LVV boundary problem.  Its boundary tolerance is enlarged by `2 δ`, and its
energy is within `‖K‖ (2 δ)` of the global optimum.  This is a finite-search existence
statement; it does not claim that the density representatives are effectively enumerable. -/
theorem exists_finset_approx_compressed_boundary_minimizer
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    (hX : X.IsHermitian) (η : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hne : ∃ τ : Matrix (Fin n) (Fin n) ℂ,
      τ.PosSemidef ∧ τ.trace = 1 ∧
        rectangularTraceNorm (compressedBoundaryLM Z τ - X) ≤ η) :
    ∃ N : Finset (Matrix (Fin n) (Fin n) ℂ),
      N.card ≤ (2 * ⌈(n : ℝ) ^ 2 / δ⌉₊ + 1) ^ (2 * n ^ 2) ∧
      (∀ ρ ∈ N, ρ.PosSemidef ∧ ρ.trace = 1) ∧
      ∃ ρ ∈ N,
        rectangularTraceNorm (compressedBoundaryLM Z ρ - X) ≤ η + 2 * δ ∧
        ∀ τ : Matrix (Fin n) (Fin n) ℂ,
          τ.PosSemidef → τ.trace = 1 →
          rectangularTraceNorm (compressedBoundaryLM Z τ - X) ≤ η →
          (ρ * K).trace.re ≤ (τ * K).trace.re + ‖K‖ * (2 * δ) := by
  classical
  obtain ⟨N, hNcard, hNdensity, hNcover⟩ :=
    exists_finset_density_rectangularTraceNorm_net (ι := Fin n) hδ
  obtain ⟨σ, _P, _Q, hσ, hmin⟩ :=
    exists_compressed_boundary_sdp_minimizer_of_nonempty Z K X hX η hne
  have hσboundary : rectangularTraceNorm (compressedBoundaryLM Z σ - X) ≤ η :=
    (compressedBoundary_rectangularTraceNorm_le_iff_exists_posSemidef_sub
      Z hσ.1.isHermitian X hX η).mpr
        ⟨_P, _Q, hσ.2.2.1, hσ.2.2.2.1, hσ.2.2.2.2.1, hσ.2.2.2.2.2.1⟩
  obtain ⟨ρ, hρN, hσρ⟩ := hNcover σ hσ.1 hσ.2.1
  have hρσ : rectangularTraceNorm (ρ - σ) ≤ 2 * δ := by
    have heq : ρ - σ = (-1 : ℂ) • (σ - ρ) := by module
    rw [heq, rectangularTraceNorm_smul]
    norm_num
    exact hσρ
  have hmap : rectangularTraceNorm
      (compressedBoundaryLM Z ρ - compressedBoundaryLM Z σ) ≤ 2 * δ :=
    (compressedBoundaryLM_distance_le Z hZ σ ρ).trans hρσ
  have hρboundary : rectangularTraceNorm (compressedBoundaryLM Z ρ - X) ≤
      η + 2 * δ := by
    calc
      rectangularTraceNorm (compressedBoundaryLM Z ρ - X) = rectangularTraceNorm
          ((compressedBoundaryLM Z ρ - compressedBoundaryLM Z σ) +
            (compressedBoundaryLM Z σ - X)) := by congr 1; abel
      _ ≤ rectangularTraceNorm
          (compressedBoundaryLM Z ρ - compressedBoundaryLM Z σ) +
            rectangularTraceNorm (compressedBoundaryLM Z σ - X) :=
        rectangularTraceNorm_add_le _ _
      _ ≤ η + 2 * δ := by linarith
  have henergy := (compressedDensity_trace_energy_perturbation σ ρ K (2 * δ) hρσ).2
  refine ⟨N, ?_, hNdensity, ρ, hρN, hρboundary, ?_⟩
  · simpa only [Fintype.card_fin] using hNcard
  · intro τ hτ hτtrace hτboundary
    have hopt := hmin τ hτ hτtrace hτboundary
    have henergyUpper := (abs_le.mp henergy).2
    linarith

/-- Threshold form of the finite-search approximation theorem.  A single feasible density
below energy `E` guarantees a member of the finite exact-density family with boundary
tolerance `η + 2 δ` and energy at most `E + ‖K‖ (2 δ)`. -/
theorem exists_finset_approx_compressed_boundary_solution_at_energy
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    (hX : X.IsHermitian) {η E : ℝ} {δ : ℝ} (hδ : 0 < δ)
    {τ₀ : Matrix (Fin n) (Fin n) ℂ} (hτ₀ : τ₀.PosSemidef)
    (hτ₀trace : τ₀.trace = 1)
    (hτ₀boundary : rectangularTraceNorm (compressedBoundaryLM Z τ₀ - X) ≤ η)
    (hτ₀energy : (τ₀ * K).trace.re ≤ E) :
    ∃ N : Finset (Matrix (Fin n) (Fin n) ℂ),
      N.card ≤ (2 * ⌈(n : ℝ) ^ 2 / δ⌉₊ + 1) ^ (2 * n ^ 2) ∧
      (∀ ρ ∈ N, ρ.PosSemidef ∧ ρ.trace = 1) ∧
      ∃ ρ ∈ N,
        rectangularTraceNorm (compressedBoundaryLM Z ρ - X) ≤ η + 2 * δ ∧
        (ρ * K).trace.re ≤ E + ‖K‖ * (2 * δ) := by
  obtain ⟨N, hNcard, hNdensity, ρ, hρN, hρboundary, hρenergy⟩ :=
    exists_finset_approx_compressed_boundary_minimizer Z hZ K X hX η hδ
      ⟨τ₀, hτ₀, hτ₀trace, hτ₀boundary⟩
  have hthreshold : (τ₀ * K).trace.re + ‖K‖ * (2 * δ) ≤
      E + ‖K‖ * (2 * δ) := by
    simpa only [add_comm] using add_le_add_right hτ₀energy (‖K‖ * (2 * δ))
  exact ⟨N, hNcard, hNdensity, ρ, hρN, hρboundary,
    (hρenergy τ₀ hτ₀ hτ₀trace hτ₀boundary).trans hthreshold⟩

/-- The finite exact-density family may be searched by retaining its members satisfying
the enlarged boundary constraint and choosing one of least compressed energy.  The
retained family is nonempty, and its finite minimizer obeys the same approximation bound
as the candidate supplied by the covering argument. -/
theorem exists_finset_minimizing_approx_compressed_boundary_solution_at_energy
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    (hX : X.IsHermitian) {η E : ℝ} {δ : ℝ} (hδ : 0 < δ)
    {τ₀ : Matrix (Fin n) (Fin n) ℂ} (hτ₀ : τ₀.PosSemidef)
    (hτ₀trace : τ₀.trace = 1)
    (hτ₀boundary : rectangularTraceNorm (compressedBoundaryLM Z τ₀ - X) ≤ η)
    (hτ₀energy : (τ₀ * K).trace.re ≤ E) :
    ∃ N : Finset (Matrix (Fin n) (Fin n) ℂ),
      N.card ≤ (2 * ⌈(n : ℝ) ^ 2 / δ⌉₊ + 1) ^ (2 * n ^ 2) ∧
      (∀ ρ ∈ N, ρ.PosSemidef ∧ ρ.trace = 1) ∧
      ∃ ρ ∈ N,
        rectangularTraceNorm (compressedBoundaryLM Z ρ - X) ≤ η + 2 * δ ∧
        (ρ * K).trace.re ≤ E + ‖K‖ * (2 * δ) ∧
        ∀ σ ∈ N,
          rectangularTraceNorm (compressedBoundaryLM Z σ - X) ≤ η + 2 * δ →
          (ρ * K).trace.re ≤ (σ * K).trace.re := by
  classical
  obtain ⟨N, hNcard, hNdensity, ρ, hρN, hρboundary, hρenergy⟩ :=
    exists_finset_approx_compressed_boundary_solution_at_energy
      Z hZ K X hX hδ hτ₀ hτ₀trace hτ₀boundary hτ₀energy
  let F := N.filter fun σ ↦
    rectangularTraceNorm (compressedBoundaryLM Z σ - X) ≤ η + 2 * δ
  have hρF : ρ ∈ F := Finset.mem_filter.mpr ⟨hρN, hρboundary⟩
  obtain ⟨σ, hσF, hσmin⟩ := Finset.exists_min_image F
    (fun ω ↦ (ω * K).trace.re) ⟨ρ, hρF⟩
  have hσenergy : (σ * K).trace.re ≤ E + ‖K‖ * (2 * δ) :=
    (hσmin ρ hρF).trans hρenergy
  refine ⟨N, hNcard, hNdensity, σ, (Finset.mem_filter.mp hσF).1,
    (Finset.mem_filter.mp hσF).2, hσenergy, ?_⟩
  intro ω hωN hωboundary
  exact hσmin ω (Finset.mem_filter.mpr ⟨hωN, hωboundary⟩)

/-- Any feasible compressed semidefinite certificate may be replaced by a globally
energy-minimizing certificate which remains below the same energy threshold. -/
theorem exists_compressed_boundary_sdp_minimizer_of_feasible
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    (hX : X.IsHermitian) {η E : ℝ}
    {τ₀ : Matrix (Fin n) (Fin n) ℂ} {P₀ N₀ : Matrix (s × b) (s × b) ℂ}
    (h₀ : IsCompressedBoundarySDPFeasibleAtEnergy Z K X η E τ₀ P₀ N₀) :
    ∃ σ : Matrix (Fin n) (Fin n) ℂ,
      ∃ P N : Matrix (s × b) (s × b) ℂ,
        IsCompressedBoundarySDPFeasibleAtEnergy Z K X η E σ P N ∧
        ∀ τ : Matrix (Fin n) (Fin n) ℂ,
          τ.PosSemidef → τ.trace = 1 →
          rectangularTraceNorm (compressedBoundaryLM Z τ - X) ≤ η →
          (σ * K).trace.re ≤ (τ * K).trace.re := by
  obtain ⟨τ₁, hτ₁, hτ₁trace, hτ₁boundary, hτ₁energy⟩ :=
    (exists_compressed_boundary_density_iff_exists_sdp_feasible_at_energy
      Z K X hX η E).mpr ⟨τ₀, P₀, N₀, h₀⟩
  obtain ⟨σ, P, N, hσ, hmin⟩ :=
    exists_compressed_boundary_sdp_minimizer_of_nonempty Z K X hX η
      ⟨τ₁, hτ₁, hτ₁trace, hτ₁boundary⟩
  have hσE : (σ * K).trace.re ≤ E :=
    (hmin τ₁ hτ₁ hτ₁trace hτ₁boundary).trans hτ₁energy
  exact ⟨σ, P, N, ⟨hσ.1, hσ.2.1, hσ.2.2.1, hσ.2.2.2.1,
    hσ.2.2.2.2.1, hσ.2.2.2.2.2.1, hσE⟩, hmin⟩

/-- The trace norm of a difference of positive-semidefinite matrices is at most the sum
of their traces. -/
theorem rectangularTraceNorm_sub_le_re_trace_add_of_posSemidef
    {n : Type*} [Fintype n] [DecidableEq n] {P N : Matrix n n ℂ}
    (hP : P.PosSemidef) (hN : N.PosSemidef) :
    rectangularTraceNorm (P - N) ≤ P.trace.re + N.trace.re :=
  (hermitian_rectangularTraceNorm_le_iff_exists_posSemidef_sub
    (hP.isHermitian.sub hN.isHermitian) (P.trace.re + N.trace.re)).mpr
      ⟨P, N, hP, hN, rfl, le_rfl⟩

/-- If a matrix is within trace-norm distance `δ` of `P - N`, for positive
semidefinite `P`, `N` of total trace at most `η`, then its trace norm is at most
`η + δ`. -/
theorem rectangularTraceNorm_le_add_of_approx_posSemidef_sub
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) {P N : Matrix n n ℂ} {η δ : ℝ}
    (hP : P.PosSemidef) (hN : N.PosSemidef)
    (hresidual : rectangularTraceNorm (H - (P - N)) ≤ δ)
    (htraces : P.trace.re + N.trace.re ≤ η) :
    rectangularTraceNorm H ≤ η + δ := by
  have hsub := rectangularTraceNorm_sub_le_re_trace_add_of_posSemidef hP hN
  calc
    rectangularTraceNorm H = rectangularTraceNorm ((H - (P - N)) + (P - N)) := by
      congr 1
      abel
    _ ≤ rectangularTraceNorm (H - (P - N)) + rectangularTraceNorm (P - N) :=
      rectangularTraceNorm_add_le _ _
    _ ≤ η + δ := by linarith

/-- An approximate semidefinite certificate for the compressed LVV boundary problem.
Only the linear matrix equation identifying the boundary residual with `P - N` is allowed
an error `δ`; positivity, normalization, the trace budget, and the energy bound remain
exact. -/
def IsApproxCompressedBoundarySDPFeasibleAtEnergy
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b]
    {n : ℕ} (Z : Matrix ((a × s) × b) (Fin n) ℂ)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    (η E δ : ℝ) (σ : Matrix (Fin n) (Fin n) ℂ)
    (P N : Matrix (s × b) (s × b) ℂ) : Prop :=
  σ.PosSemidef ∧ σ.trace = 1 ∧
    P.PosSemidef ∧ N.PosSemidef ∧
    rectangularTraceNorm ((compressedBoundaryLM Z σ - X) - (P - N)) ≤ δ ∧
    P.trace.re + N.trace.re ≤ η ∧
    (σ * K).trace.re ≤ E

/-- An error `δ` in the linear boundary-residual equation enlarges the original LVV
trace-norm tolerance by at most `δ`, without a dimension factor. -/
theorem compressed_boundary_density_of_approx_sdp_feasible_at_energy
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    {η E δ : ℝ} {σ : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsApproxCompressedBoundarySDPFeasibleAtEnergy Z K X η E δ σ P N) :
    σ.PosSemidef ∧ σ.trace = 1 ∧
      rectangularTraceNorm (compressedBoundaryLM Z σ - X) ≤ η + δ ∧
      (σ * K).trace.re ≤ E := by
  rcases h with ⟨hσ, htrace, hP, hN, hresidual, htraces, henergy⟩
  exact ⟨hσ, htrace,
    rectangularTraceNorm_le_add_of_approx_posSemidef_sub
      (compressedBoundaryLM Z σ - X) hP hN hresidual htraces,
    henergy⟩

/-- A Hermitian matrix whose least eigenvalue is at least `-ε` becomes positive
semidefinite after adding `ε` times the identity. -/
theorem Matrix.IsHermitian.add_smul_one_posSemidef_of_neg_le_minEigenvalue
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {ε : ℝ}
    (hmin : -ε ≤ minEigenvalue hA) :
    (A + (ε : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by
  have hnonneg : 0 ≤ ε + minEigenvalue hA := by linarith
  have hscalar :
      (((ε + minEigenvalue hA : ℝ) : ℂ) • (1 : Matrix n n ℂ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by exact_mod_cast hnonneg)
  have hshift := sub_minEigenvalue_smul_one_posSemidef hA
  rw [show A + (ε : ℂ) • (1 : Matrix n n ℂ) =
      (A - (minEigenvalue hA : ℂ) • 1) +
        ((ε + minEigenvalue hA : ℝ) : ℂ) • 1 by module]
  exact hshift.add hscalar

/-- An entrywise approximate Gram factorization certifies a least-eigenvalue lower bound.
If `A + ε₀ I` differs entrywise from `R Rᴴ` by at most `ζ`, the additional spectral
loss is at most `(r + 1) ζ` in matrix order `r`. -/
theorem neg_le_minEigenvalue_of_approx_gram_factor
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {ε₀ ε ζ : ℝ} (hζ : 0 ≤ ζ)
    (R : Matrix n n ℂ)
    (hentry : ∀ i j,
      ‖(A + (ε₀ : ℂ) • (1 : Matrix n n ℂ) - R * Rᴴ) i j‖ ≤ ζ)
    (hbudget : ε₀ + ((Fintype.card n : ℝ) + 1) * ζ ≤ ε) :
    -ε ≤ minEigenvalue hA := by
  let D := A + (ε₀ : ℂ) • (1 : Matrix n n ℂ) - R * Rᴴ
  have hD : D.IsHermitian := by
    dsimp only [D]
    exact (hA.add (Matrix.isHermitian_one.smul (by simp [isSelfAdjoint_iff]))).sub
      (Matrix.isHermitian_mul_conjTranspose_self R)
  have hDmin : -((Fintype.card n : ℝ) + 1) * ζ ≤ minEigenvalue hD :=
    neg_card_add_one_mul_le_minEigenvalue_of_entry_norm_le hD hζ hentry
  have hDshift :
      (D + ((((Fintype.card n : ℝ) + 1) * ζ : ℝ) : ℂ) •
        (1 : Matrix n n ℂ)).PosSemidef :=
    Matrix.IsHermitian.add_smul_one_posSemidef_of_neg_le_minEigenvalue hD
      (by simpa only [neg_mul] using hDmin)
  have hgram : (R * Rᴴ).PosSemidef := by
    simpa only [Matrix.mul_one] using
      (Matrix.PosSemidef.one.mul_mul_conjTranspose_same R)
  have hshift :
      (A + ((ε₀ + ((Fintype.card n : ℝ) + 1) * ζ : ℝ) : ℂ) •
        (1 : Matrix n n ℂ)).PosSemidef := by
    rw [show A + ((ε₀ + ((Fintype.card n : ℝ) + 1) * ζ : ℝ) : ℂ) •
        (1 : Matrix n n ℂ) = R * Rᴴ +
          (D + ((((Fintype.card n : ℝ) + 1) * ζ : ℝ) : ℂ) • 1) by
      dsimp only [D]
      module]
    exact hgram.add hDshift
  have hmin := neg_le_minEigenvalue_of_add_smul_one_posSemidef hA hshift
  linarith

/-- The shifted Gram-factor certificate is complete: every Hermitian matrix satisfying
the spectral lower bound admits such a factor, obtained from its positive square root. -/
theorem Matrix.IsHermitian.exists_add_smul_one_eq_mul_conjTranspose_of_neg_le_minEigenvalue
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {ε : ℝ}
    (hmin : -ε ≤ minEigenvalue hA) :
    ∃ R : Matrix n n ℂ, A + (ε : ℂ) • (1 : Matrix n n ℂ) = R * Rᴴ := by
  let B := A + (ε : ℂ) • (1 : Matrix n n ℂ)
  have hB : B.PosSemidef :=
    Matrix.IsHermitian.add_smul_one_posSemidef_of_neg_le_minEigenvalue hA hmin
  refine ⟨CFC.sqrt B, ?_⟩
  rw [Matrix.conjTranspose_cfc_sqrt, CFC.sqrt_mul_sqrt_self B hB.nonneg]

/-- The least-eigenvalue lower bound is equivalent to existence of a Gram factor for the
shifted matrix. -/
theorem Matrix.IsHermitian.neg_le_minEigenvalue_iff_exists_gram_factor
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {ε : ℝ} :
    -ε ≤ minEigenvalue hA ↔
      ∃ R : Matrix n n ℂ, A + (ε : ℂ) • (1 : Matrix n n ℂ) = R * Rᴴ := by
  constructor
  · exact
      Matrix.IsHermitian.exists_add_smul_one_eq_mul_conjTranspose_of_neg_le_minEigenvalue hA
  · rintro ⟨R, hR⟩
    exact neg_le_minEigenvalue_of_add_smul_one_eq_mul_conjTranspose hA R hR

/-- Repairing a Hermitian trace-one matrix whose least eigenvalue is at least `-ε`
produces an exact density matrix within trace-norm distance `2 n ε`.  The dimension
factor is the trace cost of shifting every eigenvalue by `ε`. -/
theorem exists_density_rectangularTraceNorm_sub_le_of_neg_le_minEigenvalue
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (htrace : A.trace = 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmin : -ε ≤ minEigenvalue hA) :
    ∃ A₀ : Matrix n n ℂ,
      A₀.PosSemidef ∧ A₀.trace = 1 ∧
      rectangularTraceNorm (A₀ - A) ≤ 2 * Fintype.card n * ε := by
  classical
  let x₀ : n := Classical.choice (Matrix.nonempty_of_trace_eq_one A htrace)
  let B := A + (ε : ℂ) • (1 : Matrix n n ℂ)
  have hB : B.PosSemidef := by
    exact Matrix.IsHermitian.add_smul_one_posSemidef_of_neg_le_minEigenvalue hA hmin
  let A₀ := Matrix.normalizePosSemidef x₀ B
  have hA₀ : A₀.PosSemidef := Matrix.normalizePosSemidef_posSemidef x₀ hB
  have hA₀trace : A₀.trace = 1 := Matrix.normalizePosSemidef_trace x₀ hB
  have hBtrace : B.trace.re = 1 + Fintype.card n * ε := by
    simp [B, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, htrace]
    ring
  have hshift : ((ε : ℂ) • (1 : Matrix n n ℂ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by exact_mod_cast hε)
  have hBA : rectangularTraceNorm (B - A) = Fintype.card n * ε := by
    rw [show B - A = (ε : ℂ) • (1 : Matrix n n ℂ) by simp [B]]
    rw [rectangularTraceNorm_eq_re_trace_of_posSemidef hshift,
      Matrix.trace_smul, Matrix.trace_one]
    norm_num
    ring
  have hA₀B : rectangularTraceNorm (A₀ - B) = Fintype.card n * ε := by
    rw [show A₀ = Matrix.normalizePosSemidef x₀ B by rfl,
      rectangularTraceNorm_normalizePosSemidef_sub x₀ hB, hBtrace]
    rw [abs_of_nonpos]
    · ring
    · apply sub_nonpos.mpr
      nlinarith [mul_nonneg (Nat.cast_nonneg (Fintype.card n)) hε]
  refine ⟨A₀, hA₀, hA₀trace, ?_⟩
  calc
    rectangularTraceNorm (A₀ - A) =
        rectangularTraceNorm ((A₀ - B) + (B - A)) := by congr 1; abel
    _ ≤ rectangularTraceNorm (A₀ - B) + rectangularTraceNorm (B - A) :=
      rectangularTraceNorm_add_le _ _
    _ ≤ 2 * Fintype.card n * ε := by rw [hA₀B, hBA]; nlinarith

/-- A Hermitian matrix with trace defect at most `κ` and least eigenvalue at least
`-ε` can be repaired to an exact density within trace-norm distance
`κ + 2 n ε`. -/
theorem exists_density_rectangularTraceNorm_sub_le_of_trace_defect_of_minEigenvalue
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {κ ε : ℝ}
    (htrace : |1 - A.trace.re| ≤ κ) (hε : 0 ≤ ε)
    (hmin : -ε ≤ minEigenvalue hA) :
    ∃ A₀ : Matrix n n ℂ,
      A₀.PosSemidef ∧ A₀.trace = 1 ∧
      rectangularTraceNorm (A₀ - A) ≤ κ + 2 * Fintype.card n * ε := by
  classical
  let x₀ : n := Classical.choice (inferInstance : Nonempty n)
  let B := A + (ε : ℂ) • (1 : Matrix n n ℂ)
  have hB : B.PosSemidef :=
    Matrix.IsHermitian.add_smul_one_posSemidef_of_neg_le_minEigenvalue hA hmin
  let A₀ := Matrix.normalizePosSemidef x₀ B
  have hA₀ : A₀.PosSemidef := Matrix.normalizePosSemidef_posSemidef x₀ hB
  have hA₀trace : A₀.trace = 1 := Matrix.normalizePosSemidef_trace x₀ hB
  have hBtrace : B.trace.re = A.trace.re + Fintype.card n * ε := by
    simp [B, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]
    ring
  have hshift : ((ε : ℂ) • (1 : Matrix n n ℂ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by exact_mod_cast hε)
  have hBA : rectangularTraceNorm (B - A) = Fintype.card n * ε := by
    rw [show B - A = (ε : ℂ) • (1 : Matrix n n ℂ) by simp [B]]
    rw [rectangularTraceNorm_eq_re_trace_of_posSemidef hshift,
      Matrix.trace_smul, Matrix.trace_one]
    norm_num
    ring
  have habs : |1 - B.trace.re| ≤ κ + Fintype.card n * ε := by
    rw [hBtrace]
    calc
      |1 - (A.trace.re + Fintype.card n * ε)| =
          |(1 - A.trace.re) - Fintype.card n * ε| := by congr 1; ring
      _ ≤ |1 - A.trace.re| + |Fintype.card n * ε| := abs_sub _ _
      _ ≤ κ + Fintype.card n * ε := by
        rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hε)]
        simpa only [add_comm] using
          add_le_add_right htrace (Fintype.card n * ε)
  have hA₀B : rectangularTraceNorm (A₀ - B) ≤ κ + Fintype.card n * ε := by
    rw [show A₀ = Matrix.normalizePosSemidef x₀ B by rfl,
      rectangularTraceNorm_normalizePosSemidef_sub x₀ hB]
    exact habs
  refine ⟨A₀, hA₀, hA₀trace, ?_⟩
  calc
    rectangularTraceNorm (A₀ - A) =
        rectangularTraceNorm ((A₀ - B) + (B - A)) := by congr 1; abel
    _ ≤ rectangularTraceNorm (A₀ - B) + rectangularTraceNorm (B - A) :=
      rectangularTraceNorm_add_le _ _
    _ ≤ κ + 2 * Fintype.card n * ε := by rw [hBA]; linarith

/-- Approximate positivity can be repaired inside the compressed LVV program.  If a
Hermitian trace-one matrix has least eigenvalue at least `-ε`, its repaired density has
boundary error at most `2 n ε` larger and objective value at most
`2 ‖K‖ n ε` larger. -/
theorem exists_density_program_of_neg_le_minEigenvalue
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ} [Nonempty (Fin n)]
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (htrace : A.trace = 1)
    {η E ε : ℝ} (hε : 0 ≤ ε) (hmin : -ε ≤ minEigenvalue hA)
    (hboundary : rectangularTraceNorm (compressedBoundaryLM Z A - X) ≤ η)
    (henergy : (A * K).trace.re ≤ E) :
    ∃ A₀ : Matrix (Fin n) (Fin n) ℂ,
      A₀.PosSemidef ∧ A₀.trace = 1 ∧
      rectangularTraceNorm (A₀ - A) ≤ 2 * n * ε ∧
      rectangularTraceNorm (compressedBoundaryLM Z A₀ - X) ≤ η + 2 * n * ε ∧
      (A₀ * K).trace.re ≤ E + ‖K‖ * (2 * n * ε) := by
  obtain ⟨A₀, hA₀, hA₀trace, hclose⟩ :=
    exists_density_rectangularTraceNorm_sub_le_of_neg_le_minEigenvalue
      hA htrace hε hmin
  have hclose' : rectangularTraceNorm (A₀ - A) ≤ 2 * n * ε := by
    simpa using hclose
  obtain ⟨_htraceClose, henergyClose, hboundaryClose⟩ :=
    compressedDensity_program_perturbation Z hZ A A₀ K X η (2 * n * ε) hclose' hboundary
  refine ⟨A₀, hA₀, hA₀trace, hclose', hboundaryClose, ?_⟩
  have hupper : (A₀ * K).trace.re - (A * K).trace.re ≤ ‖K‖ * (2 * n * ε) :=
    le_trans (le_abs_self _) henergyClose
  linarith

/-- Trace defect and approximate positivity can be repaired simultaneously inside the
compressed LVV program.  The common trace-norm repair radius is `κ + 2 n ε`. -/
theorem exists_density_program_of_trace_defect_of_minEigenvalue
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ} [Nonempty (Fin n)]
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    {η E κ ε : ℝ} (htrace : |1 - A.trace.re| ≤ κ)
    (hε : 0 ≤ ε) (hmin : -ε ≤ minEigenvalue hA)
    (hboundary : rectangularTraceNorm (compressedBoundaryLM Z A - X) ≤ η)
    (henergy : (A * K).trace.re ≤ E) :
    ∃ A₀ : Matrix (Fin n) (Fin n) ℂ,
      A₀.PosSemidef ∧ A₀.trace = 1 ∧
      rectangularTraceNorm (A₀ - A) ≤ κ + 2 * n * ε ∧
      rectangularTraceNorm (compressedBoundaryLM Z A₀ - X) ≤
        η + (κ + 2 * n * ε) ∧
      (A₀ * K).trace.re ≤ E + ‖K‖ * (κ + 2 * n * ε) := by
  obtain ⟨A₀, hA₀, hA₀trace, hclose⟩ :=
    exists_density_rectangularTraceNorm_sub_le_of_trace_defect_of_minEigenvalue
      hA htrace hε hmin
  have hclose' : rectangularTraceNorm (A₀ - A) ≤ κ + 2 * n * ε := by
    simpa using hclose
  obtain ⟨_htraceClose, henergyClose, hboundaryClose⟩ :=
    compressedDensity_program_perturbation Z hZ A A₀ K X η
      (κ + 2 * n * ε) hclose' hboundary
  refine ⟨A₀, hA₀, hA₀trace, hclose', hboundaryClose, ?_⟩
  have hupper : (A₀ * K).trace.re - (A * K).trace.re ≤
      ‖K‖ * (κ + 2 * n * ε) := le_trans (le_abs_self _) henergyClose
  linarith

/-- A solver certificate with spectral positivity error `ε` and boundary-equation error
`δ` yields a genuine compressed density.  The repaired boundary tolerance is
`η + δ + 2 n ε`, and the energy threshold increases by `2 ‖K‖ n ε`. -/
theorem exists_density_of_spectral_approx_sdp_certificate
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ} [Nonempty (Fin n)]
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (htrace : A.trace = 1)
    {P N : Matrix (s × b) (s × b) ℂ} (hP : P.PosSemidef) (hN : N.PosSemidef)
    {η E δ ε : ℝ} (hε : 0 ≤ ε) (hmin : -ε ≤ minEigenvalue hA)
    (hresidual : rectangularTraceNorm
      ((compressedBoundaryLM Z A - X) - (P - N)) ≤ δ)
    (htraces : P.trace.re + N.trace.re ≤ η)
    (henergy : (A * K).trace.re ≤ E) :
    ∃ A₀ : Matrix (Fin n) (Fin n) ℂ,
      A₀.PosSemidef ∧ A₀.trace = 1 ∧
      rectangularTraceNorm (A₀ - A) ≤ 2 * n * ε ∧
      rectangularTraceNorm (compressedBoundaryLM Z A₀ - X) ≤
        η + δ + 2 * n * ε ∧
      (A₀ * K).trace.re ≤ E + ‖K‖ * (2 * n * ε) := by
  have hboundary : rectangularTraceNorm (compressedBoundaryLM Z A - X) ≤ η + δ :=
    rectangularTraceNorm_le_add_of_approx_posSemidef_sub
      (compressedBoundaryLM Z A - X) hP hN hresidual htraces
  exact exists_density_program_of_neg_le_minEigenvalue
    Z hZ K X hA htrace hε hmin hboundary henergy

/-- A numerical semidefinite certificate with trace defect `κ`, spectral positivity
error `ε`, and boundary-equation error `δ` yields an exact compressed density.  All
three errors are displayed in the resulting boundary and energy bounds. -/
theorem exists_density_of_fully_approx_sdp_certificate
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ} [Nonempty (Fin n)]
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    {P N : Matrix (s × b) (s × b) ℂ} (hP : P.PosSemidef) (hN : N.PosSemidef)
    {η E δ κ ε : ℝ} (htrace : |1 - A.trace.re| ≤ κ)
    (hε : 0 ≤ ε) (hmin : -ε ≤ minEigenvalue hA)
    (hresidual : rectangularTraceNorm
      ((compressedBoundaryLM Z A - X) - (P - N)) ≤ δ)
    (htraces : P.trace.re + N.trace.re ≤ η)
    (henergy : (A * K).trace.re ≤ E) :
    ∃ A₀ : Matrix (Fin n) (Fin n) ℂ,
      A₀.PosSemidef ∧ A₀.trace = 1 ∧
      rectangularTraceNorm (A₀ - A) ≤ κ + 2 * n * ε ∧
      rectangularTraceNorm (compressedBoundaryLM Z A₀ - X) ≤
        η + δ + (κ + 2 * n * ε) ∧
      (A₀ * K).trace.re ≤ E + ‖K‖ * (κ + 2 * n * ε) := by
  have hboundary : rectangularTraceNorm (compressedBoundaryLM Z A - X) ≤ η + δ :=
    rectangularTraceNorm_le_add_of_approx_posSemidef_sub
      (compressedBoundaryLM Z A - X) hP hN hresidual htraces
  exact exists_density_program_of_trace_defect_of_minEigenvalue
    Z hZ K X hA htrace hε hmin hboundary henergy

/-- Two approximately positive Hermitian matrices can be repaired by the same scalar
shift.  Their difference is unchanged, while their total trace grows by exactly
`2 r ε` in dimension `r`. -/
theorem exists_posSemidef_pair_same_sub_of_neg_le_minEigenvalue
    {r : Type*} [Fintype r] [DecidableEq r] [Nonempty r]
    {P N : Matrix r r ℂ} (hP : P.IsHermitian) (hN : N.IsHermitian)
    {ε : ℝ}
    (hPmin : -ε ≤ minEigenvalue hP) (hNmin : -ε ≤ minEigenvalue hN) :
    ∃ P₀ N₀ : Matrix r r ℂ,
      P₀.PosSemidef ∧ N₀.PosSemidef ∧ P₀ - N₀ = P - N ∧
      P₀.trace.re + N₀.trace.re =
        P.trace.re + N.trace.re + 2 * Fintype.card r * ε := by
  let P₀ := P + (ε : ℂ) • (1 : Matrix r r ℂ)
  let N₀ := N + (ε : ℂ) • (1 : Matrix r r ℂ)
  have hP₀ : P₀.PosSemidef :=
    Matrix.IsHermitian.add_smul_one_posSemidef_of_neg_le_minEigenvalue hP hPmin
  have hN₀ : N₀.PosSemidef :=
    Matrix.IsHermitian.add_smul_one_posSemidef_of_neg_le_minEigenvalue hN hNmin
  refine ⟨P₀, N₀, hP₀, hN₀, ?_, ?_⟩
  · simp only [P₀, N₀]
    module
  · simp [P₀, N₀, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]
    ring

end TNLean.MPS.AreaLaw
