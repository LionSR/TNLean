"""F8 phase 2b, hand part: the lattice constructions that are structure literals."""
P = 'TNLean/PEPS/'


def sub(p, a, b):
    s = open(p).read(); assert a in s, (p, a[:70]); open(p, 'w').write(s.replace(a, b))


sub('TNLean/MPS/AreaLaw/StripGeometry.lean', "`TNLean.Lattice.LocalHamiltonian`; columns",
    "`ManyBody.PlaneInteraction`; columns")
SW = P + 'Approximation/SwappedSquareHamiltonianInteraction.lean'
sub(SW, """    ∃ g : Lattice.LocalHamiltonian (AreaLaw.rectangularDomain L L) (q * q) 1 (2 * J),
      g.term =""", """    ∃ g : ManyBody.PlaneInteraction (AreaLaw.rectangularDomain L L) (q * q) 1,
      (∀ X, (g.term X).IsHermitian) ∧ (∀ X, ‖g.term X‖ ≤ 2 * J) ∧ g.term =""")
sub(SW, "      g.operator = Matrix.reindex e e (F * K * Fᴴ) := by",
    "      g.hamiltonian = Matrix.reindex e e (F * K * Fᴴ) := by")
sub(SW, """  refine ⟨{ term := Function.extend (AreaLaw.rectangleAreaLawSupport L L)
              (fun i : SquareLatticeSiteOrEdge L L => Matrix.reindex e e (B i)) 0
            supported := ?_
            hermitian := ?_
            norm_le := ?_ }, rfl, ?_⟩""", """  refine ⟨{ term := Function.extend (AreaLaw.rectangleAreaLawSupport L L)
              (fun i : SquareLatticeSiteOrEdge L L => Matrix.reindex e e (B i)) 0
            mem := ?_ }, ?_, ?_, rfl, ?_⟩""")
GA = P + 'Approximation/SupportedPhysicalBufferGaussian.lean'
sub(GA, "obtain ⟨gH, _, hgOperator⟩ := h.exists_swapped_doubled_localHamiltonian",
    "obtain ⟨gH, hgH, hgHJ, _, hgOperator⟩ := h.exists_swapped_doubled_localHamiltonian")
sub(GA, "have hK' : gH.operator = K'", "have hK' : gH.hamiltonian = K'")
sub(GA, "have hD : gH.operator - K ∈", "have hD : gH.hamiltonian - K ∈")
SR = P + 'AreaLaw/SafeRectangleAreaLaw.lean'
sub(SR, """  let h' : LocalHamiltonian Λ q R (J + 1) :=
    { term := h.term
      supported := h.mem
      hermitian := hh
      norm_le := fun X ↦ (hhJ X).trans (by linarith) }
""", "")
sub(SR, "harea Λ h' E₀ Ω", "harea Λ h hh (fun X ↦ (hhJ X).trans (by linarith)) E₀ Ω")
import glob
for p in glob.glob('TNLean/**/*.lean', recursive=True):
    s = open(p).read()
    t = s.replace('_root_.TNLean.Lattice.LocalHamiltonian.', '_root_.ManyBody.PlaneInteraction.')
    if t != s:
        open(p, 'w').write(t)
# members of the range-`R` family of ground vectors come with the two hypotheses
for p in glob.glob(P + 'Approximation/*.lean'):
    s = open(p).read()
    t = s.replace("⟨H, E₀, hgs⟩", "⟨H, hH, hHJ, E₀, hgs⟩").replace(
        "obtain ⟨H, E₀, hΩ', hgap, hspan⟩ := hΩ", "obtain ⟨H, hH, hHJ, E₀, hΩ', hgap, hspan⟩ := hΩ").replace(
        "obtain ⟨H, E₀, hgap⟩ := hΩ", "obtain ⟨H, hH, hHJ, E₀, hgap⟩ := hΩ")
    if t != s:
        open(p, 'w').write(t)
