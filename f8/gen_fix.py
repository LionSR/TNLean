"""Local statements over lattice interactions applied to an interaction without its hypotheses:
scanner targets `htr Λ h S`, and the rectangular interaction placed on the lattice."""
import glob, re
for p in glob.glob('TNLean/PEPS/**/*.lean', recursive=True):
    s = open(p).read()
    t = re.sub(r"\b(htr|htarget|henergy|hsource|ht|hbound)((?: [\w'₀-₉.]+)*? Λ(?: [\w'₀-₉.]+){0,2}) h S ", r"\1\2 h hh hhJ S ", s)
    t = re.sub(r"\b(hnorm|hentropy)( Λ)? h (E₀|Ω) ", r"\1\2 h hh hhJ \3 ", t)
    t = t.replace("""      (h : PlaneInteraction Λ q R) (_ : ∀ X, (h.term X).IsHermitian) (_ : ∀ X, ‖h.term X‖ ≤ J)
          (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
      (E₀ : ℝ) (Ω : StateSpace Λ q),
      ScannerHypotheses X R J Δ CT Ctr C₁ Ce n Λ T hT h hh hhJ S E₀ Ω →""",
                  """      (h : PlaneInteraction Λ q R) (hh : ∀ X, (h.term X).IsHermitian)
      (hhJ : ∀ X, ‖h.term X‖ ≤ J) (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
      (E₀ : ℝ) (Ω : StateSpace Λ q),
      ScannerHypotheses X R J Δ CT Ctr C₁ Ce n Λ T hT h hh hhJ S E₀ Ω →""")
    t = re.sub(r"(regionalEntropy_le_of_boxEntropy_power\b[^⟩]{0,200}?) h hΩ ", r"\1 h hh hhJ hΩ ", t)
    t = re.sub(r"\.((?:log_surprisalMoment|surprisalTail)_truncated_reducedState_le) h Ω\b", r".\1 h hh hhJ Ω", t)
    t = t.replace("intro Λ T _ hT h S E₀ Ω hyp", "intro Λ T _ hT h hh hhJ S E₀ Ω hyp")
    t = t.replace("      hbox h hΩ hgap hspan A Q' hsafe'", "      hbox h hh hhJ hΩ hgap hspan A Q' hsafe'")
    # the scanner statement quantifies over the interaction and both hypotheses of its standing setting
    t = t.replace("""      (h : PlaneInteraction Λ q R) (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
      (E₀ : ℝ) (Ω : StateSpace Λ q),
      ScannerHypotheses X R J Δ CT Ctr C₁ Ce n Λ T hT h hh hhJ S E₀ Ω →""",
                  """      (h : PlaneInteraction Λ q R) (hh : ∀ X, (h.term X).IsHermitian)
      (hhJ : ∀ X, ‖h.term X‖ ≤ J) (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
      (E₀ : ℝ) (Ω : StateSpace Λ q),
      ScannerHypotheses X R J Δ CT Ctr C₁ Ce n Λ T hT h hh hhJ S E₀ Ω →""")
    t = re.sub(r"(\b(?:hcell|hmain|hbound)\b[^\n]*?) h\.toAreaLawHamiltonian E₀",
               r"\1 h.toAreaLawHamiltonian\n      h.isHermitian_toAreaLawHamiltonian_term"
               r" (h.norm_toAreaLawHamiltonian_term_le hhJ) E₀", t)
    if t != s:
        open(p, 'w').write(t); print(p)
