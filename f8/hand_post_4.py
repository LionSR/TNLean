"""Blueprint: the deleted zero family, and the sums the definitions now take from QICLean."""
import pathlib
for f in pathlib.Path('blueprint/src/chapter').glob('ch35_one_dimensional_*.tex'):
    s = f.read_text(); t = s
    for tag in ('ManyBody.Interaction.hamiltonian', 'ManyBody.Interaction.isHermitian_hamiltonian',
                'ManyBody.ChainInteraction.zero'):
        t = t.replace(f'        {tag},\n', '')
    if t != s:
        f.write_text(t)

# phase 2b: the zero lattice interaction is deleted, and the rectangular placement lemma names
# the Hamiltonian
def _sub(p, a, b):
    s = open(p).read(); assert a in s, (p, a[:60]); open(p, 'w').write(s.replace(a, b))


_sub('blueprint/src/chapter/ch24_peps_area_law_models.tex', "        ManyBody.PlaneInteraction.zero,\n", "")
for _p in ('blueprint/src/chapter/ch24_peps_rectangular_specialization.tex',
           'docs/paper-gaps/arealaw2d_rectangular_specialization_scope.tex'):
    _sub(_p, "ManyBody.RectangleInteraction.toAreaLawHamiltonian_operator",
         "ManyBody.RectangleInteraction.toAreaLawHamiltonian_hamiltonian")
