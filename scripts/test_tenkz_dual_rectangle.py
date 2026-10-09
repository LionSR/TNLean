#!/usr/bin/env python3
"""Audit the column/east exchange picture; does not replace Lean checking."""
import os
from pathlib import Path
import re
import subprocess
import tempfile

from tenkz_paths import ensure_pythonpath, tenkz_tex

ROOT = Path(__file__).resolve().parents[1]
FRAGMENT = ROOT / 'blueprint/src/chapter/ch24_peps_dual_rectangle.tex'
EXPECTED = {
    'rectColumnEast': ((6, 2), (2, 2), (2, 6)),
    'rectEastColumn': ((6, 2), (6, 6), (2, 6)),
}


def check_geometry(source):
    routes = {}
    for name, vr, vc, r, c, s, d in re.findall(
            r'\\tnwire\[kind=string, stroke=dotted, route=orth, dir=to,\s*'
            r'name=(\w+), via=\{\((\d+),(\d+)\)\}\]'
            r'\{\((\d+),(\d+)\)\}\{\((\d+),(\d+)\)\}', source):
        assert name not in routes
        routes[name] = ((int(r), int(c)), (int(vr), int(vc)), (int(s), int(d)))
    assert routes == EXPECTED, routes
    # Same lifted endpoints and positive unit-step expansion: N,N,E vs E,N,N.
    for start, corner, end in routes.values():
        assert start == (6, 2) and end == (2, 6)
        assert sum(abs(a-b) for a, b in zip(start, corner)) + sum(
            abs(a-b) for a, b in zip(corner, end)) == 8
    assert source.count(r'\tnmark[form=label]{(5,4)}{$s_1$}') == 2
    assert source.count(r'\tnmark[form=label]{(3,4)}{$s_2$}') == 2
    assert r'\tn[' not in source  # Geometry only, no unaccounted tensor indices.


def main():
    ensure_pythonpath()
    from tenkz_audit import Audit
    source = FRAGMENT.read_text()
    check_geometry(source)
    for old, new in [('via={(2,2)}', 'via={(2,3)}'),
                     ('name=rectColumnEast', 'name=rectEastColumn'),
                     ('stroke=dotted', 'stroke=solid'),
                     ('{(5,4)}{$s_1$}', '{(5,5)}{$s_1$}')]:
        try:
            check_geometry(source.replace(old, new, 1))
        except AssertionError:
            pass
        else:
            raise AssertionError(f'accepted malformed geometry: {old}')
    picture = source[source.index(r'\begin{tenkzequation}'):
                     source.index(r'\end{tenkzequation}') + len(r'\end{tenkzequation}')]
    fixture = (r'\documentclass[varwidth,border=3pt]{standalone}' '\n'
               r'\usepackage{amsmath,amssymb,amsthm,mathtools,tenkz}' '\n'
               r'\newcounter{chapter}\input{macros/common}\input{macros/diagrams}' '\n'
               r'\newenvironment{tenkzequation}{\center}{\endcenter}' '\n'
               r'\begin{document}' '\n' + picture + r'\end{document}')
    env = os.environ.copy()
    env['TEXINPUTS'] = f'{tenkz_tex()}//:{ROOT}/blueprint/src//:' + env.get('TEXINPUTS', '')
    with tempfile.TemporaryDirectory(prefix='tnlean-rectangle-') as tmp:
        work = Path(tmp)
        tex = work / 'rectangle.tex'
        tex.write_text(fixture)
        run = subprocess.run(['xelatex', '-interaction=nonstopmode', '-halt-on-error',
                              tex.name], cwd=work, env=env, text=True,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        assert run.returncode == 0, run.stdout
        assert 'Overfull' not in run.stdout, run.stdout
        info = subprocess.check_output(['pdfinfo', str(work / 'rectangle.pdf')], text=True)
        assert re.search(r'Pages:\s+1\b', info), info
        dimensions = re.search(r'Page size:\s+([\d.]+) x ([\d.]+) pts', info)
        assert dimensions, info
        width, height = map(float, dimensions.groups())
        assert width > 1.8 * height, 'equation panels wrapped vertically'
        audit = Audit(work / 'rectangle.tnlog', tex)
        audit.parse_log()
        audit.link_tex()
        for check in ['check_empty_pictures', 'check_dialects', 'check_kernel_crossings',
                      'check_kernel_checks', 'check_bbox_coverage', 'check_label_overlaps',
                      'check_equation_groups', 'check_equation_boundaries']:
            getattr(audit, check)()
        assert not audit.findings, [(f.severity, f.rule, f.msg) for f in audit.findings]
    print('PASS: routes, lifted endpoints, swept centers, four negative mutations, '
          'single-row XeLaTeX rendering and eight Tenkz audits')


if __name__ == '__main__':
    main()
