"""Prepare an isolated chapter-34 render; does not execute Lean or mutate source."""
from pathlib import Path
import argparse, hashlib, importlib.metadata, json, shutil, subprocess

parser = argparse.ArgumentParser()
parser.add_argument('--root', type=Path, required=True)
parser.add_argument('--out', type=Path, required=True)
args = parser.parse_args()
root, out = args.root.resolve(), args.out.resolve()
src = out / 'blueprint/src'
src.mkdir(parents=True, exist_ok=True)
for path in (root / 'blueprint/src').iterdir():
    if path.name in ('chapter', 'appendix') or path.name.startswith('.'):
        continue
    if path.is_dir():
        shutil.copytree(path, src/path.name, dirs_exist_ok=True)
    elif path.suffix in ('.tex', '.bib', '.cfg', '.css', '.sty'):
        shutil.copy2(path, src/path.name)
leaf = 'ch34_area_law_graph_foundations.tex'
(src/'chapter').mkdir(exist_ok=True)
leaves = [leaf, 'ch34_area_law_diamond_counting.tex']
for name in leaves:
    shutil.copy2(root/'blueprint/src/chapter'/name, src/'chapter'/name)
(src/'content.tex').write_text('\\input{chapter/'+leaf.removesuffix('.tex')+'}\n')
shutil.copy2(root/'texra-blueprint.toml', out/'texra-blueprint.toml')
config = out/'texra-blueprint.toml'
config.write_text(config.read_text().replace('[blueprint.graphs.subsets]\nft_equal_gauge = { ancestors_of = "thm:sector_bnt_equal_global_gauge", title = "Fundamental-theorem gauge cone" }\n', ''))
(out/'scripts').mkdir(exist_ok=True)
shutil.copy2(root/'scripts/tenkz_paths.py', out/'scripts/tenkz_paths.py')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = {
    'source_head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
    'target_leaf': leaf,
    'target_sha256': sha(root/'blueprint/src/chapter'/leaf),
    'target_leaves': {name: sha(root/'blueprint/src/chapter'/name) for name in leaves},
    'scope': 'One exact chapter, repository macros and bibliography; no full-book or live-browser result.',
    'router_replacement_is_fixture_only': True,
    'graph_subset_removal_is_fixture_only': True,
    'tools': {name: importlib.metadata.version(name) for name in ('texra-blueprint', 'plasTeX', 'leanblueprint')},
    'diagrams': 0,
}
(out/'focus-manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
print(json.dumps(manifest, indent=2))
