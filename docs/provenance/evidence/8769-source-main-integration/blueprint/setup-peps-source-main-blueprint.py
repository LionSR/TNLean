from pathlib import Path
import hashlib,json,shutil,subprocess,tempfile
repo=Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-source-integration')
qic=Path('/Users/siruilu/Local/agentFormalization/QICLean/worktrees/area-law-pure-tensor-power')
old=Path('/var/folders/d1/qpfb8kqs3dj482nzfg_0yvkc0000gn/T/tnlean-fixed-chronological-sources-blueprint-bvpev6yg')
base=Path(tempfile.mkdtemp(prefix='tnlean-source-main-blueprint-'));Path('/private/tmp/tnlean-source-main-integration/blueprint-dir').write_text(str(base)+'\n')
for d in ['TNLean','scripts']:
 shutil.copytree(repo/d,base/d,ignore=shutil.ignore_patterns('__pycache__'))
shutil.copytree(repo/'blueprint',base/'blueprint',ignore=shutil.ignore_patterns('web','print','*.pdf','*.log','*.aux','*.fdb_latexmk','*.fls','*.synctex.gz','__pycache__'))
for f in ['TNLean.lean','lake-manifest.json','lakefile.toml','lean-toolchain','tenkz.toml','texra-blueprint.toml']:
 shutil.copy2(repo/f,base/f)
qp=base/'.lake/packages/qiclean';qp.mkdir(parents=True)
shutil.copytree(qic/'QICLean',qp/'QICLean')
for f in ['QICLean.lean','lake-manifest.json','lakefile.toml','lean-toolchain']:shutil.copy2(qic/f,qp/f)
shutil.copytree(old/'.deps/tenkz',base/'.deps/tenkz')
for f in ['focused.tex','content-focused.tex','web.tex']:shutil.copy2(old/'blueprint/src'/f,base/'blueprint/src'/f)
subprocess.run(['git','init','-q'],cwd=base,check=True)
rev={'tn_proof_revision':subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),'qic_source_revision':subprocess.check_output(['git','-C',str(qic),'rev-parse','HEAD'],text=True).strip(),'scope':'Source-only blueprint snapshot against checked QIC integration candidate. Final dependency pins and exact integration commit will be synchronized after the checked handoff. No Lake artifacts copied.'}
(base/'source-revision.json').write_text(json.dumps(rev,indent=2)+'\n')
for package,root in [('TNLean',repo),('QICLean',qic)]:
 paths=[root/(package+'.lean'),*(root/package).rglob('*.lean')]
 (base/(package+'-source-sha256.json')).write_text(json.dumps({str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},indent=2)+'\n')
print(base,flush=True)
