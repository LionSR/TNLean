from pathlib import Path
import collections,hashlib,json,os,re,shutil,subprocess,sys,tempfile,time
root=Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-source-corrections')
records=Path('/private/tmp/tnlean-source-corrections')
old=Path(Path('/private/tmp/tnlean-source-main-integration/blueprint-dir').read_text().strip())
base=Path(tempfile.mkdtemp(prefix='tnlean-source-corrections-blueprint-'))
(records/'blueprint-dir').write_text(str(base)+'\n')
for name in ['TNLean','scripts']:shutil.copytree(root/name,base/name,ignore=shutil.ignore_patterns('__pycache__'))
shutil.copytree(root/'blueprint',base/'blueprint',ignore=shutil.ignore_patterns('web','print','*.pdf','*.log','*.aux','*.fdb_latexmk','*.fls','*.synctex.gz','__pycache__'))
for f in ['TNLean.lean','lakefile.toml','lake-manifest.json','lean-toolchain','tenkz.toml']:
 shutil.copy2(root/f,base/f)
shutil.copytree(old/'.lake/packages/qiclean',base/'.lake/packages/qiclean')
shutil.copytree(old/'.deps/tenkz',base/'.deps/tenkz')
for f in ['focused.tex','content-focused.tex','web.tex']:shutil.copy2(old/'blueprint/src'/f,base/'blueprint/src'/f)
p=base/'blueprint/src/content-focused.tex';p.write_text(p.read_text()+'\n\\input{chapter/ch24_peps_source_corrections}\n')
shutil.copy2(old/'texra-blueprint.toml',base/'texra-blueprint.toml')
shutil.copy2(root/'texra-blueprint.toml',base/'texra-blueprint.full.toml')
subprocess.run(['git','init','-q'],cwd=base,check=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
commands=[]
def run(name,cmd,cwd,env=None):
 t=time.monotonic();r=subprocess.run(cmd,cwd=cwd,env=env,capture_output=True,text=True)
 (base/(name+'.log')).write_text(r.stdout+r.stderr)
 row={'name':name,'command':cmd,'cwd':str(cwd),'seconds':round(time.monotonic()-t,3),'returncode':r.returncode,'log_sha256':sha(base/(name+'.log'))}
 commands.append(row);(base/'commands.json').write_text(json.dumps(commands,indent=2)+'\n')
 print(name,r.returncode,flush=True);assert r.returncode==0,(r.stdout+r.stderr)[-5000:]
 return r
newnames=[x['declaration'] for x in json.loads((records/'declarations.json').read_text())]
new=base/'blueprint/src/chapter/ch24_peps_source_corrections.tex'
counts=collections.Counter(x.strip() for body in re.findall(r'\\lean\{([^}]+)\}',new.read_text()) for x in body.split(','))
assert set(counts)==set(newnames) and set(counts.values())=={1}
(base/'tag-coverage.json').write_text(json.dumps(counts,indent=2)+'\n')
for package,p in [('TNLean',base),('QICLean',base/'.lake/packages/qiclean')]:
 paths=[p/(package+'.lean'),*(p/package).rglob('*.lean')]
 (base/(package+'-source-sha256.json')).write_text(json.dumps({str(f.relative_to(p)):sha(f) for f in paths},indent=2)+'\n')
(base/'blueprint-source-sha256.json').write_text(json.dumps({str(p.relative_to(base)):sha(p) for p in (base/'blueprint/src').rglob('*.tex')},indent=2)+'\n')
(base/'source-revision.json').write_text(json.dumps({'base_revision':'cbdcf495faa5d77becb6c8930f54e4860177d60e','source_commit':'pending','qic_revision':'4be0ef429c5048cf1bf4f5b7afd5b9f7b9361ca0','scope':'Exact working source bytes recorded before source commit; source-only snapshot and focused rendering, no Lake build.'},indent=2)+'\n')
run('sync',['python3','scripts/blueprint_lean_sync.py','--root',str(base),'--report',str(base/'sync.json'),'--ci','--report-duplicate-tags','--update-lean-decls'],root)
shutil.copy2(base/'blueprint/lean_decls',base/'full-lean-decls.txt')
nodes={};duplicates=[]
start=re.compile(r'\\begin\{(?:definition|theorem|lemma|proposition|corollary|remark|example)\}')
for p in sorted((base/'blueprint/src').rglob('*.tex')):
 if p.name in ['focused.tex','content-focused.tex']:continue
 s=re.sub(r'(?<!\\)%[^\n]*','',p.read_text());positions=list(start.finditer(s))
 for i,m in enumerate(positions):
  block=s[m.end():positions[i+1].start() if i+1<len(positions) else len(s)];label=re.search(r'\\label\{([^}]+)\}',block)
  if not label:continue
  key=label.group(1);deps={x.strip() for b in re.findall(r'\\uses\{([^}]+)\}',block) for x in b.split(',') if x.strip()}
  if key in nodes:duplicates.append(key)
  nodes[key]=deps
states={};cycles=[];stack=[]
def visit(n):
 if states.get(n)==2:return
 if states.get(n)==1:cycles.append(stack[stack.index(n):]+[n]);return
 states[n]=1;stack.append(n)
 for d in nodes[n]:
  if d in nodes:visit(d)
 stack.pop();states[n]=2
for n in nodes:visit(n)
assert not duplicates and not cycles
(base/'dependency-graph.json').write_text(json.dumps({'nodes':len(nodes),'edges':sum(len(x) for x in nodes.values()),'duplicate_labels':duplicates,'cycles':cycles},indent=2)+'\n')
env=os.environ.copy();env['PATH']='/Users/siruilu/.local/share/uv/tools/texra-blueprint/bin:'+env['PATH'];env['TEXINPUTS']=str(base/'.deps/tenkz/tex')+'//:'
run('pdf',['latexmk','-g','-lualatex','-interaction=nonstopmode','-halt-on-error','focused.tex'],base/'blueprint/src',env)
run('bbl',['/Users/siruilu/.local/share/uv/tools/texra-blueprint/bin/texra-blueprint','--root',str(base),'bbl'],base)
run('web',['/Users/siruilu/.local/share/uv/tools/texra-blueprint/bin/leanblueprint','web'],base/'blueprint',env)
assert not re.search(r'ERROR:|WARNING:',(base/'web.log').read_text())
script=(old/'scoped_web_check.py').read_text().replace(str(old),str(base)).replace('/worktrees/peps-source-integration','/worktrees/peps-source-corrections')
(base/'scoped_web_check.py').write_text(script)
env['PYTHONPATH']='/Users/siruilu/.local/share/uv/tools/texra-blueprint/lib/python3.14/site-packages'
run('browser',['/tmp/qic-regional-blueprint-env/bin/python',str(base/'scoped_web_check.py')],base,env)
print('BLUEPRINT_CHECKS_COMPLETE',base,flush=True)
