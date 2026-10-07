from pathlib import Path
import collections, hashlib, json, os, re, shutil, subprocess, sys, time
repo=Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-fixed-chronological-sources')
base=Path('/tmp/tnlean-fixed-chronological-sources-blueprint-dir').read_text().strip();base=Path(base)
rel=Path('blueprint/src/chapter/ch24_peps_fixed_chronological_sources.tex')
records=[]
def run(name,args,cwd=repo,env=None):
 t=time.monotonic();p=subprocess.run(args,cwd=cwd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (base/(name+'.log')).write_text(p.stdout)
 records.append({'name':name,'command':args,'cwd':str(cwd),'elapsed_seconds':time.monotonic()-t,'returncode':p.returncode})
 (base/'commands.json').write_text(json.dumps(records,indent=2)+'\n')
 print(name,p.returncode,flush=True)
 return p
for p in [rel,Path('blueprint/src/content.tex')]:shutil.copy2(repo/p,base/p)
(base/'source-sha256.json').write_text(json.dumps({str(p):hashlib.sha256((repo/p).read_bytes()).hexdigest() for p in [rel,Path('blueprint/src/content.tex')]},indent=2)+'\n')
manifest_path=Path('/private/tmp/tnlean-fixed-chronological-sources-declarations.json')
manifest=json.loads(manifest_path.read_text())
assert manifest, "Final declaration manifest is required"
tags=collections.Counter()
for payload in re.findall(r'\\lean\{([^}]+)\}',(repo/rel).read_text(),re.S):
 for name in payload.split(','):
  tags[re.sub(r'\s+',' ',name).strip()]+=1
coverage={item['declaration']:tags[item['declaration']] for item in manifest}
(base/'tag-coverage.json').write_text(json.dumps(coverage,indent=2)+'\n')
print('tag coverage',len(coverage),'declarations;',sum(n!=1 for n in coverage.values()),'nonunique',flush=True)
sys.path.insert(0,str(repo/'scripts'));import check_reader_facing_prose as prose
findings=[]
for n,line in enumerate((repo/rel).read_text().splitlines(),1):findings+=prose.check_blueprint_line(rel,n,line)
(base/'prose.json').write_text(json.dumps([{'line':f.line_no,'message':f.message} for f in findings],indent=2)+'\n')
print('prose findings',len(findings),flush=True)
run('chktex',['chktex','-q','-l','blueprint/.chktexrc',str(rel)])
env=os.environ.copy();env['CHECK_TMPDIR']=str(base)
run('latexindent',['scripts/check_latexindent_formatting.sh','--one',str(rel)],env=env)
run('sync',['python3','scripts/blueprint_lean_sync.py','--root',str(base),'--report',str(base/'sync.json'),'--ci','--report-duplicate-tags','--update-lean-decls'])
shutil.copy2(base/'blueprint/lean_decls',base/'full-lean-decls.txt')
nodes={};dups=[]
start=re.compile(r'\\begin\{(?:definition|theorem|lemma|proposition|corollary|remark|example)\}')
for path in sorted((base/'blueprint/src').rglob('*.tex')):
 if path.name in ('content-focused.tex','focused.tex'):continue
 text=path.read_text();text=re.sub(r'(?<!\\)%[^\n]*','',text)
 positions=list(start.finditer(text))
 for i,m in enumerate(positions):
  block=text[m.end():positions[i+1].start() if i+1<len(positions) else len(text)]
  label=re.search(r'\\label\{([^}]+)\}',block)
  if not label:continue
  name=label.group(1);deps=set()
  for payload in re.findall(r'\\uses\{([^}]+)\}',block):deps.update(x.strip() for x in payload.split(',') if x.strip())
  if name in nodes:dups.append(name)
  nodes[name]=deps
state={};cycles=[];stack=[]
def visit(n):
 if state.get(n)==2:return
 if state.get(n)==1:
  cycles.append(stack[stack.index(n):]+[n]);return
 state[n]=1;stack.append(n)
 for d in sorted(nodes[n]):
  if d in nodes:visit(d)
 stack.pop();state[n]=2
for n in nodes:visit(n)
(base/'dependency-graph.json').write_text(json.dumps({'nodes':len(nodes),'edges':sum(map(len,nodes.values())),'duplicate_labels':dups,'cycles':cycles,'changed_entry_edges':{n:sorted(ds) for n,ds in nodes.items() if n in (re.findall(r'\\label\{([^}]+)\}',(repo/rel).read_text()))}},indent=2)+'\n')
print('graph',len(nodes),'nodes',len(cycles),'cycles',flush=True)
env=os.environ.copy();env['PATH']='/Users/siruilu/.local/share/uv/tools/texra-blueprint/bin:'+env['PATH'];env['TEXINPUTS']=str(base/'.deps/tenkz/tex')+'//:'
run('pdf',['latexmk','-g','-lualatex','-interaction=nonstopmode','-halt-on-error','focused.tex'],cwd=base/'blueprint/src',env=env)
run('bbl',['/Users/siruilu/.local/share/uv/tools/texra-blueprint/bin/texra-blueprint','--root',str(base),'bbl'],cwd=base)
run('web',['/Users/siruilu/.local/share/uv/tools/texra-blueprint/bin/leanblueprint','web'],cwd=base/'blueprint',env=env)
print('root',base,flush=True)
web_errors=bool(re.search(r'ERROR:|WARNING:',(base/'web.log').read_text()))
if web_errors or findings or dups or cycles or any(n!=1 for n in coverage.values()) or any(r['returncode'] for r in records):raise SystemExit(1)
