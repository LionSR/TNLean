from pathlib import Path
import collections,hashlib,json,os,re,shutil,subprocess,sys,time
repo=Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-source-integration');base=Path(Path('/private/tmp/tnlean-source-main-integration/blueprint-dir').read_text().strip());records=[]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def run(name,cmd,cwd=repo,env=None):
 t=time.monotonic();p=subprocess.run(cmd,cwd=cwd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);log=base/(name+'.log');log.write_text(p.stdout)
 records.append({'name':name,'command':cmd,'cwd':str(cwd),'elapsed_seconds':round(time.monotonic()-t,3),'returncode':p.returncode,'log_sha256':sha(log)});(base/'commands.json').write_text(json.dumps(records,indent=2)+'\n');print(name,p.returncode,flush=True)
 assert p.returncode==0,p.stdout[-6000:]
focus=[Path('blueprint/src')/(s+'.tex') for s in re.findall(r'\\input\{([^}]+)\}',(base/'blueprint/src/content-focused.tex').read_text())]
shards=['8768-source-preparation','8769-party-factorization','8769-unused-pair-sources','8769-common-source-spaces','8769-source-gate-density','8769-source-block-contraction','8769-party-coarsening','8769-selective-source-preparation','8769-chronological-source-expansion','8769-fixed-chronological-sources']
names=[e['downstream']['declaration'] for s in shards for e in json.loads((repo/'docs/provenance/openai-math.d'/f'{s}.json').read_text())['entries']]
counts=collections.Counter()
for rel in focus:
 for body in re.findall(r'\\lean\{([^}]+)\}',(base/rel).read_text(),re.S):
  counts.update(x.strip() for x in body.split(','))
coverage={n:counts[n] for n in names};(base/'tag-coverage.json').write_text(json.dumps(coverage,indent=2)+'\n')
assert all(c==1 for c in coverage.values()),{n:c for n,c in coverage.items() if c!=1}
run('sync',['python3','scripts/blueprint_lean_sync.py','--root',str(base),'--report',str(base/'sync.json'),'--ci','--report-duplicate-tags','--update-lean-decls'])
shutil.copy2(base/'blueprint/lean_decls',base/'full-lean-decls.txt')
nodes={};dups=[];start=re.compile(r'\\begin\{(?:definition|theorem|lemma|proposition|corollary|remark|example)\}')
for path in sorted((base/'blueprint/src').rglob('*.tex')):
 if path.name in ('content-focused.tex','focused.tex'):continue
 text=re.sub(r'(?<!\\)%[^\n]*','',path.read_text());positions=list(start.finditer(text))
 for i,m in enumerate(positions):
  block=text[m.end():positions[i+1].start() if i+1<len(positions) else len(text)];label=re.search(r'\\label\{([^}]+)\}',block)
  if not label:continue
  n=label.group(1);deps=set(x.strip() for body in re.findall(r'\\uses\{([^}]+)\}',block) for x in body.split(',') if x.strip())
  if n in nodes:dups.append(n)
  nodes[n]=deps
state={};cycles=[];stack=[]
def visit(n):
 if state.get(n)==2:return
 if state.get(n)==1:cycles.append(stack[stack.index(n):]+[n]);return
 state[n]=1;stack.append(n)
 for d in sorted(nodes[n]):
  if d in nodes:visit(d)
 stack.pop();state[n]=2
for n in nodes:visit(n)
(base/'dependency-graph.json').write_text(json.dumps({'nodes':len(nodes),'edges':sum(map(len,nodes.values())),'duplicate_labels':dups,'cycles':cycles},indent=2)+'\n');assert not dups and not cycles
content=(base/'blueprint/src/content.tex').read_text();inputs=re.findall(r'\\input\{([^}]+)\}',content);assert len(inputs)==len(set(inputs));assert all((base/'blueprint/src'/(n+'.tex')).is_file() for n in inputs)
(base/'input-routing.json').write_text(json.dumps({'input_count':len(inputs),'duplicates':[],'missing_files':[],'all_incoming_chapters_included':all(f.relative_to('blueprint/src').with_suffix('').as_posix() in inputs for f in focus)},indent=2)+'\n')
env=os.environ.copy();env['PATH']='/Users/siruilu/.local/share/uv/tools/texra-blueprint/bin:'+env['PATH'];env['TEXINPUTS']=str(base/'.deps/tenkz/tex')+'//:'
run('pdf',['latexmk','-g','-lualatex','-interaction=nonstopmode','-halt-on-error','focused.tex'],base/'blueprint/src',env)
run('bbl',['/Users/siruilu/.local/share/uv/tools/texra-blueprint/bin/texra-blueprint','--root',str(base),'bbl'],base)
run('web',['/Users/siruilu/.local/share/uv/tools/texra-blueprint/bin/leanblueprint','web'],base/'blueprint',env)
assert not re.search(r'ERROR:|WARNING:',(base/'web.log').read_text())
print('SOURCE_BLUEPRINT_CHECKS_PASSED',len(coverage),'declarations',len(nodes),'nodes',base,flush=True)
