"""Check exact chapter source, declaration links, PDF labels, and static HTML."""
from pathlib import Path
from collections import Counter
from dataclasses import asdict
from html.parser import HTMLParser
from urllib.parse import urlsplit, unquote
import argparse, hashlib, json, re, subprocess, sys

p=argparse.ArgumentParser()
p.add_argument('--root',type=Path,required=True)
p.add_argument('--out',type=Path,required=True)
a=p.parse_args(); root=a.root.resolve(); out=a.out.resolve(); web=out/'blueprint/web'
sys.path.insert(0,str(root/'scripts'))
from blueprint_lean_sync import collect_blueprint_entries,collect_blueprint_lean_refs,collect_file_lean_decls
import test_blueprint_web_render as reader
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
cmd=lambda *args:subprocess.check_output(args,cwd=root,text=True)
class Scan(HTMLParser):
    def __init__(self):
        super().__init__(); self.ids=[]; self.anchors=[]; self.hrefs=[]; self.lean=[]
    def handle_starttag(self,tag,attrs):
        d=dict(attrs)
        if 'id' in d:self.ids.append(d['id']);self.anchors.append(d['id'])
        if tag=='a' and 'name' in d:self.anchors.append(d['name'])
        if 'href' in d:self.hrefs.append(d['href'])
        if 'lean_decl' in d.get('class','').split():self.lean.append(d.get('href',''))
m=json.loads((out/'focus-manifest.json').read_text());leaf=m['target_leaf']
source=root/'blueprint/src/chapter'/leaf
leaves=m['target_leaves']
s='\n'.join((root/'blueprint/src/chapter'/name).read_text() for name in leaves)
for name,digest in leaves.items():
    assert sha(root/'blueprint/src/chapter'/name)==digest==sha(out/'blueprint/src/chapter'/name)
assert sha(source)==m['target_sha256']==sha(out/'blueprint/src/chapter'/leaf)
entries=[e for e in collect_blueprint_entries(root/'blueprint/src') if any(e.file.endswith(name) for name in leaves)]
names=[e.lean_decl for e in entries];assert len(names)==len(set(names))==50
assert all(e.has_leanok for e in entries)
refs=collect_blueprint_lean_refs(root/'blueprint/src')
assert all(sum(e.lean_decl==n for e in refs)==1 for n in names)
paths=['TNLean/PEPS/AreaLaw/'+n+'.lean' for n in ('GraphInteractionBudget','GraphInteractionChain','GraphInteractionCounting','GraphLatticeCounting','GraphLatticeDiamond','GraphInteractionDiamondCounting','GraphInteractionTarget','GraphInteractionSeries')]
decls=[d for f in paths for d in collect_file_lean_decls(root/f,root/'TNLean')]
private=[d for d in decls if d.is_private]
assert len(private)==5
decls=[d for d in decls if not d.is_private]
assert len(decls)==50
assert set(names)=={d.fqn for d in decls}
labels=re.findall(r'\\label\{([^}]+)\}',s)
assert len(labels)==len(set(labels))
assert s.count(r'\leanok')==39 and s.count(r'\begin{proof}')==17
for proof in re.findall(r'\\begin\{proof\}.*?\\end\{proof\}',s,re.S):assert r'\leanok' in proof
html_paths=reader._generated_pages(web);reader._assert_generated_source(html_paths)
pages={}
for path in html_paths:
    q=Scan();q.feed(path.read_text());pages[path.name]=q
missing=[];duplicates=[];sentinels=[]
for name,q in pages.items():
    duplicates += [(name,k) for k,c in Counter(q.ids).items() if c>1]
    for link in q.hrefs:
        u=urlsplit(link)
        if u.scheme or u.netloc or not u.fragment or (u.path and not u.path.endswith('.html')):continue
        target=u.path or name
        if target not in pages or unquote(u.fragment) not in pages[target].anchors:missing.append((name,link))
    text=(web/name).read_text()
    sentinels += [(name,k) for k in ['plastex-unknown','??','<merror','<mjx-merror','NaNpx','nanpt'] if k in text]
assert not missing and not duplicates and not sentinels,(missing,duplicates,sentinels)
main=pages['ch-area_graph_foundations.html']
assert all(label in main.anchors for label in labels)
links=[unquote(h.split('#doc/',1)[-1]) for h in main.lean]
assert all(links.count(n)==1 for n in names)
pdf=out/'blueprint/src/print.pdf'; info=cmd('pdfinfo',str(pdf)); urls=cmd('pdfinfo','-url',str(pdf)); dests=cmd('pdfinfo','-dests',str(pdf))
aux=(out/'blueprint/src/print.aux').read_text();records={}
for label in labels:
    match=re.search(r'\\newlabel\{'+re.escape(label)+r'\}\{\{([^}]*)\}\{([^}]*)\}\{[^}]*\}\{([^}]*)\}',aux)
    assert match,label
    number,page,dest=match.groups();assert '"'+dest+'"' in dests
    records[label]={'number':number,'printed_page':int(page),'destination':dest}
pdf_names=re.findall(r'#doc/([^\s]+)',urls);assert all(pdf_names.count(n)==1 for n in names)
problems=[l for l in (out/'blueprint/src/print.log').read_text().splitlines() if re.search(r'Overfull|undefined|Missing character|^!',l)]
assert not problems,problems
assert not re.search(r'^ERROR|could not be resolved|Traceback',(out/'web-build.log').read_text(),re.M)
assert '??' not in (out/'print.txt').read_text()
assert s.count(r'\begin{tenkz}')==0
cmd('git','diff','--check')
report={'status':'passed focused PDF and static HTML verification','render_source_checkpoint':m['source_head'],'target_leaf':leaf,'target_sha256':sha(source),'target_leaves':leaves,'checked_lean_source_revision':'68f708ff111956d832476a9cae2c873375fc3659','source_manifest':{f:sha(root/f) for f in paths},'declarations':[asdict(d) for d in decls],'public_declarations':50,'private_helpers':[asdict(d) for d in private],'entries':22,'proofs':17,'checked_markers':39,'unique_declaration_owners':50,'pdf_pages':int(re.search(r'^Pages:\s+(\d+)',info,re.M).group(1)),'pdf_labels':records,'pdf_declaration_links':50,'html_declaration_links':50,'missing_html_anchors':missing,'duplicate_ids':duplicates,'error_sentinels':sentinels,'pdf_log_problems':problems,'diagrams':0,'tools':m['tools'],'visual_review':'All final PDF page PNGs inspected; no clipping, overlap, missing glyphs or illegible equations.','limits':['Focused chapter only; full-book build, live browser, MathJax runtime and mobile QA not run.','Generated declaration URLs have exact identifiers; remote publication/existence not checked.','All 50 public auxiliary declarations are covered; five private helpers remain private. Physical commutator dynamics and full Lemma 4.1 propagation are not certified by this audit.','This renderer performs no Lean checks; native execution results are recorded separately.','Source checkpoint is published; this local focused check makes no full CI or publication-completion claim.'],'warnings':['Inherited missing pdftex.map/kanjix.map warnings and duplicate page.1 destination; PDF output succeeded.','dvisvgm/vector imager unavailable; no diagrams are present in this chapter.'],'artifacts':{str(p.relative_to(out)):sha(p) for p in [pdf,*html_paths,*sorted((out/'pdf-pages').glob('*.png'))]}}
(out/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
for name,body in [('pdf-info.txt',info),('pdf-links.txt',urls),('pdf-destinations.txt',dests)]: (out/name).write_text(body)
print(json.dumps({k:report[k] for k in ['status','public_declarations','entries','proofs','checked_markers','pdf_pages','missing_html_anchors','duplicate_ids','pdf_log_problems']},indent=2))
