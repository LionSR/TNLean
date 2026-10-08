from pathlib import Path
import hashlib,importlib.util,json,re,sys
sys.dont_write_bytecode=True
w=Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-approximate-physical-output');b=Path('/private/tmp/tnlean-approximate-physical-output');spec=importlib.util.spec_from_file_location('provenance',w/'scripts/check_openai_provenance.py');p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
rows=json.loads((b/'declarations.json').read_text());pres=json.loads((b/'source-preservation.json').read_text())
for row in rows:
 t=(w/row['path']).read_text();assert row['declaration'] in p.declarations(t);p.notice_block(t,{'id':row['id'],'downstream':{'declaration':row['declaration']},'reuse_kind':'original','paper_sources':[{'version':'September 24, 2026','labels':[row['paper_label']]}]});assert not re.search(r'\b(sorry|admit|native_decide|unsafeCast|axiom)\b',p.lean_parts(t)[0])
for row in pres:
 original=Path(row['original_path']).read_text();new=(w/row['production'][0]['path']).read_text()
 if row['original_module']=='ApproximateCircuitError':original=original[:original.index('/-- The elementary')]+original[original.index('/-- Every original circuit'):]
 if row['original_module']=='EffectCircuitError':original=original.replace('private theorem norm_comp_sub_comp_le_one','theorem norm_comp_sub_comp_le_one',1)
 assert p.lean_parts(original)[0].split()==p.lean_parts(new)[0].split();assert len(new.splitlines())<=1000
(b/'notice-integrity-check.json').write_text(json.dumps({'public_declarations':len(rows),'files':len(pres),'canonical_notice_check':True,'declarations_present':True,'no_forbidden_proof_tokens':True,'proof_token_preservation_except_exact_shared_helper_promotion':True},indent=2)+'\n');print('NOTICES_AND_SCOPED_PROOF_PRESERVATION_PASS',len(rows))
