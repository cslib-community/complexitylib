#!/usr/bin/env python3
"""Checks source identities, token accounting, masking and classification without Lean."""
import importlib.util, json, pathlib, unittest
P=pathlib.Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('survey',P/'survey.py'); s=importlib.util.module_from_spec(spec);spec.loader.exec_module(s)
class Scanner(unittest.TestCase):
    def test_mask_nested_unicode_strings_and_primes(self):
        src='theorem f\' : True := by\n /- fun_prop /- ppt -/ -/\n -- polytime\n exact "ppt"\n have h := \'x\'\n fun_prop\n'
        _,code=s.lexer.masks(src)
        self.assertEqual([m[1] for m in s.TARGET.finditer(code)],['fun_prop'])
        self.assertEqual(len(src),len(code));self.assertEqual(src.count('\n'),code.count('\n'))
    def test_nonbare_tactic_arguments(self):
        src='fun_prop (maxSteps := 128) (disch := (first | assumption | simp)) <;> done'
        end=s.candidate_end(src,0,len(src))
        self.assertEqual(src[:end].strip(),'fun_prop (maxSteps := 128) (disch := (first | assumption | simp))')
    def test_classification(self):
        for src,expected in [('@[aesop safe (rule_sets := [polytime])]','attribute_registration'),
                             ('attribute [fun_prop] f','attribute_registration'),
                             ('`(tactic| first | polytime | assumption)','quoted_tactic_candidate'),
                             ('exact ``polytime','quoted_identifier_reference'),
                             ('by first | polytime | assumption','authored_tactic_candidate')]:
            m=next(s.TARGET.finditer(src));self.assertEqual(s.classify(src,m.start(),src),expected)
    def test_utf8_span_and_stable_token(self):
        src='α : True := by fun_prop';p=src.index('fun_prop');raw=src.encode()
        start=len(src[:p].encode());end=start+8
        self.assertEqual(raw[start:end],b'fun_prop');self.assertNotEqual(start,p)
    def test_pinned_index_accounting(self):
        p=P/'index';files=json.loads((p/'files.json').read_text());calls=json.loads((p/'all-target-tokens.json').read_text());commands=json.loads((p/'commands.json').read_text())
        self.assertEqual(len(calls),sum(f['target_token_count'] for f in files));self.assertEqual(len(calls),len({r['call_id'] for r in calls}))
        contexts={c['id']:c for c in commands}
        for r in calls:
            self.assertIn(r['call_id'],contexts[r['command_id']]['target_ids'])
            self.assertEqual(r['call_token'],'c'+s.sha(r['call_id'].encode())[:16])
            self.assertEqual(r['pin'],s.PIN)
        summary=json.loads((p/'summary.json').read_text())
        self.assertEqual(summary['all_exact_code_tokens'],len(calls))
        self.assertEqual(summary['parser_confirmed_calls'],0)
        self.assertEqual(summary['current_pin_calls_measured_by_this_survey'],0)
    def test_independent_source_token_reconciliation(self):
        actual={r['path']:r for r in json.loads((P/'index/files.json').read_text())}
        records=json.loads((P/'index/all-target-tokens.json').read_text());by_path={}
        for r in records:by_path.setdefault(r['path'],[]).append(r)
        for path,raw in s.source_files(s.PIN):
            if not path.endswith('.lean'):continue
            self.assertEqual(actual[path]['sha256'],s.sha(raw))
            text=raw.decode();_,masked=s.lexer.masks(text)
            expected=[(len(text[:m.start()].encode()),len(text[:m.end()].encode()),m[1]) for m in s.TARGET.finditer(masked)]
            observed=[(r['byte_start'],r['byte_end'],r['tactic']) for r in by_path.get(path,[])]
            self.assertEqual(expected,observed,path)
            for r in by_path.get(path,[]):self.assertEqual(raw[r['byte_start']:r['byte_end']].decode(),r['token_text'])
class RuntimeJoin(unittest.TestCase):
    def test_full_parser_span_and_rejection(self):
        spec=importlib.util.spec_from_file_location('join_runtime',P/'join_runtime.py');j=importlib.util.module_from_spec(spec);spec.loader.exec_module(j)
        raw=b'by fun_prop (disch := assumption)';a=3;b=len(raw);digest=s.sha(raw)
        candidate={'path':'Example.lean','source_sha256':digest,'byte_start':a,'byte_end':a+8,'tactic':'fun_prop','call_id':'head','classification':'authored_tactic_candidate'}
        record={'original_pin':j.PIN,'original_path':'Example.lean','original_sha256':digest,'original_byte_start':a,'original_byte_end':b,'original_text':raw[a:b].decode(),'tactic':'fun_prop','syntax_kind':'native-parser-kind','provenance_artifact':'synthetic-unit-test-only'}
        rows=j.join([record],[candidate],lambda _:raw)
        self.assertEqual(rows[0]['static_head_id'],'head')
        self.assertIn(f'{a}-{b}',rows[0]['runtime_full_syntax_id'])
        for field,value in [('original_pin','historical'),('original_sha256','bad'),('original_text','bad'),('original_byte_end',2),('syntax_kind','')]:
            with self.subTest(field=field),self.assertRaises(ValueError):j.join([{**record,field:value}],[candidate],lambda _:raw)
        with self.assertRaises(ValueError):j.join([record,record],[candidate],lambda _:raw)
if __name__=='__main__':unittest.main()
