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
        p=P/'index';files=json.load(open(p/'files.json'));calls=json.load(open(p/'all-target-tokens.json'));commands=json.load(open(p/'commands.json'))
        self.assertEqual(len(calls),sum(f['target_token_count'] for f in files));self.assertEqual(len(calls),len({r['call_id'] for r in calls}))
        contexts={c['id']:c for c in commands}
        for r in calls:
            self.assertIn(r['call_id'],contexts[r['command_id']]['target_ids'])
            self.assertEqual(r['call_token'],'c'+s.sha(r['call_id'].encode())[:16])
            self.assertEqual(r['pin'],s.PIN)
        summary=json.load(open(p/'summary.json'))
        self.assertEqual(summary['all_exact_code_tokens'],len(calls))
        self.assertEqual(summary['parser_confirmed_calls'],0)
        self.assertEqual(summary['current_pin_calls_measured_by_this_survey'],0)
    def test_independent_source_token_reconciliation(self):
        actual={r['path']:r for r in json.load(open(P/'index/files.json'))}
        records=json.load(open(P/'index/all-target-tokens.json'));by_path={}
        for r in records:by_path.setdefault(r['path'],[]).append(r)
        for path,raw in s.source_files(s.PIN):
            if not path.endswith('.lean'):continue
            self.assertEqual(actual[path]['sha256'],s.sha(raw))
            text=raw.decode();_,masked=s.lexer.masks(text)
            expected=[(len(text[:m.start()].encode()),len(text[:m.end()].encode()),m[1]) for m in s.TARGET.finditer(masked)]
            observed=[(r['byte_start'],r['byte_end'],r['tactic']) for r in by_path.get(path,[])]
            self.assertEqual(expected,observed,path)
            for r in by_path.get(path,[]):self.assertEqual(raw[r['byte_start']:r['byte_end']].decode(),r['token_text'])
if __name__=='__main__':unittest.main()
