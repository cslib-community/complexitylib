#!/usr/bin/env python3
"""Bounded native-format occurrence tables; never final dependencies/application counts."""
import collections,csv,json,pathlib,re,sys
out=pathlib.Path(sys.argv[1]);traces=json.loads((out/'trace-messages.json').read_text());attempts={r['event_id']:r for r in json.loads((out/'attempts.json').read_text())};counts=collections.Counter();owners=collections.defaultdict(set);examples=collections.defaultdict(list);mode_counts=collections.defaultdict(collections.Counter)
funprop=re.compile(r'^\s*\[Meta\.Tactic\.fun_prop\].*?\bapplying:\s+(\S+)')
aesop=re.compile(r'\b(?:norm|safe|unsafe)\|(?:apply|tactic|forward|cases|constructors|simp|destruct)\|(?:global|local|builtin)\|[^\s,;\])]+')
for number,trace in enumerate(traces):
 a=attempts[trace['event_id']]
 for line_number,line in enumerate(trace['message'].splitlines()):
  entries=[]
  if m:=funprop.search(line):entries.append(('fun_prop_applying_line',m.group(1)))
  if '[aesop]' in line:entries += [('aesop_rule_key_mention',m.group()) for m in aesop.finditer(line)]
  for key in entries:
   counts[key]+=1;owners[key].add(a['event_id']);mode_counts[key][a['mode']]+=1
   if len(examples[key])<4:examples[key].append({'event_id':a['event_id'],'mode':a['mode'],'static_head_id':a['static_head_id'],'runtime_full_syntax_id':a['runtime_full_syntax_id'],'path':a['path'],'trace_message_index':number,'line_index':line_number,'native_line':line,'owner_tactic_status':a['status'],'whole_command_returncode':a['whole_command_returncode']})
rows=[]
for category in ('fun_prop_applying_line','aesop_rule_key_mention'):
 top=sorted(((key,count) for key,count in counts.items() if key[0]==category),key=lambda x:(-x[1],x[0][1]))[:40]
 for (category,name),count in top:rows.append({'category':category,'printed_key':name,'retained_line_occurrences':count,'distinct_owner_attempts':len(owners[(category,name)]),'occurrence_mode_counts':dict(mode_counts[(category,name)]),'examples':examples[(category,name)]})
report={'source':'trace-messages.json (lossless gzip also archived)','native_trace_messages':len(traces),'native_trace_record_modes':dict(collections.Counter(t['mode'] for t in traces)),'top_limit_per_category':40,'all_detected_category_occurrences':dict(collections.Counter({category:sum(n for (c,_),n in counts.items() if c==category) for category in ('fun_prop_applying_line','aesop_rule_key_mention')})),'qualification':'Counts are RETAINED TRACE LINE OCCURRENCES, not unique engine applications, successful rules or final proof dependencies. Parent/child owner scopes and rendered trees can repeat the same attempt; no unsafe deduplication is performed. fun_prop applying lines indicate a printed attempted application (possibly local evidence). Aesop keys are mentions only, including queues/rendered states. Failed/censored trace owners remain labeled. Printed local names are not globally unique across goals. Trace absence proves no rule absence. Exact event/source IDs and raw trace line examples are linked.','top':rows}
(out/'rule-evidence.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
with (out/'top-rule-evidence.csv').open('w',newline='') as f:
 writer=csv.DictWriter(f,fieldnames=['category','printed_key','retained_line_occurrences','distinct_owner_attempts','example_event_id','example_static_head_id'],lineterminator='\n');writer.writeheader()
 for row in rows:writer.writerow({k:row[k] for k in ('category','printed_key','retained_line_occurrences','distinct_owner_attempts')}|{'example_event_id':row['examples'][0]['event_id'],'example_static_head_id':row['examples'][0]['static_head_id']})
print(json.dumps({'top_rows':len(rows),'native_messages':len(traces),'category_occurrences':report['all_detected_category_occurrences']}))
