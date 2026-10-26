# Original-Lake-options invocation correction

Producer: unchanged e443c8e5. Fixed source pin5bffdf2f. The old collect.py/parse.py and strict arm remain immutable.

`collect-default.py` removes ONLY the nonoriginal forced `-DwarningAsError=true`; any original package/library/source option remains (including guide's original warningAsError=true). `--json` changes message serialization only, matching pinned Lake/Build/Actions.lean:69–100. External acceptance rejects actual unsilenced SerialMessage warning/error, matching Lake.Util.Log.logSerialMessage and CLI --wfail failLv=warning, rather than changing an elaborator option. Raw process returncode and diagnostic severities remain separate. Process wall is captured before external log parsing. Non-JSON stdout is informational, as in Lake. No authenticity claim for arbitrary user-printed JSON.

Only capacity change: permitted8distinct-file pipelines,2threads/process; modes sequential per file. Existing pressure pause remains. No matching/registry/source/proof/budget change.

Control: unchanged whole Cloud and CodeComposition each baseline/import-only/measured/traced PASS, exact native module/import/decl contexts; CodeComposition's strict-mode guard failure disappears under actual options. Source option repr has no nonoriginal warningAsError entry. See default-invocation-control.

Authoritative full command (not yet executed at this freeze):

```sh
python3 evidence/1155/current-5bff/collector/collect-default.py run --checkout /home/samuel/Code/complexitylib-codex/automation-full-d7-1155 --out /home/samuel/Code/complexitylib-codex/automation-census-1155/evidence/1155/current-5bff/survey-default --headers /home/samuel/Code/complexitylib-codex/automation-census-1155/evidence/1155/current-5bff/survey-default/headers.json --producer /home/samuel/Code/complexitylib-codex/automation-census-1155/evidence/1155/current-5bff/method-v3 --traces --jobs 8
```

All647native positions reuse exact identical original bytes/parser results from dae3; new filenames are bound in headers. Five configured abstract direct-import targets prepared successfully before this arm (default-abstract-imports-result.json). No individual default supplement or source repair.
