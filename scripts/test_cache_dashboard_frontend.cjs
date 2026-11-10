// Dashboard snapshot validation and formatting checks; no browser or dependencies.
const fs = require('fs');
const path = require('path');
const vm = require('vm');
const root = path.resolve(__dirname, '..');
const directory = path.join(root, 'tools/cache-origin/dashboard');
const source = fs.readFileSync(path.join(directory, 'app.js'), 'utf8');
const replacement = '  globalThis.testAPI = {validate, bytes, bitrate, duration, leanVersion};\n})();';
if (!source.endsWith('  refresh();\n})();\n')) throw new Error('Unexpected script ending');
const context = {
  document: {getElementById() { return {addEventListener() {}}; }, querySelectorAll() {return []; }},
  setInterval() {}, Intl, Date, console,
};
vm.createContext(context);
vm.runInContext(source.replace('  refresh();\n})();\n', replacement), context);
const {validate, bytes, bitrate, duration, leanVersion} = context.testAPI;
const fixture = JSON.parse(fs.readFileSync(path.join(directory, 'preview-data.json'), 'utf8'));
validate(fixture);
const empty = JSON.parse(JSON.stringify(fixture));
empty.coverage = {since:null,until:null,records:0,invalid_records:0,excluded_requests:0,limited:true};
empty.series = []; empty.latest = null; empty.builds = []; empty.popular_builds = [];
empty.storage = {snapshot_at:null,stale:true,entry_count:null,artifact_count:null,mapping_count:null,artifact_bytes:null,mapping_bytes:null,logical_retained_bytes:null,saved_bytes:null,dedup_ratio:null,missing_artifacts:null,disk:{total_bytes:null,used_bytes:null,available_bytes:null,inodes_total:null,inodes_available:null}};
empty.gc = {status:'unknown',last_run_at:null,last_success_at:null,deleted_artifacts:null,deleted_mappings:null,deleted_bytes:null};
for (const win of Object.values(empty.windows)) {
  for (const key of Object.keys(win)) if(typeof win[key] === 'number')win[key]=0;
  win.status_counts={};win.median_seconds=null;win.p95_seconds=null;
}
validate(empty);
let failures = 0;
for (const mutate of [
  d=>{d.schema=2}, d=>{d.windows.day.seconds=-1}, d=>{d.storage=null},
  d=>{d.latest.revision='https://attacker.invalid/'},d=>{d.builds=[null]},
  d=>{d.series[0].body_bytes=Infinity},d=>{d.windows.hour.median_seconds='0'},
  d=>{d.gc.deleted_bytes=-1}, d=>{d.coverage.records=undefined},
]) {
  const data=JSON.parse(JSON.stringify(fixture));mutate(data);
  try {validate(data)} catch(_) {failures++;continue}
  throw new Error('Invalid snapshot accepted');
}
if(bytes(null)!=='—'||bitrate(0)!=='0 bit/s'||duration(null)!=='—'||leanVersion('leanprover--lean4---v4.36.0-rc2')!=='Lean v4.36.0-rc2') throw new Error('Formatting assertion failed');
console.log(`Frontend validation passed: populated/empty snapshots, ${failures} malformed snapshots rejected, null/rate/version formatting.`);
