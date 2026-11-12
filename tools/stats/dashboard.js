// Copyright (c) 2026 Christian Reitwiessner. Apache-2.0. Authors: Christian Reitwiessner.
'use strict';
const fmt = new Intl.NumberFormat('en');
const ns = 'http://www.w3.org/2000/svg';
function value(counts, metric) {
  return metric === 'total' ? counts.code + counts.comments + counts.blanks : counts[metric];
}
function series(data, ids, metric) {
  return data.snapshots.map(row => ({...row,
    value: ids.reduce((sum, id) => sum + value(row.categories[id], metric), 0)}));
}
function svgElement(tag, attrs, text) {
  const el = document.createElementNS(ns, tag);
  for (const [key, val] of Object.entries(attrs)) el.setAttribute(key, val);
  if (text !== undefined) el.textContent = text;
  return el;
}
function draw(rows, label) {
  const svg = document.getElementById('chart');
  svg.replaceChildren(svgElement('title', {id:'chart-title'}, label),
    svgElement('desc', {id:'chart-description'}, `${rows.length} daily snapshots. Exact values and source commits follow in the table.`));
  const left = 85, right = 935, top = 20, bottom = 310;
  const max = Math.max(1, ...rows.map(r => r.value));
  const x = i => rows.length === 1 ? (left + right)/2 : left + i*(right-left)/(rows.length-1);
  const y = n => bottom - n/max*(bottom-top);
  for (let tick = 0; tick <= 4; tick++) {
    const n = max*tick/4;
    svg.append(svgElement('line', {x1:left,x2:right,y1:y(n),y2:y(n),class:'grid'}),
      svgElement('text', {x:left-10,y:y(n)+4,'text-anchor':'end'}, fmt.format(Math.round(n))));
  }
  if (!rows.length) return;
  const points = rows.map((r,i) => `${x(i)},${y(r.value)}`).join(' ');
  svg.append(svgElement('polygon', {points:`${x(0)},${bottom} ${points} ${x(rows.length-1)},${bottom}`,class:'area'}),
    svgElement('polyline', {points,class:'curve'}));
  rows.forEach((row,i) => {
    const dot = svgElement('circle', {cx:x(i),cy:y(row.value),r:3});
    dot.append(svgElement('title', {}, `${row.date}: ${fmt.format(row.value)}`));
    svg.append(dot);
  });
  svg.append(svgElement('text', {x:left,y:340}, rows[0].date),
    svgElement('text', {x:right,y:340,'text-anchor':'end'}, rows.at(-1).date));
}
async function start() {
  const response = await fetch('data.json');
  if (!response.ok) throw new Error(`History request failed (${response.status})`);
  const data = await response.json();
  if (!data.snapshots.length) throw new Error('No daily snapshots available');
  const last = data.snapshots.at(-1);
  document.getElementById('status').textContent = `Latest snapshot: ${last.date} UTC · Generated ${new Date(data.generated_at).toUTCString()} · ${data.tokei}`;
  for (const metric of ['code','comments','blanks','files']) {
    document.getElementById(metric).textContent = fmt.format(Object.values(last.categories).reduce((n,c) => n+c[metric],0));
  }
  const fieldset = document.getElementById('categories');
  for (const cat of data.categories) {
    const label = document.createElement('label');
    const input = document.createElement('input');
    input.type = 'checkbox'; input.value = cat.id; input.checked = true;
    label.append(input, ` ${cat.label}`); fieldset.append(label);
  }
  function render() {
    const ids = [...fieldset.querySelectorAll('input:checked')].map(el => el.value);
    const metric = document.getElementById('metric');
    const rows = series(data,ids,metric.value);
    draw(rows, metric.selectedOptions[0].textContent);
    document.getElementById('selection').textContent = `${ids.length} categories selected · Latest selected count: ${fmt.format(rows.at(-1).value)}. Summary cards above always show all categories.`;
    const body = document.getElementById('history'); body.replaceChildren();
    rows.map((r,i) => ({...r,delta:i ? r.value-rows[i-1].value : null})).reverse().forEach(row => {
      const tr = document.createElement('tr');
      for (const text of [row.date,fmt.format(row.value),row.delta === null ? '—' : `${row.delta > 0 ? '+' : ''}${fmt.format(row.delta)}`]) {
        const td = document.createElement('td'); td.textContent = text; tr.append(td);
      }
      const td = document.createElement('td'), a = document.createElement('a');
      a.href = `https://github.com/cslib-community/cslib-frontier/commit/${row.commit}`;
      a.textContent = row.commit.slice(0,10); td.append(a); tr.append(td); body.append(tr);
    });
  }
  fieldset.addEventListener('change', render);
  document.getElementById('metric').addEventListener('change', render);
  render();
}
if (typeof document !== 'undefined') start().catch(error => {
  document.getElementById('status').textContent = `Unable to load history: ${error.message}. Try the CSV/JSON links or reload.`;
});
if (typeof module !== 'undefined') module.exports = {value,series};
