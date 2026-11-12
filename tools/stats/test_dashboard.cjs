// Copyright (c) 2026 Christian Reitwiessner. Apache-2.0. Authors: Christian Reitwiessner.
const assert = require('node:assert/strict');
const {value,series} = require('./dashboard.js');
assert.equal(value({code:2,comments:3,blanks:1},'total'),6);
const data = {snapshots:[{date:'2026-01-01',categories:{library:{code:2},tests:{code:4}}}]};
assert.equal(series(data,['library','tests'],'code')[0].value,6);
assert.equal(series(data,[],'code')[0].value,0);
assert.equal(series(data,['tests'],'code')[0].value,4);
console.log('Dashboard measure/category tests passed');
