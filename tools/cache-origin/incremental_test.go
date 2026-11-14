// Copyright (c) 2026 Samuel Schlesinger. Released under the Apache 2.0 license.

//go:build linux

package main

import (
	"bytes"
	"encoding/json"
	"net/http/httptest"
	"strings"
	"testing"
	"time"
)

func incrementalRequest(s *store, revision, mediaType string, body []byte) *httptest.ResponseRecorder {
	r := httptest.NewRequest("PUT", "/publish/"+revision, bytes.NewReader(body))
	r.Header.Set("Content-Type", mediaType)
	w := httptest.NewRecorder()
	s.handler().ServeHTTP(w, r)
	return w
}

func mappingOnly(m *inventory, entries *[]testEntry) { *entries = (*entries)[1:] }

func TestIncrementalProbeAndCommit(t *testing.T) {
	s := testStore(t)
	full := testBundle(t, testRevision, []byte("archive"), nil)
	partial := testBundle(t, testRevision, []byte("archive"), mappingOnly)
	probe := incrementalRequest(s, testRevision, probeMediaType, partial)
	var response struct {
		Version  int
		Revision string
		Missing  []string
	}
	if probe.Code != 200 || json.Unmarshal(probe.Body.Bytes(), &response) != nil ||
		response.Version != 1 || response.Revision != testRevision || len(response.Missing) != 1 || response.Missing[0] != testArtifact {
		t.Fatal(probe.Code, probe.Body.String())
	}
	gcMustExist(t, s, testArtifact, false)
	gcMustExist(t, s, (inventory{Revision: testRevision, Toolchain: testToolchain}).mapping(), false)
	if w := incrementalRequest(s, testRevision, deltaMediaType, partial); w.Code != 412 {
		t.Fatal(w.Code)
	}
	if w := incrementalRequest(s, testRevision, deltaMediaType, full); w.Code != 201 {
		t.Fatal(w.Code, w.Body)
	}
	probe = incrementalRequest(s, testRevision, probeMediaType, partial)
	if probe.Code != 200 || json.Unmarshal(probe.Body.Bytes(), &response) != nil || len(response.Missing) != 0 {
		t.Fatal(probe.Code, probe.Body)
	}
	// A different revision can reuse the retained bytes; its mapping remains required.
	revision := strings.Repeat("2", 40)
	partial = testBundle(t, revision, []byte("archive"), mappingOnly)
	if w := incrementalRequest(s, revision, deltaMediaType, partial); w.Code != 201 {
		t.Fatal(w.Code, w.Body)
	}
	// Legacy full publications remain strict, even on the new server.
	if w := testPut(s, revision, partial); w.Code != 400 {
		t.Fatal(w.Code)
	}
}

func TestIncrementalRetainedConflictsAndMalformedPackages(t *testing.T) {
	for _, mediaType := range []string{probeMediaType, deltaMediaType} {
		t.Run(mediaType, func(t *testing.T) {
			s := testStore(t)
			if w := testPut(s, testRevision, testBundle(t, testRevision, []byte("original"), nil)); w.Code != 201 {
				t.Fatal(w.Code)
			}
			revision := strings.Repeat("2", 40)
			conflict := testBundle(t, revision, []byte("replacement"), mappingOnly)
			if w := incrementalRequest(s, revision, mediaType, conflict); w.Code != 409 {
				t.Fatal(w.Code)
			}
			gcMustExist(t, s, (inventory{Revision: revision, Toolchain: testToolchain}).mapping(), false)
			for _, change := range []func(*inventory, *[]testEntry){
				func(m *inventory, e *[]testEntry) { *e = nil },
				func(m *inventory, e *[]testEntry) { mappingOnly(m, e); delete(m.Files, testArtifact) },
				func(m *inventory, e *[]testEntry) {
					mappingOnly(m, e)
					m.Files[artifactPrefix+"0000000000000001.art"] = strings.Repeat("0", 64)
				},
				func(m *inventory, e *[]testEntry) { mappingOnly(m, e); (*e)[0].data = []byte("corrupt mapping") },
			} {
				body := testBundle(t, revision, []byte("original"), change)
				if w := incrementalRequest(s, revision, mediaType, body); w.Code != 400 {
					t.Fatal(w.Code, w.Body)
				}
			}
		})
	}
	s := testStore(t)
	if w := incrementalRequest(s, testRevision, probeMediaType, testBundle(t, testRevision, []byte("unexpected payload"), nil)); w.Code != 400 {
		t.Fatal(w.Code)
	}
}

func TestIncrementalGCRaceAndConcurrentPublisher(t *testing.T) {
	s := testStore(t)
	// Orphan left by an interrupted full publication. Probe sees it, GC removes it.
	gcPut(t, s, s.root.Name(), testArtifact, []byte("archive"), time.Now())
	partial := testBundle(t, testRevision, []byte("archive"), mappingOnly)
	if w := incrementalRequest(s, testRevision, probeMediaType, partial); w.Code != 200 || !strings.Contains(w.Body.String(), `"missing":[]`) {
		t.Fatal(w.Code, w.Body)
	}
	if _, err := s.collect(48*time.Hour, true); err != nil {
		t.Fatal(err)
	}
	if w := incrementalRequest(s, testRevision, deltaMediaType, partial); w.Code != 412 {
		t.Fatal(w.Code)
	}
	gcMustExist(t, s, (inventory{Revision: testRevision, Toolchain: testToolchain}).mapping(), false)
	// A writer wins after the probe. Identical bytes work; conflicts never do.
	full := testBundle(t, testRevision, []byte("archive"), nil)
	if w := testPut(s, testRevision, full); w.Code != 201 {
		t.Fatal(w.Code)
	}
	if w := incrementalRequest(s, testRevision, deltaMediaType, partial); w.Code != 201 {
		t.Fatal(w.Code)
	}
	changed := testBundle(t, strings.Repeat("2", 40), []byte("other"), mappingOnly)
	if w := incrementalRequest(s, strings.Repeat("2", 40), deltaMediaType, changed); w.Code != 409 {
		t.Fatal(w.Code)
	}
	// Probe and delta use the same nonblocking lock as full publication and GC.
	unlock, err := s.lock()
	if err != nil {
		t.Fatal(err)
	}
	defer unlock()
	for _, mediaType := range []string{probeMediaType, deltaMediaType} {
		if w := incrementalRequest(s, testRevision, mediaType, partial); w.Code != 503 {
			t.Fatal(w.Code)
		}
	}
}

func TestProbeHTTPBodyBound(t *testing.T) {
	s := testStore(t)
	r := httptest.NewRequest("PUT", "/publish/"+testRevision, strings.NewReader(""))
	r.Header.Set("Content-Type", probeMediaType)
	r.ContentLength = maxMetadata + maxMapping + 16385
	w := httptest.NewRecorder()
	s.handler().ServeHTTP(w, r)
	if w.Code != 413 {
		t.Fatal(w.Code)
	}
	objects, err := s.objects()
	if err != nil || len(objects) != 0 {
		t.Fatal(objects, err)
	}
}
