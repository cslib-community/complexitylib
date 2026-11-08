// Copyright (c) 2026 Erik Demaine. Released under the Apache 2.0 license.

//go:build linux

package main

import (
	"archive/tar"
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"strings"
	"sync"
	"testing"
	"time"
)

const testRevision = "1111111111111111111111111111111111111111"
const testToolchain = "leanprover--lean4---v4.36.0-rc2"
const testArtifact = artifactPrefix + "0123456789abcdef.art"

func testStore(t *testing.T) *store {
	t.Helper()
	s, err := openStore(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { s.root.Close() })
	return s
}

type testEntry struct {
	name string
	data []byte
	kind byte
	size int64
}

func testBundle(t *testing.T, revision string, payload []byte, change func(*inventory, *[]testEntry)) []byte {
	t.Helper()
	mapping := []byte("\"2026-03-17\"\n[\"fedcba9876543210\",\"0123456789abcdef.ltar\"]\n")
	m := inventory{1, revision, testToolchain, map[string]string{}}
	entries := []testEntry{{testArtifact, payload, tar.TypeReg, 0}, {m.mapping(), mapping, tar.TypeReg, 0}}
	for _, e := range entries {
		sum := sha256.Sum256(e.data)
		m.Files[e.name] = hex.EncodeToString(sum[:])
	}
	if change != nil {
		change(&m, &entries)
	}
	b, err := json.Marshal(m)
	if err != nil {
		t.Fatal(err)
	}
	entries = append([]testEntry{{"publication.json", b, tar.TypeReg, 0}}, entries...)
	var out bytes.Buffer
	w := tar.NewWriter(&out)
	for _, e := range entries {
		size := int64(len(e.data))
		if e.size != 0 {
			size = e.size
		}
		h := &tar.Header{Name: e.name, Size: size, Mode: 0600, Typeflag: e.kind, Format: tar.FormatUSTAR}
		if e.kind == tar.TypeSymlink {
			h.Size = 0
			h.Linkname = "/etc/passwd"
		}
		if err := w.WriteHeader(h); err != nil {
			t.Fatal(err)
		}
		if e.kind == tar.TypeReg {
			if _, err := w.Write(e.data); err != nil {
				t.Fatal(err)
			}
		}
		if e.size > int64(len(e.data)) {
			return out.Bytes()
		} // Deliberately truncated.
	}
	if err := w.Close(); err != nil {
		t.Fatal(err)
	}
	return out.Bytes()
}

func testPut(s *store, revision string, data []byte) *httptest.ResponseRecorder {
	r := httptest.NewRequest("PUT", "/publish/"+revision, bytes.NewReader(data))
	r.Header.Set("Content-Type", "application/x-tar")
	w := httptest.NewRecorder()
	s.handler().ServeHTTP(w, r)
	return w
}

func TestPublishAndIdempotentRetry(t *testing.T) {
	s := testStore(t)
	data := testBundle(t, testRevision, []byte("opaque Lake archive"), nil)
	for range 2 {
		if w := testPut(s, testRevision, data); w.Code != 201 {
			t.Fatalf("%d: %s", w.Code, w.Body)
		}
	}
	b, err := s.read("public/"+testArtifact, maxArtifact)
	if err != nil || string(b) != "opaque Lake archive" {
		t.Fatalf("%s: %v", b, err)
	}
	m := inventory{Revision: testRevision, Toolchain: testToolchain}
	if _, err := s.read("public/"+m.mapping(), maxMapping); err != nil {
		t.Fatal("success response preceded mapping:", err)
	}
	if entries, _ := os.ReadDir(filepath.Join(s.root.Name(), "staging")); len(entries) != 0 {
		t.Fatal("staging not removed")
	}
}

func TestConflictNeverPublishesMapping(t *testing.T) {
	s := testStore(t)
	if w := testPut(s, testRevision, testBundle(t, testRevision, []byte("original"), nil)); w.Code != 201 {
		t.Fatal(w.Code)
	}
	revision := strings.Repeat("2", 40)
	if w := testPut(s, revision, testBundle(t, revision, []byte("replacement"), nil)); w.Code != 409 {
		t.Fatal(w.Code)
	}
	b, _ := s.read("public/"+testArtifact, maxArtifact)
	if string(b) != "original" {
		t.Fatal("replaced published artifact")
	}
	m := inventory{Revision: revision, Toolchain: testToolchain}
	if _, err := s.root.Stat("public/" + m.mapping()); !os.IsNotExist(err) {
		t.Fatal("conflicting mapping became visible")
	}
}

func TestRetryDoesNotRefreshMappingInstallationTime(t *testing.T) {
	s := testStore(t)
	body := testBundle(t, testRevision, []byte("artifact"), nil)
	if w := testPut(s, testRevision, body); w.Code != 201 {
		t.Fatal(w.Code)
	}
	key := (inventory{Revision: testRevision, Toolchain: testToolchain}).mapping()
	name := filepath.Join(s.root.Name(), "public", filepath.FromSlash(key))
	old := time.Now().Add(-72 * time.Hour).Truncate(time.Second)
	if err := os.Chtimes(name, old, old); err != nil {
		t.Fatal(err)
	}
	if w := testPut(s, testRevision, body); w.Code != 201 {
		t.Fatal(w.Code)
	}
	info, err := os.Stat(name)
	if err != nil || !info.ModTime().Equal(old) {
		t.Fatalf("identical retry refreshed mapping age: %v %v", info, err)
	}
}

func TestRejectsInvalidPackagesBeforePublication(t *testing.T) {
	cases := map[string]func(*inventory, *[]testEntry){
		"bad digest":     func(m *inventory, _ *[]testEntry) { m.Files[testArtifact] = strings.Repeat("0", 64) },
		"duplicate file": func(_ *inventory, e *[]testEntry) { *e = append(*e, (*e)[0]) },
		"symlink":        func(_ *inventory, e *[]testEntry) { (*e)[0].kind = tar.TypeSymlink },
		"traversal": func(m *inventory, e *[]testEntry) {
			m.Files["../escape"] = m.Files[testArtifact]
			(*e)[0].name = "../escape"
		},
		"missing file":   func(_ *inventory, e *[]testEntry) { *e = (*e)[1:] },
		"oversized file": func(_ *inventory, e *[]testEntry) { (*e)[0].size = maxArtifact + 1 },
		"unknown mapping": func(m *inventory, e *[]testEntry) {
			(*e)[1].data = []byte("\"future\"\n")
			sum := sha256.Sum256((*e)[1].data)
			m.Files[m.mapping()] = hex.EncodeToString(sum[:])
		},
		"missing reference": func(m *inventory, e *[]testEntry) {
			(*e)[1].data = bytes.ReplaceAll((*e)[1].data, []byte("0123456789abcdef"), []byte("aaaaaaaaaaaaaaaa"))
			sum := sha256.Sum256((*e)[1].data)
			m.Files[m.mapping()] = hex.EncodeToString(sum[:])
		},
	}
	for name, change := range cases {
		t.Run(name, func(t *testing.T) {
			s := testStore(t)
			if w := testPut(s, testRevision, testBundle(t, testRevision, []byte("data"), change)); w.Code != 400 {
				t.Fatal(w.Code)
			}
			objects, err := s.objects()
			if err != nil || len(objects) != 0 {
				t.Fatalf("invalid upload exposed objects: %v %v", objects, err)
			}
		})
	}
	for _, data := range [][]byte{nil, []byte("not tar"), testBundle(t, testRevision, []byte("data"), nil)[:1000], append(testBundle(t, testRevision, []byte("data"), nil), 'x')} {
		s := testStore(t)
		if testPut(s, testRevision, data).Code != 400 {
			t.Fatal("accepted truncated/trailing data")
		}
	}
}

func TestHTTPBoundaryAndBusy(t *testing.T) {
	s := testStore(t)
	for _, tc := range []struct {
		method, path, content string
		length                int64
		status                int
	}{
		{"DELETE", "/publish/" + testRevision, "application/x-tar", 0, 405},
		{"PUT", "/publish/" + testRevision, "text/plain", 0, 415},
		{"PUT", "/publish/not-a-sha", "application/x-tar", 0, 404},
		{"PUT", "/publish/" + testRevision + "?delete=1", "application/x-tar", 0, 404},
		{"PUT", "/publish/" + testRevision, "application/x-tar", maxPackage + 1, 413},
	} {
		r := httptest.NewRequest(tc.method, tc.path, nil)
		r.Header.Set("Content-Type", tc.content)
		r.ContentLength = tc.length
		w := httptest.NewRecorder()
		s.handler().ServeHTTP(w, r)
		if w.Code != tc.status {
			t.Fatalf("%s: %d", tc.path, w.Code)
		}
	}
	unlock, err := s.lock()
	if err != nil {
		t.Fatal(err)
	}
	defer unlock()
	w := testPut(s, testRevision, testBundle(t, testRevision, []byte("data"), nil))
	if w.Code != 503 || w.Header().Get("Retry-After") == "" {
		t.Fatalf("busy: %d", w.Code)
	}
}

func TestConcurrentConflictingUploads(t *testing.T) {
	s := testStore(t)
	server := httptest.NewServer(s.handler())
	defer server.Close()
	var wg sync.WaitGroup
	results := make(chan int, 8)
	for n := range 8 {
		data := testBundle(t, testRevision, []byte(fmt.Sprint(n)), nil)
		wg.Go(func() {
			r, _ := http.NewRequest("PUT", server.URL+"/publish/"+testRevision, bytes.NewReader(data))
			r.Header.Set("Content-Type", "application/x-tar")
			resp, err := http.DefaultClient.Do(r)
			if err != nil {
				results <- 0
				return
			}
			io.Copy(io.Discard, resp.Body)
			resp.Body.Close()
			results <- resp.StatusCode
		})
	}
	wg.Wait()
	close(results)
	winners := 0
	for status := range results {
		if status == 201 {
			winners++
		} else if status != 409 && status != 503 {
			t.Fatal(status)
		}
	}
	if winners != 1 {
		t.Fatalf("got %d winners", winners)
	}
}

func TestPackAndRoundTrip(t *testing.T) {
	dir := t.TempDir()
	art := []byte("compiled output placeholder")
	if err := os.WriteFile(filepath.Join(dir, "0123456789abcdef.ltar"), art, 0600); err != nil {
		t.Fatal(err)
	}
	mapping := filepath.Join(dir, "mapping.jsonl")
	if err := os.WriteFile(mapping, []byte("\"2026-03-17\"\n[\"fedcba9876543210\",\"0123456789abcdef.ltar\"]\n"), 0600); err != nil {
		t.Fatal(err)
	}
	var data bytes.Buffer
	if err := pack(&data, mapping, dir, testRevision, testToolchain); err != nil {
		t.Fatal(err)
	}
	s := testStore(t)
	if w := testPut(s, testRevision, data.Bytes()); w.Code != 201 {
		t.Fatalf("%d: %s", w.Code, w.Body)
	}
}

func FuzzMapping(f *testing.F) {
	f.Add([]byte("\"2026-03-17\"\n[\"fedcba9876543210\",\"0123456789abcdef.ltar\"]\n"))
	f.Add([]byte("\"future\"\n"))
	f.Fuzz(func(t *testing.T, data []byte) {
		refs, err := references(data)
		if err == nil {
			for key := range refs {
				if !artifactKey.MatchString(key) {
					t.Fatal(key)
				}
			}
		}
	})
}
