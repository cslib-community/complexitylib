// Copyright (c) 2026 Erik Demaine. Released under the Apache 2.0 license.

//go:build linux

package main

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"io"
	"net"
	"net/http"
	"os"
	"path/filepath"
	"testing"
	"time"
)

func TestUnixSocketPublication(t *testing.T) {
	s := testStore(t)
	socket := filepath.Join(t.TempDir(), "http.sock")
	listener, err := net.Listen("unix", socket)
	if err != nil {
		t.Fatal(err)
	}
	server := &http.Server{Handler: s.handler()}
	go server.Serve(listener)
	t.Cleanup(func() { server.Close() })
	transport := &http.Transport{DialContext: func(ctx context.Context, _, _ string) (net.Conn, error) {
		return (&net.Dialer{}).DialContext(ctx, "unix", socket)
	}}
	t.Cleanup(transport.CloseIdleConnections)
	client := &http.Client{Transport: transport, Timeout: 5 * time.Second}
	data := testBundle(t, testRevision, []byte("via Unix socket"), nil)
	r, _ := http.NewRequest("PUT", "http://local/publish/"+testRevision, bytes.NewReader(data))
	r.Header.Set("Content-Type", "application/x-tar")
	resp, err := client.Do(r)
	if err != nil {
		t.Fatal(err)
	}
	defer resp.Body.Close()
	io.Copy(io.Discard, resp.Body)
	if resp.StatusCode != 201 {
		t.Fatal(resp.StatusCode)
	}
	m := inventory{Revision: testRevision, Toolchain: testToolchain}
	if _, err := s.read("public/"+m.mapping(), maxMapping); err != nil {
		t.Fatal(err)
	}
}

func TestDotToolchainsCannotEscapeNamespace(t *testing.T) {
	for _, tc := range []string{".", ".."} {
		s := testStore(t)
		data := testBundle(t, testRevision, []byte("data"), func(m *inventory, entries *[]testEntry) {
			old := m.mapping()
			digest := m.Files[old]
			delete(m.Files, old)
			m.Toolchain = tc
			m.Files[m.mapping()] = digest
			(*entries)[1].name = m.mapping()
		})
		if testPut(s, testRevision, data).Code != 400 {
			t.Fatal("accepted toolchain", tc)
		}
		objects, err := s.objects()
		if err != nil || len(objects) != 0 {
			t.Fatalf("polluted store: %v %v", objects, err)
		}
	}
}

func TestCapacityLeavesGCWithinItsSupportedBound(t *testing.T) {
	objects := map[string]time.Time{}
	directories := map[string]bool{"a0": true, "a0/cslib-community": true, "a0/" + scope: true}
	for n := range maxObjects - len(directories) - 1 {
		objects[fmt.Sprintf("%s%016x.art", artifactPrefix, n)] = time.Time{}
	}
	existing := map[string]string{artifactPrefix + "0000000000000000.art": "digest"}
	if err := checkAdmission(objects, directories, existing); err != nil {
		t.Fatal("identical retry rejected:", err)
	}
	newKey := map[string]string{mappingPrefix + "tc/" + testRevision + ".jsonl": "digest"}
	if !errors.Is(checkAdmission(objects, directories, newKey), errCapacity) {
		t.Fatal("publication could exceed GC bound")
	}
}

func TestGCReclaimsAbandonedStaging(t *testing.T) {
	s := testStore(t)
	name := "staging/11111111111111111111111111111111"
	if err := s.root.Mkdir(name, 0700); err != nil {
		t.Fatal(err)
	}
	if err := s.write(name+"/0", []byte("interrupted upload")); err != nil {
		t.Fatal(err)
	}
	old := time.Now().Add(-25 * time.Hour)
	if err := os.Chtimes(filepath.Join(s.root.Name(), name), old, old); err != nil {
		t.Fatal(err)
	}
	report, err := s.collect(48*time.Hour, true)
	if err != nil || len(report.DeleteStaging) != 1 {
		t.Fatalf("%+v %v", report, err)
	}
	if _, err := s.root.Stat(name); !os.IsNotExist(err) {
		t.Fatal("staging survived")
	}
}

// Optional real Lake fixture: mapping.jsonl plus archives/*.ltar, produced by
// `lake build ... -o` and `lake cache stage`, not synthesized by this test.
func TestRealLakeFixture(t *testing.T) {
	fixture := os.Getenv("CACHE_ORIGIN_LAKE_FIXTURE")
	if fixture == "" {
		t.Skip("set CACHE_ORIGIN_LAKE_FIXTURE to a tiny staged Lake build")
	}
	var packageData bytes.Buffer
	if err := pack(&packageData, filepath.Join(fixture, "mapping.jsonl"), filepath.Join(fixture, "archives"), testRevision, testToolchain); err != nil {
		t.Fatal(err)
	}
	s := testStore(t)
	if w := testPut(s, testRevision, packageData.Bytes()); w.Code != 201 {
		t.Fatal(w.Code)
	}
	if export := os.Getenv("CACHE_ORIGIN_FIXTURE_EXPORT"); export != "" {
		if err := os.Mkdir(export, 0700); err != nil {
			t.Fatal(err)
		}
		public, err := s.root.OpenRoot("public")
		if err != nil {
			t.Fatal(err)
		}
		defer public.Close()
		if err := os.CopyFS(export, public.FS()); err != nil {
			t.Fatal(err)
		}
	}
}
