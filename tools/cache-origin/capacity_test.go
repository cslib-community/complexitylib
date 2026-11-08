// Copyright (c) 2026 Erik Demaine. Released under the Apache 2.0 license.

//go:build linux

package main

import (
	"archive/tar"
	"bytes"
	"encoding/json"
	"fmt"
	"net/http/httptest"
	"runtime"
	"strings"
	"testing"
)

func capacityInventory(count int) inventory {
	m := inventory{1, testRevision, strings.Repeat("t", 160), make(map[string]string, count)}
	digest := strings.Repeat("0", 64)
	m.Files[m.mapping()] = digest
	for n := 0; n < count-1; n++ {
		m.Files[fmt.Sprintf("%s%016x.art", artifactPrefix, n)] = digest
	}
	return m
}

func capacityMapping(rows int) []byte {
	var data bytes.Buffer
	data.Grow(13 + rows*45)
	data.WriteString("\"2026-03-17\"\n")
	for n := 0; n < rows; n++ {
		fmt.Fprintf(&data, "[\"%016x\",\"%016x.ltar\"]\n", n, n)
	}
	return data.Bytes()
}

func TestInventoryCapacityUsesStoreBudget(t *testing.T) {
	if err := capacityInventory(10001).validate(); err != nil {
		t.Fatal("publication beyond the old 10,000-entry ceiling rejected:", err)
	}
	m := capacityInventory(maxObjects)
	if err := m.validate(); err != nil {
		t.Fatal("full store entry budget rejected:", err)
	}
	m.Files[fmt.Sprintf("%s%016x.art", artifactPrefix, maxObjects)] = strings.Repeat("0", 64)
	if err := m.validate(); err == nil {
		t.Fatal("accepted inventory exceeding store entry budget")
	}
}

func TestMappingCapacityUsesStoreBudget(t *testing.T) {
	data := capacityMapping(maxObjects)
	refs, err := references(data)
	if err != nil || len(refs) != maxObjects {
		t.Fatalf("full row budget rejected: refs=%d err=%v", len(refs), err)
	}
	data = append(data, fmt.Appendf(nil, "[\"%016x\",\"%016x.ltar\"]\n", maxObjects, maxObjects)...)
	if _, err := references(data); err == nil {
		t.Fatal("accepted mapping exceeding row budget")
	}
}

func TestCapacityParsersAtStoreBudget(t *testing.T) {
	metadata, err := json.Marshal(capacityInventory(maxObjects))
	if err != nil {
		t.Fatal(err)
	}
	// Match Python json.dumps' default separator spacing. Keys/values cannot
	// contain colons or commas, so this preserves their contents exactly.
	metadata = bytes.ReplaceAll(metadata, []byte(":"), []byte(": "))
	metadata = bytes.ReplaceAll(metadata, []byte(","), []byte(", "))
	if len(metadata) > maxMetadata {
		t.Fatalf("full supported inventory needs %d bytes, limit is %d", len(metadata), maxMetadata)
	}
	mapping := capacityMapping(maxObjects - 1)
	if len(mapping) > maxMapping {
		t.Fatalf("full supported mapping needs %d bytes, limit is %d", len(mapping), maxMapping)
	}
	// Permit a standalone run of this test to measure the real parsers while
	// inventory and references coexist, as they do during publication.
	runtime.GC()
	var decoded inventory
	if err := decodeJSON(metadata, &decoded); err != nil {
		t.Fatal(err)
	}
	if err := decoded.validate(); err != nil {
		t.Fatal(err)
	}
	refs, err := references(mapping)
	if err != nil || len(refs)+1 != len(decoded.Files) {
		t.Fatalf("mapping/inventory mismatch: refs=%d files=%d err=%v", len(refs), len(decoded.Files), err)
	}
	var memory runtime.MemStats
	runtime.ReadMemStats(&memory)
	t.Logf("entries=%d metadata=%d mapping=%d heap_alloc=%d heap_sys=%d", len(decoded.Files), len(metadata), len(mapping), memory.HeapAlloc, memory.HeapSys)
	runtime.KeepAlive(decoded)
}

func TestInventoryMetadataByteBoundary(t *testing.T) {
	s := testStore(t)
	metadata, err := json.Marshal(capacityInventory(2))
	if err != nil {
		t.Fatal(err)
	}
	metadata = append(metadata, bytes.Repeat([]byte(" "), maxMetadata-len(metadata))...)
	var body bytes.Buffer
	w := tar.NewWriter(&body)
	if err := w.WriteHeader(&tar.Header{Name: "publication.json", Size: int64(len(metadata)), Mode: 0600, Typeflag: tar.TypeReg, Format: tar.FormatUSTAR}); err != nil {
		t.Fatal(err)
	}
	if _, err := w.Write(metadata); err != nil {
		t.Fatal(err)
	}
	if err := w.Close(); err != nil {
		t.Fatal(err)
	}
	// A valid inventory exactly at the byte limit reaches the later package
	// completeness check; the package intentionally contains no payload files.
	if err := s.publish(&body, testRevision); err == nil || err.Error() != "incomplete package" {
		t.Fatalf("metadata at limit was not accepted: %v", err)
	}
	body.Reset()
	w = tar.NewWriter(&body)
	if err := w.WriteHeader(&tar.Header{Name: "publication.json", Size: maxMetadata + 1, Mode: 0600, Typeflag: tar.TypeReg, Format: tar.FormatUSTAR}); err != nil {
		t.Fatal(err)
	}
	if err := s.publish(&body, testRevision); err == nil || err.Error() != "inventory must be the first regular USTAR entry" {
		t.Fatalf("oversized metadata was not rejected before reading its body: %v", err)
	}
}

func TestPackageCapacityUses64BitHTTPBoundary(t *testing.T) {
	s := testStore(t)
	for _, tc := range []struct {
		length int64
		status int
	}{
		{1<<30 + 1, 400}, // Past the old byte cap, validation is reached.
		{maxPackage, 400},
		{maxPackage + 1, 413},
	} {
		r := httptest.NewRequest("PUT", "/publish/"+testRevision, nil)
		r.Header.Set("Content-Type", "application/x-tar")
		r.ContentLength = tc.length
		w := httptest.NewRecorder()
		s.handler().ServeHTTP(w, r)
		// Empty bodies are not publications; this checks whether the HTTP
		// size guard admits the declared length to package validation.
		if w.Code != tc.status {
			t.Fatalf("length %d: got %d, want %d", tc.length, w.Code, tc.status)
		}
	}
}
