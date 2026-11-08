// Copyright (c) 2026 Erik Demaine. Released under the Apache 2.0 license.

//go:build linux

package main

import (
	"bytes"
	"fmt"
	"io/fs"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"strings"
	"testing"
	"time"
)

const gcDay = 24 * time.Hour

func gcStore(t *testing.T) (*store, string, time.Time) {
	t.Helper()
	dir := t.TempDir()
	s, err := openStore(dir)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { s.root.Close() })
	now := time.Date(2026, 11, 5, 12, 0, 0, 0, time.UTC)
	s.now = func() time.Time { return now }
	// The permanent coordination file is not part of a GC dry-run's payload changes.
	unlock, err := s.lock()
	if err != nil {
		t.Fatal(err)
	}
	unlock()
	return s, dir, now
}

func gcArtifact(n int) string {
	return fmt.Sprintf("%s%016x.art", artifactPrefix, n)
}

func gcMapping(tc string, n int) string {
	return fmt.Sprintf("%s%s/%040x.jsonl", mappingPrefix, tc, n)
}

func gcMappingBytes(artifacts ...int) []byte {
	var b strings.Builder
	b.WriteString("\"2026-03-17\"\n")
	for i, n := range artifacts {
		fmt.Fprintf(&b, "[\"%016x\",\"%016x.ltar\"]\n", i+1, n)
	}
	return []byte(b.String())
}

func gcPut(t *testing.T, s *store, dir, key string, data []byte, modified time.Time) {
	t.Helper()
	name := "public/" + key
	if err := s.root.MkdirAll(filepath.ToSlash(filepath.Dir(name)), 0755); err != nil {
		t.Fatal(err)
	}
	if err := s.write(name, data); err != nil {
		t.Fatal(err)
	}
	if err := os.Chtimes(filepath.Join(dir, filepath.FromSlash(name)), modified, modified); err != nil {
		t.Fatal(err)
	}
}

func gcMustExist(t *testing.T, s *store, key string, want bool) {
	t.Helper()
	_, err := s.root.Stat("public/" + key)
	if want && err != nil {
		t.Fatalf("wanted %s to exist: %v", key, err)
	}
	if !want && !os.IsNotExist(err) {
		t.Fatalf("wanted %s absent, got %v", key, err)
	}
}

type gcFileSnapshot struct {
	Contents string
	Mode     fs.FileMode
	Modified time.Time
}

func gcSnapshot(t *testing.T, dir string) map[string]gcFileSnapshot {
	t.Helper()
	out := map[string]gcFileSnapshot{}
	err := filepath.WalkDir(dir, func(name string, entry fs.DirEntry, err error) error {
		if err != nil || entry.IsDir() {
			return err
		}
		info, err := entry.Info()
		if err != nil {
			return err
		}
		data, err := os.ReadFile(name)
		if err != nil {
			return err
		}
		rel, err := filepath.Rel(dir, name)
		out[rel] = gcFileSnapshot{string(data), info.Mode(), info.ModTime()}
		return err
	})
	if err != nil {
		t.Fatal(err)
	}
	return out
}

func TestGCExpiresSupersededMappingsAndKeepsLatestAcrossIdlePeriods(t *testing.T) {
	s, dir, now := gcStore(t)
	for _, n := range []int{1, 2, 3, 4} {
		gcPut(t, s, dir, gcArtifact(n), []byte{byte(n)}, now.Add(-400*gcDay))
	}
	old := gcMapping("tc-one", 1)
	boundary := gcMapping("tc-one", 2)
	recent := gcMapping("tc-two", 3)
	finalOldToolchain := gcMapping("tc-three", 4)
	gcPut(t, s, dir, old, gcMappingBytes(1), now.Add(-3*gcDay))
	gcPut(t, s, dir, boundary, gcMappingBytes(2), now.Add(-2*gcDay))
	gcPut(t, s, dir, recent, gcMappingBytes(3), now.Add(-2*gcDay+time.Hour))
	gcPut(t, s, dir, finalOldToolchain, gcMappingBytes(4), now.Add(-300*gcDay))
	report, err := s.collect(2*gcDay, true)
	if err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(report.ExpiredMappings, []string{old, boundary, finalOldToolchain}) ||
		!reflect.DeepEqual(report.DeleteArtifacts, []string{gcArtifact(1), gcArtifact(2), gcArtifact(4)}) {
		t.Fatalf("expired mappings and their unique artifacts must disappear together: %+v", report)
	}
	for _, key := range append(report.ExpiredMappings, report.DeleteArtifacts...) {
		gcMustExist(t, s, key, false)
	}
	gcMustExist(t, s, recent, true)
	gcMustExist(t, s, gcArtifact(3), true)
	// The latest publication stays useful even if the repository is quiet.
	s.now = func() time.Time { return now.Add(365 * gcDay) }
	if _, err := s.collect(2*gcDay, true); err != nil {
		t.Fatal(err)
	}
	gcMustExist(t, s, recent, true)
	gcMustExist(t, s, gcArtifact(3), true)
}

func TestGCRetiringToolchainPreservesSharedArtifacts(t *testing.T) {
	s, dir, now := gcStore(t)
	gcPut(t, s, dir, gcArtifact(1), []byte("shared"), now.Add(-365*gcDay))
	old := gcMapping("old-toolchain", 1)
	current := gcMapping("active-toolchain", 2)
	gcPut(t, s, dir, old, gcMappingBytes(1), now.Add(-3*gcDay))
	gcPut(t, s, dir, current, gcMappingBytes(1), now)
	report, err := s.collect(2*gcDay, true)
	if err != nil || !reflect.DeepEqual(report.ExpiredMappings, []string{old}) || len(report.DeleteArtifacts) != 0 {
		t.Fatalf("retirement affected a live shared artifact: %+v %v", report, err)
	}
	gcMustExist(t, s, gcArtifact(1), true)
	gcMustExist(t, s, current, true)
}

func TestGCLatestTimestampTieIsDeterministicAcrossToolchains(t *testing.T) {
	s, dir, now := gcStore(t)
	first, latest := gcMapping("tc-a", 1), gcMapping("tc-b", 2)
	old := now.Add(-3 * gcDay)
	for _, n := range []int{1, 2} {
		gcPut(t, s, dir, gcArtifact(n), []byte{byte(n)}, old)
	}
	gcPut(t, s, dir, first, gcMappingBytes(1), old)
	gcPut(t, s, dir, latest, gcMappingBytes(2), old)
	report, err := s.collect(2*gcDay, true)
	if err != nil || !reflect.DeepEqual(report.ExpiredMappings, []string{first}) {
		t.Fatalf("unexpected latest selection: %+v %v", report, err)
	}
	gcMustExist(t, s, latest, true)
	gcMustExist(t, s, gcArtifact(2), true)
	gcMustExist(t, s, gcArtifact(1), false)
}

func TestGCDeletesUnreferencedArtifactsImmediatelyRegardlessOfAge(t *testing.T) {
	s, dir, now := gcStore(t)
	gcPut(t, s, dir, gcArtifact(1), []byte("old orphan"), now.Add(-365*gcDay))
	gcPut(t, s, dir, gcArtifact(2), []byte("new orphan"), now)
	report, err := s.collect(2*gcDay, true)
	if err != nil || !reflect.DeepEqual(report.DeleteArtifacts, []string{gcArtifact(1), gcArtifact(2)}) {
		t.Fatalf("all orphans must disappear on the first pass: %+v %v", report, err)
	}
	gcMustExist(t, s, gcArtifact(1), false)
	gcMustExist(t, s, gcArtifact(2), false)
	// The collector has no persistent reference counts or deletion clocks.
	if _, err := s.root.Stat("state/gc.json"); !os.IsNotExist(err) {
		t.Fatalf("unexpected GC state file: %v", err)
	}
	report, err = s.collect(2*gcDay, true)
	if err != nil || len(report.DeleteArtifacts) != 0 || len(report.ExpiredMappings) != 0 {
		t.Fatalf("empty collection should be repeatable: %+v %v", report, err)
	}
}

func TestGCDryRunReportsSameDeletionsWithoutChangingFiles(t *testing.T) {
	s, dir, now := gcStore(t)
	gcPut(t, s, dir, gcArtifact(1), []byte("one"), now.Add(-365*gcDay))
	gcPut(t, s, dir, gcArtifact(2), []byte("two"), now)
	gcPut(t, s, dir, gcMapping("tc", 1), gcMappingBytes(1), now.Add(-3*gcDay))
	gcPut(t, s, dir, gcMapping("tc", 2), gcMappingBytes(2), now)
	before := gcSnapshot(t, dir)

	dry, err := s.collect(2*gcDay, false)
	if err != nil || len(dry.ExpiredMappings) != 1 || !reflect.DeepEqual(dry.DeleteArtifacts, []string{gcArtifact(1)}) || dry.Applied {
		t.Fatalf("unexpected dry-run report: %+v, %v", dry, err)
	}
	if after := gcSnapshot(t, dir); !reflect.DeepEqual(before, after) {
		t.Fatal("dry run modified files")
	}
	applied, err := s.collect(2*gcDay, true)
	if err != nil || !applied.Applied {
		t.Fatalf("apply failed: %+v %v", applied, err)
	}
	dry.Applied = true
	if !reflect.DeepEqual(dry, applied) {
		t.Fatalf("apply differs from dry run: %+v versus %+v", applied, dry)
	}
	gcMustExist(t, s, gcArtifact(1), false)
	gcMustExist(t, s, gcArtifact(2), true)
}

func TestGCFailsClosedBeforeDeletingOnBadMappings(t *testing.T) {
	for name, bad := range map[string][]byte{
		"invalid-json":      []byte("\"2026-03-17\"\nnot json\n"),
		"unknown-version":   []byte("\"2099-01-01\"\n[\"0000000000000001\",\"0000000000000001.ltar\"]\n"),
		"missing-reference": gcMappingBytes(999),
	} {
		t.Run(name, func(t *testing.T) {
			s, dir, now := gcStore(t)
			gcPut(t, s, dir, gcArtifact(1), []byte("live"), now)
			gcPut(t, s, dir, gcArtifact(2), []byte("collectible"), now)
			// Even an expired malformed mapping must be read and stop the pass.
			gcPut(t, s, dir, gcMapping("tc", 1), bad, now.Add(-3*gcDay))
			gcPut(t, s, dir, gcMapping("tc", 2), gcMappingBytes(1), now)
			before := gcSnapshot(t, dir)
			if _, err := s.collect(2*gcDay, true); err == nil {
				t.Fatal("bad mapping did not stop collection")
			}
			if after := gcSnapshot(t, dir); !reflect.DeepEqual(before, after) {
				t.Fatal("failed collection changed files")
			}
		})
	}
}

func TestGCPublicationRestoresCollectedArtifactAndProtectsIt(t *testing.T) {
	s, dir, now := gcStore(t)
	artifact := gcArtifact(1)
	gcPut(t, s, dir, artifact, []byte("artifact"), now.Add(-365*gcDay))
	if _, err := s.collect(2*gcDay, true); err != nil {
		t.Fatal(err)
	}
	gcMustExist(t, s, artifact, false)
	fixture := t.TempDir()
	mapping := filepath.Join(fixture, "mapping.jsonl")
	if err := os.WriteFile(mapping, gcMappingBytes(1), 0600); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(fixture, "0000000000000001.ltar"), []byte("artifact"), 0600); err != nil {
		t.Fatal(err)
	}
	var body bytes.Buffer
	revision := fmt.Sprintf("%040x", 1)
	if err := pack(&body, mapping, fixture, revision, "tc"); err != nil {
		t.Fatal(err)
	}
	if err := s.publish(&body, revision); err != nil {
		t.Fatal(err)
	}
	// Publication installs files using the filesystem's real clock.
	s.now = time.Now
	if _, err := s.collect(2*gcDay, true); err != nil {
		t.Fatal(err)
	}
	gcMustExist(t, s, artifact, true)
	gcMustExist(t, s, gcMapping("tc", 1), true)
	if err := s.root.Remove("public/" + gcMapping("tc", 1)); err != nil {
		t.Fatal(err)
	}
	if _, err := s.collect(2*gcDay, true); err != nil {
		t.Fatal(err)
	}
	gcMustExist(t, s, artifact, false)
}

func TestGCStoreLockExcludesPublicationAndOtherProcesses(t *testing.T) {
	if dir := os.Getenv("CACHE_ORIGIN_GC_LOCK_CHILD"); dir != "" {
		s, err := openStore(dir)
		if err != nil {
			t.Fatal(err)
		}
		defer s.root.Close()
		if _, err := s.collect(2*gcDay, true); err == nil || !strings.Contains(err.Error(), "store busy") {
			t.Fatalf("child GC should encounter held lock: %v", err)
		}
		if err := s.publish(strings.NewReader(""), strings.Repeat("1", 40)); err == nil || !strings.Contains(err.Error(), "store busy") {
			t.Fatalf("child publication should encounter held lock before reading: %v", err)
		}
		return
	}
	s, dir, _ := gcStore(t)
	unlock, err := s.lock()
	if err != nil {
		t.Fatal(err)
	}
	defer unlock()
	cmd := exec.Command(os.Args[0], "-test.run=^TestGCStoreLockExcludesPublicationAndOtherProcesses$")
	cmd.Env = append(os.Environ(), "CACHE_ORIGIN_GC_LOCK_CHILD="+dir)
	if output, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("interprocess exclusion failed: %v\n%s", err, output)
	}
}

func TestGCRejectsFutureMappingBeforeDeleting(t *testing.T) {
	s, dir, now := gcStore(t)
	gcPut(t, s, dir, gcArtifact(1), []byte("live"), now)
	gcPut(t, s, dir, gcArtifact(2), []byte("orphan"), now)
	gcPut(t, s, dir, gcMapping("tc", 1), gcMappingBytes(1), now.Add(time.Hour))
	before := gcSnapshot(t, dir)
	if _, err := s.collect(2*gcDay, true); err == nil {
		t.Fatal("future mapping timestamp was accepted")
	}
	if !reflect.DeepEqual(before, gcSnapshot(t, dir)) {
		t.Fatal("future mapping caused writes or deletion")
	}
}
