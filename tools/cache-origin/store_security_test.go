// Copyright (c) 2026 Erik Demaine. Released under the Apache 2.0 license.

//go:build linux

package main

import (
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"syscall"
	"testing"
	"time"
)

func TestStoreRejectsUnsafeDirectoryPermissions(t *testing.T) {
	for _, tc := range []struct {
		name string
		mode os.FileMode
	}{
		{".", 0770}, {".", 0707}, {"public", 0775}, {"public", 0757},
		{"state", 0750}, {"state", 0701}, {"staging", 0710},
		{"public/" + mappingPrefix + "tc", 0775},
	} {
		t.Run(fmt.Sprintf("%s-%o", tc.name, tc.mode), func(t *testing.T) {
			dir := t.TempDir()
			s, err := openStore(dir)
			if err != nil {
				t.Fatal(err)
			}
			if strings.HasPrefix(tc.name, "public/") {
				if err := s.root.MkdirAll(tc.name, 0755); err != nil {
					t.Fatal(err)
				}
			}
			name := filepath.Join(dir, filepath.FromSlash(tc.name))
			if err := os.Chmod(name, tc.mode); err != nil {
				t.Fatal(err)
			}
			if w := testPut(s, testRevision, testBundle(t, testRevision, []byte("data"), nil)); w.Code == 201 {
				t.Fatal("unsafe directory accepted during publication")
			}
			if _, err := s.root.Stat("public/" + testArtifact); !os.IsNotExist(err) {
				t.Fatal("unsafe publication exposed an artifact", err)
			}
			s.root.Close()
			if reopened, err := openStore(dir); err == nil {
				reopened.root.Close()
				t.Fatal("unsafe directory accepted at startup")
			}
		})
	}
}

func TestStoreRejectsSymlinkRootAndNamespaceParents(t *testing.T) {
	dir := t.TempDir()
	alias := filepath.Join(t.TempDir(), "root")
	if err := os.Symlink(dir, alias); err != nil {
		t.Fatal(err)
	}
	if s, err := openStore(alias); err == nil {
		s.root.Close()
		t.Fatal("symlink root accepted")
	}
	s := testStore(t)
	outside := t.TempDir()
	if err := s.root.Symlink(outside, "public/a0"); err != nil {
		t.Fatal(err)
	}
	if w := testPut(s, testRevision, testBundle(t, testRevision, []byte("data"), nil)); w.Code == 201 {
		t.Fatal("published through symlink namespace")
	}
	if entries, err := os.ReadDir(outside); err != nil || len(entries) != 0 {
		t.Fatal("unsafe namespace publication escaped store", err)
	}
	if _, err := s.root.Stat("public/" + (inventory{Revision: testRevision, Toolchain: testToolchain}).mapping()); !os.IsNotExist(err) {
		t.Fatal("unsafe namespace publication exposed mapping", err)
	}
}

func TestStoreRejectsWritablePathAncestor(t *testing.T) {
	parent := t.TempDir()
	dir := filepath.Join(parent, "store")
	if err := os.Mkdir(dir, 0700); err != nil {
		t.Fatal(err)
	}
	if err := os.Chmod(parent, 0770); err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { os.Chmod(parent, 0700) })
	if s, err := openStore(dir); err == nil {
		s.root.Close()
		t.Fatal("writable ancestor can redirect nginx pathname")
	}
}

func TestStoreRejectsUnsafeLock(t *testing.T) {
	for _, kind := range []string{"group-readable", "group-writable", "symlink", "hardlink", "fifo"} {
		t.Run(kind, func(t *testing.T) {
			s := testStore(t)
			if kind == "symlink" {
				if err := s.write("state/target", []byte("")); err != nil {
					t.Fatal(err)
				}
				if err := s.root.Symlink("target", "state/lock"); err != nil {
					t.Fatal(err)
				}
			} else if kind == "fifo" {
				if err := syscall.Mkfifo(filepath.Join(s.root.Name(), "state", "lock"), 0600); err != nil {
					t.Fatal(err)
				}
			} else {
				if err := s.write("state/lock", nil); err != nil {
					t.Fatal(err)
				}
				if kind == "hardlink" {
					if err := s.root.Link("state/lock", "state/other"); err != nil {
						t.Fatal(err)
					}
				} else {
					mode := os.FileMode(0640)
					if kind == "group-writable" {
						mode = 0620
					}
					if err := s.root.Chmod("state/lock", mode); err != nil {
						t.Fatal(err)
					}
				}
			}
			if unlock, err := s.lock(); err == nil {
				unlock()
				t.Fatal("unsafe lock accepted")
			}
			if reopened, err := openStore(s.root.Name()); err == nil {
				reopened.root.Close()
				t.Fatal("unsafe lock accepted at startup")
			}
		})
	}
}

func TestStoreRejectsWrongOwners(t *testing.T) {
	if os.Geteuid() != 0 {
		t.Skip("changing a fixture's owner requires root")
	}
	for _, name := range []string{".", "public", "state", "staging", "state/lock", "public/" + testArtifact, "public/" + mappingPrefix + "tc"} {
		t.Run(name, func(t *testing.T) {
			s := testStore(t)
			if name == "state/lock" {
				if err := s.write(name, nil); err != nil {
					t.Fatal(err)
				}
			} else if name == "public/"+testArtifact {
				if err := s.root.MkdirAll(filepath.ToSlash(filepath.Dir(name)), 0755); err != nil {
					t.Fatal(err)
				}
				if err := s.write(name, []byte("untrusted")); err != nil {
					t.Fatal(err)
				}
			} else if strings.HasPrefix(name, "public/") {
				if err := s.root.MkdirAll(name, 0755); err != nil {
					t.Fatal(err)
				}
			}
			full := filepath.Join(s.root.Name(), filepath.FromSlash(name))
			if err := os.Chown(full, 65534, -1); err != nil {
				t.Fatal(err)
			}
			t.Cleanup(func() { os.Chown(full, 0, -1) })
			if reopened, err := openStore(s.root.Name()); err == nil {
				reopened.root.Close()
				t.Fatal("wrong owner accepted at startup")
			}
		})
	}
}

func TestStoreRejectsWritablePublicFiles(t *testing.T) {
	s := testStore(t)
	if w := testPut(s, testRevision, testBundle(t, testRevision, []byte("original"), nil)); w.Code != 201 {
		t.Fatal(w.Code)
	}
	if err := s.root.Chmod("public/"+testArtifact, 0664); err != nil {
		t.Fatal(err)
	}
	if reopened, err := openStore(s.root.Name()); err == nil {
		reopened.root.Close()
		t.Fatal("group-writable public file accepted")
	}
	if _, err := s.collect(time.Hour, true); err == nil {
		t.Fatal("GC accepted a group-writable public file")
	}
}

func TestPublicEntryCapCountsDirectoriesAndAdmissionParents(t *testing.T) {
	s := testStore(t)
	if err := s.root.MkdirAll("public/"+mappingPrefix+"empty", 0755); err != nil {
		t.Fatal(err)
	}
	// Root + the four fixed mapping parents + a toolchain are six entries.
	if _, _, err := s.scanPublicLimit(5); err == nil {
		t.Fatal("empty directories bypassed traversal bound")
	}
	if _, dirs, err := s.scanPublicLimit(6); err != nil || len(dirs) != 5 {
		t.Fatalf("unexpected directory accounting: %v %v", dirs, err)
	}
	objects := map[string]time.Time{}
	for n := range maxObjects - 7 {
		objects[fmt.Sprint(n)] = time.Time{}
	}
	files := map[string]string{mappingPrefix + "new/" + testRevision + ".jsonl": "digest"}
	// The mapping needs five directories + one file, besides the public root.
	if err := checkAdmission(objects, nil, files); err != nil {
		t.Fatal("exact boundary rejected", err)
	}
	objects["one-more"] = time.Time{}
	if !errors.Is(checkAdmission(objects, nil, files), errCapacity) {
		t.Fatal("missing namespace parents were not included in admission")
	}
}

func TestGCPrunesEmptyNamespaceDirectories(t *testing.T) {
	s := testStore(t)
	for _, name := range []string{"public/" + artifactPrefix, "public/" + mappingPrefix + "empty"} {
		if err := s.root.MkdirAll(name, 0755); err != nil {
			t.Fatal(err)
		}
	}
	if _, err := s.collect(48*time.Hour, false); err != nil {
		t.Fatal(err)
	}
	if _, dirs, err := s.scanPublic(); err != nil || len(dirs) == 0 {
		t.Fatal("dry run removed namespace directories", err)
	}
	if _, err := s.collect(48*time.Hour, true); err != nil {
		t.Fatal(err)
	}
	if _, dirs, err := s.scanPublic(); err != nil || len(dirs) != 0 {
		t.Fatalf("empty namespaces leaked: %v %v", dirs, err)
	}
}

func TestGCToolchainChurnDoesNotLeakDirectories(t *testing.T) {
	s := testStore(t)
	for n := range 12 {
		revision := fmt.Sprintf("%040x", n+1)
		tc := fmt.Sprintf("tc-%d", n)
		body := testBundle(t, revision, []byte("shared"), func(m *inventory, entries *[]testEntry) {
			old := m.mapping()
			digest := m.Files[old]
			delete(m.Files, old)
			m.Toolchain = tc
			m.Files[m.mapping()] = digest
			(*entries)[1].name = m.mapping()
		})
		if err := s.publish(strings.NewReader(string(body)), revision); err != nil {
			t.Fatal(err)
		}
		if _, err := s.collect(time.Nanosecond, true); err != nil {
			t.Fatal(err)
		}
		objects, dirs, err := s.scanPublic()
		if err != nil || len(objects) != 2 || len(dirs) != 8 {
			t.Fatalf("toolchain churn leaked entries: files=%d dirs=%d err=%v", len(objects), len(dirs), err)
		}
		if !dirs[mappingPrefix+tc] {
			t.Fatal("current toolchain directory removed")
		}
	}
}

func TestGCUnsafeNamespaceFailsBeforeDeletion(t *testing.T) {
	s, dir, now := gcStore(t)
	gcPut(t, s, dir, gcArtifact(1), []byte("orphan"), now)
	if err := s.root.Mkdir("public/unexpected", 0755); err != nil {
		t.Fatal(err)
	}
	before := gcSnapshot(t, dir)
	if _, err := s.collect(time.Hour, true); err == nil {
		t.Fatal("unexpected namespace directory accepted")
	}
	if after := gcSnapshot(t, dir); !reflect.DeepEqual(before, after) {
		t.Fatal("unsafe namespace caused partial collection")
	}
}

func TestGCRejectsUnsafeStagingDirectory(t *testing.T) {
	s, dir, now := gcStore(t)
	gcPut(t, s, dir, gcArtifact(1), []byte("orphan"), now)
	if err := s.root.Mkdir("staging/11111111111111111111111111111111", 0750); err != nil {
		t.Fatal(err)
	}
	before := gcSnapshot(t, dir)
	if _, err := s.collect(time.Hour, true); err == nil {
		t.Fatal("nonprivate staging directory accepted")
	}
	if after := gcSnapshot(t, dir); !reflect.DeepEqual(before, after) {
		t.Fatal("unsafe staging caused partial collection")
	}
}
