// Copyright (c) 2026 Erik Demaine. Released under the Apache 2.0 license.

//go:build linux

package main

import (
	"archive/tar"
	"bytes"
	"crypto/rand"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"io/fs"
	"os"
	"path"
	"sort"
	"time"
)

var errConflict = errors.New("published key has different contents")
var errCapacity = errors.New("public entry capacity reached")

func (s *store) publish(body io.Reader, revision string) error {
	unlock, err := s.lock()
	if err != nil {
		return err
	}
	defer unlock()
	dir := fmt.Sprintf("staging/%x", randomID())
	if err := s.root.Mkdir(dir, 0700); err != nil {
		return err
	}
	defer s.root.RemoveAll(dir)
	tr := tar.NewReader(body)
	h, err := tr.Next()
	if err != nil || h.Name != "publication.json" || !plainHeader(h) || h.Size > maxMetadata {
		return fmt.Errorf("inventory must be the first regular USTAR entry")
	}
	b, err := io.ReadAll(tr)
	if err != nil {
		return err
	}
	var m inventory
	if err := decodeJSON(b, &m); err != nil {
		return err
	}
	if err := m.validate(); err != nil {
		return err
	}
	if m.Revision != revision {
		return fmt.Errorf("URL and inventory revisions differ")
	}
	staged := map[string]string{}
	for {
		h, err = tr.Next()
		if err == io.EOF {
			break
		}
		if err != nil {
			return err
		}
		expected, ok := m.Files[h.Name]
		limit := int64(maxArtifact)
		if h.Name == m.mapping() {
			limit = maxMapping
		}
		if !ok || staged[h.Name] != "" || !plainHeader(h) || h.Size <= 0 || h.Size > limit {
			return fmt.Errorf("unexpected, duplicate or oversized entry %q", h.Name)
		}
		name := fmt.Sprintf("%s/%d", dir, len(staged))
		f, err := s.root.OpenFile(name, os.O_CREATE|os.O_EXCL|os.O_WRONLY, 0600)
		if err != nil {
			return err
		}
		_, err = io.CopyN(f, tr, h.Size)
		if err == nil {
			err = f.Sync()
		}
		if err = errors.Join(err, f.Close()); err != nil {
			return err
		}
		actual, err := s.digest(name)
		if err != nil {
			return err
		}
		if actual != expected {
			return fmt.Errorf("digest mismatch: %s", h.Name)
		}
		staged[h.Name] = name
	}
	// Permit only bounded zero record-padding after the tar end marker.
	padding, err := io.ReadAll(io.LimitReader(body, 10241))
	if err != nil {
		return err
	}
	if len(padding) > 10240 || !bytes.Equal(padding, make([]byte, len(padding))) {
		return fmt.Errorf("invalid trailing package bytes")
	}
	if len(staged) != len(m.Files) {
		return fmt.Errorf("incomplete package")
	}
	mapping, err := s.read(staged[m.mapping()], maxMapping)
	if err != nil {
		return err
	}
	refs, err := references(mapping)
	if err != nil {
		return err
	}
	if len(refs)+1 != len(staged) {
		return fmt.Errorf("inventory must contain exactly the mapping's artifacts")
	}
	for key := range refs {
		if staged[key] == "" {
			return fmt.Errorf("missing referenced artifact %s", key)
		}
	}
	// Preflight every conflict before installing any file. Retries accept identical
	// bytes, but never silently preserve an unexpected artifact under a Lake hash.
	objects, directories, err := s.scanPublic()
	if err != nil {
		return err
	}
	if err := checkAdmission(objects, directories, m.Files); err != nil {
		return err
	}
	for key, expected := range m.Files {
		actual, err := s.digest("public/" + key)
		if errors.Is(err, fs.ErrNotExist) {
			continue
		}
		if err != nil {
			return err
		}
		if actual != expected {
			return fmt.Errorf("%w: %s", errConflict, key)
		}
	}
	keys := make([]string, 0, len(refs))
	for key := range refs {
		keys = append(keys, key)
	}
	sort.Strings(keys)
	keys = append(keys, m.mapping())
	for _, key := range keys {
		if _, err := s.root.Lstat("public/" + key); err == nil {
			continue
		} else if !errors.Is(err, fs.ErrNotExist) {
			return err
		}
		if err := s.install(staged[key], key); err != nil {
			return err
		}
	}
	// Flush directory creation too before acknowledging publication. Crash or disk
	// failure may leave unreferenced artifacts, which the collector can reclaim.
	return s.syncDir("public")
}

func randomID() []byte {
	b := make([]byte, 16)
	if _, err := rand.Read(b); err != nil {
		panic(err)
	}
	return b
}

func checkAdmission(objects map[string]time.Time, directories map[string]bool, files map[string]string) error {
	count := 1 + len(objects) + len(directories)
	newDirectories := map[string]bool{}
	for key := range files {
		if _, ok := objects[key]; !ok {
			count++
		}
		for dir := path.Dir(key); dir != "."; dir = path.Dir(dir) {
			if !directories[dir] {
				newDirectories[dir] = true
			}
		}
	}
	count += len(newDirectories)
	if count > maxObjects {
		return errCapacity
	}
	return nil
}

func plainHeader(h *tar.Header) bool {
	return h != nil && h.Typeflag == tar.TypeReg && h.Format == tar.FormatUSTAR && h.Linkname == "" && len(h.PAXRecords) == 0 && len(h.Xattrs) == 0
}

// pack consumes Lake's original mapping and staged .ltar files. It never builds
// Lean or changes workflow configuration; the caller supplies the producer SHA.
func pack(w io.Writer, mapping, archives, revision, toolchain string) error {
	f, err := os.Open(mapping)
	if err != nil {
		return err
	}
	b, err := io.ReadAll(io.LimitReader(f, maxMapping+1))
	f.Close()
	if err != nil {
		return err
	}
	refs, err := references(b)
	if err != nil {
		return err
	}
	m := inventory{1, revision, toolchain, map[string]string{}}
	files := map[string]string{m.mapping(): mapping}
	for key := range refs {
		files[key] = path.Join(archives, path.Base(key)[:16]+".ltar")
	}
	keys := make([]string, 0, len(files))
	for key, name := range files {
		f, err := os.Open(name)
		if err != nil {
			return err
		}
		info, err := f.Stat()
		if err != nil || !info.Mode().IsRegular() || info.Size() > maxArtifact {
			f.Close()
			return fmt.Errorf("invalid input file %s", name)
		}
		m.Files[key], err = hashStream(f)
		f.Close()
		if err != nil {
			return err
		}
		keys = append(keys, key)
	}
	if err := m.validate(); err != nil {
		return err
	}
	metadata, err := json.Marshal(m)
	if err != nil {
		return err
	}
	if len(metadata) > maxMetadata {
		return fmt.Errorf("inventory exceeds limit")
	}
	tw := tar.NewWriter(w)
	if err := tw.WriteHeader(&tar.Header{Name: "publication.json", Mode: 0600, Size: int64(len(metadata)), Typeflag: tar.TypeReg, Format: tar.FormatUSTAR}); err != nil {
		return err
	}
	if _, err := tw.Write(metadata); err != nil {
		return err
	}
	sort.Strings(keys)
	for _, key := range keys {
		f, err := os.Open(files[key])
		if err != nil {
			return err
		}
		info, err := f.Stat()
		if err == nil {
			err = tw.WriteHeader(&tar.Header{Name: key, Mode: 0600, Size: info.Size(), Typeflag: tar.TypeReg, Format: tar.FormatUSTAR})
		}
		if err == nil {
			_, err = io.Copy(tw, f)
		}
		f.Close()
		if err != nil {
			return err
		}
	}
	return tw.Close()
}
