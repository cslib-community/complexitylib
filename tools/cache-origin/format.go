// Copyright (c) 2026 Erik Demaine. Released under the Apache 2.0 license.

package main

import (
	"bufio"
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"regexp"
)

const (
	scope          = "cslib-community/complexitylib"
	artifactPrefix = "a0/" + scope + "/"
	mappingPrefix  = "r0/" + scope + "/tc/"
	maxFiles       = 10000
	maxMetadata    = 4 << 20
	maxMapping     = 8 << 20
	maxPackage     = 1 << 30
	maxArtifact    = 256 << 20
	maxObjects     = 100000
)

var (
	hashID      = regexp.MustCompile(`^[0-9a-f]{16}$`)
	revisionID  = regexp.MustCompile(`^[0-9a-f]{40}$`)
	toolchainID = regexp.MustCompile(`^[A-Za-z0-9_.+-]{1,160}$`)
	digestID    = regexp.MustCompile(`^[0-9a-f]{64}$`)
	stagingID   = regexp.MustCompile(`^[0-9a-f]{32}$`)
	artifactKey = regexp.MustCompile(`^a0/` + scope + `/[0-9a-f]{16}\.art$`)
	mappingKey  = regexp.MustCompile(`^r0/` + scope + `/tc/[A-Za-z0-9_.+-]{1,160}/[0-9a-f]{40}\.jsonl$`)
)

type inventory struct {
	Version   int               `json:"version"`
	Revision  string            `json:"revision"`
	Toolchain string            `json:"toolchain"`
	Files     map[string]string `json:"files"`
}

func (m inventory) mapping() string {
	return mappingPrefix + m.Toolchain + "/" + m.Revision + ".jsonl"
}

func decodeJSON(data []byte, target any) error {
	d := json.NewDecoder(bytes.NewReader(data))
	d.DisallowUnknownFields()
	if err := d.Decode(target); err != nil {
		return err
	}
	if d.Decode(new(any)) != io.EOF {
		return fmt.Errorf("trailing JSON data")
	}
	return nil
}

func (m inventory) validate() error {
	if m.Version != 1 || !revisionID.MatchString(m.Revision) || !toolchainID.MatchString(m.Toolchain) || m.Toolchain == "." || m.Toolchain == ".." || len(m.Files) < 2 || len(m.Files) > maxFiles {
		return fmt.Errorf("invalid inventory identity or file count")
	}
	if _, ok := m.Files[m.mapping()]; !ok {
		return fmt.Errorf("missing revision mapping")
	}
	for name, digest := range m.Files {
		if (name != m.mapping() && !artifactKey.MatchString(name)) || !digestID.MatchString(digest) {
			return fmt.Errorf("invalid inventory entry %q", name)
		}
	}
	return nil
}

// Accept precisely the module-output format emitted by pinned Lake v4.36.0-rc2.
// Fail closed if a future producer introduces another output shape or version.
func references(data []byte) (map[string]bool, error) {
	if len(data) > maxMapping {
		return nil, fmt.Errorf("mapping exceeds limit")
	}
	s := bufio.NewScanner(bytes.NewReader(data))
	s.Buffer(make([]byte, 4096), 4096)
	if !s.Scan() || s.Text() != `"2026-03-17"` {
		return nil, fmt.Errorf("unsupported Lake mapping version")
	}
	refs, inputs := map[string]bool{}, map[string]bool{}
	for n := 0; s.Scan(); n++ {
		var row []string
		if n >= maxFiles || json.Unmarshal(s.Bytes(), &row) != nil || len(row) != 2 || !hashID.MatchString(row[0]) || len(row[1]) != 21 || row[1][16:] != ".ltar" || !hashID.MatchString(row[1][:16]) || inputs[row[0]] {
			return nil, fmt.Errorf("unsupported or duplicate mapping row")
		}
		inputs[row[0]] = true
		refs[artifactPrefix+row[1][:16]+".art"] = true
	}
	if err := s.Err(); err != nil {
		return nil, err
	}
	if len(refs) == 0 {
		return nil, fmt.Errorf("empty mapping")
	}
	return refs, nil
}

func hashStream(r io.Reader) (string, error) {
	h := sha256.New()
	_, err := io.Copy(h, r)
	return hex.EncodeToString(h.Sum(nil)), err
}
