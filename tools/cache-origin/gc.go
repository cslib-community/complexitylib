// Copyright (c) 2026 Erik Demaine. Released under the Apache 2.0 license.

//go:build linux

package main

import (
	"fmt"
	"io/fs"
	"path"
	"sort"
	"strings"
	"time"
)

type gcReport struct {
	ExpiredMappings []string `json:"expired_mappings"`
	DeleteArtifacts []string `json:"delete_artifacts"`
	DeleteStaging   []string `json:"delete_staging"`
	Applied         bool     `json:"applied"`
}

func (s *store) collect(retain time.Duration, apply bool) (gcReport, error) {
	report := gcReport{Applied: apply}
	if retain <= 0 {
		return report, fmt.Errorf("retention must be positive")
	}
	unlock, err := s.lock()
	if err != nil {
		return report, err
	}
	defer unlock()
	objects, directories, err := s.scanPublic()
	if err != nil {
		return report, err
	}
	// Preserve one latest publication across ALL toolchains, including idle periods.
	// Identical retries keep their original mtime, so they cannot become latest.
	latest := ""
	for key, modified := range objects {
		if mappingKey.MatchString(key) && (latest == "" || modified.After(objects[latest]) || modified.Equal(objects[latest]) && key > latest) {
			latest = key
		}
	}
	staging, err := fs.ReadDir(s.root.FS(), "staging")
	if err != nil {
		return report, err
	}
	for _, d := range staging {
		if !d.IsDir() || !stagingID.MatchString(d.Name()) {
			return report, fmt.Errorf("unexpected staging entry")
		}
		if err := s.safeDirectory("staging/"+d.Name(), true); err != nil {
			return report, err
		}
		info, err := d.Info()
		if err != nil {
			return report, err
		}
		if s.now().Sub(info.ModTime()) >= 24*time.Hour {
			report.DeleteStaging = append(report.DeleteStaging, "staging/"+d.Name())
		}
	}
	// Validate ALL mappings before deleting anything, even
	// expired mappings. Unknown formats or a missing artifact stop the entire pass.
	marked := map[string]bool{}
	for key, modified := range objects {
		if !mappingKey.MatchString(key) {
			continue
		}
		if modified.After(s.now()) {
			return report, fmt.Errorf("mapping timestamp is in the future")
		}
		b, err := s.read("public/"+key, maxMapping)
		if err != nil {
			return report, err
		}
		refs, err := references(b)
		if err != nil {
			return report, fmt.Errorf("%s: %w", key, err)
		}
		expired := key != latest && s.now().Sub(modified) >= retain
		for ref := range refs {
			if _, ok := objects[ref]; !ok {
				return report, fmt.Errorf("missing artifact %s", ref)
			}
			if !expired {
				marked[ref] = true
			}
		}
		if expired {
			report.ExpiredMappings = append(report.ExpiredMappings, key)
		}
	}
	for key := range objects {
		if strings.HasPrefix(key, artifactPrefix) && !marked[key] {
			report.DeleteArtifacts = append(report.DeleteArtifacts, key)
		}
	}
	sort.Strings(report.ExpiredMappings)
	sort.Strings(report.DeleteArtifacts)
	if !apply {
		return report, nil
	}
	for _, dir := range report.DeleteStaging {
		if err := s.root.RemoveAll(dir); err != nil {
			return report, err
		}
	}
	for _, key := range append(report.ExpiredMappings, report.DeleteArtifacts...) {
		if err := s.root.Remove("public/" + key); err != nil {
			return report, err
		}
		if err := s.syncDir(path.Dir("public/" + key)); err != nil {
			return report, err
		}
	}
	return report, s.pruneDirectories(directories)
}
