// Copyright (c) 2026 Erik Demaine. Released under the Apache 2.0 license.

//go:build linux

package main

import (
	"errors"
	"fmt"
	"io"
	"io/fs"
	"os"
	"path"
	"path/filepath"
	"sort"
	"strings"
	"syscall"
	"time"
)

type store struct {
	root *os.Root
	now  func() time.Time
}

func openStore(dir string) (*store, error) {
	var err error
	if dir, err = safeRootPath(dir); err != nil {
		return nil, err
	}
	r, err := os.OpenRoot(dir)
	if err != nil {
		return nil, err
	}
	s := &store{r, time.Now}
	if err := s.safeDirectory(".", false); err != nil {
		r.Close()
		return nil, err
	}
	for _, p := range []string{"public", "staging", "state"} {
		mode := fs.FileMode(0700)
		if p == "public" {
			mode = 0755
		}
		if err = r.Mkdir(p, mode); err != nil && !errors.Is(err, fs.ErrExist) {
			r.Close()
			return nil, err
		}
		if err := s.safeDirectory(p, p != "public"); err != nil {
			r.Close()
			return nil, err
		}
	}
	if _, _, err := s.scanPublic(); err != nil {
		r.Close()
		return nil, err
	}
	if info, err := r.Lstat("state/lock"); err == nil {
		if err := safeFile(info, true); err != nil {
			r.Close()
			return nil, fmt.Errorf("unsafe store lock: %w", err)
		}
	} else if !errors.Is(err, fs.ErrNotExist) {
		r.Close()
		return nil, err
	}
	if err := s.syncDir("."); err != nil {
		r.Close()
		return nil, err
	}
	return s, nil
}

// nginx resolves the public pathname independently of this process's root fd.
// Protect its ancestors too, so another uid cannot rename the whole store.
// A root-owned sticky /tmp is safe for a service-owned private child directory.
func safeRootPath(dir string) (string, error) {
	dir, err := filepath.Abs(filepath.Clean(dir))
	if err != nil {
		return "", err
	}
	for name := dir; ; name = filepath.Dir(name) {
		info, err := os.Lstat(name)
		if err != nil {
			return "", err
		}
		stat, ok := info.Sys().(*syscall.Stat_t)
		if !ok || !info.IsDir() || info.Mode()&os.ModeSymlink != 0 ||
			stat.Uid != 0 && stat.Uid != uint32(os.Geteuid()) ||
			info.Mode().Perm()&0022 != 0 && !(name != dir && stat.Uid == 0 && info.Mode()&os.ModeSticky != 0) {
			return "", fmt.Errorf("unsafe store path %s", name)
		}
		if name == filepath.Dir(name) {
			return dir, nil
		}
	}
}

// Other uids must not be able to replace names below the store or interfere
// with the permanent lock. The service uid/operator remains a trusted writer.
func safeOwnerMode(info fs.FileInfo, private bool) error {
	stat, ok := info.Sys().(*syscall.Stat_t)
	if !ok || stat.Uid != uint32(os.Geteuid()) || info.Mode().Perm()&0022 != 0 ||
		private && info.Mode().Perm()&0077 != 0 {
		return fmt.Errorf("wrong owner or unsafe permissions")
	}
	return nil
}

func safeFile(info fs.FileInfo, private bool) error {
	if !info.Mode().IsRegular() {
		return fmt.Errorf("not a regular file")
	}
	if err := safeOwnerMode(info, private); err != nil {
		return err
	}
	if private && info.Sys().(*syscall.Stat_t).Nlink != 1 {
		return fmt.Errorf("control file has multiple hard links")
	}
	return nil
}

func (s *store) safeDirectory(name string, private bool) error {
	info, err := s.root.Lstat(name)
	if err != nil {
		return err
	}
	if !info.IsDir() || info.Mode()&os.ModeSymlink != 0 || info.Mode().Perm()&0700 != 0700 {
		return fmt.Errorf("unsafe store directory %s", name)
	}
	if err := safeOwnerMode(info, private); err != nil {
		return fmt.Errorf("unsafe store directory %s: %w", name, err)
	}
	return nil
}

// A single nonblocking interprocess lock covers each whole publication or GC pass.
// The lock file is permanent: never unlink it and create two independent locks.
func (s *store) lock() (func(), error) {
	if _, err := safeRootPath(s.root.Name()); err != nil {
		return nil, err
	}
	for _, name := range []string{".", "public", "staging", "state"} {
		if err := s.safeDirectory(name, name == "staging" || name == "state"); err != nil {
			return nil, err
		}
	}
	if info, err := s.root.Lstat("state/lock"); err == nil {
		if err := safeFile(info, true); err != nil {
			return nil, fmt.Errorf("unsafe store lock: %w", err)
		}
	} else if !errors.Is(err, fs.ErrNotExist) {
		return nil, err
	}
	f, err := s.root.OpenFile("state/lock", os.O_CREATE|os.O_RDWR|syscall.O_NOFOLLOW, 0600)
	if err != nil {
		return nil, err
	}
	info, err := f.Stat()
	if err == nil {
		err = safeFile(info, true)
	}
	if err != nil {
		f.Close()
		return nil, fmt.Errorf("unsafe store lock: %w", err)
	}
	if err = syscall.Flock(int(f.Fd()), syscall.LOCK_EX|syscall.LOCK_NB); err != nil {
		f.Close()
		return nil, fmt.Errorf("store busy: %w", err)
	}
	return func() { f.Close() }, nil
}

func (s *store) regular(name string) (*os.File, error) {
	info, err := s.root.Lstat(name)
	if err != nil {
		return nil, err
	}
	if err := safeFile(info, strings.HasPrefix(name, "state/")); err != nil {
		return nil, fmt.Errorf("unsafe file %s: %w", name, err)
	}
	return s.root.Open(name)
}

func (s *store) read(name string, limit int64) ([]byte, error) {
	f, err := s.regular(name)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	b, err := io.ReadAll(io.LimitReader(f, limit+1))
	if int64(len(b)) > limit {
		return nil, fmt.Errorf("file too large: %s", name)
	}
	return b, err
}

func (s *store) digest(name string) (string, error) {
	f, err := s.regular(name)
	if err != nil {
		return "", err
	}
	defer f.Close()
	return hashStream(f)
}

func (s *store) syncDir(name string) error {
	f, err := s.root.Open(name)
	if err != nil {
		return err
	}
	defer f.Close()
	return f.Sync()
}

func (s *store) write(name string, data []byte) error {
	f, err := s.root.OpenFile(name, os.O_WRONLY|os.O_CREATE|os.O_EXCL, 0600)
	if err != nil {
		return err
	}
	_, err = f.Write(data)
	if err == nil {
		err = f.Sync()
	}
	return errors.Join(err, f.Close())
}

// Link is atomic create-if-absent. The completed, fsynced inode never becomes
// visible under its public key until this step; nothing writes it afterwards.
func (s *store) install(source, key string) error {
	dest := "public/" + key
	if err := s.root.MkdirAll(path.Dir(dest), 0755); err != nil {
		return err
	}
	for dir := path.Dir(dest); dir != "."; dir = path.Dir(dir) {
		if err := s.safeDirectory(dir, false); err != nil {
			return err
		}
	}
	if err := s.root.Chmod(source, 0444); err != nil {
		return err
	}
	if err := s.root.Link(source, dest); err != nil {
		return err
	}
	// Persist every newly created parent, not just the leaf directory.
	for dir := path.Dir(dest); dir != "."; dir = path.Dir(dir) {
		if err := s.syncDir(dir); err != nil {
			return err
		}
	}
	return nil
}

// Walk only our two public namespaces and reject links or unexpected entries.
// No process other than this service/operator may mutate the store directories.
func (s *store) objects() (map[string]time.Time, error) {
	objects, _, err := s.scanPublic()
	return objects, err
}

// Read bounded batches rather than fs.WalkDir's whole-directory allocation.
// maxObjects bounds every namespace entry, including the public root and dirs.
func (s *store) scanPublic() (map[string]time.Time, map[string]bool, error) {
	return s.scanPublicLimit(maxObjects)
}

func (s *store) scanPublicLimit(limit int) (map[string]time.Time, map[string]bool, error) {
	objects := map[string]time.Time{}
	directories := map[string]bool{}
	count := 1
	var walk func(string) error
	walk = func(dir string) error {
		if err := s.safeDirectory(dir, false); err != nil {
			return err
		}
		f, err := s.root.Open(dir)
		if err != nil {
			return err
		}
		defer f.Close()
		for {
			entries, err := f.ReadDir(128)
			if err != nil && !errors.Is(err, io.EOF) {
				return err
			}
			for _, entry := range entries {
				count++
				if count > limit {
					return fmt.Errorf("oversized public store")
				}
				name := path.Join(dir, entry.Name())
				key := strings.TrimPrefix(name, "public/")
				if entry.IsDir() {
					if !namespaceDirectory(key) {
						return fmt.Errorf("unexpected public directory %s", key)
					}
					directories[key] = true
					if err := walk(name); err != nil {
						return err
					}
					continue
				}
				if !artifactKey.MatchString(key) && !mappingKey.MatchString(key) {
					return fmt.Errorf("unexpected public entry %s", key)
				}
				info, err := entry.Info()
				if err != nil {
					return err
				}
				if err := safeFile(info, false); err != nil {
					return fmt.Errorf("unsafe public entry %s: %w", key, err)
				}
				objects[key] = info.ModTime()
			}
			if errors.Is(err, io.EOF) {
				return nil
			}
		}
	}
	err := walk("public")
	return objects, directories, err
}

func namespaceDirectory(key string) bool {
	for _, prefix := range []string{artifactPrefix, mappingPrefix} {
		if strings.HasPrefix(prefix, key+"/") {
			return true
		}
	}
	if strings.HasPrefix(key, mappingPrefix) {
		tc := strings.TrimPrefix(key, mappingPrefix)
		return toolchainID.MatchString(tc) && tc != "." && tc != ".."
	}
	return false
}

// Remove only known, empty directories, deepest first, after file deletion and
// under the same publication/GC lock. No namespace directory survives forever.
func (s *store) pruneDirectories(directories map[string]bool) error {
	names := make([]string, 0, len(directories))
	for name := range directories {
		names = append(names, "public/"+name)
	}
	sort.Slice(names, func(i, j int) bool { return len(names[i]) > len(names[j]) })
	for _, name := range names {
		f, err := s.root.Open(name)
		if err != nil {
			return err
		}
		entries, err := f.ReadDir(1)
		f.Close()
		if err != nil && !errors.Is(err, io.EOF) {
			return err
		}
		if len(entries) != 0 {
			continue
		}
		if err := s.root.Remove(name); err != nil {
			return err
		}
		if err := s.syncDir(path.Dir(name)); err != nil {
			return err
		}
	}
	return nil
}
