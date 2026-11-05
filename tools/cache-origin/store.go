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
	"syscall"
	"time"
)

type store struct {
	root *os.Root
	now  func() time.Time
}

func openStore(dir string) (*store, error) {
	r, err := os.OpenRoot(dir)
	if err != nil {
		return nil, err
	}
	s := &store{r, time.Now}
	for _, p := range []string{"public", "staging", "state"} {
		mode := fs.FileMode(0700)
		if p == "public" {
			mode = 0755
		}
		if err = r.Mkdir(p, mode); err != nil && !errors.Is(err, fs.ErrExist) {
			r.Close()
			return nil, err
		}
		info, e := r.Lstat(p)
		if e != nil || !info.IsDir() || info.Mode()&os.ModeSymlink != 0 {
			r.Close()
			return nil, fmt.Errorf("unsafe store directory %s", p)
		}
	}
	if err := s.syncDir("."); err != nil {
		r.Close()
		return nil, err
	}
	return s, nil
}

// A single nonblocking interprocess lock covers each whole publication or GC pass.
// The lock file is permanent: never unlink it and create two independent locks.
func (s *store) lock() (func(), error) {
	f, err := s.root.OpenFile("state/lock", os.O_CREATE|os.O_RDWR, 0600)
	if err != nil {
		return nil, err
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
	if !info.Mode().IsRegular() {
		return nil, fmt.Errorf("not a regular file: %s", name)
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
	objects := map[string]time.Time{}
	err := fs.WalkDir(s.root.FS(), "public", func(name string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if d.IsDir() {
			return nil
		}
		key := name[len("public/"):]
		if !artifactKey.MatchString(key) && !mappingKey.MatchString(key) {
			return fmt.Errorf("unexpected public entry %s", key)
		}
		info, err := d.Info()
		if err != nil {
			return err
		}
		if !info.Mode().IsRegular() || len(objects) >= maxObjects {
			return fmt.Errorf("unsafe or oversized public store")
		}
		objects[key] = info.ModTime()
		return nil
	})
	return objects, err
}
