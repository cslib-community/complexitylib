// Copyright (c) 2026 Erik Demaine. Released under the Apache 2.0 license.

//go:build linux

package main

import (
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"log"
	"net"
	"net/http"
	"os"
	"strings"
	"syscall"
	"time"
)

func (s *store) handler() http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Cache-Control", "no-store")
		revision := strings.TrimPrefix(r.URL.Path, "/publish/")
		if r.URL.RawQuery != "" || r.URL.EscapedPath() != r.URL.Path || !strings.HasPrefix(r.URL.Path, "/publish/") || !revisionID.MatchString(revision) {
			http.NotFound(w, r)
			return
		}
		if r.Method != http.MethodPut {
			w.Header().Set("Allow", "PUT")
			http.Error(w, "PUT required", http.StatusMethodNotAllowed)
			return
		}
		mediaType := r.Header.Get("Content-Type")
		if mediaType != fullMediaType && mediaType != probeMediaType && mediaType != deltaMediaType {
			http.Error(w, "application/x-tar required", http.StatusUnsupportedMediaType)
			return
		}
		limit := int64(maxPackage)
		if mediaType == probeMediaType {
			limit = maxMetadata + maxMapping + 16384
		}
		if r.ContentLength > limit {
			http.Error(w, "package too large", http.StatusRequestEntityTooLarge)
			return
		}
		r.Body = http.MaxBytesReader(w, r.Body, limit)
		defer r.Body.Close()
		missing, err := s.receive(r.Body, revision, mediaType)
		if err != nil {
			status := http.StatusBadRequest
			var tooLarge *http.MaxBytesError
			var filesystemError *os.PathError
			switch {
			case errors.Is(err, syscall.EWOULDBLOCK):
				status = http.StatusServiceUnavailable
				w.Header().Set("Retry-After", "5")
			case errors.Is(err, errMissing):
				status = http.StatusPreconditionFailed
			case errors.Is(err, errConflict):
				status = http.StatusConflict
			case errors.As(err, &tooLarge):
				status = http.StatusRequestEntityTooLarge
			case errors.Is(err, syscall.ENOSPC), errors.Is(err, syscall.EDQUOT), errors.Is(err, errCapacity):
				status = http.StatusInsufficientStorage
			case errors.As(err, &filesystemError):
				status = http.StatusInternalServerError
			}
			log.Printf("publication rejected: %v", err)
			http.Error(w, http.StatusText(status), status)
			return
		}
		w.Header().Set("Content-Type", "application/json")
		if mediaType == probeMediaType {
			json.NewEncoder(w).Encode(struct {
				Version  int      `json:"version"`
				Revision string   `json:"revision"`
				Missing  []string `json:"missing"`
			}{1, revision, missing})
			return
		}
		w.WriteHeader(http.StatusCreated)
		json.NewEncoder(w).Encode(map[string]string{"revision": revision, "status": "published"})
	})
}

func run(args []string) error {
	if len(args) == 0 {
		return fmt.Errorf("usage: cache-origin serve|pack|gc [options]")
	}
	f := flag.NewFlagSet(args[0], flag.ContinueOnError)
	root := f.String("root", "", "existing dedicated store directory (serve/gc)")
	socket := f.String("socket", "", "new Unix socket path (serve)")
	retain := f.Duration("retain", 48*time.Hour, "maximum age of superseded mappings; latest publication is kept (gc)")
	apply := f.Bool("apply", false, "apply GC; otherwise report without deleting files")
	mapping := f.String("mapping", "", "Lake build -o mapping (pack)")
	archives := f.String("archives", "", "Lake cache stage directory (pack)")
	revision := f.String("revision", "", "producer Git commit (pack)")
	toolchain := f.String("toolchain", "", "Lake URL-encoded toolchain name (pack)")
	if err := f.Parse(args[1:]); err != nil {
		return err
	}
	if f.NArg() != 0 {
		return fmt.Errorf("unexpected positional arguments")
	}
	if args[0] == "pack" {
		return pack(os.Stdout, *mapping, *archives, *revision, *toolchain)
	}
	if args[0] != "serve" && args[0] != "gc" {
		return fmt.Errorf("unknown command %q", args[0])
	}
	if *root == "" {
		return fmt.Errorf("--root is required")
	}
	s, err := openStore(*root)
	if err != nil {
		return err
	}
	defer s.root.Close()
	if args[0] == "gc" {
		report, err := s.collect(*retain, *apply)
		if err != nil {
			return err
		}
		log.Printf("cache_gc_summary applied=%t artifacts=%d mappings=%d bytes=%d", report.Applied,
			len(report.DeleteArtifacts), len(report.ExpiredMappings), report.DeletedBytes)
		return json.NewEncoder(os.Stdout).Encode(report)
	}
	if *socket == "" {
		return fmt.Errorf("--socket is required; no TCP listener is provided")
	}
	l, err := net.Listen("unix", *socket)
	if err != nil {
		return err
	}
	defer l.Close()
	if err := os.Chmod(*socket, 0660); err != nil {
		return err
	}
	server := &http.Server{Handler: s.handler(), ReadHeaderTimeout: 5 * time.Second, ReadTimeout: 5 * time.Minute, WriteTimeout: 5 * time.Minute, IdleTimeout: 30 * time.Second, MaxHeaderBytes: 8192}
	return server.Serve(l)
}

func main() {
	if err := run(os.Args[1:]); err != nil {
		log.Fatal(err)
	}
}
