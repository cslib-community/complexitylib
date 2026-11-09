/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module  -- shake: keep-downstream, shake: keep-all
-- upstream: local-only (project root; every other module imports `Cslib.Init` through it)

public import Cslib.Init

/-!
# CslibFrontier.Init

Every module of this library transitively imports this file, which in turn publicly imports
`Cslib.Init`. This keeps the library under cslib's invariant that all modules publicly import
`Cslib.Init`, so that any module can be moved upstream unchanged (after rewriting the import
prefix `CslibFrontier.` to `Cslib.`).
-/
