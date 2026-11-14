/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import VersoManual
import CslibFrontierGuide
import CslibFrontierGuide.ApiDocs

/-!
# The guide's HTML generator

`scripts/guide.sh` checks the chapters and runs this generator through Lake’s `lean` command with `--run`,
writing the pages to `guide/.lake/build/site/html-multi`. Lake builds its imports and applies
the project options before Lean interprets `main`; it does not need native code for the
imported library. `lake -d guide exe guide --output <dir>` also remains available for native
generation.
-/

open Verso.Genre.Manual

def main (options : List String) : IO UInt32 := do
  let env ← CslibFrontierGuide.ApiDocs.importEnv `CslibFrontierGuide
  let apiDocs := CslibFrontierGuide.ApiDocs.linkTargets env
  manualMain (%doc CslibFrontierGuide) (options := options) (config := {
    emitTeX := false
    emitHtmlSingle := .no
    emitHtmlMulti := .immediately
    htmlDepth := 2
    sourceLink := some "https://github.com/cslib-community/cslib-frontier"
    issueLink := some "https://github.com/cslib-community/cslib-frontier/issues"
    linkTargets := fun state remotes => state.localTargets ++ remotes.remoteTargets ++ apiDocs })
