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

`lake -d guide exe guide --output <dir>` writes the guide's pages to `<dir>/html-multi`;
`scripts/guide.sh` runs it. The chapters' Lean examples are checked when `lake -d guide build`
elaborates them, before this program runs.
-/

open Verso.Genre.Manual

def main (options : List String) : IO UInt32 := do
  let env ← ComplexityGuide.ApiDocs.importEnv `CslibFrontierGuide
  let apiDocs := ComplexityGuide.ApiDocs.linkTargets env
  manualMain (%doc CslibFrontierGuide) (options := options) (config := {
    emitTeX := false
    emitHtmlSingle := .no
    emitHtmlMulti := .immediately
    htmlDepth := 2
    sourceLink := some "https://github.com/cslib-community/cslib-frontier"
    issueLink := some "https://github.com/cslib-community/cslib-frontier/issues"
    linkTargets := fun state remotes => state.localTargets ++ remotes.remoteTargets ++ apiDocs })
