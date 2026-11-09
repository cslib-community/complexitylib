/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import VersoManual

/-!
# Links from the guide's code to the API documentation

Names in the guide's highlighted Lean code link to their entries in the API documentation that
doc-gen4 generates from `docbuild/` and that is published next to the guide. doc-gen4 documents a
declaration on its module's page, at `<root>/<Module/Path>.html#<name>`. Highlighted code records a
constant's name but not its module, so the generator imports the guide's environment once to look
modules up.

Only modules that the API documentation has pages for are linked: the library's modules and their
imports, and Lean's own modules, which doc-gen4 always documents. Declarations from Verso or from
the guide itself get no link.
-/

namespace CslibFrontierGuide.ApiDocs

open Lean Verso Code Genre Manual

/-- The published API documentation for `CslibFrontier` and `Cslib`. -/
def defaultRoot : String := "https://www.cslib.io/cslib-frontier/"

/-- The published external API documentation for `Mathlib` and Lean core dependencies. -/
def mathlibRoot : String := "https://leanprover-community.github.io/mathlib4_docs/"

/-- The modules imported in `env` that the API documentation has pages for: the library's modules,
everything they import, and the modules of Lean itself. -/
def documentedModules (env : Environment) : NameSet := Id.run do
  let names := env.header.moduleNames
  let index : Std.HashMap Name Nat := names.zipIdx.foldl (init := {}) fun m (n, i) => m.insert n i
  let mut documented : NameSet := {}
  let mut pending := names.filter (·.getRoot == `CslibFrontier)
  while h : pending.size > 0 do
    let mod := pending.back
    pending := pending.pop
    unless documented.contains mod do
      documented := documented.insert mod
      if let some i := index[mod]? then
        pending := pending ++ env.header.moduleData[i]!.imports.map (·.module)
  return names.foldl (init := documented) fun s n =>
    if [`Init, `Std, `Lean, `Lake].contains n.getRoot then s.insert n else s

/-- Imports `module`, normally the guide's root module, to find each declaration's module. -/
def importEnv (module : Name) : IO Environment := do
  initSearchPath (← findSysroot)
  importModules #[{ module }] {} (loadExts := false)

/-- Links each documented constant in highlighted code to its API documentation entry under
`root` (for `CslibFrontier` and `Cslib` modules) or `depRoot` (for `Mathlib` and Lean core modules),
using doc-gen4's page and anchor scheme. -/
def linkTargets (env : Environment) (root : String := defaultRoot)
    (depRoot : String := mathlibRoot) : LinkTargets Manual.TraverseContext :=
  let documented := documentedModules env
  { const := fun name _ => Id.run do
      let some idx := env.getModuleIdxFor? name | return #[]
      let some mod := env.header.moduleNames[idx.toNat]? | return #[]
      unless documented.contains mod do return #[]
      let base := if [`CslibFrontier, `Cslib].contains mod.getRoot then root else depRoot
      let page := "/".intercalate (mod.components.map (·.toString (escape := false)))
      return #[{ shortDescription := "API", description := s!"API documentation for {name}",
                 href := s!"{base}{page}.html#{name}" }] }

end CslibFrontierGuide.ApiDocs
