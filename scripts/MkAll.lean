/-
Copyright (c) 2024 Yaël Dillies, Damiano Testa. All rights reserved.
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Damiano Testa, Samuel Schlesinger
-/

-- upstream: local-only (project scaffolding)

import Cli.Basic
import Lake.CLI.Main
import Mathlib.Util.GetAllModules

-- Lake's executable API requires this import; this project script is not a library module.
set_option linter.style.header false

/-! # Generate import aggregators with Lake's library source directories

Adapted from Mathlib's `scripts/mk_all.lean` by Yaël Dillies and Damiano Testa. The command-line
options, module-style inference, import sorting and update exit codes follow that script.
Each library is scanned relative to its configured `srcDir`, so a root such as
`abstracts/CslibFrontierAbstracts.lean` imports `CslibFrontierAbstracts.*`, without an `abstracts`
prefix.
The shared `Mathlib.Util.GetAllModules` utility supplies discovery and deterministic sorting.
-/

namespace ComplexityScripts.MkAll

open Lean System.FilePath

/-- A module directory relative to the library's actual source directory. -/
structure LibraryRoot where
  sourceDir : System.FilePath
  moduleDir : String

/-- Read the root package's configured library roots and resolve an optional `--lib` subfolder. -/
def getLibraryRoots (selected : Option String) : IO (Array LibraryRoot) := do
  let (elanInstall?, leanInstall?, lakeInstall?) ← Lake.findInstall?
  let config ← Lake.MonadError.runEIO <|
    Lake.mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? }
  let some ws ← Lake.loadWorkspace config |>.toBaseIO
    | throw <| IO.userError "failed to load Lake workspace"
  let package := ws.root
  let mut roots : Array LibraryRoot := #[]
  for lib in package.leanLibs do
    let sourceDir ← IO.FS.realPath lib.srcDir
    for root in lib.roots do
      roots := roots.push ⟨sourceDir, Name.toStringWithSep pathSeparator.toString false root⟩
  if let some selected := selected then
    for root in roots do
      if selected == root.moduleDir || selected.startsWith (root.moduleDir.push pathSeparator) then
        return #[{ root with moduleDir := selected }]
    -- Preserve the stock command's ability to scan an arbitrary package-relative subfolder.
    return #[⟨← IO.FS.realPath package.srcDir, selected⟩]
  -- Preserve Mathlib's own exceptions when this script is used there.
  if package.baseName == `mathlib then
    roots := roots.filter fun root => root.moduleDir != "Cache" && root.moduleDir != "MathlibTest"
    roots := roots.push ⟨← IO.FS.realPath package.srcDir, "Mathlib".push pathSeparator ++ "Tactic"⟩
  return roots

/-- Generate or check one aggregator in its library's source directory, restoring the caller's
working directory even if scanning or writing fails. -/
def updateRoot (root : LibraryRoot) (git check moduleFlag : Bool) : IO Bool := do
  let previousDir ← IO.currentDir
  try
    IO.Process.setCurrentDir root.sourceDir
    let d := root.moduleDir
    let fileName := addExtension d "lean"
    let displayName := root.sourceDir / fileName
    let fileExists ← pathExists fileName
    let existingContent ← if fileExists then IO.FS.readFile fileName else pure ""
    let useModule ← if moduleFlag then pure true
      else if fileExists then
        try
          let header ← Lean.parseImports' existingContent fileName.toString
          pure header.isModule
        catch e =>
          throw <| IO.userError s!"\
            Could not parse the header of '{displayName}' to determine whether it should be a \
            module file: {e.toString}\n\
            Fix or delete the file, then re-run `mk_all` (with `--module` if you want a \
            module-style aggregator)."
      else pure false
    let mut allFiles ← getAllModulesSorted git d
    if d == "Mathlib" then
      allFiles := #["Std", "Batteries"] ++ allFiles
    let fileContent :=
      (if useModule then "module  -- shake: keep-all --deprecated_module: ignore\n\n" else "") ++
      ("\n".intercalate
        (allFiles.map ((if useModule then "public " else "") ++ "import " ++ ·)).toList) ++
      (if d == "Mathlib" then "\n\nset_option linter.style.longLine false" else "") ++ "\n"
    if !fileExists then
      if check then
        IO.println s!"File '{displayName}' does not exist"
      else
        IO.println s!"Creating '{displayName}'"
        IO.FS.writeFile fileName fileContent
      return true
    else if existingContent != fileContent then
      if check then
        IO.println s!"The file '{displayName}' is out of date: \
          run `lake exe mk_all{if git then " --git" else ""}` to update it"
      else
        IO.println s!"Updating '{displayName}'"
        IO.FS.writeFile fileName fileContent
      return true
    return false
  finally
    IO.Process.setCurrentDir previousDir

/-- The `mk_all` exit code counts changed or missing files, capped at 125 as in Mathlib. -/
def mkAllCLI (args : Cli.Parsed) : IO UInt32 := do
  let git := (args.flag? "git").isSome
  let check := (args.flag? "check").isSome
  let moduleFlag := (args.flag? "module").isSome
  let selected := (args.flag? "lib").map (·.as! String)
  let roots ← getLibraryRoots selected
  let mut updates := 0
  -- A nested root such as Mathlib/Tactic must be generated before its parent.
  for root in roots.reverse do
    if ← updateRoot root git check moduleFlag then
      updates := updates + 1
  if updates == 0 then
    IO.println "No update necessary"
  return min updates 125

open Cli in
/-- The stock `mk_all` options, with source directories resolved from the Lake configuration. -/
def mkAll : Cmd := `[Cli|
  mk_all VIA mkAllCLI; ["0.0.1"]
  "Generate a file importing all Lean files below each library root. \
   Library source directories are read from Lake. Use --lib to select a library or subfolder."
  FLAGS:
    lib : String; "Create an aggregator for the specified library root or subfolder."
    git;          "Use the folder content information from git."
    check;        "Only check if the files are up-to-date; print an error if not."
    module;       "Force module style with public imports; otherwise infer the existing style."
]

end ComplexityScripts.MkAll

/-- The entrypoint to the source-directory-aware `lake exe mk_all` command. -/
def main (args : List String) : IO UInt32 := ComplexityScripts.MkAll.mkAll.validate args
