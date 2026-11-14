#!/usr/bin/env python3
"""Check public-import reachability against fixtures and the previous closure algorithm."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
CLOSURE = ROOT / ".lake/packages/importGraph/ImportGraph/Graph/TransitiveClosure.lean"

FIXTURE = r'''
import Lean
import ImportGraph.Graph.TransitiveClosure
import CheckInitImports

/-! Regression tests for the required public-import path to `Cslib.Init`. -/

open Lean

private def pub (name : Name) : Import := { module := name, isExported := true }
private def priv (name : Name) : Import := { module := name, isExported := false }
private def ordered (names : List Name) : List Name := (NameSet.ofList names).toList

-- Direct, transitive and diamond paths work even when dependencies come later in the input.
#guard missingInitImports #[
  (`CslibFrontier.Top, #[pub `CslibFrontier.Left, pub `CslibFrontier.Right]),
  (`CslibFrontier.Right, #[pub `CslibFrontier.Base]),
  (`CslibFrontier.Left, #[pub `CslibFrontier.Base]),
  (`CslibFrontier.Base, #[pub `Cslib.Init])] == []

-- A private edge anywhere in a path breaks it; one public alternative is sufficient.
#guard missingInitImports #[
  (`CslibFrontier.Private, #[priv `Cslib.Init]),
  (`CslibFrontier.Blocked, #[pub `CslibFrontier.Private]),
  (`CslibFrontier.Mixed, #[priv `CslibFrontier.Private, pub `Cslib.Init]),
  (`CslibFrontier, #[priv `CslibFrontier.Private]),
  (`Dependency.Bad, #[])] == ordered [`CslibFrontier.Blocked, `CslibFrontier.Private]

-- Exceptions exempt only the named module, not its importers. Publicly referenced leaves count.
#guard missingInitImports #[
  (`CslibFrontier.Child, #[pub `CslibFrontier.Exception]),
  (`CslibFrontier.Exception, #[]),
  (`CslibFrontier.Ref, #[pub `CslibFrontier.Missing])]
    [`CslibFrontier.Exception] ==
  ordered [`CslibFrontier.Child, `CslibFrontier.Missing, `CslibFrontier.Ref]

-- Cycles are harmless to the traversal; only a cycle with a public exit to Init is accepted.
#guard missingInitImports #[
  (`CslibFrontier.GoodA, #[pub `CslibFrontier.GoodB]),
  (`CslibFrontier.GoodB, #[pub `CslibFrontier.GoodA, pub `Cslib.Init]),
  (`CslibFrontier.BadA, #[pub `CslibFrontier.BadB]),
  (`CslibFrontier.BadB, #[pub `CslibFrontier.BadA])] ==
  ordered [`CslibFrontier.BadA, `CslibFrontier.BadB]

#guard missingInitImports #[] == []

-- Compare with the previous algorithm on every four-vertex DAG whose six possible edges are
-- absent, private or public. Reverse the module order too; no topological-order assumption is used.
private def oldMissing (modules : Array (Name × Array Import)) : List Name :=
  let graph := modules.foldl (init := ({} : NameMap (Array Name))) fun graph (name, imports) =>
    graph.insert name (imports.filter (·.isExported) |>.map (·.module))
  (graph.transitiveClosure.filter fun name imports =>
    name.getRoot == `CslibFrontier && name != `CslibFrontier &&
      !imports.contains `Cslib.Init).keys

private def dag (code : Nat) : Array (Name × Array Import) := Id.run do
  let names := #[`Cslib.Init, `CslibFrontier.A, `CslibFrontier.B, `CslibFrontier.C]
  let mut remaining := code
  let mut modules := #[]
  for i in [:names.size] do
    let mut imports := #[]
    for j in [:i] do
      match remaining % 3 with
      | 1 => imports := imports.push (priv names[j]!)
      | 2 => imports := imports.push (pub names[j]!)
      | _ => pure ()
      remaining := remaining / 3
    modules := modules.push (names[i]!, imports)
  return modules

#guard (List.range (3 ^ 6)).all fun code =>
  let modules := dag code
  missingInitImports modules == oldMissing modules &&
    missingInitImports modules.reverse == oldMissing modules
'''


@unittest.skipUnless(shutil.which("lean"), "needs Lean")
class PublicImportTests(unittest.TestCase):
    def test_public_paths_exceptions_and_small_graph_equivalence(self):
        self.assertTrue(CLOSURE.is_file(), "Missing pinned import-graph reference source")
        with tempfile.TemporaryDirectory() as temporary:
            build = Path(temporary)
            closure = build / "ImportGraph/Graph/TransitiveClosure.olean"
            closure.parent.mkdir(parents=True)
            fixture = build / "Fixture.lean"
            fixture.write_text(FIXTURE)
            env = {**os.environ, "LEAN_PATH": str(build)}
            # Compile only the checker and the tiny, pinned reference implementation. No Lake
            # build, shared outputs or library compilation is needed for these graph fixtures.
            commands = [
                ["lean", "-DwarningAsError=true", "-o", str(build / "CheckInitImports.olean"),
                 "scripts/CheckInitImports.lean"],
                ["lean", "-DwarningAsError=true", "-o", str(closure), str(CLOSURE)],
                ["lean", "-DwarningAsError=true", str(fixture)],
            ]
            for command in commands:
                result = subprocess.run(command, cwd=ROOT, env=env, text=True,
                                        capture_output=True, timeout=60)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
