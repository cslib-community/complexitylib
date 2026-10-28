"""Regression fixtures for generated API documentation coverage (no Lean build)."""

from contextlib import closing, redirect_stdout
import io
import json
from pathlib import Path
import sqlite3
import tempfile
import unittest
from unittest.mock import patch

import check_docs


class CheckOutputTests(unittest.TestCase):
    # Both names survived in a reused doc-gen4 cache after their sources were removed.
    obsolete_modules = (
        "Complexity.Computability.Circuit.Basic",
        "Complexity.Computability.Machines.Turing.MultiTape.Plumbing.WriteWord",
    )

    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.docs = self.root / "docbuild/.lake/build/doc"
        self.database = self.docs.parent / "api-docs.db"
        root_patch = patch.object(check_docs, "ROOT", self.root)
        root_patch.start()
        self.addCleanup(root_patch.stop)
        for module in ("Complexity", "Complexity.Current"):
            self.write(self.root / (module.replace(".", "/") + ".lean"))
            self.write(self.page(module))
            self.write(self.module_data(module), "{}")
        with closing(sqlite3.connect(self.database)) as db, db:
            db.execute("CREATE TABLE modules (name TEXT PRIMARY KEY, source_url TEXT)")
            db.executemany("INSERT INTO modules (name) VALUES (?)",
                           [("Complexity",), ("Complexity.Current",)])
        for name in ("index.html", "search.html", "search.js", "declaration-data.js",
                     "references.html", "references.bib", "find/index.html"):
            self.write(self.docs / name)
        self.index = {"modules": {"Complexity": {}, "Complexity.Current": {}},
                      "declarations": {}}
        for name in ("Cslib.Complexity.CookLevin.SAT_npComplete",
                     "Cslib.Complexity.NP_eq_PCP_log",
                     "Cslib.Crypto.OneWay.exists_pseudorandomFunction"):
            self.index["declarations"][name] = {"docLink": "./Complexity/Current.html#" + name}
        self.write(self.page("Complexity.Current"), "\n".join(
            f'<div id="{name}"></div>' for name in self.index["declarations"]))
        self.published_index = None
        pub_patch = patch.object(
            check_docs, "fetch_published_external_index", side_effect=self.default_published_index
        )
        pub_patch.start()
        self.addCleanup(pub_patch.stop)

    def default_published_index(self):
        if self.published_index is not None:
            return self.published_index
        declarations = dict(self.index.get("declarations", {}))
        for module in self.index.get("modules", {}):
            if module.split(".", 1)[0] in check_docs.LOCAL_DOC_ROOTS:
                continue
            page = self.page(module)
            if page.is_file():
                rel = module.replace(".", "/") + ".html"
                for anchor in check_docs.page_anchors(page):
                    declarations.setdefault(anchor, {"docLink": f"./{rel}#{anchor}"})
        return {
            "modules": dict(self.index.get("modules", {})),
            "declarations": declarations,
        }

    def write(self, path, text=""):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def page(self, module):
        return self.docs / (module.replace(".", "/") + ".html")

    def module_data(self, module):
        return self.docs.parent / "doc-data" / f"declaration-data-{module}.bmp"

    def check(self):
        self.write(self.docs / "declarations/declaration-data.bmp", json.dumps(self.index))
        with redirect_stdout(io.StringIO()):
            check_docs.check_output()

    def assert_failure(self, message):
        with self.assertRaises(ValueError) as error:
            self.check()
        self.assertEqual(str(error.exception), message)

    def test_current_modules_and_other_roots_pass(self):
        for name in ("Cslib.Extra", "Mathlib.Extra", "ComplexityTests", "ComplexityExtra.Old"):
            self.index["modules"][name] = {}
            self.write(self.page(name))
            self.write(self.module_data(name), "{}")
            with closing(sqlite3.connect(self.database)) as db, db:
                db.execute("INSERT INTO modules (name) VALUES (?)", (name,))
        self.check()

    def test_obsolete_intermediate_data_only(self):
        for name in reversed(self.obsolete_modules):
            self.write(self.module_data(name), "{}")
        self.assert_failure("Obsolete modules in per-module declaration data: "
                            + ", ".join(self.obsolete_modules))
        for name in self.obsolete_modules:
            self.assertEqual(self.module_data(name).read_text(), "{}")

    def test_missing_intermediate_data(self):
        for name in ("Complexity", "Complexity.Current"):
            with self.subTest(module=name):
                self.module_data(name).unlink()
                self.assert_failure("Missing modules in per-module declaration data: " + name)
                self.write(self.module_data(name), "{}")

    def test_obsolete_database_modules_only(self):
        with closing(sqlite3.connect(self.database)) as db, db:
            db.executemany("INSERT INTO modules (name) VALUES (?)",
                           [(name,) for name in reversed(self.obsolete_modules)])
        before = self.database.read_bytes()
        self.assert_failure("Obsolete modules in documentation database: "
                            + ", ".join(self.obsolete_modules))
        self.assertEqual(self.database.read_bytes(), before)

    def test_missing_database_modules(self):
        for name in ("Complexity", "Complexity.Current"):
            with self.subTest(module=name):
                with closing(sqlite3.connect(self.database)) as db, db:
                    db.execute("DELETE FROM modules WHERE name = ?", (name,))
                self.assert_failure("Missing modules in documentation database: " + name)
                with closing(sqlite3.connect(self.database)) as db, db:
                    db.execute("INSERT INTO modules (name) VALUES (?)", (name,))

    def test_missing_database_is_not_created(self):
        self.database.unlink()
        self.assert_failure("Missing documentation database: api-docs.db")
        self.assertFalse(self.database.exists())

    def test_invalid_database_fails(self):
        self.database.write_bytes(b"not a database")
        with self.assertRaises(sqlite3.DatabaseError):
            self.check()

    def artifact_bytes(self):
        return {str(path.relative_to(self.docs.parent)): path.read_bytes()
                for path in self.docs.parent.rglob("*") if path.is_file()}

    def test_wal_database_does_not_create_sidecars(self):
        with closing(sqlite3.connect(self.database)) as db:
            db.execute("PRAGMA journal_mode=WAL")
        self.check()  # Also writes the fixture's assembled index before the snapshot.
        self.assertFalse(self.database.with_name("api-docs.db-wal").exists())
        self.assertFalse(self.database.with_name("api-docs.db-shm").exists())
        before = self.artifact_bytes()
        self.check()
        self.assertEqual(self.artifact_bytes(), before)

    def test_committed_wal_rows_are_checked_without_mutation(self):
        # Keep a connection open so committed changes remain solely in the WAL.
        with closing(sqlite3.connect(self.database)) as db:
            db.execute("PRAGMA journal_mode=WAL")
            db.execute("PRAGMA wal_autocheckpoint=0")
            self.check()
            db.execute("INSERT INTO modules (name) VALUES ('Complexity.Removed')")
            db.commit()
            before = self.artifact_bytes()
            self.assert_failure("Obsolete modules in documentation database: Complexity.Removed")
            self.assertEqual(self.artifact_bytes(), before)
            db.execute("DELETE FROM modules WHERE name IN ('Complexity.Removed', 'Complexity')")
            db.commit()
            before = self.artifact_bytes()
            self.assert_failure("Missing modules in documentation database: Complexity")
            self.assertEqual(self.artifact_bytes(), before)

    def test_config_only_does_not_inspect_output(self):
        with patch.object(check_docs, "check_config") as config, \
                patch.object(check_docs, "check_output") as output, \
                patch("sys.argv", ["check_docs.py", "--config-only"]), \
                redirect_stdout(io.StringIO()):
            check_docs.main()
        config.assert_called_once_with()
        output.assert_not_called()

    def test_obsolete_index_only(self):
        for name in reversed(self.obsolete_modules):
            self.index["modules"][name] = {}
        self.assert_failure("Obsolete modules in search index: " + ", ".join(self.obsolete_modules))

    def test_obsolete_pages_only(self):
        for name in reversed(self.obsolete_modules):
            self.write(self.page(name))
        self.assert_failure("Obsolete module pages: " + ", ".join(self.obsolete_modules))
        for name in self.obsolete_modules:
            self.assertTrue(self.page(name).is_file())

    def test_obsolete_index_and_page(self):
        name = self.obsolete_modules[0]
        self.index["modules"][name] = {}
        self.write(self.page(name))
        self.assert_failure("Obsolete modules in search index: " + name)
        del self.index["modules"][name]
        self.assert_failure("Obsolete module pages: " + name)

    def test_missing_current_module(self):
        del self.index["modules"]["Complexity.Current"]
        self.assert_failure("Missing module in search index: Complexity.Current")

    def test_missing_current_page(self):
        self.page("Complexity.Current").unlink()
        self.assert_failure("Missing module page: Complexity.Current")

    def test_missing_root_module(self):
        del self.index["modules"]["Complexity"]
        self.assert_failure("Missing module in search index: Complexity")

    def test_missing_root_page(self):
        self.page("Complexity").unlink()
        self.assert_failure("Missing module page: Complexity")

    def test_missing_theorem_anchor(self):
        self.write(self.page("Complexity.Current"))
        self.assert_failure("Missing theorem anchor: Cslib.Complexity.CookLevin.SAT_npComplete")

    def test_broken_internal_link_in_complexity_page_fails(self):
        self.write(self.page("Complexity"), '<a href="./Missing/Page.html">bad</a>')
        self.assert_failure("Broken internal link in Complexity.html: Missing/Page.html")

    def test_broken_internal_link_in_navbar_fails(self):
        self.write(self.docs / "navbar.html", '<div class="nav_link"><a href="./Lean/Gone.html">Gone</a></div>')
        self.assert_failure("Broken internal link in navbar.html: Lean/Gone.html")

    def test_broken_internal_link_in_retained_dependency_page_fails(self):
        self.index["modules"]["Std.Linked"] = {"importedBy": ["Complexity.Current"], "url": "./Std/Linked.html"}
        self.write(self.page("Std.Linked"), '<a href="./LinkedElsewhere.html">bad</a>')
        self.assert_failure("Broken internal link in Std/Linked.html: Std/LinkedElsewhere.html")

    def test_outside_root_link_fails_even_when_sibling_file_exists(self):
        self.write(self.docs.parent / "outside.html", "<div>sibling outside docs root</div>")
        self.write(self.page("Complexity"), '<a href="../outside.html">escape</a>')
        self.assert_failure("Broken internal link in Complexity.html: ../outside.html")
        self.write(self.page("Complexity"), '<a href="/outside.html">root-escape</a>')
        self.assert_failure("Broken internal link in Complexity.html: /outside.html")

    def test_protocol_relative_external_link_passes(self):
        self.write(
            self.page("Complexity"),
            '<a href="//example.org/documentation.html">protocol-relative</a>',
        )
        self.check()

    def test_html_escaped_numeric_entity_in_href_path_resolves(self):
        self.write(self.docs / "A'B.html", "<div>target</div>")
        self.write(
            self.page("Complexity"),
            '<a href="./A&#39;B.html#frag">entity-link</a>',
        )
        self.check()

    def test_trim_externalizes_dependencies_and_filters_index(self):
        self.index["modules"]["Init.Prelude"] = {"importedBy": ["Complexity.Current"], "url": "./Init/Prelude.html"}
        self.index["modules"]["Lean"] = {"importedBy": [], "url": "./Lean.html"}
        self.index["modules"]["Std.Linked"] = {"importedBy": [], "url": "./Std/Linked.html"}
        self.index["modules"]["Std.LinkedElsewhere"] = {"importedBy": [], "url": "./Std/LinkedElsewhere.html"}
        self.index["modules"]["Std.FromCslib"] = {"importedBy": [], "url": "./Std/FromCslib.html"}
        self.index["modules"]["Mathlib.Data.List"] = {"importedBy": ["Complexity.Current"], "url": "./Mathlib/Data/List.html"}
        self.index["modules"]["Lake.Unused"] = {"importedBy": [], "url": "./Lake/Unused.html"}
        self.index["modules"]["Lean.Unused"] = {"importedBy": ["Lake.Unused", "Lean"], "url": "./Lean/Unused.html"}
        self.index["modules"]["Cslib.Base"] = {"importedBy": ["Complexity.Current"], "url": "./Cslib/Base.html"}
        self.index["declarations"]["Nat"] = {"docLink": "./Init/Prelude.html#Nat", "kind": "inductive"}
        self.index["declarations"]["List.map"] = {"docLink": "./Mathlib/Data/List.html#List.map", "kind": "def"}
        self.index["declarations"]["Cslib.Base.foo"] = {"docLink": "./Cslib/Base.html#Cslib.Base.foo", "kind": "def"}
        self.index["instances"] = {
            "Inhabited": ["Nat", "Cslib.Base.foo"],
            "UnusedClass": ["Nat"],
        }
        self.index["instancesFor"] = {
            "Unit": ["Cslib.Base.foo"],
            "Nat": ["Nat"],
        }
        for mod in ("Std.LinkedElsewhere", "Std.FromCslib", "Lake.Unused", "Lean.Unused"):
            self.write(self.page(mod), f'<div id="{mod}">core</div>')
        self.write(
            self.page("Init.Prelude"),
            '<div id="Nat"></div><code>import <a href=".././Lean.html">Lean</a></code>',
        )
        self.write(
            self.page("Lean"),
            '<div class="imports"><details><summary>Imports</summary><ul>'
            '<li><a href="./Init/Prelude.html">Init.Prelude</a></li>'
            '<li><a href="./Lean/Unused.html">Lean.Unused</a></li>'
            '</ul></details></div><main></main>',
        )
        self.write(
            self.page("Std.Linked"),
            '<div id="Std.Linked"></div><a href="./LinkedElsewhere.html#Std.LinkedElsewhere">transitive core</a>',
        )
        self.write(
            self.page("Mathlib.Data.List"),
            '<div id="List.map"></div>',
        )
        self.write(
            self.page("Cslib.Base"),
            '<code><a href=".././Std/FromCslib.html">Std/FromCslib.lean</a></code> '
            '<code><a href=".././Cslib/Unimported.html">Cslib/Unimported.lean</a></code>',
        )
        self.write(
            self.page("Complexity"),
            '<a href="./Std/Linked.html#Std.Linked">linked core</a> '
            '<a href="./Mathlib/Data/List.html#List.map">mathlib decl</a> '
            '<a href="./Init/Prelude.html#Eq.rec">kernel recursor</a>',
        )
        self.write(
            self.docs / "navbar.html",
            '<div class="nav_link"><a href="./">index</a></div>'
            '<details class="nav_sect" data-path="./Complexity.html"><summary>Complexity (<a href="./Complexity.html">file</a>)</summary>'
            '<div class="nav_link"><a href="./Complexity/Current.html">Current</a></div></details>'
            '<details class="nav_sect" data-path="./Init.html"><summary>Init</summary>'
            '<div class="nav_link"><a href="./Init/Prelude.html">Prelude</a></div></details>'
            '<details class="nav_sect" data-path="./Lake.html"><summary>Lake (<a href="./Lake/Unused.html">file</a>)</summary>'
            '<div class="nav_link"><a href="./Lake/Unused.html">Unused</a></div></details>',
        )
        self.write(self.docs / "declarations/declaration-data.bmp", json.dumps(self.index))

        check_docs.trim_output()
        with redirect_stdout(io.StringIO()):
            check_docs.check_output()

        for ext_mod in ("Init.Prelude", "Lean", "Std.Linked", "Std.LinkedElsewhere",
                        "Std.FromCslib", "Mathlib.Data.List", "Lake.Unused", "Lean.Unused"):
            self.assertFalse(self.page(ext_mod).exists(), ext_mod)
        self.assertTrue(self.page("Complexity").is_file())
        self.assertTrue(self.page("Cslib.Base").is_file())
        self.assertEqual(
            self.page("Cslib.Base").read_text(),
            f'<code><a href="{check_docs.MATHLIB_DOCS_URL}Std/FromCslib.html">Std/FromCslib.lean</a></code> '
            '<code>Cslib/Unimported.lean</code>',
        )
        self.assertEqual(
            self.page("Complexity").read_text(),
            f'<a href="{check_docs.MATHLIB_DOCS_URL}Std/Linked.html#Std.Linked">linked core</a> '
            f'<a href="{check_docs.MATHLIB_DOCS_URL}Mathlib/Data/List.html#List.map">mathlib decl</a> '
            f'<a href="{check_docs.MATHLIB_DOCS_URL}Init/Prelude.html#Eq.rec">kernel recursor</a>',
        )
        trimmed = json.loads((self.docs / "declarations/declaration-data.bmp").read_text())
        self.assertEqual(set(trimmed["modules"]), {"Complexity", "Complexity.Current", "Cslib.Base"})
        self.assertNotIn("Nat", trimmed["declarations"])
        self.assertNotIn("List.map", trimmed["declarations"])
        self.assertIn("Cslib.Base.foo", trimmed["declarations"])
        self.assertEqual(trimmed["instances"], {"Inhabited": ["Cslib.Base.foo"]})
        self.assertEqual(trimmed["instancesFor"], {"Unit": ["Cslib.Base.foo"]})
        navbar = (self.docs / "navbar.html").read_text()
        self.assertNotIn("Init/Prelude.html", navbar)
        self.assertNotIn("Lake/Unused.html", navbar)
        self.assertIn("Complexity/Current.html", navbar)

        # Repeated trimming on an already-trimmed tree is idempotent.
        check_docs.trim_output()
        with redirect_stdout(io.StringIO()):
            check_docs.check_output()

    def test_trim_rejects_broken_dependency_page_or_anchor(self):
        self.write(self.docs / "declarations/declaration-data.bmp", json.dumps(self.index))
        self.write(self.page("Complexity"), '<a href="./Init/Missing.html">unindexed page</a>')
        with self.assertRaises(ValueError) as error:
            check_docs.trim_output()
        self.assertEqual(
            str(error.exception),
            "Broken dependency link in Complexity.html: Init/Missing.html",
        )

        self.index["modules"]["Mathlib.Data.List"] = {
            "importedBy": ["Complexity.Current"], "url": "./Mathlib/Data/List.html",
        }
        self.write(self.docs / "declarations/declaration-data.bmp", json.dumps(self.index))
        self.write(self.page("Complexity"), '<a href="./Mathlib/Data/List.html#List.map">missing page</a>')
        with self.assertRaises(ValueError) as error:
            check_docs.trim_output()
        self.assertEqual(
            str(error.exception),
            "Broken dependency link in Complexity.html: Mathlib/Data/List.html",
        )

        self.write(self.page("Mathlib.Data.List"), '<div id="List.filter"></div>')
        self.write(self.page("Complexity"), '<a href="./Mathlib/Data/List.html#List.renamed">missing anchor</a>')
        with self.assertRaises(ValueError) as error:
            check_docs.trim_output()
        self.assertEqual(
            str(error.exception),
            "Broken dependency anchor in Complexity.html: Mathlib/Data/List.html#List.renamed",
        )

    def test_check_output_rejects_broken_external_dependency_link_or_anchor(self):
        (self.docs.parent / check_docs.EXTERNAL_TARGETS_FILE).write_text(json.dumps({
            "source": "published",
            "pages": ["Mathlib/Data/List.html"],
            "anchors": {"Mathlib/Data/List.html": ["List.map"]},
        }))
        self.write(
            self.page("Complexity"),
            f'<a href="{check_docs.MATHLIB_DOCS_URL}Mathlib/Gone.html">gone</a>',
        )
        self.assert_failure("Broken external dependency link in Complexity.html: Mathlib/Gone.html")

        self.write(
            self.page("Complexity"),
            f'<a href="{check_docs.MATHLIB_DOCS_URL}Complexity/Current.html">local as mathlib</a>',
        )
        self.assert_failure(
            "Broken external dependency link in Complexity.html: Complexity/Current.html"
        )

        self.write(
            self.page("Complexity"),
            f'<a href="{check_docs.MATHLIB_DOCS_URL}Mathlib/Data/List.html#List.renamed">renamed</a>',
        )
        self.assert_failure(
            "Broken external dependency anchor in Complexity.html: Mathlib/Data/List.html#List.renamed"
        )

    def test_legacy_local_only_external_targets_manifest_is_upgraded_or_rejected(self):
        legacy_manifest = self.docs.parent / check_docs.EXTERNAL_TARGETS_FILE
        legacy_manifest.write_text(json.dumps({
            "pages": [
                "Mathlib/LinearAlgebra/Matrix/Defs.html",
                "Mathlib/Tactic/TautoSet.html",
            ],
            "anchors": {
                "Mathlib/LinearAlgebra/Matrix/Defs.html": ["Matrix.ofArray"],
                "Mathlib/Tactic/TautoSet.html": ["Mathlib.Tactic.TautoSet.specialize_all"],
            },
        }))
        self.published_index = {
            "modules": {
                "Mathlib.LinearAlgebra.Matrix.Defs": {},
                "Mathlib.LinearAlgebra.Matrix.Array": {},
                "Mathlib.Tactic.TautoSet": {},
            },
            "declarations": {
                "Matrix.ofArray": {
                    "docLink": "./Mathlib/LinearAlgebra/Matrix/Array.html#Matrix.ofArray",
                },
            },
        }
        self.write(
            self.page("Complexity"),
            f'<a href="{check_docs.MATHLIB_DOCS_URL}Mathlib/LinearAlgebra/Matrix/Defs.html#Matrix.ofArray">ofArray</a> '
            f'<a href="{check_docs.MATHLIB_DOCS_URL}Mathlib/Tactic/TautoSet.html#Mathlib.Tactic.TautoSet.specialize_all">specialize_all</a>',
        )
        self.write(self.docs / "declarations/declaration-data.bmp", json.dumps(self.index))

        # Running check_output directly on an old-trimmed tree does not trust the legacy manifest.
        with patch.object(
            check_docs, "fetch_published_external_index", wraps=self.default_published_index
        ) as fetch_mock:
            self.assert_failure(
                "Broken external dependency anchor in Complexity.html: "
                "Mathlib/LinearAlgebra/Matrix/Defs.html#Matrix.ofArray"
            )
            self.assertEqual(fetch_mock.call_count, 1)

        # Running trim_output then check_output on an old-trimmed tree fetches the published
        # index, remaps/repairs the links, and upgrades the manifest to source="published".
        with patch.object(
            check_docs, "fetch_published_external_index", wraps=self.default_published_index
        ) as fetch_mock:
            check_docs.trim_output()
            with redirect_stdout(io.StringIO()):
                check_docs.check_output()
            self.assertEqual(fetch_mock.call_count, 1)

        upgraded = json.loads(legacy_manifest.read_text())
        self.assertEqual(upgraded.get("source"), "published")
        self.assertEqual(
            self.page("Complexity").read_text(),
            f'<a href="{check_docs.MATHLIB_DOCS_URL}Mathlib/LinearAlgebra/Matrix/Array.html#Matrix.ofArray">ofArray</a> '
            f'<a href="{check_docs.MATHLIB_DOCS_URL}Mathlib/Tactic/TautoSet.html">specialize_all</a>',
        )

    def test_trim_redirects_omitted_recursors_to_the_documented_type(self):
        self.index["modules"]["Init.Core"] = {}
        self.index["declarations"]["Sum"] = {
            "docLink": "./Init/Core.html#Sum", "kind": "inductive",
        }
        self.index["declarations"]["Prod"] = {
            "docLink": "./Init/Core.html#Prod", "kind": "structure",
        }
        self.write(self.page("Init.Core"), '<div id="Sum"></div><div id="Prod"></div>')
        prefixes = ("./", check_docs.API_DOCS_URL, check_docs.MATHLIB_DOCS_URL)
        links = [f'<a href="{prefix}Init/Core.html#{name}.rec">{name}.rec</a>'
                 for prefix in prefixes for name in ("Sum", "Prod")]
        self.write(self.page("Complexity"), "\n".join(links))
        self.write(self.docs / "declarations/declaration-data.bmp", json.dumps(self.index))

        check_docs.trim_output()
        with redirect_stdout(io.StringIO()):
            check_docs.check_output()
        expected = "\n".join(
            f'<a href="{check_docs.MATHLIB_DOCS_URL}Init/Core.html#{name}">{name}.rec</a>'
            for _ in prefixes for name in ("Sum", "Prod")
        )
        self.assertEqual(self.page("Complexity").read_text(), expected)
        check_docs.trim_output()
        self.assertEqual(self.page("Complexity").read_text(), expected)

    def test_trim_recursor_fallback_rejects_unproved_targets(self):
        for module in ("Init.Core", "Init.Other"):
            self.index["modules"][module] = {}
            self.write(self.page(module), '<div id="Sum"></div><div id="ordinary"></div>')
        self.index["declarations"]["Sum"] = {
            "docLink": "./Init/Core.html#Sum", "kind": "inductive",
        }
        self.index["declarations"]["ordinary"] = {
            "docLink": "./Init/Core.html#ordinary", "kind": "def",
        }
        self.write(self.docs / "declarations/declaration-data.bmp", json.dumps(self.index))
        for target in ("Init/Core.html#Missing.rec", "Init/Core.html#ordinary.rec",
                       "Init/Core.html#Sum.missing", "Init/Other.html#Sum.rec"):
            with self.subTest(target=target):
                self.write(self.page("Complexity"), f'<a href="./{target}">bad</a>')
                with self.assertRaisesRegex(ValueError, "Broken dependency anchor"):
                    check_docs.trim_output()

    def test_trim_preserves_a_documented_recursor_anchor(self):
        self.index["modules"]["Init.Core"] = {}
        self.index["declarations"]["Sum"] = {
            "docLink": "./Init/Core.html#Sum", "kind": "inductive",
        }
        self.write(self.page("Init.Core"), '<div id="Sum"></div><div id="Sum.rec"></div>')
        self.write(self.page("Complexity"), '<a href="./Init/Core.html#Sum.rec">rec</a>')
        self.write(self.docs / "declarations/declaration-data.bmp", json.dumps(self.index))
        check_docs.trim_output()
        self.assertEqual(self.page("Complexity").read_text(),
                         f'<a href="{check_docs.MATHLIB_DOCS_URL}Init/Core.html#Sum.rec">rec</a>')

    def test_trim_remaps_moved_and_falls_back_for_omitted_published_declarations(self):
        self.index["modules"]["Mathlib.LinearAlgebra.Matrix.Defs"] = {
            "importedBy": ["Complexity.Current"],
            "url": "./Mathlib/LinearAlgebra/Matrix/Defs.html",
        }
        self.index["modules"]["Mathlib.Tactic.TautoSet"] = {
            "importedBy": ["Complexity.Current"],
            "url": "./Mathlib/Tactic/TautoSet.html",
        }
        self.index["declarations"]["Matrix.ofArray"] = {
            "docLink": "./Mathlib/LinearAlgebra/Matrix/Defs.html#Matrix.ofArray",
            "kind": "def",
        }
        self.index["declarations"]["Mathlib.Tactic.TautoSet.specialize_all"] = {
            "docLink": "./Mathlib/Tactic/TautoSet.html#Mathlib.Tactic.TautoSet.specialize_all",
            "kind": "def",
        }
        self.write(
            self.page("Mathlib.LinearAlgebra.Matrix.Defs"),
            '<div id="Matrix.ofArray"></div>',
        )
        self.write(
            self.page("Mathlib.Tactic.TautoSet"),
            '<div id="Mathlib.Tactic.TautoSet.specialize_all"></div>',
        )
        self.published_index = {
            "modules": {
                "Mathlib.LinearAlgebra.Matrix.Defs": {},
                "Mathlib.LinearAlgebra.Matrix.Array": {},
                "Mathlib.Tactic.TautoSet": {},
            },
            "declarations": {
                "Matrix.ofArray": {
                    "docLink": "./Mathlib/LinearAlgebra/Matrix/Array.html#Matrix.ofArray",
                },
            },
        }
        self.write(
            self.page("Complexity"),
            '<a href="./Mathlib/LinearAlgebra/Matrix/Defs.html#Matrix.ofArray">ofArray</a> '
            '<a href="./Mathlib/Tactic/TautoSet.html#Mathlib.Tactic.TautoSet.specialize_all">specialize_all</a>',
        )
        self.write(self.docs / "declarations/declaration-data.bmp", json.dumps(self.index))

        check_docs.trim_output()
        with redirect_stdout(io.StringIO()):
            check_docs.check_output()

        self.assertEqual(
            self.page("Complexity").read_text(),
            f'<a href="{check_docs.MATHLIB_DOCS_URL}Mathlib/LinearAlgebra/Matrix/Array.html#Matrix.ofArray">ofArray</a> '
            f'<a href="{check_docs.MATHLIB_DOCS_URL}Mathlib/Tactic/TautoSet.html">specialize_all</a>',
        )

    def test_check_output_rejects_local_only_or_unremapped_published_anchor(self):
        self.index["modules"]["Mathlib.LinearAlgebra.Matrix.Defs"] = {}
        self.index["modules"]["Mathlib.Tactic.TautoSet"] = {}
        self.write(
            self.page("Mathlib.LinearAlgebra.Matrix.Defs"),
            '<div id="Matrix.ofArray"></div>',
        )
        self.write(
            self.page("Mathlib.Tactic.TautoSet"),
            '<div id="Mathlib.Tactic.TautoSet.specialize_all"></div>',
        )
        self.write(self.module_data("Mathlib.LinearAlgebra.Matrix.Defs"), "{}")
        self.write(self.module_data("Mathlib.Tactic.TautoSet"), "{}")
        self.published_index = {
            "modules": {
                "Mathlib.LinearAlgebra.Matrix.Defs": {},
                "Mathlib.LinearAlgebra.Matrix.Array": {},
                "Mathlib.Tactic.TautoSet": {},
            },
            "declarations": {
                "Matrix.ofArray": {
                    "docLink": "./Mathlib/LinearAlgebra/Matrix/Array.html#Matrix.ofArray",
                },
            },
        }
        self.write(
            self.page("Complexity"),
            f'<a href="{check_docs.MATHLIB_DOCS_URL}Mathlib/LinearAlgebra/Matrix/Defs.html#Matrix.ofArray">stale moved</a>',
        )
        self.assert_failure(
            "Broken external dependency anchor in Complexity.html: "
            "Mathlib/LinearAlgebra/Matrix/Defs.html#Matrix.ofArray"
        )

        self.write(
            self.page("Complexity"),
            f'<a href="{check_docs.MATHLIB_DOCS_URL}Mathlib/Tactic/TautoSet.html#Mathlib.Tactic.TautoSet.specialize_all">omitted</a>',
        )
        self.assert_failure(
            "Broken external dependency anchor in Complexity.html: "
            "Mathlib/Tactic/TautoSet.html#Mathlib.Tactic.TautoSet.specialize_all"
        )

    def test_url_query_preservation_and_api_docs_dependency_normalization(self):
        self.index["modules"]["Mathlib.Data.List"] = {
            "importedBy": ["Complexity.Current"], "url": "./Mathlib/Data/List.html",
        }
        self.index["declarations"]["List.map"] = {
            "docLink": "./Mathlib/Data/List.html#List.map", "kind": "def",
        }
        self.write(self.page("Mathlib.Data.List"), '<div id="List.map"></div>')
        self.write(
            self.page("Complexity"),
            '<a href="./Mathlib/Data/List.html?foo=1#List.map">rel query</a> '
            f'<a href="{check_docs.MATHLIB_DOCS_URL}Mathlib/Data/List.html?bar=2#List.map">abs mathlib query</a> '
            f'<a href="{check_docs.API_DOCS_URL}Mathlib/Data/List.html?baz=3#List.map">api docs dep</a>',
        )
        self.write(self.docs / "declarations/declaration-data.bmp", json.dumps(self.index))

        check_docs.trim_output()
        with redirect_stdout(io.StringIO()):
            check_docs.check_output()

        self.assertEqual(
            self.page("Complexity").read_text(),
            f'<a href="{check_docs.MATHLIB_DOCS_URL}Mathlib/Data/List.html?foo=1#List.map">rel query</a> '
            f'<a href="{check_docs.MATHLIB_DOCS_URL}Mathlib/Data/List.html?bar=2#List.map">abs mathlib query</a> '
            f'<a href="{check_docs.MATHLIB_DOCS_URL}Mathlib/Data/List.html?baz=3#List.map">api docs dep</a>',
        )

        self.write(
            self.page("Complexity"),
            f'<a href="{check_docs.API_DOCS_URL}Mathlib/Data/List.html">unrewritten api docs dep</a>',
        )
        self.assert_failure("Broken internal link in Complexity.html: Mathlib/Data/List.html")


class CheckGuideLinksTests(unittest.TestCase):
    page = "Complexity/Reduction.html"

    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        root_patch = patch.object(check_docs, "ROOT", self.root)
        root_patch.start()
        self.addCleanup(root_patch.stop)
        self.docs = self.root / "docbuild/.lake/build/doc"
        self.guide = self.root / "guide/.lake/build/site/html-multi"
        (self.docs / "Complexity").mkdir(parents=True)
        (self.docs / "index.html").write_text("")
        (self.docs / self.page).write_text(
            '<div class="decl" id="Cslib.Complexity.NPComplete"></div>'
            '<div class="decl" id="Cslib.«term_&lt;=p_»"></div>')
        self.guide.mkdir(parents=True)
        pub_patch = patch.object(check_docs, "fetch_published_external_index", return_value=None)
        pub_patch.start()
        self.addCleanup(pub_patch.stop)

    def link(self, target):
        return f'<a href="{check_docs.API_DOCS_URL}{target}">x</a>'

    def check(self, *targets):
        (self.guide / "index.html").write_text("".join(map(self.link, targets)))
        with redirect_stdout(io.StringIO()):
            check_docs.check_guide_links()

    def assert_failure(self, message, *targets):
        with self.assertRaises(ValueError) as error:
            self.check(*targets)
        self.assertEqual(str(error.exception), message)

    def test_existing_pages_and_anchors_pass(self):
        self.check("", f"{self.page}#Cslib.Complexity.NPComplete",
                   f"{self.page}#Cslib.«term_&lt;=p_»", "abstracts/catalogue.pdf")

    def test_unknown_abstract_fails(self):
        self.assert_failure("Guide links to an unknown formal abstract: abstracts/gone.pdf",
                            "abstracts/gone.pdf")

    def test_staged_abstract_requires_file(self):
        (self.docs / "abstracts").mkdir()
        self.assert_failure("Guide links to a missing documentation page: abstracts/catalogue.pdf",
                            "abstracts/catalogue.pdf")
        (self.docs / "abstracts/catalogue.pdf").write_bytes(b"%PDF")
        self.check("abstracts/catalogue.pdf")

    def test_missing_page(self):
        self.assert_failure("Guide links to a missing documentation page: Complexity/Gone.html",
                            "Complexity/Gone.html#Cslib.Complexity.NPComplete")

    def test_missing_anchor(self):
        self.assert_failure(
            f"Guide links to a missing documentation anchor: {self.page}#Cslib.Complexity.NP",
            f"{self.page}#Cslib.Complexity.NP")

    def test_external_mathlib_links_and_anchors(self):
        (self.docs.parent / check_docs.EXTERNAL_TARGETS_FILE).write_text(json.dumps({
            "source": "published",
            "pages": ["Mathlib/Data/Finset/Defs.html"],
            "anchors": {"Mathlib/Data/Finset/Defs.html": ["Finset"]},
        }))
        (self.guide / "index.html").write_text(
            f'<a href="{check_docs.MATHLIB_DOCS_URL}Mathlib/Data/Finset/Defs.html#Finset">Finset</a>'
        )
        with redirect_stdout(io.StringIO()):
            check_docs.check_guide_links()

        (self.guide / "index.html").write_text(
            f'<a href="{check_docs.MATHLIB_DOCS_URL}Mathlib/Gone.html#Finset">Gone</a>'
        )
        with self.assertRaises(ValueError) as error:
            check_docs.check_guide_links()
        self.assertEqual(
            str(error.exception),
            "Guide links to a missing documentation page: Mathlib/Gone.html",
        )

        (self.guide / "index.html").write_text(
            f'<a href="{check_docs.MATHLIB_DOCS_URL}Mathlib/Data/Finset/Defs.html#Finset.Renamed">Renamed</a>'
        )
        with self.assertRaises(ValueError) as error:
            check_docs.check_guide_links()
        self.assertEqual(
            str(error.exception),
            "Guide links to a missing documentation anchor: Mathlib/Data/Finset/Defs.html#Finset.Renamed",
        )

    def test_missing_guide(self):
        (self.guide).rmdir()
        with self.assertRaises(ValueError) as error:
            check_docs.check_guide_links()
        self.assertEqual(str(error.exception), "Missing guide output")


class CheckConfigTests(unittest.TestCase):
    """The guide and the API documentation share the library's toolchain and package checkouts."""

    toolchain = "leanprover/lean4:v4.36.0-rc1"

    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        root_patch = patch.object(check_docs, "ROOT", self.root)
        root_patch.start()
        self.addCleanup(root_patch.stop)
        bibliography = "@book{AroraBarak09,\n}\n"
        (self.root / "references.bib").write_text(bibliography)
        (self.root / "docbuild/docs").mkdir(parents=True)
        (self.root / "docbuild/docs/references.bib").write_text(bibliography)
        (self.root / "guide").mkdir()
        self.manifests = {
            "": [self.package("cslib", "a")],
            "docbuild": [self.package("doc-gen4", "d", "v4.36.0-rc1"), self.package("cslib", "a"),
                         self.package("MD4Lean", "m")],
            "guide": [self.package("verso", "v", "v4.36.0-rc1"), self.package("cslib", "a"),
                      self.package("MD4Lean", "m")],
        }
        self.generators = {"docbuild": "doc-gen4", "guide": "verso"}
        for project, generator in self.generators.items():
            (self.root / project / "lean-toolchain").write_text(self.toolchain + "\n")
            (self.root / project / "lakefile.toml").write_text(
                f'[[require]]\nname = "{generator}"\nrev = "v4.36.0-rc1"\n')
        (self.root / "lean-toolchain").write_text(self.toolchain + "\n")

    @staticmethod
    def package(name, rev, input_rev="main"):
        return {"name": name, "type": "git", "url": f"https://example.com/{name}", "rev": rev,
                "inputRev": input_rev, "subDir": None}

    def write_manifests(self):
        for project, packages in self.manifests.items():
            (self.root / project / "lake-manifest.json").write_text(
                json.dumps({"packages": packages}))

    def check(self):
        self.write_manifests()
        check_docs.check_config()

    def assert_failure(self, message):
        with self.assertRaises(ValueError) as error:
            self.check()
        self.assertEqual(str(error.exception), message)

    def test_consistent_projects_pass(self):
        self.check()

    def test_guide_lockfile_follows_the_library(self):
        self.manifests["guide"][1]["rev"] = "b"
        self.assert_failure(
            'Guide lockfile differs for cslib: rev is "b" in guide/lake-manifest.json but "a" in '
            "lake-manifest.json; update guide/lake-manifest.json to match the root pin")

    def test_root_pin_bump_requires_documentation_lockfiles(self):
        # #1372 moved the root cslib pin without the docs projects' lockfiles (#1397).
        self.manifests[""][0]["rev"] = "b"
        self.assert_failure(
            'Documentation lockfile differs for cslib: rev is "a" in docbuild/lake-manifest.json '
            'but "b" in lake-manifest.json; update docbuild/lake-manifest.json to match the '
            "root pin")

    def test_root_dependency_must_be_locked(self):
        self.manifests[""].append(self.package("mathlib", "x"))
        self.assert_failure(
            "Documentation lockfile omits mathlib; copy its entry from lake-manifest.json into "
            "docbuild/lake-manifest.json")

    def test_command_line_reports_drift(self):
        self.manifests[""][0]["rev"] = "b"
        stderr = io.StringIO()
        with patch("sys.argv", ["check_docs.py", "--config-only"]), \
                patch("sys.stderr", stderr), self.assertRaises(SystemExit) as raised:
            self.write_manifests()
            check_docs.main()
        self.assertEqual(raised.exception.code, 1)
        self.assertIn("Documentation check failed: Documentation lockfile differs for cslib: rev",
                      stderr.getvalue())

    def test_verso_tag_follows_the_toolchain(self):
        (self.root / "guide/lakefile.toml").write_text(
            '[[require]]\nname = "verso"\nrev = "v4.35.0"\n')
        self.assert_failure("verso tag must match the Lean version")

    def test_guide_lockfile_has_a_current_verso_tag(self):
        self.manifests["guide"][0]["inputRev"] = "v4.35.0"
        self.assert_failure("Guide lockfile has a stale verso tag")

    def test_shared_packages_agree(self):
        self.manifests["guide"][2]["rev"] = "n"
        self.assert_failure("Guide and documentation lockfiles differ for MD4Lean: rev")


if __name__ == "__main__":
    unittest.main()
