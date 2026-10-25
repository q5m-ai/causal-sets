"""Real pinned-Lean adversarial tests for both axiom-audit entry points.

Unlike test_formal_check's fake Lake, these execute the actual audit bodies.
No mathlib download/build is needed. Skipped when Lean 4.19.0 is unavailable.
"""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent
FORMAL = ROOT / "formal"
PRELUDE = "import Lean.Elab.Command\nimport Lean.Util.CollectAxioms\n"


class FormalAxiomTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        local = FORMAL / ".tools/lean-4.19.0-linux/bin/lean"
        cls.lean = str(local) if local.is_file() else shutil.which("lean")
        if not cls.lean:
            raise unittest.SkipTest("install the pinned Lean toolchain for real axiom tests")
        version = subprocess.run([cls.lean, "--version"], capture_output=True,
                                 text=True, cwd=FORMAL, check=True).stdout
        if "version 4.19.0," not in version:
            raise unittest.SkipTest("real axiom tests require pinned Lean 4.19.0")
        shell = (FORMAL / "check.sh").read_text()
        source = shell.split('cat >> "$audit_source" <<\'LEAN\'\n', 1)[1].split("\nLEAN", 1)[0]
        aggregate = (FORMAL / "Audit.lean").read_text()
        aggregate = "run_cmd" + aggregate.split("run_cmd", 1)[1].split("-- These are", 1)[0]
        cls.audits = {"source": source, "aggregate": aggregate}

    def run_lean(self, content):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Fixture.lean"
            path.write_text(PRELUDE + content)
            return subprocess.run([self.lean, "-DwarningAsError=true", str(path)],
                                  cwd=FORMAL, capture_output=True, text=True, timeout=60,
                                  env={**os.environ, "LEAN_NUM_THREADS": "1"})

    def check_both(self, fixture, succeeds, error=None):
        fixture += "\nnamespace BoundaryDraft\ntheorem clean : True := True.intro\nend BoundaryDraft\n"
        for name, audit in self.audits.items():
            with self.subTest(audit=name):
                result = self.run_lean(fixture + audit)
                output = result.stdout + result.stderr
                self.assertEqual(result.returncode == 0, succeeds, output)
                if error:
                    self.assertIn(error, output)

    def test_allowed_axioms_and_unused_private_axiom(self):
        self.check_both("""
namespace BoundaryDraft
private axiom unused : False
theorem ext (p q : Prop) (h : p ↔ q) : p = q := propext h
noncomputable def choice {α : Sort u} (h : Nonempty α) : α := Classical.choice h
end BoundaryDraft
""", True)

    def test_rejects_public_axiom(self):
        self.check_both("axiom BoundaryDraft.forbidden : False\n", False, "Unexpected axiom")

    def test_rejects_private_transitive_dependency(self):
        self.check_both("""
namespace BoundaryDraft
private axiom forbidden : False
private theorem helper : False := forbidden
theorem exposed : False := helper
end BoundaryDraft
""", False, "Unexpected axiom")

    def test_rejects_definition_and_opaque_dependencies(self):
        for declaration in ("noncomputable def exposed", "opaque exposed"):
            with self.subTest(declaration=declaration):
                self.check_both(f"""
namespace BoundaryDraft
private axiom forbidden : Nat
{declaration} : Nat := forbidden
end BoundaryDraft
""", False, "Unexpected axiom")

    def test_rejects_constructor_type_dependency(self):
        self.check_both("""
namespace BoundaryDraft
private axiom Forbidden : Type
inductive Exposed where
  | mk : Forbidden → Exposed
end BoundaryDraft
""", False, "Unexpected axiom")

    def test_rejects_sorry(self):
        self.check_both("theorem BoundaryDraft.bad : False := by sorry\n", False)

    def test_other_namespace_is_still_a_source_root(self):
        fixture = """
namespace Outside
private axiom forbidden : False
theorem exposed : False := forbidden
end Outside
"""
        result = self.run_lean(fixture + self.audits["source"])
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Unexpected axiom", result.stdout + result.stderr)

    def test_shared_traversal_matches_stock_collector_union(self):
        result = self.run_lean("""
namespace Fixture
private axiom hidden : False
private theorem helper : False := hidden
theorem good : True := True.intro
theorem ext (p q : Prop) (h : p ↔ q) : p = q := propext h
theorem bad : False := helper
def repeated : False := bad
end Fixture
run_cmd do
  let env ← Lean.getEnv
  let roots := [``Fixture.good, ``Fixture.ext, ``Fixture.bad, ``Fixture.repeated]
  let mut expected : Lean.NameSet := {}
  let mut state : Lean.CollectAxioms.State := {}
  for root in roots do
    for axiomName in (← Lean.collectAxioms root) do
      expected := expected.insert axiomName
    let (_, next) := ((Lean.CollectAxioms.collect root).run env).run state
    state := next
    -- Check equality after EVERY prefix, not just the final union.
    unless state.axioms.all expected.contains &&
        expected.toList.all state.axioms.contains do
      throwError "Shared traversal differs from the stock collector"
""")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
