"""Compare complete scores with the pinned Specimen implementation."""

import os
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
SPECIMEN = ROOT.parent / "specimen-reference"
PIN = "121cf23435a17d93f1dde283daa62d2899628a8b"


def run(command, cwd):
    return subprocess.check_output(command, cwd=cwd, text=True).strip().splitlines()


assert run(["git", "rev-parse", "HEAD"], SPECIMEN) == [PIN]
expected = (HERE / "expected.txt").read_text().strip().splitlines()
lean = run(["lake", "env", "lean", str(HERE / "SpecimenParity.lean")], SPECIMEN)
build = Path(os.environ.get("QC_BUILD_DIR", ROOT / "_build-validated"))
rocq = run([str(build / "default/plugin/test_budget_aware_score.exe")], ROOT)
assert lean == expected, ("Specimen", lean, expected)
assert rocq == expected, ("QuickChick", rocq, expected)
print(f"BudgetAware: {len(expected)} completed-score cases match Specimen {PIN[:8]}")
