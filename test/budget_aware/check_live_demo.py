"""Check BudgetAware's diagnostic on real Rocq schedule candidates."""

import os
import subprocess
import tempfile
from pathlib import Path


root = Path(__file__).resolve().parents[2]
build = Path(os.environ.get("QC_BUILD_DIR", root / "_build-validated"))
source = root / "doc/BudgetAwareDemo.v"

with tempfile.TemporaryDirectory() as temporary:
    env = os.environ.copy()
    env["QC_BUDGET_AWARE_DEMO"] = "budget_root"
    result = subprocess.run(
        [os.environ.get("COQC", "coqc"),
         "-I", str(build / "install/default/lib"),
         "-Q", str(build / "default/src"), "QuickChick",
         "-noglob", "-o", str(Path(temporary) / "BudgetAwareDemo.vo"),
         str(source)],
        cwd=root, env=env, text=True, capture_output=True, check=True,
    )
    output = result.stdout + result.stderr

assert "candidate=0 selectivity=0 density=Checking" in output
assert "steps: (x : nat) <-G (finite x) ; check (loose x)" in output
assert "candidate=1 selectivity=1 density=Checking" in output
assert "steps: (x : nat) <-G (loose x) ; check (finite x)" in output
assert "best=0 built-in-selected=0" in output
assert "unavailable" not in output
print("BudgetAware live diagnostic: finite and loose producer scores")
