"""Exercise score bounds on the doubly self-merged SemGuS relation."""

import os
import re
import subprocess
import tempfile
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BUILD = Path(os.environ.get("QC_BUILD_DIR", ROOT / "_build-validated"))
COQC = os.environ.get("COQC", "coqc")
RANKING = re.compile(
    r"^\[schedule-ranking\] policy=density_then_vars derive=Gen "
    r"candidates=(\d+) selected-id=(\d+) "
    r"selected-density=(\w+) selected-var-uses=(\d+)"
)
PRUNING = re.compile(
    r"^\[schedule-pruning\] constructor=(\S+) mode=(\w+) "
    r"prefixes=(\d+) leaves=(\d+) cuts=(\d+)"
)


def run(mode, directory):
    environment = os.environ.copy()
    environment["QC_SCHEDULE_TRACE"] = "1"
    environment["QC_SCHEDULE_RANKING"] = "density_then_vars"
    environment.pop("QC_SCHEDULE_SCORE_PRUNING", None)
    if mode != "off":
        environment["QC_SCHEDULE_SCORE_PRUNING"] = mode
    command = [
        COQC,
        "-I", str(BUILD / "install/default/lib"),
        "-Q", str(BUILD / "default/src"), "QuickChick",
        "-noglob", "-o", str(directory / "SemgusMerge.vo"),
        str(HERE / "SemgusMerge.v"),
    ]
    log = directory / f"{mode}.log"
    with log.open("w") as stream:
        result = subprocess.run(command, cwd=ROOT, env=environment,
                                stdout=stream, stderr=subprocess.STDOUT,
                                timeout=90)
    if result.returncode:
        raise AssertionError(f"SemGuS {mode} failed; see {log}")
    rankings = []
    cuts = 0
    for line in log.open(errors="replace"):
        if match := RANKING.match(line):
            rankings.append(match.groups())
        if match := PRUNING.match(line):
            cuts += int(match.group(5))
    assert rankings, (mode, "missing ranking trace")
    return rankings[-1], cuts


with tempfile.TemporaryDirectory() as temporary:
    directory = Path(temporary)
    baseline, _ = run("off", directory)
    verified, _ = run("verify", directory)
    bounded, cuts = run("1", directory)
    assert baseline == verified == bounded, (baseline, verified, bounded)
    assert baseline[0] == "12", baseline
    assert cuts > 0, cuts
    print(f"double self-merge: {baseline[0]} root candidates; "
          f"same winner in all modes; {cuts} dependency-search cuts")
