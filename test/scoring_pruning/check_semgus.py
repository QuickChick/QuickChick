"""Exercise score bounds on the doubly self-merged SemGuS relation."""

import os
import re
import subprocess
import tempfile
import time
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
WORK = re.compile(
    r"^\[schedule-pruning-work\] constructor=(\S+) "
    r"bound-cache-hits=(\d+) bound-cache-misses=(\d+) "
    r"leaf-cache-hits=(\d+)"
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
    started = time.monotonic()
    with log.open("w") as stream:
        result = subprocess.run(command, cwd=ROOT, env=environment,
                                stdout=stream, stderr=subprocess.STDOUT,
                                timeout=90)
    if result.returncode:
        raise AssertionError(f"SemGuS {mode} failed; see {log}")
    rankings = []
    root_searches = []
    work = []
    for line in log.open(errors="replace"):
        if match := RANKING.match(line):
            rankings.append(match.groups())
        if match := PRUNING.match(line):
            root_searches.append(match.groups())
        if match := WORK.match(line):
            work.append(match.groups())
    assert rankings, (mode, "missing ranking trace")
    return rankings[-1], root_searches, work, time.monotonic() - started


with tempfile.TemporaryDirectory() as temporary:
    directory = Path(temporary)
    ordinary, off_searches, off_work, off_seconds = run("off", directory)
    baseline, baseline_searches, baseline_work, baseline_seconds = run("baseline", directory)
    verified, verify_searches, verify_work, verify_seconds = run("verify", directory)
    bounded, prune_searches, prune_work, prune_seconds = run("1", directory)
    assert ordinary == baseline == verified == bounded, (
        ordinary, baseline, verified, bounded)
    assert baseline[0] == "12", baseline
    assert not off_searches, off_searches
    assert not off_work, off_work
    assert len(baseline_searches) == len(verify_searches) == len(prune_searches) == 1
    assert len(baseline_work) == len(verify_work) == len(prune_work) == 1
    assert baseline_searches[0][1:] == ("baseline", "0", "12", "0")
    verify_root, prune_root = verify_searches[0], prune_searches[0]
    assert verify_root[1:] == ("verify", "25", "12", "0"), verify_root
    assert prune_root[1:] == ("prune", "25", "12", "0"), prune_root
    assert int(prune_work[0][1]) > 0 and int(prune_work[0][2]) > 0
    assert prune_work[0][3] == "12", prune_work
    print(f"double self-merge: 12 root leaves verified over 25 prefixes; "
          f"same winner, zero cuts; seconds off/baseline/verify/prune: "
          f"{off_seconds:.1f}/{baseline_seconds:.1f}/"
          f"{verify_seconds:.1f}/{prune_seconds:.1f}")
