"""Compare the opt-in real-scorer bound with an unpruned local-plugin run."""

import os
import re
import subprocess
import tempfile
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BUILD = Path(os.environ.get("QC_BUILD_DIR", ROOT / "_build-validated"))
COQC = os.environ.get("COQC", "coqc")
SUMMARY = re.compile(
    r"\[schedule-ranking\] policy=(\w+) derive=Gen "
    r"candidates=(\d+) selected-id=(\d+) "
    r"selected-density=(\w+) selected-var-uses=(\d+)"
    r"(?: selected-counts=([\d,]+))?"
)
WORK = re.compile(
    r"\[schedule-pruning\] constructor=ProbeRoot mode=(\w+) "
    r"prefixes=(\d+) leaves=(\d+) cuts=(\d+)"
)


def with_scorer(source, ranking, destination):
    # The scorer is selected in the file, after the QuickChick import.
    text = source.read_text()
    marker = "From QuickChick Require Import QuickChick.\n"
    if marker not in text:
        raise AssertionError(f"{source.name} does not import QuickChick")
    # coqc requires the source and output names to coincide.
    selected = destination.parent / ranking / source.name
    selected.parent.mkdir(exist_ok=True)
    selected.write_text(text.replace(marker, marker + f"QC Scorer {ranking}.\n", 1))
    return selected


def run(mode, ranking, source, destination, reuse=True):
    source = with_scorer(source, ranking, destination)
    environment = os.environ.copy()
    environment["QC_SCHEDULE_TRACE"] = "1"
    # Pruning is on by default, so "off" must disable it explicitly.
    environment["QC_SCHEDULE_SCORE_PRUNING"] = "0" if mode == "off" else mode
    if not reuse:
        environment["QC_SCHEDULE_REUSE_STABLE"] = "0"
    command = [
        COQC,
        "-I", str(BUILD / "install/default/lib"),
        "-Q", str(BUILD / "default/src"), "QuickChick",
        "-noglob", "-o", str(destination), str(source),
    ]
    result = subprocess.run(command, cwd=ROOT, env=environment,
                            text=True, capture_output=True)
    if result.returncode:
        raise AssertionError(f"{source.name} ({mode}, {ranking}) failed:\n"
                             f"{result.stdout}{result.stderr}")
    output = result.stdout + result.stderr
    summaries = SUMMARY.findall(output)
    assert summaries, (mode, ranking)
    work = WORK.findall(output)
    return summaries[-1], work[-1] if work else None


with tempfile.TemporaryDirectory() as temporary:
    destination = Path(temporary)
    for ranking in ("density_then_vars", "density_counts_then_vars"):
        source = HERE / "Probe.v"
        baseline, _ = run("off", ranking, source, destination / "Probe.vo")
        verified, verify_work = run("verify", ranking, source,
                                    destination / "Probe.vo")
        bounded, prune_work = run("1", ranking, source,
                                  destination / "Probe.vo")
        assert baseline[0] == verified[0] == bounded[0] == ranking
        assert baseline[1] == verified[1] == "4", (baseline, verified)
        assert bounded[1] == "1", bounded
        assert baseline[3:] == verified[3:] == bounded[3:], (
            baseline, verified, bounded)
        assert verify_work == ("verify", "8", "4", "0"), verify_work
        assert prune_work == ("prune", "7", "1", "3"), prune_work

    # This fixture has a cycle-dependent score. The verifier must leave its
    # provisional grade out of every bound and match final candidate scoring.
    cycle = ROOT / "test/scoring_cycles/Connected.v"
    cold, _ = run("baseline", "density_then_vars", cycle,
                  destination / "Connected.vo", reuse=False)
    warm, _ = run("baseline", "density_then_vars", cycle,
                  destination / "Connected.vo")
    verified, _ = run("verify", "density_then_vars", cycle,
                      destination / "Connected.vo")
    bounded, _ = run("1", "density_then_vars", cycle,
                     destination / "Connected.vo")
    assert cold[1] == warm[1] == verified[1]
    assert cold[3:] == warm[3:] == verified[3:] == bounded[3:]

print("real scorer: four leaves verified, three safely pruned; mutual cycle verified")
