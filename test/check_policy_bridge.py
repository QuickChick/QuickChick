"""Exercise the experimental Rocq policy bridge with the local plugin."""

import os
import subprocess
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BUILD = Path(os.environ.get("QC_BUILD_DIR", ROOT / "_build-validated"))
COQC = os.environ.get("COQC", "coqc")
SOURCE = ROOT / "test/policy_quote_probe.v"


def run_probe(destination: Path, **probes: str) -> subprocess.CompletedProcess:
    environment = os.environ.copy()
    for name in (
        "QC_POLICY_QUOTE_PROBE",
        "QC_POLICY_SCORE_PROBE",
        "QC_POLICY_STEP_PROBE",
        "QC_POLICY_SCHEDULE_PROBE",
        "QC_POLICY_COMPARE_PROBE",
        "QC_SCHEDULE_TRACE",
    ):
        environment.pop(name, None)
    environment.update(probes)
    command = [
        COQC,
        "-I", str(BUILD / "install/default/lib"),
        "-Q", str(BUILD / "default/src"), "QuickChick",
        "-noglob", "-o", str(destination), str(SOURCE),
    ]
    result = subprocess.run(command, cwd=ROOT, env=environment,
                            text=True, capture_output=True)
    return result


def compile_probe(destination: Path, **probes: str) -> str:
    result = run_probe(destination, **probes)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    return result.stdout + result.stderr


with tempfile.TemporaryDirectory() as temporary:
    output = Path(temporary) / "policy_quote_probe.vo"
    quoted = compile_probe(
        output,
        QC_POLICY_QUOTE_PROBE="1",
        QC_POLICY_SCORE_PROBE="policy_quote_record_score",
        QC_POLICY_STEP_PROBE="policy_quote_step_fields",
        QC_POLICY_SCHEDULE_PROBE="policy_quote_match_links",
    )
    for expected in (
        "[policy-quote] Rocq score={| quote_depth := 2; quote_weight := 3 |}",
        "[policy-step] step=0 score=(0, 2, 0)",
        "[policy-step] step=0 score=(1, 0, 1)",
        "[policy-step] step=0 score=(1, 1, 0)",
        "[policy-schedule] score=(true, true)",
    ):
        assert expected in quoted, expected

    compared = compile_probe(
        output,
        QC_POLICY_SCHEDULE_PROBE="policy_quote_order_sensitive_cost",
        QC_POLICY_COMPARE_PROBE="policy_quote_compare_cost",
    )
    assert (
        "[policy-compare] candidates=4 best=3 lt=2 eq=1 gt=0" in compared
    ), compared

    rejected = run_probe(
        output,
        QC_POLICY_SCHEDULE_PROBE="policy_quote_candidate_cost",
        QC_POLICY_COMPARE_PROBE="policy_quote_bad_compare",
    )
    assert rejected.returncode != 0, "invalid comparator was accepted"
    assert "comparator must return comparison" in (
        rejected.stdout + rejected.stderr
    ), rejected.stdout + rejected.stderr

    default = compile_probe(output, QC_SCHEDULE_TRACE="1")
    assert (
        "policy=density_then_vars derive=Gen candidates=4 selected-id=0"
        in default
    ), default

print("Rocq policy bridge: scoped views, pins, match links, and record comparison")
