"""Check discovery-order effects in the installed local scheduling plugin."""

import os
import re
import subprocess
import tempfile
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BUILD = Path(os.environ.get("QC_BUILD_DIR", ROOT / "_build-validated"))
COQC = os.environ.get("COQC", "coqc")

DONE = re.compile(
    r"GenSizedSuchThat_(asym_[a-z]+)_[A-Z]+:.*Done, Density: "
    r"(Checking|Backtracking|Neutral|Partial|Total), "
    r"cycle-independent: (true|false)"
)
STARTED = re.compile(r"^Inductive name: (asym_[a-z]+)$", re.MULTILINE)


def score(filename: str, destination: Path):
    source = HERE / filename
    command = [
        COQC,
        "-I", str(BUILD / "install/default/lib"),
        "-Q", str(BUILD / "default/src"), "QuickChick",
        "-noglob", "-o", str(destination), str(source),
    ]
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise AssertionError(f"{filename} failed:\n{result.stdout}{result.stderr}")
    output = result.stdout + result.stderr
    matches = DONE.findall(output)
    entries = {key: (grade, independent) for key, grade, independent in matches}
    return entries, STARTED.findall(output), matches


with tempfile.TemporaryDirectory() as temporary:
    temp = Path(temporary)
    a, a_order, _ = score("AFirst.v", temp / "AFirst.vo")
    b, b_order, _ = score("BFirst.v", temp / "BFirst.vo")
    pair, pair_order, _ = score("Pair.v", temp / "Pair.vo")
    triple, triple_order, _ = score("Triple.v", temp / "Triple.vo")
    connected, _, connected_matches = score("Connected.v", temp / "Connected.vo")

assert a["asym_b"] == ("Partial", "false"), a
assert b["asym_b"] == ("Total", "false"), b
assert pair["asym_b"] == ("Partial", "false"), pair
assert triple["asym_b"] == ("Total", "false"), triple
assert pair["asym_pair"] == ("Partial", "false"), pair
assert triple["asym_triple"] == ("Total", "false"), triple
assert a_order[:3] == ["asym_a", "asym_b"], a_order
assert b_order[:3] == ["asym_b", "asym_a"], b_order
assert pair_order[:3] == ["asym_pair", "asym_a", "asym_b"], pair_order
assert triple_order[:4] == ["asym_triple", "asym_c", "asym_b", "asym_a"], triple_order
assert [grade for key, grade, _ in connected_matches if key == "asym_b"] == [
    "Total", "Partial"
], connected_matches
assert connected["asym_root"] == ("Total", "false"), connected

print("cycle order: asym_b Partial from A-first, Total from B-first; "
      "pair Partial, triple Total; connected root sees both")
