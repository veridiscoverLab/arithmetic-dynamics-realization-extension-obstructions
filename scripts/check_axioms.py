#!/usr/bin/env python3
"""Compile public audits and interface regressions; reject unexpected axioms."""

from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
TARGETS = (
    "ArithDyn/Axioms.lean",
    "ArithDyn/Extension/BridgeAxioms.lean",
    "ArithDyn/Extension/ProjTwistAxioms.lean",
    "ArithDyn/Extension/EndpointAxioms.lean",
    "tests/ProjectiveEndpoint.lean",
    "tests/PolarizedInput.lean",
)
# Lean declaration names may themselves contain apostrophes.
DEPENDENCIES = re.compile(r"'([^\n]+)' depends on axioms:\s*\[([^\]]*)\]")
NO_DEPENDENCIES = re.compile(r"'([^\n]+)' does not depend on (?:any )?axioms")


def main() -> int:
    total = 0
    for target in TARGETS:
        expected = len(re.findall(r"^\s*#print axioms\s+", (ROOT / target).read_text(), re.M))
        try:
            result = subprocess.run(
                ["lake", "env", "lean", target], cwd=ROOT,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, check=False,
            )
        except FileNotFoundError:
            print("lake was not found; install elan and run lake build first.", file=sys.stderr)
            return 1
        if result.returncode:
            print(result.stdout, end="")
            print(f"FAIL: Lean rejected {target}", file=sys.stderr)
            return 1
        records = DEPENDENCIES.findall(result.stdout)
        count = len(records) + len(NO_DEPENDENCIES.findall(result.stdout))
        if count != expected or expected == 0:
            print(result.stdout, end="")
            print(f"FAIL: {target}: expected {expected} audits, found {count}", file=sys.stderr)
            return 1
        for name, raw in records:
            extra = {item.strip() for item in raw.split(",") if item.strip()} - ALLOWED
            if extra:
                print(f"FAIL: {name}: unexpected dependencies {sorted(extra)}", file=sys.stderr)
                return 1
        total += count
        print(f"PASS: {target} ({count} axiom checks)", flush=True)
    print(f"PASS: {total} checks; both interface regressions compiled.")
    print("This audits the declared theorem types; it does not discharge geometric TODOs.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
