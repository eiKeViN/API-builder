#!/usr/bin/env python3
"""Run real Lean negative/positive representation-evolution checks."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "evidence" / "evolution"
CLIENT = HERE / "Evolution/Client.lean"
CONTRACT = HERE / "Evolution/Contract.lean"
MAP = HERE / "Evolution/Map.lean"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    RESULTS.mkdir(parents=True, exist_ok=True)
    original_map = MAP.read_bytes()
    assert original_map == (HERE / 'variants/v2-fixed.lean').read_bytes(), 'Preserve edited fixture'
    stable_hashes = {"client": digest(CLIENT), "contract": digest(CONTRACT)}
    cases = []

    def run(label: str, variant: str, *, expect_success: bool, clean: bool = False,
            target: str = "Evolution.Client", expected_diagnostics: tuple[str, ...] = ()) -> None:
        assert digest(CLIENT) == stable_hashes["client"]
        assert digest(CONTRACT) == stable_hashes["contract"]
        shutil.copyfile(HERE / "variants" / variant, MAP)
        if clean:
            for relative in ['.lake/build/lib/lean/Evolution', '.lake/build/ir/Evolution']:
                shutil.rmtree(HERE / relative, ignore_errors=True)
        started = time.monotonic()
        command = ["lake", "build", target]
        result = subprocess.run(command, cwd=HERE, text=True, capture_output=True)
        output = result.stdout + result.stderr
        (RESULTS / f"{label}.log").write_text(output)
        diagnostic_match = all(fragment in output for fragment in expected_diagnostics)
        row = {
            "case": label,
            "variant": variant,
            "command": command,
            "clean_build": clean,
            "expected_success": expect_success,
            "exit_code": result.returncode,
            "expected_diagnostics": list(expected_diagnostics),
            "diagnostics_matched": diagnostic_match,
            "expectation_met": ((result.returncode == 0) == expect_success) and diagnostic_match,
            "elapsed_seconds": round(time.monotonic() - started, 3),
            "client_sha256": digest(CLIENT),
            "contract_sha256": digest(CONTRACT),
            "source_sha256": digest(MAP),
        }
        cases.append(row)
        print(json.dumps(row), flush=True)
        if not row["expectation_met"]:
            print(output, flush=True)
            raise RuntimeError(f"Unexpected result in {label}")

    try:
        run("01-v1-clean", "v1.lean", expect_success=True, clean=True)
        run("02-v2-old-rfl-rejected", "v2-broken-rfl.lean", expect_success=False,
            expected_diagnostics=("Evolution/Map.lean", "Type mismatch", "Iff.rfl"))
        run("03-v2-adapter-incremental", "v2-fixed.lean", expect_success=True)
        run("04-v2-adapter-clean", "v2-fixed.lean", expect_success=True, clean=True)
        # The new body's exported theorem is valid, but fails the old expected type.
        run("05-body-mirror-core-compiles", "v2-body-mirror.lean", expect_success=True,
            target="Evolution.Map")
        run("06-body-mirror-contract-rejected", "v2-body-mirror.lean", expect_success=False,
            target="Evolution.Contract",
            expected_diagnostics=("Evolution/Contract.lean", "Type mismatch", "mem_map"))
        run("07-restored-final", "v2-fixed.lean", expect_success=True)
    finally:
        MAP.write_bytes(original_map)
        (RESULTS / "results.json").write_text(json.dumps({
            "lean": "4.36.0-rc2",
            "mathlib_revision": "6da929dc62a7af33b577a22d4a01c08ddfd4f8f6",
            "stable_hashes": stable_hashes,
            "cases": cases,
            "all_expectations_met": len(cases) == 7 and all(c["expectation_met"] for c in cases),
            "limits": [
                "A controlled subgroup image experiment, not a full mathlib refactor.",
                "The type checker fixes a chosen theorem type; it is not a general semantic comparator.",
                "Body-mirroring output is supplied explicitly; no new generator is claimed here.",
                "Elapsed times include shared environment effects and are not performance benchmarks."
            ]
        }, indent=2) + "\n")


if __name__ == "__main__":
    main()
