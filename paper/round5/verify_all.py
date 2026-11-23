#!/usr/bin/env python3
"""Reproduce the exact finite checks used by the completed proof draft.

Run without -O: python3 round5/verify_all.py
Only Python's standard library is needed by the verifiers.
These checks do not replace the paper proofs or claim Lean formalization.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

HERE = Path(__file__).resolve().parent
CHECKS = [
    "global_general_certificates.py",
    "global_trianglefree_certificates.py",
    "global_small_seed_certificates.py",
    "global_sizefive_certificates.py",
    "global_ten_eight_certificates.py",
    "zero_verify_eight.py",
    "zero_verify_eight_extension.py",
    "zero_verify_triple.py",
    "global_rank1_verify.py",
    "matrix_rank2_transfer_verify.py",
    "matrix_mixed3_verify.py",
    "matrix_mixed3_strip_verify.py",
    "matrix_size5_triangle_verify.py",
    "matrix_size4_verify.py",
    "root_entropy_ac_verify.py",
    "matrix_typeB_entropy_verify.py",
    "zero_entropy_ac_audit.py",
    "zero_entropy_b_audit.py",
]


def main():
    if not __debug__:
        raise SystemExit("Do not use python -O: assertions are part of the finite checks.")
    results = []
    for name in CHECKS:
        path = HERE / name
        r = subprocess.run([sys.executable, str(path)], cwd=HERE,
            capture_output=True, text=True)
        results.append({"script": name, "exit_code": r.returncode,
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "stdout": r.stdout, "stderr": r.stderr})
        print(("PASS " if r.returncode == 0 else "FAIL ") + name, flush=True)
        if r.returncode:
            print(r.stdout)
            print(r.stderr, file=sys.stderr)
            break
    success = len(results) == len(CHECKS) and all(r["exit_code"] == 0 for r in results)
    report = {"finite_checks_passed": success, "checks_run": len(results),
        "checks_expected": len(CHECKS),
        "scope": "Exact finite certificates; not a formal verification of the paper proof.",
        "results": results}
    (HERE / "final_verification_report.json").write_text(json.dumps(report, indent=2) + "\n")
    if not success:
        raise SystemExit(1)
    print(f"ALL {len(CHECKS)} FINITE CHECKS PASSED")


if __name__ == "__main__":
    main()
