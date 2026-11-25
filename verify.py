#!/usr/bin/env python3
"""Reproduce the Lean proof and audit its dependencies, using pinned versions.

Requires elan/lake on PATH and network access for the initial dependency fetch.
The numerical cross-check is separate from the machine proof.
"""
from pathlib import Path
import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
MODULES = ["ChainModel", "CoreBounds", "PolynomialCertificate", "CauchyCertificate", "Main"]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def run_logged(args, name, env=None):
    logs = ROOT / "verification"
    logs.mkdir(exist_ok=True)
    print("\n> " + " ".join(args), flush=True)
    with (logs / name).open("w", encoding="utf-8") as log:
        proc = subprocess.Popen(args, cwd=ROOT, env=env, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True, encoding="utf-8")
        assert proc.stdout is not None
        for line in proc.stdout:
            print(line, end="", flush=True)
            log.write(line)
        code = proc.wait()
    if code:
        raise SystemExit(f"Verification stopped: {' '.join(args)} exited with {code}.")
    return (logs / name).read_text(encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-cache", action="store_true",
                        help="Use dependencies already present locally.")
    args = parser.parse_args()
    if not shutil.which("lake"):
        raise SystemExit("lake is missing. Install the official Lean toolchain manager elan first.")

    for module in MODULES:
        source = (ROOT / (module + ".lean")).read_text(encoding="utf-8")
        if re.search(r"\b(sorry|admit|native_decide|unsafe)\b|(?m:^\s*axiom\b)", source):
            raise SystemExit(f"Disallowed proof shortcut token found in {module}.lean.")

    if not args.skip_cache:
        imports = sorted({m for path in ROOT.glob("*.lean")
                          for m in re.findall(r"^import\s+(Mathlib\.[\w.]+)",
                                              path.read_text(encoding="utf-8"), re.MULTILINE)})
        # This is a temporary curl configuration for the cache subprocess only.
        # It does not change the user's global curl settings.
        with tempfile.TemporaryDirectory(prefix="verified-chain-cache-") as cache_config:
            Path(cache_config, ".curlrc").write_text(
                "parallel-max = 4\nretry-delay = 10\n", encoding="utf-8")
            cache_env = dict(os.environ)
            cache_env["CURL_HOME"] = cache_config
            run_logged(["lake", "exe", "cache", "get", *imports], "cache.log", cache_env)

    run_logged(["lake", "env", "lean", "--version"], "toolchain.log")
    run_logged(["lake", "build"], "build.log")
    axioms = run_logged(["lake", "env", "lean", "Main.lean"], "axioms.log")
    reports = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", axioms, re.DOTALL)
    if len(reports) < 10:
        raise SystemExit("Expected all ten axiom reports from Main.lean.")
    for report in reports:
        actual = {entry.strip() for entry in report.split(",") if entry.strip()}
        if not actual <= ALLOWED_AXIOMS:
            raise SystemExit(f"Unexpected axiom dependency: {actual - ALLOWED_AXIOMS}")
    if "sorryAx" in axioms:
        raise SystemExit("An admitted proof was detected.")
    # A single multi-module invocation launches concurrent replay tasks, each
    # loading an imported environment. Separate processes preserve the same
    # kernel checks while keeping peak memory practical on smaller machines.
    for module in MODULES:
        run_logged(["lake", "env", "leanchecker", "--verbose", module],
                   f"kernel_replay_{module}.log")
    run_logged([sys.executable, "numerical_check.py"], "numerical_check.log")
    print("\nPASS: source compilation, allowed-axiom audit, kernel replay, and independent numerical check.")
    print("The numerical check is explanatory; the infinite-chain theorem is proved by Lean.")


if __name__ == "__main__":
    main()
