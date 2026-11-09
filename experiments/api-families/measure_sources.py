#!/usr/bin/env python3
"""Measure canonical Lean sources; run `python3 measure_sources.py [--check]`.

The scanner preserves line numbers and strings, removes nested Lean comments,
and counts every remaining nonblank physical line. No Lean file is modified.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parent
FILES = {
    "map_handwritten_helper": "MapBaseline/Handwritten.lean",
    "map_macro_provider": "MapBaseline/MacroCommand.lean",
    "map_macro_consumer": "MapBaseline/Macro.lean",
    "map_contract_checker": "MapBaseline/Contract.lean",
    "map_framework_adapter": "MapBaseline/Framework.lean",
    "map_specifications": "MapBaseline/Specifications.lean",
    "map_recipe_consumer": "MapBaseline/Recipe.lean",
    "sdk_family": "../../ApiBuilder/Family.lean",
    "sdk_family_elab": "../../ApiBuilder/FamilyElab.lean",
    "ag_installer": "AGExperiment/Install.lean",
    "ag_framework_adapter": "AGExperiment/Recipe.lean",
    "ag_common_capability_input": "AGExperiment/Core.lean",
    "ag_macro_consumer_and_tests": "AGExperiment/Tests.lean",
    "ag_recipe_consumer_and_tests": "AGExperiment/RecipeTests.lean",
    "holdout_macro_consumer": "Holdout/Macro.lean",
    "holdout_specifications": "Holdout/Specifications.lean",
    "holdout_reference": "Holdout/Reference.lean",
    "holdout_recipe_consumer": "Holdout/Recipe.lean",
    "map_handwritten_clients": "MapBaseline/Client.lean",
    "map_generic_clients": "MapBaseline/GenericClient.lean",
    "map_macro_clients": "MapBaseline/MacroClient.lean",
    "map_recipe_clients": "MapBaseline/RecipeClient.lean",
    "map_contract_comparison_harness": "MapBaseline/AllContracts.lean",
    "holdout_macro_clients": "Holdout/MacroClient.lean",
    "holdout_recipe_clients": "Holdout/RecipeClient.lean",
}


def strip_comments(source):
    """Return source with comments replaced by spaces, preserving newlines."""
    out = []
    i = depth = hashes = 0
    state = "code"
    while i < len(source):
        c, pair = source[i], source[i:i + 2]
        if state == "line":
            if c == "\n":
                state = "code"
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue
        if depth:
            if pair == "/-":
                depth += 1
                out.extend("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
            continue
        if state == "string":
            out.append(c)
            i += 1
            if c == "\\" and i < len(source):
                out.append(source[i])
                i += 1
            elif c == '"':
                state = "code"
            continue
        if state == "raw":
            closing = '"' + "#" * hashes
            if source.startswith(closing, i):
                out.extend(closing)
                i += len(closing)
                state = "code"
            else:
                out.append(c)
                i += 1
            continue
        if pair == "--":
            state = "line"
            out.extend("  ")
            i += 2
        elif pair == "/-":
            depth = 1
            out.extend("  ")
            i += 2
        elif c == '"':
            state = "string"
            out.append(c)
            i += 1
        elif c == "r" and (match := re.match(r'r(#+)"', source[i:])):
            token = match.group(0)
            hashes = len(match.group(1))
            out.extend(token)
            i += len(token)
            state = "raw"
        else:
            out.append(c)
            i += 1
    if depth:
        raise ValueError("unclosed block comment")
    return "".join(out)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def measure():
    files, contents = {}, {}
    for key, relative in FILES.items():
        path = ROOT / relative
        source = path.read_text()
        stripped = strip_comments(source)
        lines = stripped.splitlines()
        contents[key] = lines
        files[key] = {
            "path": relative,
            "sha256": sha256(path),
            "physical_lines": len(source.splitlines()),
            "nonblank_lines_before_comment_removal": sum(bool(s.strip()) for s in source.splitlines()),
            "sloc": sum(bool(s.strip()) for s in lines),
            "code_line_numbers": [i for i, s in enumerate(lines, 1) if s.strip()],
            "stripped_nonwhitespace_characters": sum(not c.isspace() for c in stripped),
        }

    def calls(key, prefix):
        # A command's indented continuation lines belong to the same input.
        lines = contents[key]
        blocks = []
        for i, line in enumerate(lines):
            if not line.startswith(prefix):
                continue
            indexes = [i + 1]
            for j in range(i + 1, len(lines)):
                if not lines[j].strip() or not lines[j][0].isspace():
                    break
                indexes.append(j + 1)
            blocks.append({"start_line": i + 1, "code_line_numbers": indexes, "sloc": len(indexes)})
        return {"file": FILES[key], "prefix": prefix, "blocks": blocks,
                "sloc": sum(b["sloc"] for b in blocks)}

    commands = {
        "map_macro_invocations": calls("map_macro_consumer", "derive_map_comap "),
        "map_macro_creation_checks": calls("map_macro_consumer", "#map_contract "),
        "map_handwritten_creation_checks": calls("map_handwritten_helper", "#map_contract "),
        "map_recipe_invocations": calls("map_recipe_consumer", "api_family "),
        "map_recipe_checks": calls("map_recipe_consumer", "#api_check "),
        "ag_core_installer_invocations": calls("ag_macro_consumer_and_tests", "install_scheme_property_core "),
        "ag_source_installer_invocations": calls("ag_macro_consumer_and_tests", "install_scheme_property_source "),
        "ag_recipe_invocations": calls("ag_recipe_consumer_and_tests", "api_family "),
        "ag_recipe_checks": calls("ag_recipe_consumer_and_tests", "#api_check "),
        "holdout_macro_invocations": calls("holdout_macro_consumer", "derive_map_comap "),
        "holdout_macro_checks": calls("holdout_macro_consumer", "#map_contract "),
        "holdout_recipe_invocations": calls("holdout_recipe_consumer", "api_family "),
        "holdout_recipe_checks": calls("holdout_recipe_consumer", "#api_check "),
    }

    def scenario(keys, note):
        assert len(keys) == len(set(keys))
        return {
            "files": keys,
            "source_sloc": sum(files[k]["sloc"] for k in keys),
            "stripped_nonwhitespace_characters": sum(files[k]["stripped_nonwhitespace_characters"] for k in keys),
            "note": note,
        }

    scenarios = {
        "map_handwritten_with_actual_creation_checker": scenario(
            ["map_handwritten_helper", "map_contract_checker"],
            "Canonical manual source imports the checker and runs three self-reference checks. The same handwritten declarations are the independent oracle for macro/recipe comparisons."),
        "map_macro_with_actual_oracle_and_checker": scenario(
            ["map_macro_provider", "map_macro_consumer", "map_contract_checker", "map_handwritten_helper"],
            "Canonical macro imports both checker and handwritten oracle and checks outputs at creation. Shared files are counted once."),
        "map_recipe_full_new_source": scenario(
            ["map_macro_provider", "map_contract_checker", "map_framework_adapter", "map_specifications", "map_recipe_consumer", "map_handwritten_helper"],
            "Includes mandatory independently authored reference, shared generator once, checker, adapter, specifications and calls. Existing SDK is separately reported."),
        "sdk_reused_existing_source": scenario(
            ["sdk_family", "sdk_family_elab"],
            "Existing directly reused SDK closure, not new experimental authoring and not a per-family charge. The unrelated milestone-0 SDK.lean is not used."),
        "ag_common_core_and_installer": scenario(
            ["ag_common_capability_input", "ag_installer"],
            "Common mathematical/probe inputs plus standalone installer. Input commands are separately measured because consumer files also contain tests."),
        "ag_recipe_extra_adapter": scenario(
            ["ag_framework_adapter"],
            "Additional adapter over the same standalone installer and common inputs; uses existing SDK."),
        "holdout_macro_marginal_with_contract": scenario(
            ["holdout_macro_consumer", "holdout_reference"],
            "Two new families, actual consumer/checks and independently authored oracle. Previously shared generator/checker are not recharged."),
        "holdout_recipe_marginal": scenario(
            ["holdout_specifications", "holdout_recipe_consumer", "holdout_reference"],
            "Two new families including required oracle, specifications and calls/rechecks. Previously shared generator/checker/adapter/SDK are not recharged."),
    }
    manifest = json.loads((ROOT / "../../lake-manifest.json").read_text())
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    result = {
        "schema_version": 2,
        "authority": "Canonical experiments/api-families sources; regenerate with python3 measure_sources.py. Historical pre-integration measurements are not authoritative for these files.",
        "rule": {
            "metric": "Non-comment, nonblank physical Lean source lines (SLOC)",
            "include": "Imports, module/public/namespace/section/end, attributes, syntax, proofs, calls and creation-time checks all count. Inline code/comment lines count once; string contents are preserved.",
            "exclude": "Blank/comment-only lines; nested block and line comments. No staged duplicates, generated output, external Lean/mathlib source or runtime setup in production scenarios. Selected clients and validation harnesses are separately inventoried.",
            "method": "Stateful scanner preserving line numbers, escaped strings and r# raw strings. Exact per-file SHA-256 and counted line numbers are included.",
            "limitation": "SLOC and nonwhitespace character counts are formatting-sensitive, not measures of developer time, token cost, maintenance savings or productivity. Scenario totals overlap and must not be added.",
        },
        "execution_context": {"lean": (ROOT / "lean-toolchain").read_text().strip(), "mathlib_revision": mathlib["rev"]},
        "measurement_script_sha256": sha256(Path(__file__)),
        "files": files,
        "pure_command_inputs": commands,
        "scenarios": scenarios,
        "interpretation": [
            "Handwritten is already the generic-helper API baseline: most proofs call GaloisConnection; semilinear right laws use independent preimage proofs to avoid extra assumptions.",
            "Specification.reference is mandatory and the adapter invokes Contract.check against it. Oracle declarations are an actual dependency and author/maintenance cost, not free test material. Generated proofs are forbidden to call oracle or native gold frontend rules.",
            "Canonical Handwritten and Macro files include creation-time comparator imports/checks. Their full-file costs are counted exactly as delivered, including the manual self-check and macro's independent reference import.",
            "References and the shared generator are each counted once in each scenario. Reused SDK code is separately visible, not recharged for each consumer. Existing mathematical dependency source is shared and unpriced here.",
            "The command and framework have different lifecycle-management promises. Neither a shorter invocation nor a larger implementation establishes a productivity ranking.",
            "Held-out adaptation still includes contexts/specifications, calls and a twelve-wrapper independent reference even though shared producers require no source changes.",
            "AG common probe definitions, property equivalences and aggregate capabilities are experiment input shared by both routes. The experiment generates concrete instance registrations using existing mathlib mathematics.",
            "Validation clients and negative tests are not conflated with production source. No developer-time or real-upgrade maintenance benefit is measured.",
        ],
    }
    for record in files.values():
        if sha256(ROOT / record["path"]) != record["sha256"]:
            raise RuntimeError("source changed during measurement: " + record["path"])
    return result


def markdown(data):
    files, calls, scenarios = data["files"], data["pure_command_inputs"], data["scenarios"]

    def row(label, key):
        f = files[key]
        return f'| {label} | `{f["path"]}` | {f["physical_lines"]} | {f["sloc"]} |'

    lines = [
        "# Canonical source costs", "",
        "Reproduce from this package with `python3 measure_sources.py`; verify an existing measurement with `python3 measure_sources.py --check`. The authoritative machine-readable result is `evidence/costs.json`.", "",
        "Count all physical Lean lines containing non-comment code, including imports and namespace/check scaffolding. Remove blank lines, `--` comments and nested `/- ... -/` comments while preserving strings. JSON includes file hashes, exact counted line numbers and supplementary nonwhitespace character counts.", "",
        "**The handwritten API already uses the generic GaloisConnection helpers. The framework adapter requires an independently authored reference, so that oracle is a real input and maintenance cost. Comparing invocation lines alone does not establish productivity.**", "",
        "| Component | Canonical relative path | Physical lines | SLOC |",
        "|---|---|---:|---:|",
    ]
    for label, key in [
        ("Handwritten/helper, 18 wrappers and creation checks", "map_handwritten_helper"),
        ("Standalone command provider", "map_macro_provider"),
        ("Three-family command consumer and creation checks", "map_macro_consumer"),
        ("Independent contract checker", "map_contract_checker"),
        ("Framework adapter", "map_framework_adapter"),
        ("Three-family specifications", "map_specifications"),
        ("Three-family recipe consumer", "map_recipe_consumer"),
        ("Existing SDK data/audit layer", "sdk_family"),
        ("Existing SDK command layer", "sdk_family_elab"),
    ]:
        lines.append(row(label, key))
    lines += ["", "Complete delivered source dependencies, counting each file once:", ""]
    for key, label in [
        ("map_handwritten_with_actual_creation_checker", "Manual/helper plus its actual creation checker"),
        ("map_macro_with_actual_oracle_and_checker", "Command plus its actual checker and oracle"),
        ("map_recipe_full_new_source", "Recipe's new source, including its required oracle"),
    ]:
        lines.append(f'- {label}: **{scenarios[key]["source_sloc"]} SLOC**.')
    lines += [
        f'- Existing SDK reused by the recipe: **{scenarios["sdk_reused_existing_source"]["source_sloc"]} SLOC**, reported separately from new authoring.', "",
        f'Pure three-family requests are {calls["map_macro_invocations"]["sloc"]} command lines versus {calls["map_recipe_invocations"]["sloc"]} recipe lines. This excludes the specifications, reference, provider, checker and adapter listed above. Recipe rechecks add {calls["map_recipe_checks"]["sloc"]} lines. Canonical handwritten and command modules each also execute three creation-time `#map_contract` checks.', "",
        "The oracle here implements full independent wrapper declarations. Its signatures are used for comparison; generated proofs cannot call it. The manual self-check does not supply an independent oracle for the intended mathematical signature. The paths also promise different lifecycle features, so these totals are an inventory rather than a same-functionality ranking.", "",
        "## AG installer", "",
        "| Component | Canonical relative path | Physical lines | SLOC |",
        "|---|---|---:|---:|",
    ]
    for label, key in [
        ("Common probe/capability input", "ag_common_capability_input"),
        ("Standalone installer", "ag_installer"),
        ("Additional framework adapter", "ag_framework_adapter"),
        ("Standalone consumer and tests, whole file", "ag_macro_consumer_and_tests"),
        ("Recipe consumer and tests, whole file", "ag_recipe_consumer_and_tests"),
    ]:
        lines.append(row(label, key))
    ag_calls = calls["ag_core_installer_invocations"]["sloc"] + calls["ag_source_installer_invocations"]["sloc"]
    lines += [
        "",
        f'Both routes share {files["ag_common_capability_input"]["sloc"]} SLOC of concrete probe/capability input and the {files["ag_installer"]["sloc"]}-SLOC installer. Pure installation requests take {ag_calls} lines (five core and three source requests); recipe requests take {calls["ag_recipe_invocations"]["sloc"]} lines plus {calls["ag_recipe_checks"]["sloc"]} recheck lines. Whole consumer files also contain tests, so their full-file sizes are listed separately.', "",
        "## Frozen held-out families", "",
        "| Component | Canonical relative path | Physical lines | SLOC |",
        "|---|---|---:|---:|",
    ]
    for label, key in [
        ("Command consumer with independent checks", "holdout_macro_consumer"),
        ("Recipe specifications", "holdout_specifications"),
        ("Independent reference, 12 wrappers", "holdout_reference"),
        ("Recipe consumer with rechecks", "holdout_recipe_consumer"),
    ]:
        lines.append(row(label, key))
    lines += [
        "",
        f'Bare requests are {calls["holdout_macro_invocations"]["sloc"]} lines for the command and {calls["holdout_recipe_invocations"]["sloc"]} for the recipe. Actual marginal authored source including the new reference is **{scenarios["holdout_macro_marginal_with_contract"]["source_sloc"]} SLOC** for command consumption and **{scenarios["holdout_recipe_marginal"]["source_sloc"]} SLOC** for specifications plus recipe consumption. Existing generator/checker/adapter/SDK are not recharged, but remain infrastructure and maintenance dependencies.', "",
        "The reusable producers transfer without edits to these two new objects. These measurements do not establish reduced developer time or long-term maintenance cost. Concrete specifications and independently authored oracle signatures remain costs to simplify and measure.", "",
        "All paths above are relative to this package. Generated output, dependency source, environment setup and staged duplicate copies are excluded from production totals. JSON separately inventories selected clients and validation harnesses. No Lean source is changed by measurement; scenario totals overlap and must not be added.", "",
    ]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="verify existing JSON/Markdown without writing")
    args = parser.parse_args()
    data = measure()
    outputs = {
        ROOT / "evidence/costs.json": json.dumps(data, ensure_ascii=False, indent=2) + "\n",
        ROOT / "COSTS.md": markdown(data),
    }
    for path, text in outputs.items():
        relative = path.relative_to(ROOT)
        if args.check:
            if not path.exists() or path.read_text() != text:
                raise SystemExit(f"stale or missing measurement: {relative}")
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        print(("verified " if args.check else "wrote ") + str(relative))


if __name__ == "__main__":
    main()
