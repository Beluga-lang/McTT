""" Check the axiom usage of every lemma/theorem/corollaries in all *.v files in a 
    given directory (default "../theories/") 
"""
import argparse
import os
import re
import subprocess
import sys
import uuid
from pathlib import Path
from typing import List, Tuple, Optional

# "loc" is used by the frontend for token locations
expected_axioms = ["functional_extensionality_dep","loc"]

# get the lcoal name of the axiom, thus not affected by the module scope
def local_axiom_name(s: str) -> str:
    parts = s.rsplit('.', 1)
    if len(parts) > 1:
        return parts[1]
    return s

def gather_lemmas(file_path: Path, project_dir: Path):
    content = file_path.read_text(encoding="utf-8")
    local_decl_pattern = re.compile(r"\[local\]\s*\n\s*(Lemma|Theorem|Corollary)\s+(.+?)(\s|:)", re.MULTILINE)
    decl_pattern = re.compile(r"^([ \t]*)(Lemma|Theorem|Corollary)\s+(.+?)(\s|:)", re.MULTILINE)
    local_matches = list(local_decl_pattern.finditer(content))
    matches = list(decl_pattern.finditer(content))
    lemma_names = []
    local_lemma_names = []
    rel_path = f"{file_path.relative_to(project_dir)}"

    for local_match in local_matches:
        local_lemma_name = local_match.group(2)
        print(f"Warning: theorem {local_lemma_name} in {rel_path} marked with #[local] is skipped.")
        local_lemma_names.append(local_lemma_name)

    for match in matches:
        lemma_name = match.group(3)
        if lemma_name not in local_lemma_names:
            lemma_names.append(lemma_name)

    return rel_path, lemma_names, local_lemma_names


def create_assumption_file(all_files_lemma_names: List[Tuple[str, List[str]]], project_dir: Path):
    check_file_dir = Path.joinpath(project_dir, "Temp_" + str(uuid.uuid4().hex) + ".v").resolve()
    section_id = 0

    with open(check_file_dir, "w+", encoding="utf-8") as check_file:
        for path, _ in all_files_lemma_names:
            check_file.write(f"From Mctt Require {path.replace('/','.')[:-2]}." + "\n")

        check_file.write("\n")
        for path, file_lemma_names in all_files_lemma_names:
            if file_lemma_names == []:
                continue
            check_file.write(f"Section Section_{section_id}." + "\n")
            check_file.write(f"Import {path.replace('/','.')[:-2]}.")
            for lemma_name in file_lemma_names:
                marker = f"{path} : {lemma_name}"
                snippet = f'\nGoal True. idtac "<<<{marker}>>>". Abort.\n' f"Print Assumptions {lemma_name}."
                check_file.write(snippet)

            check_file.write("\n")
            check_file.write(f"End Section_{section_id}." + "\n\n")
            section_id += 1
    return check_file_dir


def get_assumptions(check_file_dir: Path, project_dir: Path):
    outputs = []
    errors = []
    try:
        with subprocess.Popen(
            ["coqc", "-R", ".", "Mctt", f"{check_file_dir}"],
            cwd=project_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        ) as process:
            assert process.stdout is not None
            for line in process.stdout:
                output = line.decode("utf8")
                outputs.append(output)
            if process.stderr is not None:
                for line in process.stderr:
                    error = line.decode("utf8")
                    errors.append(error)
                if len(errors) > 0:
                    print("Errors from `coqc`:")
                    for error in errors:
                        print(error, end='')
                    sys.exit(1)
    except Exception as e:
        print(f"Error running `coqc`: {e}")
        sys.exit(1)
    finally:
        os.remove(check_file_dir)
    return outputs


def extract_assumptions(assumption_outputs: List[str]) -> Tuple[List, set, List]:
    marker_pattern = re.compile(r"^<<<(.+?) : (.+?)>>>$")
    axiom_name_pattern = re.compile(r"^(\S+) :(.*)$")

    current_name = None
    expected_assumptions = []
    current_expected_assumptions: List[str] = []
    current_unexpected_assumptions: List[str] = []
    in_assumption_block = False
    unexpected_assumptions = []
    # TODO: record the signature of each unexpected axiom beside its name
    unexpected_axioms = set()

    for assumption_output in assumption_outputs:
        stripped = assumption_output.strip()

        marker_match = marker_pattern.match(assumption_output)
        if marker_match:
            if current_name:
                if current_expected_assumptions:
                    expected_assumptions.append((current_name, current_expected_assumptions))
                if current_unexpected_assumptions:
                    unexpected_assumptions.append((current_name, current_unexpected_assumptions))
            path = marker_match.group(1)
            lemma = marker_match.group(2)
            current_name = f"{path} - {lemma}"
            current_expected_assumptions = []
            current_unexpected_assumptions = []
            in_assumption_block = False
            continue

        if stripped.startswith("Axioms:"):
            in_assumption_block = True
            assert (not current_expected_assumptions) and (not current_unexpected_assumptions)
            continue

        if stripped.startswith("Closed under the global context"):
            in_assumption_block = False
            assert (not current_expected_assumptions) and (not current_unexpected_assumptions)
            continue

        axiom_name_match = axiom_name_pattern.match(assumption_output)
        if in_assumption_block and axiom_name_match:
            axiom_name: str = local_axiom_name(axiom_name_match.group(1))
            if axiom_name in expected_axioms:
                current_expected_assumptions.append(axiom_name)
            else:
                current_unexpected_assumptions.append(axiom_name)
                unexpected_axioms.add(axiom_name)

    return expected_assumptions, unexpected_axioms, unexpected_assumptions


def find_all_v_files(directory: Path) -> list:
    return sorted(list(directory.rglob("*.v")))


def main(project_dir: str, output_dir: Optional[str] = None):
    project_path = Path(project_dir)
    v_files = find_all_v_files(project_path)
    all_lemma_names = []
    for f in v_files:
        rel_path, lemma_names, _ = gather_lemmas(f, project_path)
        all_lemma_names.append((rel_path, lemma_names))

    check_file_dir = create_assumption_file(all_lemma_names, project_path)
    assumption_outputs = get_assumptions(check_file_dir, project_path)
    _, unexpected_axioms, unexpected_assumptions = extract_assumptions(assumption_outputs)

    if unexpected_axioms:
        print("Unexpected axiom usage:")
        print(unexpected_axioms)

        print("\nDetailed usage:")
        for unexpected_assumption in unexpected_assumptions:
            print(unexpected_assumption)
        sys.exit(1)
    else:
        print(f"Allowed axioms are {expected_axioms}.")
        print("No unexpected axiom usage.")

    if output_dir is not None:
        assert os.access(os.path.dirname(output_dir), os.W_OK)
        with open(output_dir, "w+", encoding="utf-8") as f:
            for unexpected_assumption in unexpected_assumptions:
                f.write(str(unexpected_assumption))


if __name__ == "__main__":
    DEFAULT_DIR = str(Path.joinpath(Path(os.path.dirname(os.path.abspath(__file__))).parent, "./theories"))
    parser = argparse.ArgumentParser(
        prog='Check the axiom usage of every lemma/theorem/corollaries in a given directory (default "../theories/")'
    )
    parser.add_argument("--project_dir", default=DEFAULT_DIR)
    parser.add_argument("--output_dir", default=None)
    args = parser.parse_args()
    main(args.project_dir, args.output_dir)
