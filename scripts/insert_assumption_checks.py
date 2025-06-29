import re
import sys
from pathlib import Path

COQ_ID = r"[A-Za-z_][A-Za-z0-9_']*"

def insert_debug_blocks_in_file(file_path: Path, root_dir: Path):
    content = file_path.read_text(encoding='utf-8')
    decl_pattern = re.compile(rf'^([ \t]*)(Lemma|Theorem|Corollary)\s+({COQ_ID})', re.MULTILINE)
    matches = list(decl_pattern.finditer(content))

    rel_path = f"./{file_path.relative_to(root_dir)}"

    for match in reversed(matches):
        indentation = match.group(1)
        name = match.group(3)
        start_pos = match.end()

        qed_pattern = re.compile(r'.*(Qed\.|Defined\.|Admitted\.)', re.MULTILINE)
        qed_match = qed_pattern.search(content, pos=start_pos)

        if qed_match:
            insert_pos = qed_match.end()
            marker = f"{rel_path} - {name}"
            snippet = (
                f'\n{indentation}Goal True. idtac "<<<{marker}>>>". Abort.\n'
                f'{indentation}Print Assumptions {name}.'
            )
            content = content[:insert_pos] + snippet + content[insert_pos:]

    file_path.write_text(content, encoding='utf-8')

def find_all_v_files(directory: Path) -> list:
    return sorted(list(directory.rglob('*.v')))

def main():
    if len(sys.argv) != 2:
        print("Usage: python insert_assumption_checks.py <directory>")
        sys.exit(1)

    root_dir = Path(sys.argv[1]).resolve()
    if not root_dir.is_dir():
        print(root_dir)
        insert_debug_blocks_in_file(root_dir, '/')
        return 0

    print(f"Inserting debug statements into all .v files under: {root_dir}")
    v_files = find_all_v_files(root_dir)
    for f in v_files:
        insert_debug_blocks_in_file(f, root_dir)

if __name__ == "__main__":
    main()
