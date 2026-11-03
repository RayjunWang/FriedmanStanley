"""Build a source-only GitHub archive with an explicit, credential-free file list."""
from pathlib import Path
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT.parent / "fs-cofinality-lean-github.zip"
DIRECTORIES = ("Definitions", "FSCofinalityProof", "Solutions", "Prove2Me")
ROOT_FILES = (
    "README.md", "lakefile.lean", "lake-manifest.json", "lean-toolchain",
    ".gitignore", "FSCofinalityProof.lean", "AuditAll.lean", "AuditMain.lean",
    "AuditRoot.lean", "AuditParameterSequences.lean", "tools/package_project.py",
    "Prove2Me/README.md",
)
PUBLIC_DOCS = (
    "docs/progress.md", "docs/verification.md", "docs/proof-outline.md",
    "docs/prove2me-acceptance.json",
)


def main():
    paths = [ROOT / name for name in ROOT_FILES]
    paths += [p for directory in DIRECTORIES
              for p in sorted((ROOT / directory).rglob("*.lean"))]
    paths += [ROOT / name for name in PUBLIC_DOCS if (ROOT / name).is_file()]
    paths += sorted((ROOT / "docs" / "readbacks").glob("*.md"))
    if not all(p.is_file() for p in paths):
        raise RuntimeError("Missing required release file")
    manifest = {
        "format": 1,
        "files": [{"path": p.relative_to(ROOT).as_posix(),
                   "sha256": hashlib.sha256(p.read_bytes()).hexdigest(),
                   "bytes": p.stat().st_size} for p in paths],
    }
    manifest_bytes = (json.dumps(manifest, indent=2) + "\n").encode("utf-8")
    (ROOT / "docs" / "source-manifest.json").write_bytes(manifest_bytes)
    with zipfile.ZipFile(DEST, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        for p in paths:
            archive.write(p, "fs-cofinality-lean/" + p.relative_to(ROOT).as_posix())
        archive.writestr("fs-cofinality-lean/docs/source-manifest.json", manifest_bytes)
    print(json.dumps({"archive": str(DEST), "files": len(paths) + 1,
                      "bytes": DEST.stat().st_size,
                      "sha256": hashlib.sha256(DEST.read_bytes()).hexdigest()}))


if __name__ == "__main__":
    main()
