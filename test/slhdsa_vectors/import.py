#!/usr/bin/env python3
"""Import additional public-API SLH-DSA vectors from a pinned ACVP checkout."""

import argparse
import hashlib
import json
from pathlib import Path


# NIST ACVP-Server revision 975de31eb83d87039ec88934fdc47d8c312b892d.
SOURCES = {
    "SLH-DSA-sigGen-FIPS205/prompt.json":
        "afa673eacdf0aec53512a159159b7632684adfcd0d88f8640a7f6f5796aacdc8",
    "SLH-DSA-sigGen-FIPS205/expectedResults.json":
        "71e8e0f7e4b0cfd1747314299204d9d4d50968d200a4ae873921eaa7aabeaad1",
    "SLH-DSA-sigVer-FIPS205/prompt.json":
        "4e7beb1233e47baa0acdd36417c66c45811aa40a4e32ffdb1a35d93b13b289fb",
    "SLH-DSA-sigVer-FIPS205/expectedResults.json":
        "259f5e2a0665de0adc0fefa45b5db3a2a6ed13c3c44d14bdaf64a80aee12c687",
}


def load_sources(source_dir):
    documents = {}
    for name, expected in SOURCES.items():
        data = (source_dir / name).read_bytes()
        if hashlib.sha256(data).hexdigest() != expected:
            raise SystemExit(f"Source checksum mismatch: {name}")
        documents[name] = json.loads(data)
    return documents


def external_groups(document):
    return [group for group in document["testGroups"]
            if group.get("signatureInterface") == "external"
            and group.get("preHash") == "pure"]


def expected_tests(document):
    return {(group["tgId"], test["tcId"]): test
            for group in document["testGroups"] for test in group["tests"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source_dir", type=Path,
                        help="ACVP-Server gen-val/json-files directory")
    parser.add_argument("target_dir", type=Path)
    args = parser.parse_args()
    documents = load_sources(args.source_dir)

    generation = documents["SLH-DSA-sigGen-FIPS205/prompt.json"]
    generated = expected_tests(documents["SLH-DSA-sigGen-FIPS205/expectedResults.json"])
    signatures = []
    for group in external_groups(generation):
        # Keep expensive signing bounded: an 8192-byte message for deterministic
        # signing, and the maximum 255-byte context for hedged signing, per set.
        deterministic = group["deterministic"]
        test = (max(group["tests"], key=lambda item: len(item["message"]))
                if deterministic
                else max(group["tests"], key=lambda item: len(item["context"])))
        expected = generated[group["tgId"], test["tcId"]]
        signatures.append([
            group["parameterSet"], f'{group["tgId"]}/{test["tcId"]}',
            "deterministic" if deterministic else "hedged", test["sk"],
            test["message"], test["context"], test.get("additionalRandomness", ""),
            expected["signature"],
        ])

    verification = documents["SLH-DSA-sigVer-FIPS205/prompt.json"]
    verified = expected_tests(documents["SLH-DSA-sigVer-FIPS205/expectedResults.json"])
    verifications = []
    for group in external_groups(verification):
        for test in group["tests"]:
            expected = verified[group["tgId"], test["tcId"]]
            verifications.append([
                group["parameterSet"], f'{group["tgId"]}/{test["tcId"]}',
                test["pk"], test["message"], test["context"], test["signature"],
                "valid" if expected["testPassed"] else "invalid",
            ])

    assert len(signatures) == 24
    assert len(verifications) == 168
    assert sum(row[-1] == "valid" for row in verifications) == 24
    args.target_dir.mkdir(parents=True, exist_ok=True)
    checksums = []
    for name, rows in [("siggen-extra.txt", signatures), ("sigver.txt", verifications)]:
        data = ("\n".join("\t".join(row) for row in rows) + "\n").encode("ascii")
        (args.target_dir / name).write_bytes(data)
        checksums.append(f"{hashlib.sha256(data).hexdigest()}  {name}\n")
        print(f"{name}: {len(rows)} cases")
    (args.target_dir / "SHA256SUMS").write_text("".join(checksums))
    (args.target_dir / "SOURCE_SHA256SUMS").write_text(
        "".join(f"{digest}  {name}\n" for name, digest in SOURCES.items()))


if __name__ == "__main__":
    main()
