# SPDX-License-Identifier: Apache-2.0
"""Compare the adopted witness with an externally supplied, pinned CBETA XML.

The XML is not redistributed. Pass its downloaded path as the sole argument.
The report distinguishes CBETA's edited running text from Taisho apparatus.
"""

import difflib
import hashlib
from pathlib import Path
import sys
import unicodedata
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parents[1]
XML_SHA256 = "f5507df86309f861ef2b92e9ba9db985c6db0ad357553599c6e921e15deca761"


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: compare_cbeta_witness.py PINNED_XML")
    raw = Path(sys.argv[1]).read_bytes()
    if hashlib.sha256(raw).hexdigest() != XML_SHA256:
        raise SystemExit("XML checksum differs from the audited pinned source")
    root = ET.fromstring(raw)
    divisions = [node for node in root.iter()
                 if node.tag.endswith("}div") and node.get("type") == "jing"]
    if len(divisions) != 1:
        raise SystemExit("expected one sutra-body division")
    text = "".join(divisions[0].itertext())
    cbeta = "".join(ch for ch in text if not ch.isspace()
                    and not unicodedata.category(ch).startswith("P"))
    adopted = (ROOT / "sources/text/heart-sutra-t251-received-262.txt").read_text(
        encoding="utf-8").removesuffix("\n")
    expected = cbeta.replace("遠離顛倒夢想", "遠離一切顛倒夢想")
    expected = expected.replace("帝", "諦").replace("般羅", "波羅")
    expected = expected.replace("莎婆", "薩婆")
    if len(cbeta) != 260 or len(adopted) != 262 or expected != adopted:
        raise SystemExit("body count or declared variant comparison changed")
    print("Pinned CBETA T08n0251, running text at T08.0848c06-22")
    print(f"XML SHA-256: {XML_SHA256}")
    print("Excluded: titles, bylines, prefaces, apparatus, punctuation, whitespace")
    print(f"CBETA running body: {len(cbeta)} codepoints; adopted body: {len(adopted)}")
    print("Differences, zero-based half-open offsets (CBETA -> adopted):")
    for tag, i, j, k, l in difflib.SequenceMatcher(None, cbeta, adopted,
                                                 autojunk=False).get_opcodes():
        if tag != "equal":
            print(f"  {tag}: [{i}:{j}] {cbeta[i:j]!r} -> [{k}:{l}] {adopted[k:l]!r}")
    print("Only length change: insertion of 一切 after 遠離 (+2).")
    print("Mantra: 帝->諦 (4), 般羅->波羅 (2), 莎婆->薩婆 (1).")
    print("At 0848c22 CBETA reads 莎婆; its apparatus records Taisho 僧莎")
    print("and Song/Yuan/Ming 薩婆. These are distinct witnesses, not one base text.")
    print("PASS: the declared variants reconstruct the adopted witness exactly.")


if __name__ == "__main__":
    main()
