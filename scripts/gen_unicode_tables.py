#!/usr/bin/env python3
"""gen_unicode_tables.py - the Calculator's Unicode tables, generated from Unicode's files.

  python3 -I scripts/gen_unicode_tables.py                write Principia/Unicode/Tables.lean
  python3 -I scripts/gen_unicode_tables.py --check        regenerate and compare byte for byte
  python3 -I scripts/gen_unicode_tables.py --cross-check  compare the tables with Python's
                                                          unicodedata (it must carry 15.1.0)

Text is normalized to NFC as version 1 does,
from Unicode's data files at the version version 1's `unicodedata` used, 15.1.0 (v1's
generators: "Python 3.13: Unicode 15.1.0"). The inputs are Unicode's own files, committed
unchanged in vectors/unicode/ beside Unicode's licence (LICENSE, Unicode License v3) and
refused unless each has the SHA-256 recorded below:

  UnicodeData.txt            general category, canonical combining class, decompositions
  CompositionExclusions.txt  the composition exclusions that UnicodeData.txt cannot give
  NormalizationTest.txt      not read here; Tests/Unicode.lean runs it (its SHA-256 is checked)

The Lean file holds four table texts, each parsed once by Principia/Unicode.lean:

  combining classes     "START-END:CCC" or "CP:CCC", every code point whose canonical
                        combining class is not 0, CCC in decimal
  decompositions        "CP:D1 D2 ...", every code point with a canonical decomposition but
                        the Hangul syllables (decomposed by Unicode's arithmetic), its full
                        decomposition: the mapping applied again until it no longer applies
  compositions          "FIRST SECOND:COMPOSITE", the primary composites: each canonical
                        mapping of two code points whose code point is not excluded from
                        composition (Full_Composition_Exclusion: CompositionExclusions.txt,
                        the singletons, the non-starter decompositions), Hangul aside
  general categories    "START-END:Gc" or "CP:Gc", every code point not Cn (unassigned)

Code points are upper-case hexadecimal, items are joined by ";" in increasing order. The file
also records the least code point each table reaches (Principia/Unicode.lean's guards and the
theorems over ASCII rest on them) and each table's item count (Tests/Unicode.lean checks that
every item reads). Standard library only.
"""
import hashlib
import os
import sys

VERSION = "15.1.0"
URL = "https://www.unicode.org/Public/15.1.0/ucd/"
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DATA = os.path.join(ROOT, "vectors", "unicode")
OUT = os.path.join(ROOT, "Principia", "Unicode", "Tables.lean")
SOURCES = [
    ("UnicodeData.txt", "2fc713e6a31a87c4850a37fe2caffa4218180fadb5de86b43a143ddb4581fb86"),
    ("CompositionExclusions.txt",
     "59d2d9e3dfdf0a999cf9dae11d594f053631222679a2f5710315ea07f7fe82af"),
    ("NormalizationTest.txt", "871238e37e3be0696ec2bd0891119a041b052da1a84485eda05a5438724b223e"),
]
CATEGORIES = ["Lu", "Ll", "Lt", "Lm", "Lo", "Mn", "Mc", "Me", "Nd", "Nl", "No", "Pc", "Pd",
              "Ps", "Pe", "Pi", "Pf", "Po", "Sm", "Sc", "Sk", "So", "Zs", "Zl", "Zp", "Cc",
              "Cf", "Cs", "Co", "Cn"]
# Hangul (Unicode 15.1.0, section 3.12).
S_BASE, L_BASE, V_BASE, T_BASE = 0xAC00, 0x1100, 0x1161, 0x11A7
L_COUNT, V_COUNT, T_COUNT = 19, 21, 28
N_COUNT = V_COUNT * T_COUNT
S_COUNT = L_COUNT * N_COUNT
LAST = 0x10FFFF
WIDTH = 96


def fail(msg):
    print("gen_unicode_tables: " + msg, file=sys.stderr)
    sys.exit(1)


def read_source(name, digest):
    """A source file's bytes, refused unless its SHA-256 is the recorded one."""
    path = os.path.join(DATA, name)
    try:
        with open(path, "rb") as f:
            data = f.read()
    except OSError as e:
        fail("cannot read %s (%s); fetch %s%s" % (path, e, URL, name))
    got = hashlib.sha256(data).hexdigest()
    if got != digest:
        fail("%s has SHA-256 %s, not Unicode %s's %s; refused" % (name, got, VERSION, digest))
    return data


def unicode_data(text):
    """Per code point: general category, combining class, canonical mapping (or None)."""
    gc, ccc, canon = {}, {}, {}
    first = None
    for n, line in enumerate(text.split("\n"), 1):
        if not line:
            continue
        f = line.split(";")
        if len(f) != 15:
            fail("UnicodeData.txt:%d: %d fields, not 15" % (n, len(f)))
        cp = int(f[0], 16)
        if f[1].endswith(", First>"):
            first = cp
            continue
        lo = cp
        if f[1].endswith(", Last>"):
            if first is None:
                fail("UnicodeData.txt:%d: a range's Last without its First" % n)
            lo, first = first, None
            if f[5]:
                fail("UnicodeData.txt:%d: a range with a decomposition" % n)
        if f[2] not in CATEGORIES:
            fail("UnicodeData.txt:%d: unknown general category %s" % (n, f[2]))
        for c in range(lo, cp + 1):
            gc[c] = f[2]
            if int(f[3]):
                ccc[c] = int(f[3])
        if f[5] and not f[5].startswith("<"):
            canon[cp] = [int(x, 16) for x in f[5].split()]
    return gc, ccc, canon


def exclusions(text):
    """The code points CompositionExclusions.txt lists."""
    out = set()
    for line in text.split("\n"):
        body = line.split("#", 1)[0].strip()
        if body:
            out.add(int(body, 16))
    return out


def full(cp, canon):
    """The full canonical decomposition of a code point (Hangul aside)."""
    if cp not in canon:
        return [cp]
    return [d for c in canon[cp] for d in full(c, canon)]


def runs(values):
    """Maximal runs (lo, hi, value) of equal values over a dict code point -> value."""
    out = []
    for cp in sorted(values):
        v = values[cp]
        if out and out[-1][1] == cp - 1 and out[-1][2] == v:
            out[-1] = (out[-1][0], cp, v)
        else:
            out.append((cp, cp, v))
    return out


def span(lo, hi):
    return ("%X" % lo) if lo == hi else ("%X-%X" % (lo, hi))


def tables(sources):
    gc, ccc, canon = unicode_data(sources["UnicodeData.txt"].decode("ascii"))
    excluded = exclusions(sources["CompositionExclusions.txt"].decode("utf-8"))
    hangul = range(S_BASE, S_BASE + S_COUNT)
    if any(c in canon for c in hangul):
        fail("UnicodeData.txt maps a Hangul syllable")
    if any(c not in canon for c in excluded):
        fail("CompositionExclusions.txt lists a code point with no canonical mapping")
    decomp = {cp: full(cp, canon) for cp in canon}
    # Full_Composition_Exclusion: the listed exclusions, the singletons and the non-starter
    # decompositions (Unicode Standard Annex 15, sections 1.3 and X.2 of the Unicode Standard's chapter 3).
    comp = {}
    for cp, m in canon.items():
        if len(m) != 2 or cp in excluded or ccc.get(cp, 0) or ccc.get(m[0], 0):
            continue
        if (m[0], m[1]) in comp:
            fail("two composites for one pair")
        comp[(m[0], m[1])] = cp
    floors = {
        "combining": min(ccc),
        "decomposition": min(min(decomp), S_BASE),
        "second": min(min(b for _, b in comp), V_BASE, T_BASE + 1),
    }
    ccc_text = ";".join("%s:%d" % (span(lo, hi), v) for lo, hi, v in runs(ccc))
    decomp_text = ";".join("%X:%s" % (cp, " ".join("%X" % d for d in decomp[cp]))
                           for cp in sorted(decomp))
    comp_text = ";".join("%X %X:%X" % (a, b, comp[(a, b)]) for a, b in sorted(comp))
    gc_text = ";".join("%s:%s" % (span(lo, hi), v)
                       for lo, hi, v in runs({c: k for c, k in gc.items() if k != "Cn"}))
    return {
        "combining": (ccc_text, len(runs(ccc))),
        "decomposition": (decomp_text, len(decomp)),
        "composition": (comp_text, len(comp)),
        "category": (gc_text, len(runs({c: k for c, k in gc.items() if k != "Cn"}))),
        "floors": floors,
    }


def literal(text):
    """A Lean string literal over lines of at most WIDTH characters, broken after a ';' and
    continued by string gaps (a backslash ending the line)."""
    lines, cur = [], ""
    for item in text.split(";"):
        piece = item if not cur else ";" + item
        if cur and len(cur) + len(piece) > WIDTH - 6:
            lines.append(cur + ";")
            cur = item
        else:
            cur += piece
    lines.append(cur)
    return "\n".join(("  \"" if i == 0 else "    ") + ln + ("\\" if i < len(lines) - 1 else "\"")
                     for i, ln in enumerate(lines))


def lean(t):
    fl = t["floors"]
    out = [
        "/-!",
        "# Unicode %s's tables (generated; do not edit)" % VERSION,
        "",
        "Written by the Unicode tables' generator from Unicode's data files at %s," % VERSION,
        "which are kept unchanged beside the library under Unicode's licence; the generator's",
        "check regenerates this file and compares it byte for byte. The format of each table",
        "text is the generator's; `Principia.Unicode` parses each once.",
        "-/",
        "",
        "namespace Principia.Unicode.Tables",
        "",
        "/-- The Unicode version the tables are generated at. -/",
        "def unicodeVersion : String := \"%s\"" % VERSION,
        "",
        "/-- Each source file and its SHA-256, which the generator checks before reading it. -/",
        "def sources : List (String × String) := [",
    ]
    for i, (name, digest) in enumerate(SOURCES):
        out.append("  (\"%s\",\n    \"%s\")%s" % (name, digest, "," if i < len(SOURCES) - 1 else "]"))
    out += [
        "",
        "/-- The least code point whose canonical combining class is not 0. -/",
        "def combiningFloor : Nat := 0x%X" % fl["combining"],
        "",
        "/-- The least code point with a canonical decomposition, the Hangul syllables included. -/",
        "def decompositionFloor : Nat := 0x%X" % fl["decomposition"],
        "",
        "/-- The least code point that is ever the second of a canonical composition, Hangul's",
        "included. -/",
        "def compositionSecondFloor : Nat := 0x%X" % fl["second"],
        "",
    ]
    docs = {
        "combining": ("combiningClassText", "combiningClassCount",
                      "Every code point whose canonical combining class is not 0, in runs:\n"
                      "`START-END:CCC` or `CP:CCC`, the class in decimal."),
        "decomposition": ("decompositionText", "decompositionCount",
                          "Every code point with a canonical decomposition, Hangul syllables\n"
                          "aside, and its full canonical decomposition: `CP:C1 C2 ...`."),
        "composition": ("compositionText", "compositionCount",
                        "The primary composites, Hangul aside: `FIRST SECOND:COMPOSITE`, ordered"
                        "\nby the pair."),
        "category": ("generalCategoryText", "generalCategoryCount",
                     "Every code point's general category but Cn, in runs: `START-END:Gc` or\n"
                     "`CP:Gc`; a code point in no run is Cn (unassigned)."),
    }
    for key in ("combining", "decomposition", "composition", "category"):
        name, count, doc = docs[key]
        text, n = t[key]
        out += [
            "/-- %s -/" % doc,
            "def %s : String :=" % name,
            literal(text),
            "",
            "/-- The number of items in `%s`. -/" % name,
            "def %s : Nat := %d" % (count, n),
            "",
        ]
    out += ["end Principia.Unicode.Tables", ""]
    return "\n".join(out)


def parse_back(t):
    """The four texts read back as Principia/Unicode.lean reads them."""
    def hx(s):
        return int(s, 16)
    ccc, gc, decomp, comp = {}, {}, {}, {}
    for item in t["combining"][0].split(";"):
        r, v = item.split(":")
        lo, _, hi = r.partition("-")
        for c in range(hx(lo), hx(hi or lo) + 1):
            ccc[c] = int(v)
    for item in t["category"][0].split(";"):
        r, v = item.split(":")
        lo, _, hi = r.partition("-")
        for c in range(hx(lo), hx(hi or lo) + 1):
            gc[c] = v
    for item in t["decomposition"][0].split(";"):
        c, ds = item.split(":")
        decomp[hx(c)] = [hx(d) for d in ds.split(" ")]
    for item in t["composition"][0].split(";"):
        ab, c = item.split(":")
        a, b = ab.split(" ")
        comp[(hx(a), hx(b))] = hx(c)
    return ccc, gc, decomp, comp


def reference_nfc(s, ccc, decomp, comp, compose=True):
    """NFD (compose=False) or NFC of a list of code points, on the tables read back."""
    out = []
    for c in s:
        if S_BASE <= c < S_BASE + S_COUNT:
            i = c - S_BASE
            out += [L_BASE + i // N_COUNT, V_BASE + (i % N_COUNT) // T_COUNT]
            if i % T_COUNT:
                out.append(T_BASE + i % T_COUNT)
        else:
            out += decomp.get(c, [c])
    i = 0
    while i < len(out):  # canonical ordering: stable sort of each run of non-starters
        if ccc.get(out[i], 0) == 0:
            i += 1
            continue
        j = i
        while j < len(out) and ccc.get(out[j], 0):
            j += 1
        out[i:j] = sorted(out[i:j], key=lambda c: ccc.get(c, 0))
        i = j
    if not compose:
        return out
    res, starter, last = [], None, 0
    for c in out:
        k = ccc.get(c, 0)
        if starter is not None and (last == 0 or last < k):
            a = res[starter]
            x = None
            if L_BASE <= a < L_BASE + L_COUNT and V_BASE <= c < V_BASE + V_COUNT:
                x = S_BASE + ((a - L_BASE) * V_COUNT + (c - V_BASE)) * T_COUNT
            elif (S_BASE <= a < S_BASE + S_COUNT and (a - S_BASE) % T_COUNT == 0
                  and T_BASE < c < T_BASE + T_COUNT):
                x = a + (c - T_BASE)
            else:
                x = comp.get((a, c))
            if x is not None:
                res[starter] = x
                continue
        if k == 0:
            starter = len(res)
        last = k
        res.append(c)
    return res


def cross_check(t, sources):
    import unicodedata
    if unicodedata.unidata_version != VERSION:
        fail("this Python's unicodedata is %s, not %s: no cross-check"
             % (unicodedata.unidata_version, VERSION))
    ccc, gc, decomp, comp = parse_back(t)
    bad = 0
    for cp in range(LAST + 1):
        ch = chr(cp)
        s = [cp]
        if gc.get(cp, "Cn") != unicodedata.category(ch):
            bad += 1
            print("category U+%04X: %s, unicodedata %s" % (cp, gc.get(cp, "Cn"),
                                                           unicodedata.category(ch)))
        if ccc.get(cp, 0) != unicodedata.combining(ch):
            bad += 1
            print("combining class U+%04X" % cp)
        if [ord(c) for c in unicodedata.normalize("NFD", ch)] != reference_nfc(s, ccc, decomp,
                                                                              comp, False):
            bad += 1
            print("NFD U+%04X" % cp)
        if [ord(c) for c in unicodedata.normalize("NFC", ch)] != reference_nfc(s, ccc, decomp,
                                                                              comp):
            bad += 1
            print("NFC U+%04X" % cp)
    pairs = 0
    for (a, b), c in comp.items():
        pairs += 1
        if unicodedata.normalize("NFC", chr(a) + chr(b)) != chr(c):
            bad += 1
            print("composition U+%04X U+%04X" % (a, b))
    lines = 0
    for line in sources["NormalizationTest.txt"].decode("utf-8").split("\n"):
        body = line.split("#", 1)[0].strip()
        if not body or body.startswith("@"):
            continue
        cols = [[int(x, 16) for x in c.split()] for c in body.split(";")[:5]]
        lines += 1
        for i, c in enumerate(cols):
            want = cols[1] if i < 3 else cols[3]
            py = [ord(x) for x in unicodedata.normalize("NFC", "".join(map(chr, c)))]
            if reference_nfc(c, ccc, decomp, comp) != want or py != want:
                bad += 1
                print("NormalizationTest NFC: %s" % body)
    print("cross-check against unicodedata %s: %d code points (general category, combining "
          "class, NFD, NFC), %d composition pairs, %d NormalizationTest lines (NFC of all five "
          "columns, by the tables and by unicodedata): %d disagreements"
          % (unicodedata.unidata_version, LAST + 1, pairs, lines, bad))
    return bad == 0


def main(argv):
    mode = argv[1] if len(argv) > 1 else ""
    if mode not in ("", "--check", "--cross-check") or len(argv) > 2:
        fail("usage: gen_unicode_tables.py [--check | --cross-check]")
    sources = {name: read_source(name, digest) for name, digest in SOURCES}
    t = tables(sources)
    text = lean(t)
    if mode == "--cross-check":
        return 0 if cross_check(t, sources) else 1
    if mode == "--check":
        try:
            with open(OUT, "rb") as f:
                have = f.read()
        except OSError:
            have = b""
        if have != text.encode("utf-8"):
            print("gen_unicode_tables: %s differs from what Unicode %s's files give; "
                  "regenerate with python3 -I scripts/gen_unicode_tables.py"
                  % (os.path.relpath(OUT, ROOT), VERSION), file=sys.stderr)
            return 1
        print("gen_unicode_tables: %s is what Unicode %s's files give (sources' SHA-256 "
              "checked)" % (os.path.relpath(OUT, ROOT), VERSION))
        return 0
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w", encoding="utf-8", newline="\n") as f:
        f.write(text)
    print("gen_unicode_tables: wrote %s: %d combining-class runs, %d decompositions, %d "
          "compositions, %d general-category runs" % (
              os.path.relpath(OUT, ROOT), t["combining"][1], t["decomposition"][1],
              t["composition"][1], t["category"][1]))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
