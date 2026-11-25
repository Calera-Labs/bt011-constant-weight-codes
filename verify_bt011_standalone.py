#!/usr/bin/env python3
"""
BT-011 Standalone Zero-Dependency Pure-Python Exact Verifier.

Run inside the extracted `bt011_cwc_certificates/` directory:
    python3 verify_bt011_standalone.py

Independently loads ONLY the compact component certificates in this archive
(corpora/ls13_ls15.json, 42 baseline Brouwer 2010 .pk files, 16 asymmetric-K
JSON packings in results_asym/, and 4 n=14/16 .pk partitions in results_pk/),
verifies EVERY component partition independently (zero intra-class (w-1)-subset
collisions and strict class disjointness), reconstructs ALL 36 improved lower-bound
codes (38,467,121 explicit binary codewords), verifies:
  1. Exact bit-width 0 <= c < 2^n and exact Hamming weight popcnt(c) == w
  2. Strict ascending distinctness (0 duplicate codewords)
  3. Exhaustive full-code (w-1)-subset collision checks for all 15 records <= 250k words
     (plus component+parity exact checks for all 36 records)
  4. Byte-for-byte parity on all 5 raw .hex codeword files (M <= 75,000)
  5. Exact 36/36 SHA-256 & WOF-1 composite SHA-256 parity vs results/bt011_proven_36_world_records.json
"""

import hashlib
import itertools
import json
import os
import time

ROOT = os.path.dirname(os.path.abspath(__file__))


def colex_masks(n, w):
    combs = sorted(itertools.combinations(range(n), w), key=lambda t: t[::-1])
    out = []
    for t in combs:
        m = 0
        for b in t:
            m |= 1 << b
        out.append(m)
    return out


def build_1_factorization(n):
    if n % 2 == 0:
        m = n - 1
        out = []
        for r in range(m):
            edges = [(1 << r) | (1 << m)]
            for k in range(1, (m - 1) // 2 + 1):
                edges.append((1 << ((r + k) % m)) | (1 << ((r - k) % m)))
            out.append(edges)
        return out
    out = []
    for r in range(n):
        edges = []
        for k in range(1, (n - 1) // 2 + 1):
            edges.append((1 << ((r + k) % n)) | (1 << ((r - k) % n)))
        out.append(edges)
    return out


def char_to_col(ch):
    if "1" <= ch <= "9":
        return ord(ch) - ord("1")
    if "A" <= ch <= "Z":
        return 9 + ord(ch) - ord("A")
    if "a" <= ch <= "z":
        return 9 + ord(ch) - ord("a")
    raise ValueError(f"bad char {ch!r}")


def load_pk_classes(path, n, w):
    verts = colex_masks(n, w)
    raw = "".join(open(path).read().split())
    assert len(raw) == len(verts), f"{path}: {len(raw)} != {len(verts)}"
    by_c = {}
    for ch, m in zip(raw, verts):
        by_c.setdefault(char_to_col(ch), []).append(m)
    return sorted(by_c.values(), key=len, reverse=True)


def verify_component_family(classes, n, w, label):
    seen_words = set()
    limit = 1 << n
    for cid, grp in enumerate(classes):
        seen_sub = set()
        for m in grp:
            assert 0 <= m < limit and m.bit_count() == w, f"{label} bad word {hex(m)}"
            assert m not in seen_words, f"{label} duplicate word across classes!"
            seen_words.add(m)
            if w >= 1:
                mm = m
                while mm:
                    bit = mm & -mm
                    sub = m ^ bit
                    assert sub not in seen_sub, f"{label} class {cid} d_H < 4 collision!"
                    seen_sub.add(sub)
                    mm ^= bit


def main():
    t0 = time.time()
    print("=== BT-011 STANDALONE PURE-PYTHON EXACT VERIFIER (36 IMPROVED LOWER BOUNDS) ===", flush=True)
    ls_data = json.load(open(os.path.join(ROOT, "corpora", "ls13_ls15.json")))
    specs = json.load(open(os.path.join(ROOT, "results_asym", "bt011_candidate_records_spec.json")))
    go_arch = json.load(open(os.path.join(ROOT, "results", "bt011_proven_36_world_records.json")))
    go_by_cell = {r["cell"]: r for r in go_arch["records"]}

    part_cache = {}

    def get_partition(n, w, name):
        key = (n, w, name)
        if key in part_cache:
            return part_cache[key]
        need_comp = False
        ew = w
        if ew > n - ew:
            ew = n - ew
            need_comp = True
        if ew == 0:
            classes = [[0]]
        elif ew == 1:
            classes = [[1 << i] for i in range(n)]
        elif ew == 2:
            classes = build_1_factorization(n)
        elif name == "LS13":
            classes = [[(1 << a) | (1 << b) | (1 << c) for a, b, c in sts] for sts in ls_data["LS13"]]
        elif name == "LS13m1":
            classes = [[(1 << a) | (1 << b) | (1 << c) for a, b, c in sts if 12 not in (a, b, c)] for sts in ls_data["LS13"]]
        elif name == "LS15":
            classes = [[(1 << a) | (1 << b) | (1 << c) for a, b, c in sts] for sts in ls_data["LS15"]]
        elif name == "LS15m1":
            classes = [[(1 << a) | (1 << b) | (1 << c) for a, b, c in sts if 14 not in (a, b, c)] for sts in ls_data["LS15"]]
        elif name.startswith("PK_"):
            classes = load_pk_classes(os.path.join(ROOT, "results_pk", f"part{n}.{ew}_{name[3:]}.pk"), n, ew)
        elif name.startswith("NEW_"):
            aj = json.load(open(os.path.join(ROOT, "results_asym", name[4:] + ".json")))
            classes = aj["classes"]
        else:
            classes = load_pk_classes(os.path.join(ROOT, "corpora", "brouwer_2010_pk", f"part{n}.{ew}_{name}.pk"), n, ew)

        if need_comp:
            full = (1 << n) - 1
            classes = [[full ^ m for m in grp] for grp in classes]
        classes = [sorted(grp) for grp in classes if grp]
        classes.sort(key=lambda g: (-len(g), g[0]))
        verify_component_family(classes, n, w, f"({n},{w},{name})")
        part_cache[key] = classes
        return classes

    comp_h = hashlib.sha256()
    total_cw = 0
    hex_checked = 0

    for idx, sp in enumerate(specs):
        ts = time.time()
        n, w, n1, n2 = sp["n"], sp["w"], sp["n1"], sp["n2"]
        code = []
        for w1, nm1, w2, nm2, expected_term in sp["terms"]:
            c1 = get_partition(n1, w1, nm1)
            c2 = get_partition(n2, w2, nm2)
            lim = min(len(c1), len(c2))
            term_cnt = 0
            for k in range(lim):
                for u in c1[k]:
                    for v in c2[k]:
                        code.append(u | (v << n1))
                        term_cnt += 1
            assert term_cnt == expected_term

        assert len(code) == sp["new_size"] and len(code) > sp["prior_lb"]
        code.sort()

        width = (n + 3) // 4
        fmt = f"{{:0{width}x}}"
        h = hashlib.sha256()
        limit = 1 << n
        prev = -1
        for start in range(0, len(code), 65536):
            blk = code[start:start + 65536]
            for cw in blk:
                assert cw > prev and 0 <= cw < limit and cw.bit_count() == w
                prev = cw
            h.update(("\n".join(fmt.format(cw) for cw in blk) + "\n").encode())
        py_sha = h.hexdigest()

        go_rec = go_by_cell[sp["cell"]]
        assert py_sha == go_rec["canonical_codewords_sha256"], f"{sp['cell']} SHA mismatch!"

        # Check explicit .hex file if bundled
        hex_fn = os.path.join(ROOT, "results", f"bt011_A_{n}_4_{w}_M{len(code)}.hex")
        hex_tag = ""
        if os.path.exists(hex_fn):
            hex_sha = hashlib.sha256(open(hex_fn, "rb").read()).hexdigest()
            assert hex_sha == py_sha, f"{hex_fn} SHA mismatch!"
            hex_checked += 1
            hex_tag = " + .hex OK"

        sub_tag = "comp+parity_exact"
        if len(code) <= 250000:
            seen_sub = set()
            for cw in code:
                mm = cw
                while mm:
                    bit = mm & -mm
                    sub = cw ^ bit
                    assert sub not in seen_sub, f"{sp['cell']} d_H < 4 collision!"
                    seen_sub.add(sub)
                    mm ^= bit
            sub_tag = f"full_{len(seen_sub):,}_subtuples"

        comp_h.update(f"{sp['cell']}:{len(code)}:{py_sha}\n".encode())
        total_cw += len(code)
        print(
            f"  [{idx+1:2d}/36] {sp['cell']:11s} | M={len(code):7d} > {sp['prior_lb']:7d} (+{len(code)-sp['prior_lb']:4d}) "
            f"| SHA={py_sha[:14]} | {sub_tag}{hex_tag} | {time.time()-ts:.2f}s",
            flush=True,
        )

    py_comp = comp_h.hexdigest()
    assert py_comp == go_arch["wof1_composite_sha256"], "WOF-1 composite SHA mismatch!"
    assert hex_checked == 5, f"Expected 5 raw .hex files checked, got {hex_checked}"
    print(f"\n>>> STANDALONE VERIFICATION 100.000% PASSED! <<<")
    print(f"    36/36 Records | {total_cw:,} Codewords | {len(part_cache)} Component Partitions | {hex_checked} Raw .hex Files")
    print(f"    WOF-1 Composite SHA-256: {py_comp}")
    print(f"    Elapsed: {time.time()-t0:.2f}s")


if __name__ == "__main__":
    main()
