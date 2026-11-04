#!/usr/bin/env python3
"""Decide the exact width conditions derived in BV_LEAN/QF_BV/EXACT_CONDITIONS.md.

No SMT solver or third-party package. Bad widths include constructive witnesses.
Square cases use modular root lifting, rather than enumerating all 2**n words.
Numerical verification is an independent check, not a substitute for the proofs.
"""
from __future__ import annotations
import argparse
import csv
from pathlib import Path

RULES = (223, 238, 270, 271, 296, 298, 301, 379, 380, 458, 473, 477, 522, 669, 670, 719, 1101, 1246, 1343)


def valuation2(a: int) -> int:
    assert a > 0
    return (a & -a).bit_length() - 1


def balanced(n: int, a: int, q: int) -> bool:
    # These branches also avoid constructing powers with a potentially huge q.
    if q == 0 or q >= n:
        return True
    return (((1 << (2 * q)) - 1) * a + a % (1 << q)) % (1 << (n + q)) == 0


def square_roots_nonzero(r: int, n: int) -> list[int]:
    """All roots of a*a == r (mod 2**n), for 0<r<2**n."""
    assert 0 < r < 1 << n
    order = valuation2(r)
    if order % 2:
        return []
    v = order // 2
    m, odd = n - 2 * v, r >> (2 * v)
    roots = [1]
    for k in range(1, m):
        mask = (1 << (k + 1)) - 1
        roots = [b for a in roots for b in (a, a + (1 << k)) if (b * b - odd) & mask == 0]
    return sorted((a + j * (1 << m)) << v for a in roots for j in range(1 << v))


def evaluate(n: int, a: int, d: int) -> dict[int, tuple[int, int]]:
    p = 1 << n
    mask = p - 1
    def left(x, q): return 0 if q >= n else (x << q) & mask
    def right(x, q): return 0 if q >= n else x >> q
    aa, dd = left(a, a), left(d, d)
    ad, da = left(a, d), left(d, a)
    aq = right(a, a*a & mask)
    dq = right(d, d*d & mask)
    A, B = left(a, mask-a), left(a, (-a) & mask)
    C, D = left(d, mask-d), left(d, (-d) & mask)
    return {
        223: (right(a, mask - ((-a) & mask)), right((2*a) & mask, a)),
        238: (left(a, mask-aa), 0), 270: (right(a, mask-dd), 0), 271: (left(a, mask-dd), 0),
        296: (right(a, A), right(a, B)), 298: (left(a, A), right(a, B)),
        379: (right(a, C), right(a, D)), 380: (left(a, C), right(a, D)),
        301: (left(a, aq), right(a, aq)), 477: (left(a, dq), right(a, dq)),
        458: (a & left(d, ad), a & right(d, ad)),
        473: (a & left(d, da), a & right(d, da)),
        522: (left(a, right(d, dd)), right(a, right(d, dd))),
        669: (right(a, left(mask, a)), right(a, aa)),
        670: (left(a, left(mask, a)), right(a, aa)),
        719: (right(a, left(a | d, a)), right(a, aa)),
        1101: (d & right(a, ad), a & right(d, ad)),
        1246: (right(a*a & mask, (2*a) & mask), 0),
        1343: (right(a & d, da), a & right(d, da)),
    }


def input_conditions(n: int, a: int, d: int) -> dict[int, bool]:
    p, half = 1 << n, 1 << max(n-1, 0)
    def left(x, q): return 0 if q >= n else (x << q) & (p-1)
    def right(x, q): return 0 if q >= n else x >> q
    def cross(x, y):
        b = left(x, y)
        return b == 0 or y & right(x, b) == 0
    cA, cD = left(a, p-1-a) != half, left(d, p-1-d) != half
    safe = a == 0 or n <= a or left(a, a) != 0
    return {
        223: (n != 1 or a != 1) and (n != 2 or a != 2),
        238: n != 2 or a != 1,
        270: n != 2 or d != 1 or a < 2,
        271: n != 2 or d != 1 or a % 2 == 0,
        296: cA, 298: cA, 379: a == 0 or cD, 380: a == 0 or cD,
        301: balanced(n, a, right(a, a*a % p)),
        477: balanced(n, a, right(d, d*d % p)),
        458: cross(a, d), 1101: cross(a, d), 473: cross(d, a), 1343: cross(d, a),
        522: left(d, d) != 0 or balanced(n, a, d),
        669: safe, 670: safe,
        719: a == 0 or left(a, a) != 0 or left(d, a) == 0,
        1246: n != 1 or a == 0,
    }


def classify(n: int) -> dict[int, tuple[int, int] | None]:
    """None means valid for every input; otherwise return a concrete (s,t)."""
    if n < 0:
        raise ValueError("Width must be nonnegative")
    p = 1 << n
    out = dict.fromkeys(RULES)
    if n in (1, 2): out[223] = (n, 0)
    if n == 2:
        out[238], out[270], out[271] = (1, 0), (2, 1), (1, 1)
    if n == 1: out[1246] = (1, 0)
    e = next((e for e in range(1, n+1) if e + valuation2(e) == n), None)
    if e is not None:
        out[296] = out[298] = (p-e, 0)
        out[379] = out[380] = (1, p-e)
    a = next((a for a in range(1, n) if a + valuation2(a) >= n), None)
    if a is not None:
        out[669] = out[670] = (a, 0)
        out[522], out[719] = (1, a), (a, 1)
    for d in range(1, n):
        if 1 << d >= n: break
        r = n % (1 << d)
        j = next((j for j in range(d.bit_length()) if (d >> j) & 1 and j < r <= d+j), None)
        if j is not None:
            b = n-r
            x = (b >> d) + (1 << (b+j))
            out[458] = out[1101] = (x, d)
            out[473] = out[1343] = (d, x)
            break
    # A zero square residue has roots divisible by 2**ceil(n/2), which is >=n;
    # hence its count q=a is either 0 or >=n. Only positive residues need lifting.
    for r in range(1, n):
        for a in square_roots_nonzero(r, n):
            q = a >> r
            if 0 < q < n:
                if out[477] is None: out[477] = (1, a)
                if out[301] is None and not balanced(n, a, q): out[301] = (a, 0)
        if out[301] is not None and out[477] is not None: break
    for rule, witness in out.items():
        if witness is not None:
            a, d = witness
            assert 0 <= a < p and 0 <= d < p, (n, rule, witness)
            l, r = evaluate(n, a, d)[rule]
            assert l != r, (n, rule, witness, l, r)
    return out


def verify_small(limit: int) -> None:
    inputs = 0
    for n in range(limit+1):
        all_valid = dict.fromkeys(RULES, True)
        for a in range(1 << n):
            for d in range(1 << n):
                values, conditions = evaluate(n, a, d), input_conditions(n, a, d)
                for rule, (l, r) in values.items():
                    assert (l == r) == conditions[rule], (n, a, d, rule)
                    all_valid[rule] &= l == r
                inputs += 1
        predicted = classify(n)
        assert all(all_valid[r] == (predicted[r] is None) for r in RULES), n
        # Independently validate the modular-root enumeration too.
        for r in range(1, n):
            assert square_roots_nonzero(r, n) == [a for a in range(1 << n) if a*a % (1 << n) == r]
    print(f"Exhaustive check passed: widths 0..{limit}, {inputs} input pairs, {len(RULES)} rules.")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-width', type=int, default=64)
    parser.add_argument('--widths', type=int, nargs='+')
    parser.add_argument('--verify-small', type=int)
    parser.add_argument('--csv', type=Path)
    args = parser.parse_args()
    if args.verify_small is not None: verify_small(args.verify_small)
    widths = args.widths if args.widths is not None else range(args.max_width+1)
    rows = []
    for n in widths:
        result = classify(n)
        for rule in RULES:
            witness = result[rule]
            values = evaluate(n, *witness)[rule] if witness is not None else ('', '')
            rows.append(dict(width=n, rule=rule, valid_for_all_inputs=witness is None,
                             s=witness[0] if witness is not None else '',
                             t=witness[1] if witness is not None else '', lhs=values[0], rhs=values[1]))
    if args.csv:
        args.csv.parent.mkdir(parents=True, exist_ok=True)
        with args.csv.open('w', newline='') as stream:
            writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
            writer.writeheader(); writer.writerows(rows)
        print(f"Wrote {len(rows)} classifications to {args.csv}.")
    else:
        for rule in RULES:
            good = [r['width'] for r in rows if r['rule'] == rule and r['valid_for_all_inputs']]
            print(f"{rule}: valid widths = {good}")

if __name__ == '__main__':
    main()
