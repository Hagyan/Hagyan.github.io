"""Explicit polynomial-bit finite-sequence coding for the arithmetic bridge.

This implements coding/decoding, not PA proofs of its correctness. It never
encodes the exponentially large expanded word. Run on the saved local proofs:
  python3 packed_summary_tables.py summary-arithmetic-demo.json
"""
from math import isqrt
import json
import sys


def pair(a, b):
    if type(a) is not int or type(b) is not int or min(a, b) < 0:
        raise ValueError("Pair components must be natural numbers")
    return (a + b) ** 2 + a + 1


def unpair(z):
    if type(z) is not int or z <= 0:
        raise ValueError("Not a pair code")
    s = isqrt(z - 1)
    a = z - 1 - s * s
    if a > s:
        raise ValueError("Gap in the pairing range")
    return a, s - a


def pack(values):
    values = list(values)
    if any(type(x) is not int or x < 0 for x in values):
        raise ValueError("Sequence entries must be natural numbers")
    width = max(1, max((x.bit_length() for x in values), default=0))
    payload = 0
    for x in reversed(values):
        payload = (payload << width) + x
    return pair(len(values), pair(width, payload))


def fields(code):
    length, rest = unpair(code)
    width, payload = unpair(rest)
    if width < 1 or payload.bit_length() > length * width:
        raise ValueError("Malformed finite sequence")
    return length, width, payload


def lookup(code, i):
    n, w, p = fields(code)
    if type(i) is not int or not 0 <= i < n:
        raise ValueError("Sequence index out of range")
    return (p >> (w * i)) & ((1 << w) - 1)


def unpack(code):
    n, w, p = fields(code)
    mask = (1 << w) - 1
    out = []
    for _ in range(n):
        out.append(p & mask)
        p >>= w
    return out


def triple_code(row):
    length, closes, opens = row
    return pair(length, pair(closes, opens))


def triple_decode(code):
    length, rest = unpair(code)
    closes, opens = unpair(rest)
    return [length, closes, opens]


def audit(data):
    table = data["table"]
    gates = [gate["result"] for gate in data["gates"]]
    table_code = pack(triple_code(t) for t in table)
    gate_code = pack(triple_code(t) for t in gates)
    # A local table must include the intermediate accumulators, not just roots.
    local_code = pair(table_code, gate_code)
    assert [triple_decode(t) for t in unpack(table_code)] == table
    assert [triple_decode(t) for t in unpack(gate_code)] == gates
    for i, row in enumerate(table):
        assert triple_decode(lookup(table_code, i)) == row
    assert unpair(local_code) == (table_code, gate_code)

    # This auxiliary alphabet is explicit; it does not identify the agenda's
    # unspecified character enumeration or Bew formula.
    digits = {"(": 0, ")": 1, "x": 2}
    rhs_codes = []
    for i, rhs in enumerate(data["grammar"]):
        atoms = []
        for a in rhs:
            if type(a) is int:
                assert 0 <= a < i
                atoms.append(2 * a + 1)
            else:
                atoms.append(2 * digits[a])
        code = pack(atoms)
        assert unpack(code) == atoms
        rhs_codes.append(code)
    grammar_code = pack(rhs_codes)
    assert unpack(grammar_code) == rhs_codes
    print("PASS: packed root table, all intermediate accumulators, lookup equations and grammar round trips.")
    print("Encoded bit lengths:", {"grammar": grammar_code.bit_length(),
          "root_table": table_code.bit_length(), "accumulator_table": gate_code.bit_length(),
          "combined_local_table": local_code.bit_length()})
    print("No expanded word code computed. These are executable coding checks, not PA or Lean proofs.")


if __name__ == "__main__":
    audit(json.load(open(sys.argv[1])))
