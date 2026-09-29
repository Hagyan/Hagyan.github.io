#!/usr/bin/env python3
"""Independent numeric check of the SMALL boundary example's printed terms.

This test is not a Lean proof. It exercises the serialization bridge using an
integer decoder based on isqrt, independently of Lean's bounded-search decoder.
Never use numeric evaluation for the exponentially large demonstration family.
"""

from math import isqrt
from pathlib import Path

from check_local_file import check_text


def pair(a, b):
    return (a + b) ** 2 + a + 1


def unpair(z):
    assert z > 0
    s = isqrt(z - 1)
    a = z - 1 - s * s
    b = s - a
    assert a >= 0 and b >= 0 and pair(a, b) == z
    return a, b


def summary(word):
    raw = 0
    for c in word.encode("ascii"):
        raw = 128 * raw + c
    return len(word), 128 ** len(word), raw


def main():
    checker = check_text(Path("boundary-quotation-with-trace.pabin").read_text(encoding="ascii"))
    assert len(checker.definitions) == 12
    values = [None] * len(checker.nodes)
    for node, index in sorted(checker.nodes.items(), key=lambda item: item[1]):
        op, *children = node
        if op == "var0":
            continue
        if op == "zero":
            result = 0
        else:
            args = [values[i] for i in children]
            assert all(a is not None and a.bit_length() <= 100_000 for a in args)
            if op == "D":
                result = 2 * args[0]
            elif op == "E":
                result = 2 * args[0] + 1
            elif op == "+":
                result = args[0] + args[1]
            elif op == "*":
                result = args[0] * args[1]
            else:
                raise AssertionError(op)
        assert result.bit_length() <= 100_000
        values[index] = result
    register = lambda i: values[checker.definitions[i]]
    expected = [summary(w) for w in ["(>", "(=00)", "(>(=00)(=00))"]]
    assert [tuple(register(3 * i + j) for j in range(3)) for i in range(3)] == expected
    trace = register(11)
    trace_bits = trace.bit_length()
    decoded = []
    for _ in range(3):
        head, trace = unpair(trace)
        length, rest = unpair(head)
        scale, raw = unpair(rest)
        decoded.append((length, scale, raw))
    assert trace == 0 and decoded == expected
    print(f"Printed terms independently verified: 3 word summaries; 3 decoded trace entries; packed trace {trace_bits} bits.")


if __name__ == "__main__":
    main()
