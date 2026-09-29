"""Save and independently replay local arithmetic proofs for a summary table.

This checks a PA-admissible object calculus, not Lean, Enderton files, or Bew.
Usage: python3 pa_summary_replay.py --write summary-arithmetic-demo.json
       python3 pa_summary_replay.py --verify summary-arithmetic-demo.json
"""
import argparse
from dataclasses import asdict
import json
from pathlib import Path

from pa_eq_kernel import Kernel, Term, Proof, BinaryArithmetic
from pa_summary_certificate import (Formula, IntroStep, IntroKernel, exists,
                                   join_body, prove_join, intro_data)


FORMAT = "MAISO11-local-summary-arithmetic-v1"


def natural(n):
    if type(n) is not int or n < 0:
        raise ValueError("Expected a natural number")
    return n


def triple(xs):
    if type(xs) not in (list, tuple) or len(xs) != 3:
        raise ValueError("Expected summary triple")
    return tuple(natural(n) for n in xs)


def character_summary(c):
    if type(c) is not str or len(c) != 1:
        raise ValueError("Expected one literal character")
    return (1, 0, 1) if c == "(" else (1, 1, 0) if c == ")" else (1, 0, 0)


def snapshot_with_aggregate(k, logic, grammar, table, gates, aggregate_root):
    return {"format": FORMAT, "zero": k.zero,
            "terms": [asdict(t) for t in k.terms],
            "proofs": [asdict(p) for p in k.proofs],
            "logical_proof": intro_data(logic),
            "grammar": grammar, "table": table, "gates": gates,
            "aggregate_root": aggregate_root}


def freeze(x):
    return tuple(freeze(a) for a in x) if isinstance(x, list) else x


def read_formula_nodes(rows, k):
    if type(rows) is not list:
        raise ValueError("Malformed formula DAG")
    formulas = []
    for i, row in enumerate(rows):
        if type(row) is not list or not row or type(row[0]) is not str:
            raise ValueError("Malformed formula node")
        tag = row[0]
        if tag == "eq" and len(row) == 3:
            if any(type(t) is not int or not 0 <= t < len(k.terms) for t in row[1:]):
                raise ValueError("Invalid equation term reference")
            f = Formula(tag, tuple(row[1:]))
        elif tag in ("and", "or") and len(row) == 3:
            a, b = row[1:]
            if any(type(j) is not int or not 0 <= j < i for j in (a, b)):
                raise ValueError("Formula DAG has a forward or invalid edge")
            f = Formula(tag, (formulas[a], formulas[b]))
        elif tag == "exists" and len(row) == 3 and type(row[1]) is str:
            j = row[2]
            if type(j) is not int or not 0 <= j < i:
                raise ValueError("Invalid existential body reference")
            f = Formula(tag, (row[1], formulas[j]))
        else:
            raise ValueError("Invalid formula constructor or arity")
        formulas.append(f)
    return formulas


def restore(data):
    if data.get("format") != FORMAT:
        raise ValueError("Wrong certificate format")
    k = Kernel()
    k.zero = data["zero"]
    k.terms = [Term(x["tag"], freeze(x["args"])) for x in data["terms"]]
    k.proofs = [Proof(x["rule"], freeze(x["args"]), x["lhs"], x["rhs"],
                      freeze(x["context"])) for x in data["proofs"]]
    k.check_all()
    logic = IntroKernel(k)
    logical = data["logical_proof"]
    formulas = read_formula_nodes(logical["nodes"], k)

    def fref(i):
        if type(i) is not int or not 0 <= i < len(formulas):
            raise ValueError("Invalid formula-DAG reference")
        return formulas[i]

    for x in logical["steps"]:
        rule, a = x["rule"], x["args"]
        if rule in ("arithmetic", "and"):
            args = tuple(a)
        elif rule in ("or_left", "or_right") and len(a) == 2:
            args = (a[0], fref(a[1]))
        elif rule == "exists" and len(a) == 4:
            args = (a[0], fref(a[1]), a[2], a[3])
        else:
            raise ValueError("Malformed logical step")
        logic.steps.append(IntroStep(rule, args, fref(x["conclusion"])))
    logic.check_all()
    return k, logic


def expected_join(k, x, y, result):
    # Reconstruct requested syntax independently of the arithmetic proof printer.
    # This computes numeral syntax, not the truth of the requested equation.
    memo = {0: k.zero}

    def numeral(n):
        natural(n)
        if n not in memo:
            half = numeral(n // 2)
            memo[n] = k.suc(k.add(half, half)) if n % 2 else k.add(half, half)
        return memo[n]

    before = len(k.terms)
    terms = tuple(numeral(n) for n in (*x, *y, *result))
    body = join_body(k, terms, k.var("c"), k.var("u"), k.var("v"))
    goal = exists("c", exists("u", exists("v", body)))
    if len(k.terms) != before:
        raise ValueError("Requested goal uses undeclared term syntax")
    return goal


def verify(data):
    k, logic = restore(data)
    rules = data["grammar"]
    table = [triple(t) for t in data["table"]]
    gates = data["gates"]
    if len(rules) != len(table):
        raise ValueError("Grammar/table length mismatch")
    count = 0
    for i, rhs in enumerate(rules):
        if type(rhs) is not list:
            raise ValueError("Invalid grammar RHS")
        accumulator = (0, 0, 0)
        for j, atom in enumerate(rhs):
            if type(atom) is int:
                if not 0 <= atom < i:
                    raise ValueError("Grammar reference is not earlier")
                item = table[atom]
            else:
                item = character_summary(atom)
            if count >= len(gates):
                raise ValueError("Missing concatenation proof")
            gate = gates[count]
            if gate["definition"] != i or gate["atom"] != j:
                raise ValueError("Mislabelled gate position")
            result = triple(gate["result"])
            p = natural(gate["root"])
            if p >= len(logic.steps):
                raise ValueError("Missing logical proof root")
            goal = expected_join(k, accumulator, item, result)
            if logic.steps[p].conclusion != goal:
                raise ValueError("Checked root does not prove the requested join")
            accumulator = result
            count += 1
        if accumulator != table[i]:
            raise ValueError("Table entry differs from final certified accumulator")
    if count != len(gates):
        raise ValueError("Extra gate records")
    root = natural(data["aggregate_root"])
    if root >= len(logic.steps):
        raise ValueError("Missing conjunction root")
    expected = logic.steps[natural(gates[0]["root"])].conclusion if gates else None
    for gate in gates[1:]:
        expected = Formula("and", (expected,
                                     logic.steps[natural(gate["root"])].conclusion))
    if not gates or logic.steps[root].conclusion != expected:
        raise ValueError("Aggregate root is not the conjunction of the Join proofs")
    return {"definitions": len(rules), "joins": count, "terms": len(k.terms),
            "arithmetic_proofs": len(k.proofs), "logic_steps": len(logic.steps),
            "formula_nodes": len(data["logical_proof"]["nodes"]),
            "aggregate_root": root,
            "final_summary": table[-1] if table else None}


def build(rules):
    k = Kernel()
    binary = BinaryArithmetic(k)
    logic = IntroKernel(k)
    table, gates = [], []
    for i, rhs in enumerate(rules):
        accumulator = (0, 0, 0)
        for j, atom in enumerate(rhs):
            if type(atom) is int:
                if not 0 <= atom < i:
                    raise ValueError("Invalid input grammar reference")
                item = table[atom]
            else:
                item = character_summary(atom)
            accumulator, p = prove_join(k, binary, logic, accumulator, item)
            gates.append({"definition": i, "atom": j,
                          "result": accumulator, "root": p})
        table.append(accumulator)
    if not gates:
        raise ValueError("Demo grammar should contain at least one join")
    aggregate = natural(gates[0]["root"])
    for gate in gates[1:]:
        aggregate = logic.and_intro(aggregate, natural(gate["root"]))
    logic.check_all()
    return snapshot_with_aggregate(k, logic, rules, table, gates, aggregate)


def demo_rules():
    # Empty rules and empty references are intentional. No expanded word is built.
    rules = [[], ["("], [")"]]
    opener, closer = 1, 2
    for _ in range(100):
        rules.append([opener, opener])
        opener = len(rules) - 1
        rules.append([closer, closer])
        closer = len(rules) - 1
    rules.append([0, opener, "x", closer, 0])
    return rules


def mutation_checks(data):
    # Fresh JSON parses guarantee no generator caches or proof objects are reused.
    pristine = json.dumps(data)
    for label, mutate in [
        ("wrong table output", lambda d: d["table"][-1].__setitem__(1, 1)),
        ("wrong gate claim", lambda d: d["gates"][-1]["result"].__setitem__(1, 1)),
        ("wrong proof root", lambda d: d["gates"][-1].__setitem__("root", 0)),
        ("wrong aggregate root", lambda d: d.__setitem__("aggregate_root", 0)),
        ("cyclic grammar", lambda d: d["grammar"][0].append(0)),
        ("corrupt equality", lambda d: next(p for p in d["proofs"]
                                             if p["rhs"] != d["zero"]).__setitem__("rhs", d["zero"])),
    ]:
        d = json.loads(pristine)
        mutate(d)
        try:
            verify(d)
        except (AssertionError, ValueError, IndexError, TypeError):
            print("REJECT:", label)
        else:
            raise AssertionError("Mutation accepted: " + label)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", type=Path)
    mode.add_argument("--verify", type=Path)
    args = parser.parse_args()
    if args.write:
        data = build(demo_rules())
        args.write.write_text(json.dumps(data, separators=(",", ":")) + "\n")
        print("Saved arithmetic proof object:", args.write.name, args.write.stat().st_size, "bytes")
        # Replay the bytes actually written, not the in-memory generated objects.
        data = json.loads(args.write.read_text())
        print("PASS:", verify(data))
        mutation_checks(data)
    else:
        print("PASS:", verify(json.loads(args.verify.read_text())))
    print("PA-admissible object calculus only: not Lean, Enderton wire, or fixed-Bew verification.")


if __name__ == "__main__":
    main()
