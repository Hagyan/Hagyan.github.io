#!/usr/bin/env python3
"""Diagnostic parser/checker for the printed LOCAL quotation certificates.

This is independently executed Python, not part of the Lean certificate.
It accepts only the equality/instantiation fragment documented in README.md.
It is NOT the complete PA-bin checker or an arithmetic proof predicate.

Term interning checks exact expanded syntax without arithmetic evaluation or
materializing repeated trees. In this output format every definition is a
whole closed term; the SOURCE quotation compiler still accepts raw fragments.
"""

from __future__ import annotations

import argparse
from pathlib import Path


class Invalid(ValueError):
    pass


class Checker:
    def __init__(self):
        self.definitions: dict[int, int] = {}
        self.lines: list[tuple] = []
        self.nodes: dict[tuple, int] = {}
        self.closed: list[bool] = []
        var = self.node(("var0",), False)
        self.universal = ("all", ("eq", var, var))

    def node(self, key, closed):
        if key not in self.nodes:
            self.nodes[key] = len(self.nodes)
            self.closed.append(closed)
        return self.nodes[key]

    def parse_record(self, line: str):
        self.text, self.pos = line, 0
        if line.startswith("def "):
            self.take("def ")
            name = self.identifier()
            if name != len(self.definitions):
                raise Invalid("definition identifier is not the next fresh identifier")
            self.take(" := ")
            value = self.term()
            if not self.closed[value]:
                raise Invalid("term definition is not closed")
            self.end()
            self.definitions[name] = value
            return
        if line.startswith("A"):
            self.take("A")
            f = self.formula()
            self.end()
            if f != self.universal:
                if not (f[0] == "imp" and f[1] == self.universal and f[2][0] == "eq"):
                    raise Invalid("not an axiom of the local fragment")
                _, x, y = f[2]
                if x != y or not self.closed[x]:
                    raise Invalid("instantiation conclusion is not closed reflexivity")
            self.lines.append(f)
            return
        if line.startswith("M["):
            self.take("M[")
            a = self.identifier()
            self.take(",")
            i = self.identifier()
            self.take("]")
            f = self.formula()
            self.end()
            if a >= len(self.lines) or i >= len(self.lines):
                raise Invalid("MP references a line that is not earlier")
            if self.lines[i] != ("imp", self.lines[a], f):
                raise Invalid("MP formulas do not match")
            self.lines.append(f)
            return
        raise Invalid("unknown record tag")

    def take(self, token: str):
        if not self.text.startswith(token, self.pos):
            raise Invalid(f"expected {token!r} at character {self.pos}")
        self.pos += len(token)

    def end(self):
        if self.pos != len(self.text):
            raise Invalid(f"unparsed characters after {self.pos}")

    def identifier(self):
        self.take("u")
        length = 0
        while self.text.startswith("1", self.pos):
            self.pos += 1
            length += 1
        self.take("0")
        body = self.text[self.pos : self.pos + length]
        if not body or len(body) != length or body[0] != "1" or set(body) - {"0", "1"}:
            raise Invalid("invalid self-delimiting binary identifier")
        self.pos += length
        return int(body, 2) - 1

    def term(self):
        if self.text.startswith("0", self.pos):
            self.pos += 1
            return self.node(("zero",), True)
        if self.text.startswith("v0", self.pos):
            self.pos += 2
            return self.node(("var0",), False)
        if self.text.startswith("u", self.pos):
            i = self.identifier()
            if i not in self.definitions:
                raise Invalid("undefined abbreviation")
            return self.definitions[i]
        self.take("(")
        if self.pos == len(self.text):
            raise Invalid("unfinished term")
        op = self.text[self.pos]
        self.pos += 1
        if op in "DE":
            x = self.term()
            key = (op, x)
            closed = self.closed[x]
        elif op in "+*":
            x, y = self.term(), self.term()
            key = (op, x, y)
            closed = self.closed[x] and self.closed[y]
        else:
            raise Invalid(f"unknown term operator {op!r}")
        self.take(")")
        return self.node(key, closed)

    def formula(self):
        self.take("(")
        if self.pos == len(self.text):
            raise Invalid("unfinished formula")
        op = self.text[self.pos]
        self.pos += 1
        if op == "=":
            result = ("eq", self.term(), self.term())
        elif op == ">":
            result = ("imp", self.formula(), self.formula())
        elif op == "A":
            self.take("v0")
            result = ("all", self.formula())
        else:
            raise Invalid(f"unknown formula operator {op!r}")
        self.take(")")
        return result


def check_text(text: str):
    if not text.isascii() or not text.endswith("\n"):
        raise Invalid("expected newline-terminated ASCII")
    checker = Checker()
    for number, line in enumerate(text.splitlines(), 1):
        try:
            checker.parse_record(line)
        except Invalid as exc:
            raise Invalid(f"record {number}: {exc}") from exc
    if not checker.lines:
        raise Invalid("no proof lines")
    return checker


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("file", type=Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    text = args.file.read_text(encoding="ascii")
    checker = check_text(text)
    print(f"Accepted local fragment: {len(checker.definitions)} definitions, "
          f"{len(checker.lines)} proof lines, {len(text)} characters.")
    if args.self_test:
        first_mp = next(x for x in text.splitlines() if x.startswith("M["))
        # Swap MP's antecedent and implication references: a real rule violation.
        refs, goal = first_mp[2:].split("]", 1)
        left, right = refs.split(",")
        malformed = text.replace(first_mp, f"M[{right},{left}]{goal}", 1)
        try:
            check_text(malformed)
        except Invalid:
            print("Rejected deliberately reversed MP references.")
        else:
            raise AssertionError("reversed MP references were accepted")
        # Redeclaring u_0 as the second definition must fail freshness.
        records = text.splitlines()
        defs = [i for i, row in enumerate(records) if row.startswith("def ")]
        second = defs[1]
        records[second] = "def u101 := " + records[second].split(" := ", 1)[1]
        try:
            check_text("\n".join(records) + "\n")
        except Invalid:
            print("Rejected deliberately reused definition identifier.")
        else:
            raise AssertionError("reused identifier was accepted")


if __name__ == "__main__":
    main()
