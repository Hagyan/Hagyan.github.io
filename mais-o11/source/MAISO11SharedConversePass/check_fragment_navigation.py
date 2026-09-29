"""Executable audit, NOT a Lean or PA certificate.

Independent tuple/array model of fragment summaries, interval queries, and
matching delimiters. A grammar atom is a literal character or an earlier index.
Run: python3 check_fragment_navigation.py
"""
from dataclasses import dataclass
from itertools import product
import random


def join(x, y):
    return x[0] + y[0], min(x[1], x[0] + y[1])


def literal(c):
    d = 1 if c == "(" else -1 if c == ")" else 0
    return d, min(0, d)


def direct_summary(word):
    height = low = 0
    for c in word:
        height += 1 if c == "(" else -1 if c == ")" else 0
        low = min(low, height)
    return height, low


@dataclass
class Work:
    definitions: int = 0
    atoms: int = 0
    queries: int = 0


class Grammar:
    def __init__(self, rules):
        self.rules = rules
        self.table = []
        self.mass = len(rules) + sum(map(len, rules))
        for i, rhs in enumerate(rules):
            length, summary = 0, (0, 0)
            for a in rhs:
                assert (isinstance(a, int) and 0 <= a < i) or (
                    isinstance(a, str) and len(a) == 1)
                n, s = self.entry(a)
                length += n
                summary = join(summary, s)
            self.table.append((length, summary))

    def entry(self, a):
        return self.table[a] if isinstance(a, int) else (1, literal(a))

    def expand_small(self, i):
        assert all(length <= 10000 for length, _ in self.table[:i + 1])
        words = []
        for rhs in self.rules[:i + 1]:
            words.append("".join(words[a] if isinstance(a, int) else a for a in rhs))
        return words[i]

    def interval(self, i, p, q, work=None):
        assert p >= 0 and q >= 0
        work = work if work is not None else Work()
        work.queries += 1

        def visit(j, start, count):
            work.definitions += 1
            out = (0, 0)
            for a in self.rules[j]:
                if count == 0:
                    break
                work.atoms += 1
                length, summary = self.entry(a)
                if length <= start:
                    start -= length
                    continue
                if start == 0 and length <= count:
                    first = summary
                elif isinstance(a, int):
                    first = visit(a, start, count)
                else:
                    # Partial selection of a unit character cannot happen here.
                    assert start == 0 and count >= 1
                    first = summary
                out = join(out, first)
                count = max(0, count - (length - start))
                start = 0
            return out

        return visit(i, p, q)

    def matching_close(self, i, a, work=None):
        work = work if work is not None else Work()
        length = self.table[i][0]
        if not 0 <= a < length or self.interval(i, a, 1, work) != (1, 0):
            return None
        remaining = length - a - 1

        def crossed(t):
            return self.interval(i, a + 1, t, work)[1] <= -1

        if not crossed(remaining):
            return None
        lo, hi = 0, remaining  # lo is false, hi is true.
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if crossed(mid):
                hi = mid
            else:
                lo = mid
        return a + hi

    def check_match(self, i, a, j):
        length = self.table[i][0]
        return (0 <= a < j < length
                and self.interval(i, a, 1) == (1, 0)
                and self.interval(i, j, 1) == (-1, -1)
                and self.interval(i, a + 1, j - a - 1) == (0, 0))


def direct_match(word, a):
    if not 0 <= a < len(word) or word[a] != "(":
        return None
    height = 1
    for j in range(a + 1, len(word)):
        height += 1 if word[j] == "(" else -1 if word[j] == ")" else 0
        if height == 0:
            return j
    return None


def run():
    interval_checks = match_checks = certificate_checks = 0
    # Empty rules at several positions exercise zero-length references.
    for n in range(7):
        for letters in product("()x", repeat=n):
            word = "".join(letters)
            k = n // 2
            g = Grammar([[], list(word[:k]), [], list(word[k:]), [0, 1, 2, 3, 0]])
            root = 4
            assert g.expand_small(root) == word
            for p in range(n + 3):
                for q in range(n + 3):
                    work = Work()
                    assert g.interval(root, p, q, work) == direct_summary(word[p:p + q])
                    assert work.definitions + work.atoms <= 2 * g.mass
                    interval_checks += 1
            for a in range(n + 1):
                expected = direct_match(word, a)
                assert g.matching_close(root, a) == expected
                match_checks += 1
                for j in range(n + 1):
                    assert g.check_match(root, a, j) == (expected is not None and expected == j)
                    certificate_checks += 1

    rng = random.Random(110026)
    for _ in range(500):
        rules = []
        for i in range(12):
            choices = list("()x") + list(range(i))
            rules.append([rng.choice(choices) for _ in range(rng.randrange(5))])
        g = Grammar(rules)
        root = 11
        word = g.expand_small(root)
        assert g.table[root] == (len(word), direct_summary(word))
        for _ in range(40):
            p, q = rng.randrange(len(word) + 4), rng.randrange(len(word) + 4)
            work = Work()
            assert g.interval(root, p, q, work) == direct_summary(word[p:p + q])
            assert work.definitions + work.atoms <= 2 * g.mass
            interval_checks += 1
            a = rng.randrange(len(word) + 1)
            expected = direct_match(word, a)
            assert g.matching_close(root, a) == expected
            if expected is not None:
                assert g.check_match(root, a, expected)
            match_checks += 1

    # Exponential unary spine: never call expand_small for this grammar.
    rules = [["("], [")"]]
    opener, closer = 0, 1
    for _ in range(100):
        rules.append([opener, opener])
        opener = len(rules) - 1
        rules.append([closer, closer])
        closer = len(rules) - 1
    rules.append([opener, "x", closer])
    g = Grammar(rules)
    root, depth = len(rules) - 1, 2 ** 100
    assert g.table[root] == (2 * depth + 1, (0, 0))
    huge_work = []
    for a in [0, 1, depth // 2, depth - 1]:
        work = Work()
        j = g.matching_close(root, a, work)
        assert j == 2 * depth - a
        assert g.check_match(root, a, j)
        assert not g.check_match(root, a, j - 1)
        assert work.queries <= 2 + (g.table[root][0]).bit_length()
        huge_work.append((a, j, work.queries, work.definitions + work.atoms))
    print(f"PASS: {interval_checks} interval comparisons; {match_checks} matching comparisons; "
          f"{certificate_checks} exhaustive match-certificate comparisons.")
    print(f"Huge grammar: mass={g.mass}; expanded length={g.table[root][0]}; no expansion.")
    print("Huge matches (opening, closing, queries, visited definitions+atoms):")
    for row in huge_work:
        print(row)
    print("This is an executable audit, not a Lean kernel check or a PA proof.")


if __name__ == "__main__":
    run()
