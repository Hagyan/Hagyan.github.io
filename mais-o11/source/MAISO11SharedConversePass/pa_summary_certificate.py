"""Closed existential certificates for nonnegative parenthesis-summary joins.

Object calculus: equational PA fragment from pa_eq_kernel plus admissible
first-order introduction rules. This is NOT the fixed Enderton file checker,
the fixed Bew predicate, or a Lean kernel certificate.
"""
from dataclasses import dataclass
import json
from pathlib import Path

from pa_eq_kernel import Kernel, BinaryArithmetic, build_lemmas


@dataclass(frozen=True)
class Formula:
    tag: str
    args: tuple


def eq(a, b):
    return Formula("eq", (a, b))


def both(a, b):
    return Formula("and", (a, b))


def either(a, b):
    return Formula("or", (a, b))


def exists(v, body):
    return Formula("exists", (v, body))


def conjunction(fs):
    assert fs
    out = fs[-1]
    for f in reversed(fs[:-1]):
        out = both(f, out)
    return out


def validate_formula(k, f):
    if not isinstance(f, Formula) or type(f.args) is not tuple:
        raise ValueError("Malformed formula")
    if f.tag == "eq":
        if len(f.args) != 2 or any(type(t) is not int or not 0 <= t < len(k.terms)
                                    for t in f.args):
            raise ValueError("Invalid equality term reference")
    elif f.tag in ("and", "or"):
        if len(f.args) != 2:
            raise ValueError("Invalid binary formula")
        for part in f.args:
            validate_formula(k, part)
    elif f.tag == "exists":
        if len(f.args) != 2 or type(f.args[0]) is not str:
            raise ValueError("Invalid existential binder")
        validate_formula(k, f.args[1])
    else:
        raise ValueError("Unknown formula constructor")


def free_vars(k, f):
    if f.tag == "eq":
        return k.term_vars(f.args[0]) | k.term_vars(f.args[1])
    if f.tag in ("and", "or"):
        return free_vars(k, f.args[0]) | free_vars(k, f.args[1])
    if f.tag == "exists":
        return free_vars(k, f.args[1]) - {f.args[0]}
    raise ValueError("Unknown formula constructor")


def subst(k, f, name, term):
    if f.tag == "eq":
        return eq(*(k.subst_term(t, {name: term}) for t in f.args))
    if f.tag in ("and", "or"):
        return Formula(f.tag, tuple(subst(k, x, name, term) for x in f.args))
    if f.tag == "exists":
        v, body = f.args
        if v == name or name not in free_vars(k, body):
            return f
        if v in k.term_vars(term):
            raise ValueError("Capture-unsafe substitution")
        return exists(v, subst(k, body, name, term))
    raise ValueError("Unknown formula constructor")


@dataclass(frozen=True)
class IntroStep:
    rule: str
    args: tuple
    conclusion: Formula


class IntroKernel:
    """No arbitrary assumptions, computation rule, or semantic truth oracle."""
    def __init__(self, arithmetic):
        self.k = arithmetic
        self.steps = []

    def emit(self, rule, args, conclusion):
        i = len(self.steps)
        self.steps.append(IntroStep(rule, tuple(args), conclusion))
        return i

    def arithmetic(self, p):
        if not self.k.is_closed(p):
            raise ValueError("An open arithmetic assumption cannot be imported")
        return self.emit("arithmetic", (p,), eq(*self.k.eq(p)))

    def and_intro(self, p, q):
        return self.emit("and", (p, q), both(self.steps[p].conclusion,
                                            self.steps[q].conclusion))

    def or_intro(self, p, other, left):
        own = self.steps[p].conclusion
        f = either(own, other) if left else either(other, own)
        return self.emit("or_left" if left else "or_right", (p, other), f)

    def exists_intro(self, variable, body, witness, p):
        if subst(self.k, body, variable, witness) != self.steps[p].conclusion:
            raise ValueError("Existential premise is not the required instance")
        return self.emit("exists", (variable, body, witness, p), exists(variable, body))

    def check_all(self):
        self.k.check_all()
        checked = []

        def prior(p):
            if type(p) is not int or not 0 <= p < len(checked):
                raise ValueError("Invalid or forward logical reference")
            return checked[p]

        for step in self.steps:
            rule, a = step.rule, step.args
            if type(a) is not tuple or type(step.conclusion) is not Formula:
                raise ValueError("Malformed logical proof record")
            validate_formula(self.k, step.conclusion)
            if rule == "arithmetic":
                if len(a) != 1:
                    raise ValueError("Malformed arithmetic reference")
                p, = a
                if type(p) is not int or not 0 <= p < len(self.k.proofs):
                    raise ValueError("Invalid arithmetic reference")
                if not self.k.is_closed(p):
                    raise ValueError("Undischarged arithmetic hypothesis")
                f = eq(*self.k.eq(p))
            elif rule == "and":
                if len(a) != 2:
                    raise ValueError("Malformed conjunction introduction")
                f = both(prior(a[0]), prior(a[1]))
            elif rule == "or_left":
                if len(a) != 2:
                    raise ValueError("Malformed left disjunction introduction")
                validate_formula(self.k, a[1])
                f = either(prior(a[0]), a[1])
            elif rule == "or_right":
                if len(a) != 2:
                    raise ValueError("Malformed right disjunction introduction")
                validate_formula(self.k, a[1])
                f = either(a[1], prior(a[0]))
            elif rule == "exists":
                if len(a) != 4:
                    raise ValueError("Malformed existential introduction")
                v, body, w, p = a
                if type(v) is not str or type(w) is not int or not 0 <= w < len(self.k.terms):
                    raise ValueError("Invalid existential variable or witness")
                validate_formula(self.k, body)
                if subst(self.k, body, v, w) != prior(p):
                    raise ValueError("Bad existential instance")
                f = exists(v, body)
            else:
                raise ValueError("Unknown introduction rule")
            if f != step.conclusion:
                raise ValueError("Declared conclusion does not follow")
            checked.append(f)
        return True


def join_body(k, terms, c, u, v):
    lx, rx, ox, ly, ry, oy, length, closes, opens = terms
    return conjunction([
        eq(k.add(c, u), ox), eq(k.add(c, v), ry),
        either(eq(u, k.zero), eq(v, k.zero)),
        eq(k.add(lx, ly), length),
        eq(k.add(rx, v), closes), eq(k.add(u, oy), opens),
    ])


def prove_join(k, binary, logic, x, y):
    lx, rx, ox = x
    ly, ry, oy = y
    if any(type(n) is not int or n < 0 for n in (*x, *y)):
        raise ValueError("Summary coordinates must be natural numbers")
    c = min(ox, ry)
    u, v = ox - c, ry - c
    result = (lx + ly, rx + v, u + oy)
    terms = tuple(binary.num(n) for n in (*x, *y, *result))
    arithmetic_pairs = [(c, u), (c, v), (lx, ly), (rx, v), (u, oy)]
    ps = [logic.arithmetic(binary.add_proof(a, b)) for a, b in arithmetic_pairs]
    zero_proof = logic.arithmetic(k.refl(k.zero))
    if u == 0:
        branch = logic.or_intro(zero_proof, eq(binary.num(v), k.zero), True)
    else:
        assert v == 0
        branch = logic.or_intro(zero_proof, eq(binary.num(u), k.zero), False)
    pieces = ps[:2] + [branch] + ps[2:]
    p = pieces[-1]
    for q in reversed(pieces[:-1]):
        p = logic.and_intro(q, p)
    body = join_body(k, terms, k.var("c"), k.var("u"), k.var("v"))
    body_c = subst(k, body, "c", binary.num(c))
    body_cu = subst(k, body_c, "u", binary.num(u))
    p = logic.exists_intro("v", body_cu, binary.num(v), p)
    p = logic.exists_intro("u", exists("v", body_c), binary.num(u), p)
    p = logic.exists_intro("c", exists("u", exists("v", body)), binary.num(c), p)
    assert not free_vars(k, logic.steps[p].conclusion)
    return result, p


def intro_data(logic):
    """Serialize formulas as a postorder DAG; growing conjunctions stay shared."""
    nodes, identities = [], {}

    def add(f):
        old = identities.get(id(f))
        if old is not None:
            return old
        if f.tag == "eq":
            row = ["eq", *f.args]
        elif f.tag in ("and", "or"):
            row = [f.tag, add(f.args[0]), add(f.args[1])]
        elif f.tag == "exists":
            row = ["exists", f.args[0], add(f.args[1])]
        else:
            raise ValueError("Unknown formula constructor")
        i = len(nodes)
        nodes.append(row)
        identities[id(f)] = i
        return i

    steps = []
    for s in logic.steps:
        args = []
        for a in s.args:
            args.append(add(a) if isinstance(a, Formula) else a)
        steps.append({"rule": s.rule, "args": args,
                      "conclusion": add(s.conclusion)})
    return {"nodes": nodes, "steps": steps}


def run():
    k = Kernel()
    binary = BinaryArithmetic(k, build_lemmas(k))
    logic = IntroKernel(k)
    roots = []
    for rx in range(3):
        for ox in range(3):
            for ry in range(3):
                for oy in range(3):
                    x, y = (rx + ox, rx, ox), (ry + oy, ry, oy)
                    out, p = prove_join(k, binary, logic, x, y)
                    assert out == (sum((x[0], y[0])), rx + max(ry - ox, 0),
                                   oy + max(ox - ry, 0))
                    roots.append(p)
    # The numeric values are exponential in the bit length, without unary expansion.
    for bits in [16, 64, 100]:
        out, p = prove_join(k, binary, logic, (2**bits, 0, 2**bits),
                           (2**(bits - 1), 2**(bits - 1), 0))
        assert out == (3 * 2**(bits - 1), 0, 2**(bits - 1))
        roots.append(p)
    assert logic.check_all()

    # Mutate a root conclusion: the checker must reject the forged proof.
    original = logic.steps[roots[-1]]
    logic.steps[roots[-1]] = IntroStep(original.rule, original.args,
                                     eq(binary.num(0), binary.num(1)))
    try:
        logic.check_all()
    except (ValueError, AssertionError):
        pass
    else:
        raise AssertionError("Forged logical conclusion was accepted")
    logic.steps[roots[-1]] = original
    assert logic.check_all()
    print(f"PASS: {len(roots)} closed existential join proofs checked; forged conclusion rejected.")
    print(f"Arithmetic proof records: {len(k.proofs)}; term nodes: {len(k.terms)}; "
          f"logical introduction records: {len(logic.steps)}.")
    print("Object calculus uses PA-admissible rules; this is not an Enderton wire or Lean certificate.")


if __name__ == "__main__":
    run()
