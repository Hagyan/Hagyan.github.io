"""Emit an independent Lean certificate for the concrete compressed demo.

The emitted theorems verify summary computation and all local Join relations
for the fixed 204-rule grammar by explicit Nat witnesses.  This checks the
finite mathematical instance in Lean; it does not check the Python proof graph,
an Enderton PA-bin file, or the fixed Bew predicate.

Usage:
  python3 emit_summary_lean.py summary-arithmetic-demo.json SummaryFiniteCheck.lean
"""
import argparse
import json
from pathlib import Path

from pa_summary_replay import verify, character_summary, triple


def srow(row):
    n, r, o = triple(row)
    return f"⟨{n}, {r}, {o}⟩"


def lean_atom(atom):
    if type(atom) is int:
        return f".ref {atom}"
    if atom not in ("(", ")", "x"):
        raise ValueError(f"Demo Lean emitter does not support character {atom!r}")
    return f".lit '{atom}'"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    data = json.loads(args.certificate.read_text())
    stats = verify(data)
    rules = data["grammar"]
    table = [triple(x) for x in data["table"]]

    gates = []
    for i, rhs in enumerate(rules):
        acc = (0, 0, 0)
        for j, atom in enumerate(rhs):
            item = table[atom] if type(atom) is int else character_summary(atom)
            gate = data["gates"][len(gates)]
            out = triple(gate["result"])
            c = min(acc[2], item[1])
            u, v = acc[2] - c, item[1] - c
            expected = (acc[0] + item[0], acc[1] + v, u + item[2])
            if expected != out or gate["definition"] != i or gate["atom"] != j:
                raise ValueError("Replay-checked gate metadata changed during Lean export")
            gates.append((acc, item, out, c, u, v))
            acc = out
        if acc != table[i]:
            raise ValueError("Replay-checked table changed during Lean export")

    lines = [
        "import Std",
        "",
        "set_option autoImplicit false",
        "set_option warningAsError true",
        "set_option maxRecDepth 4096",
        "set_option maxHeartbeats 10000000",
        "",
        "namespace MAISO11.SummaryFiniteCheck",
        "",
        "structure Summary where",
        "  len : Nat",
        "  closes : Nat",
        "  opens : Nat",
        "  deriving DecidableEq, Repr",
        "",
        "inductive Atom where",
        "  | ref : Nat → Atom",
        "  | lit : Char → Atom",
        "  deriving DecidableEq, Repr",
        "",
        "structure Gate where",
        "  left : Summary",
        "  right : Summary",
        "  result : Summary",
        "  deriving DecidableEq, Repr",
        "",
        "def emptySummary : Summary := ⟨0, 0, 0⟩",
        "",
        "def charSummary : Char → Summary",
        "  | '(' => ⟨1, 0, 1⟩",
        "  | ')' => ⟨1, 1, 0⟩",
        "  | _ => ⟨1, 0, 0⟩",
        "",
        "def itemSummary (done : List Summary) : Atom → Summary",
        "  | .ref i => done.getD i emptySummary",
        "  | .lit c => charSummary c",
        "",
        "def joinSummary (x y : Summary) : Summary :=",
        "  let c := min x.opens y.closes",
        "  let u := x.opens - c",
        "  let v := y.closes - c",
        "  ⟨x.len + y.len, x.closes + v, u + y.opens⟩",
        "",
        "def foldRhs (done : List Summary) (acc : Summary) : List Atom → Summary",
        "  | [] => acc",
        "  | a :: rest => foldRhs done (joinSummary acc (itemSummary done a)) rest",
        "",
        "def summarizeRules : List (List Atom) → List Summary → List Summary",
        "  | [], done => done",
        "  | rhs :: rest, done =>",
        "      let result := foldRhs done emptySummary rhs",
        "      summarizeRules rest (done ++ [result])",
        "",
        "def scanRhs (done : List Summary) (acc : Summary) : List Atom → List Gate",
        "  | [] => []",
        "  | a :: rest =>",
        "      let right := itemSummary done a",
        "      let result := joinSummary acc right",
        "      ⟨acc, right, result⟩ :: scanRhs done result rest",
        "",
        "def buildGates : List (List Atom) → List Summary → List Gate",
        "  | [], _ => []",
        "  | rhs :: rest, done =>",
        "      let result := foldRhs done emptySummary rhs",
        "      scanRhs done emptySummary rhs ++ buildGates rest (done ++ [result])",
        "",
        "def atomWellFormed (current : Nat) : Atom → Bool",
        "  | .ref i => decide (i < current)",
        "  | .lit c => decide (c = '(' ∨ c = ')' ∨ c = 'x')",
        "",
        "def grammarWellFormed : Nat → List (List Atom) → Bool",
        "  | _, [] => true",
        "  | i, rhs :: rest => rhs.all (atomWellFormed i) && grammarWellFormed (i + 1) rest",
        "",
        "def Join (x y z : Summary) : Prop :=",
        "  ∃ c u v : Nat,",
        "    c + u = x.opens ∧",
        "    c + v = y.closes ∧",
        "    (u = 0 ∨ v = 0) ∧",
        "    x.len + y.len = z.len ∧",
        "    x.closes + v = z.closes ∧",
        "    u + y.opens = z.opens",
        "",
        "def GateValid (g : Gate) : Prop := Join g.left g.right g.result",
        "",
        "def GatesValid : List Gate → Prop",
        "  | [] => True",
        "  | g :: rest => GateValid g ∧ GatesValid rest",
        "",
        "def demoGrammar : List (List Atom) := [",
    ]
    lines += ["  [" + ", ".join(lean_atom(a) for a in rhs) + "]," for rhs in rules]
    lines += ["]", "", "def checkedSummaryTable : List Summary := ["]
    lines += [f"  {srow(row)}," for row in table]
    lines += ["]", "", "def computedSummaryTable : List Summary := summarizeRules demoGrammar []", "",
              "def computedGateList : List Gate := buildGates demoGrammar []", "",
              "theorem grammar_is_well_formed : grammarWellFormed 0 demoGrammar = true := by decide", "",
              "theorem computed_table_matches_certificate : computedSummaryTable = checkedSummaryTable := by decide", "",
              "theorem root_summary_is_balanced_length_2_pow_101_plus_1 :",
              "    computedSummaryTable.getLast? = some ⟨2535301200456458802993406410753, 0, 0⟩ := by decide", "",
              "theorem binary_length_identity : 2 ^ 101 + 1 = 2535301200456458802993406410753 := by decide", "",
              f"theorem gate_count_is_407 : computedGateList.length = {len(gates)} := by decide", ""]

    for i, (left, right, result, c, u, v) in enumerate(gates):
        name = f"checkedGate{i:04d}"
        lines += [
            f"def {name} : Gate := ⟨{srow(left)}, {srow(right)}, {srow(result)}⟩",
            f"theorem {name}_join : GateValid {name} := by",
            f"  exact Exists.intro {c} (Exists.intro {u} (Exists.intro {v} (by decide)))",
            "",
        ]

    names = [f"checkedGate{i:04d}" for i in range(len(gates))]
    lines.append("def checkedGateList : List Gate := [" + ", ".join(names) + "]")
    lines.append("")
    lines.append("theorem checked_gate_list_matches_computation : checkedGateList = computedGateList := by decide")
    lines.append("")

    def proof_chain(i):
        if i == len(gates):
            return "True.intro"
        return f"And.intro {names[i]}_join ({proof_chain(i + 1)})"

    lines += [
        "theorem checked_gates_valid : GatesValid checkedGateList := by",
        f"  exact {proof_chain(0)}",
        "",
        "theorem computed_gates_valid : GatesValid computedGateList := by",
        "  rw [← checked_gate_list_matches_computation]",
        "  exact checked_gates_valid",
        "",
        "end MAISO11.SummaryFiniteCheck",
        "",
    ]
    args.output.write_text("\n".join(lines))
    print(f"Wrote {args.output} ({args.output.stat().st_size} bytes)")
    print(f"Lean input: {len(rules)} grammar definitions, {len(gates)} local Join witnesses")
    print(f"Expected root summary: {table[-1]}")
    print("The exported file independently recomputes the table and validates all Join witnesses.")
    print("It does not encode the Python proof graph, Enderton PA-bin checker, or fixed Bew predicate.")


if __name__ == "__main__":
    main()
