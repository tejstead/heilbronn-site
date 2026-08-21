"""Render curated exact-form strings ("(√13 − 1) / 36", "3 − 2√2",
"[2 − ∛(3/2 − √(239/3)/6) − ∛(3/2 + √(239/3)/6)] / 18") as presentation
MathML, preserving their layout exactly — sympy's printer canonicalizes
expressions into forms nobody would write on a page.

The parser also numerically evaluates what it parsed, so callers can check
the rendered form against the independently validated exact decimal: the
pretty output is provably the same number.

Grammar (whitespace-insensitive):
    expr    := term (("+" | "−" | "-") term)*
    term    := atom (("/" atom) | atom-juxtaposition)*   # 2√2, 9√65
    atom    := number | radical | group
    radical := ("√" | "∛") atom
    group   := "(" expr ")" | "[" expr "]"

Division renders as a stacked <mfrac>; parentheses that directly wrap a
radicand or a fraction's operand are absorbed (the vinculum replaces them).
"""

import re


class Node:
    def __init__(self, kind, *kids, value=None):
        self.kind = kind      # num | add | sub-chain ops | frac | sqrt | root3 | mul | group
        self.kids = list(kids)
        self.value = value


class Parser:
    def __init__(self, s):
        self.toks = re.findall(r"\d+\.?\d*|[√∛()\[\]+/]|[−-]", s.replace(" ", ""))
        self.i = 0

    def peek(self):
        return self.toks[self.i] if self.i < len(self.toks) else None

    def eat(self):
        t = self.peek()
        self.i += 1
        return t

    def parse(self):
        e = self.expr()
        if self.peek() is not None:
            raise ValueError(f"trailing tokens: {self.toks[self.i:]}")
        return e

    def expr(self):
        terms = [("+", self.term())]
        while self.peek() in ("+", "−", "-"):
            op = "+" if self.eat() == "+" else "−"
            terms.append((op, self.term()))
        if len(terms) == 1:
            return terms[0][1]
        return Node("sum", *[t for t in terms], value=None)

    def term(self):
        left = self.atom()
        while True:
            t = self.peek()
            if t == "/":
                self.eat()
                right = self.atom()
                left = Node("frac", left, right)
            elif t in ("√", "∛") or (t is not None and re.match(r"\d", t)) or t in ("(", "["):
                # juxtaposition = multiplication (2√2)
                left = Node("mul", left, self.atom())
            else:
                return left

    def atom(self):
        t = self.peek()
        if t is None:
            raise ValueError("unexpected end")
        if t in ("√", "∛"):
            self.eat()
            return Node("sqrt" if t == "√" else "root3", self.atom())
        if t in ("(", "["):
            close = ")" if t == "(" else "]"
            self.eat()
            e = self.expr()
            if self.eat() != close:
                raise ValueError(f"expected {close}")
            return Node("group", e)
        if re.match(r"\d", t):
            self.eat()
            return Node("num", value=t)
        raise ValueError(f"unexpected token {t!r}")


def strip_group(n):
    return n.kids[0] if n.kind == "group" else n


def evaluate(n):
    if n.kind == "num":
        return float(n.value)
    if n.kind == "group":
        return evaluate(n.kids[0])
    if n.kind == "sum":
        total = 0.0
        for op, kid in n.kids:
            total += evaluate(kid) if op == "+" else -evaluate(kid)
        return total
    if n.kind == "frac":
        return evaluate(n.kids[0]) / evaluate(n.kids[1])
    if n.kind == "mul":
        return evaluate(n.kids[0]) * evaluate(n.kids[1])
    if n.kind == "sqrt":
        return evaluate(n.kids[0]) ** 0.5
    if n.kind == "root3":
        return evaluate(n.kids[0]) ** (1 / 3)
    raise ValueError(n.kind)


def to_mml(n, drop_parens=False):
    if n.kind == "num":
        return f"<mn>{n.value}</mn>"
    if n.kind == "group":
        inner = to_mml(n.kids[0])
        if drop_parens:
            return f"<mrow>{inner}</mrow>"
        return f'<mrow><mo fence="true">(</mo>{inner}<mo fence="true">)</mo></mrow>'
    if n.kind == "sum":
        parts = []
        for idx, (op, kid) in enumerate(n.kids):
            if idx > 0 or op == "−":
                parts.append(f"<mo>{op if op != '+' else '+'}</mo>")
            parts.append(to_mml(kid))
        return f"<mrow>{''.join(parts)}</mrow>"
    if n.kind == "frac":
        num = to_mml(strip_group(n.kids[0]), drop_parens=True)
        den = to_mml(strip_group(n.kids[1]), drop_parens=True)
        return f"<mfrac><mrow>{num}</mrow><mrow>{den}</mrow></mfrac>"
    if n.kind == "mul":
        return f"<mrow>{to_mml(n.kids[0])}{to_mml(n.kids[1])}</mrow>"
    if n.kind == "sqrt":
        return f"<msqrt>{to_mml(strip_group(n.kids[0]), drop_parens=True)}</msqrt>"
    if n.kind == "root3":
        return (f"<mroot><mrow>{to_mml(strip_group(n.kids[0]), drop_parens=True)}</mrow>"
                f"<mn>3</mn></mroot>")
    raise ValueError(n.kind)


def exact_to_mathml(display):
    """Parse a curated display string; return (mathml, numeric value).
    Raises on anything it can't parse — callers fall back to plain text."""
    tree = Parser(display).parse()
    mml = to_mml(strip_group(tree), drop_parens=True)
    return (f'<math xmlns="http://www.w3.org/1998/Math/MathML">{mml}</math>',
            evaluate(tree))


def poly_to_mathml(poly):
    """"152*x**3 + 12*x**2 - 14*x + 1" -> MathML polynomial."""
    s = poly.replace(" ", "")
    terms = re.findall(r"[+-]?[^+-]+", s)
    parts = []
    for idx, t in enumerate(terms):
        sign = "−" if t.startswith("-") else "+"
        t = t.lstrip("+-")
        if idx > 0 or sign == "−":
            parts.append(f"<mo>{sign}</mo>")
        m = re.fullmatch(r"(?:(\d+)\*?)?([a-z])(?:\*\*(\d+))?|(\d+)", t)
        if not m:
            raise ValueError(f"cannot parse term {t!r}")
        if m.group(4):
            parts.append(f"<mn>{m.group(4)}</mn>")
            continue
        coeff, var, exp = m.group(1), m.group(2), m.group(3)
        if coeff:
            parts.append(f"<mn>{coeff}</mn>")
        if exp:
            parts.append(f"<msup><mi>{var}</mi><mn>{exp}</mn></msup>")
        else:
            parts.append(f"<mi>{var}</mi>")
    return (f'<math xmlns="http://www.w3.org/1998/Math/MathML">'
            f"<mrow>{''.join(parts)}</mrow></math>")
