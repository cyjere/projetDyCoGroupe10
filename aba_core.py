# -*- coding: utf-8 -*-
"""
aba_core.py — Générateur ABA / ABA+ (frameworks plats)

Fonctionnalités (Question 1) :
  * définition des littéraux, règles, hypothèses (assumptions) et contraires ;
  * conversion automatique vers un framework non-circulaire puis atomique ;
  * génération de tous les arguments et de toutes les attaques ;
  * préférences entre hypothèses (clôture transitive) et calcul des
    attaques ABA+ normales / inverses (Čyras & Toni, 2016).
"""

import re
import itertools
from dataclasses import dataclass, field
from typing import Dict, List, Set, Tuple, FrozenSet

Argument = Tuple[FrozenSet[str], str]          # (support, conclusion)
Attack = Tuple[Argument, Argument]             # (attaquant, attaqué)


# =============================================================================
# 1. Structure de données
# =============================================================================

@dataclass
class ABAFramework:
    literals: Set[str] = field(default_factory=set)
    assumptions: Set[str] = field(default_factory=set)
    contraries: Dict[str, str] = field(default_factory=dict)
    # id de règle -> (corps, tête)
    rules: Dict[str, Tuple[FrozenSet[str], str]] = field(default_factory=dict)
    # ensemble de couples (x, y) signifiant  x < y  (x strictement moins préféré que y)
    less_than: Set[Tuple[str, str]] = field(default_factory=set)
    warnings: List[str] = field(default_factory=list)

    def non_assumptions(self):
        return self.literals - self.assumptions

    def copy(self):
        return ABAFramework(
            literals=set(self.literals),
            assumptions=set(self.assumptions),
            contraries=dict(self.contraries),
            rules=dict(self.rules),
            less_than=set(self.less_than),
            warnings=list(self.warnings),
        )


# =============================================================================
# 2. Parsing du format texte de l'énoncé
# =============================================================================

_ID = r"[A-Za-z0-9_']+"


def _split_list(s):
    return [x.strip() for x in s.split(",") if x.strip()]


def parse_preferences(lines):
    """
    Formats acceptés (une ou plusieurs lignes PREF) :
        PREF: a > b
        PREF: a,b > c          (a > c et b > c)
        PREF: a > b > c        (chaîne)
        PREF: a > b ; c > d    (plusieurs préférences sur une ligne)
    Renvoie l'ensemble des couples (x, y) avec x < y, clôturé transitivement.
    """
    less = set()
    for stmt in lines:
        for part in re.split(r"[;\n]", stmt):
            part = part.strip()
            if not part:
                continue
            levels = [_split_list(x) for x in part.split(">")]
            if len(levels) < 2 or any(not lv for lv in levels):
                raise ValueError(f"Préférence mal formée : « {part} »")
            for hi, lo in zip(levels, levels[1:]):
                for h in hi:
                    for l in lo:
                        less.add((l, h))          # l < h
    # clôture transitive
    changed = True
    while changed:
        changed = False
        for (x, y) in list(less):
            for (y2, z) in list(less):
                if y == y2 and (x, z) not in less:
                    less.add((x, z))
                    changed = True
    return less


def parse_aba_text(text):
    fw = ABAFramework()
    lines = [l.strip() for l in text.splitlines()]
    pref_lines = []
    declared_literals = None

    for line in lines:
        if not line or line.startswith("#"):
            continue

        m = re.match(r"^L\s*:\s*\[(.*)\]\s*$", line)
        if m:
            declared_literals = set(_split_list(m.group(1)))
            continue

        m = re.match(r"^A\s*:\s*\[(.*)\]\s*$", line)
        if m:
            fw.assumptions = set(_split_list(m.group(1)))
            continue

        m = re.match(rf"^C\(\s*({_ID})\s*\)\s*:\s*({_ID})\s*$", line)
        if m:
            fw.contraries[m.group(1)] = m.group(2)
            continue

        m = re.match(rf"^\[\s*({_ID})\s*\]\s*:\s*({_ID})\s*<-\s*(.*)$", line)
        if m:
            rid, head, body = m.group(1), m.group(2), m.group(3)
            if rid in fw.rules:
                raise ValueError(f"Identifiant de règle dupliqué : {rid}")
            fw.rules[rid] = (frozenset(_split_list(body)), head)
            continue

        m = re.match(r"^PREF\s*:\s*(.*)$", line)
        if m:
            if m.group(1).strip():
                pref_lines.append(m.group(1))
            continue

        fw.warnings.append(f"Ligne ignorée (format non reconnu) : « {line} »")

    fw.less_than = parse_preferences(pref_lines)

    # --- validation / complétion de L ---------------------------------------
    used = set(fw.assumptions) | set(fw.contraries.values())
    for body, head in fw.rules.values():
        used |= set(body) | {head}
    for (x, y) in fw.less_than:
        used |= {x, y}

    if declared_literals is None:
        fw.warnings.append("Aucune ligne « L: [...] » : les littéraux sont déduits des règles.")
        fw.literals = used
    else:
        missing = used - declared_literals
        if missing:
            fw.warnings.append("Littéraux utilisés mais absents de L (ajoutés) : "
                               + ", ".join(sorted(missing)))
        fw.literals = declared_literals | used

    # --- contrôles de cohérence ---------------------------------------------
    for a in sorted(fw.assumptions):
        if a not in fw.contraries:
            raise ValueError(f"L'hypothèse « {a} » n'a pas de contraire (C({a}): ...).")
    for a in sorted(fw.contraries):
        if a not in fw.assumptions:
            raise ValueError(f"C({a}) est défini mais « {a} » n'est pas une hypothèse.")
    for rid, (body, head) in fw.rules.items():
        if head in fw.assumptions:
            raise ValueError(f"Règle {rid} : une hypothèse ({head}) ne peut pas être "
                             f"la tête d'une règle (ABA plat).")
    for (x, y) in fw.less_than:
        if x not in fw.assumptions or y not in fw.assumptions:
            raise ValueError("Les préférences ne portent que sur des hypothèses "
                             f"(« {x} » / « {y} »).")
        if x == y:
            raise ValueError(f"Préférences cycliques : {x} < {x}.")
    return fw


# =============================================================================
# 3. Propriétés : circularité et atomicité
# =============================================================================

def dependency_graph(fw):
    """Arc b -> h pour chaque règle h <- ..., b, ... (b non-hypothèse)."""
    g = {x: set() for x in fw.literals}
    for body, head in fw.rules.values():
        for b in body:
            if b not in fw.assumptions:
                g.setdefault(b, set()).add(head)
                g.setdefault(head, set())
    return g


def is_circular(fw):
    """Vrai si un littéral dépend (transitivement) de lui-même."""
    g = dependency_graph(fw)
    WHITE, GREY, BLACK = 0, 1, 2
    color = {x: WHITE for x in g}

    def dfs(u):
        color[u] = GREY
        for v in g[u]:
            if color[v] == GREY:
                return True
            if color[v] == WHITE and dfs(v):
                return True
        color[u] = BLACK
        return False

    return any(color[x] == WHITE and dfs(x) for x in list(g))


def is_atomic(fw):
    """Atomique : le corps de chaque règle ne contient que des hypothèses."""
    return all(body <= fw.assumptions for body, _ in fw.rules.values())


def _fresh(name, taken):
    while name in taken:
        name += "'"
    taken.add(name)
    return name


# =============================================================================
# 4. Conversions
# =============================================================================

def to_non_circular(fw):
    """
    Construction par niveaux (dépliage borné).
    Soit k le nombre de littéraux non-hypothèses qui sont têtes de règles.
    Pour chaque littéral non-hypothèse x on crée x_1, ..., x_{k-1} ; x lui-même
    joue le rôle du niveau k.  x_i signifie « x dérivable par un arbre de
    hauteur <= i ».  Pour chaque règle  h <- B  et chaque niveau i :
        * i = 1 : h_1 <- B              seulement si B ne contient que des hypothèses
        * i > 1 : h_i <- B^{(i-1)}       (chaque non-hypothèse b de B devient b_{i-1})
    Un arbre de dérivation sans répétition a une hauteur <= k, donc les
    conclusions et supports d'origine sont conservés, et le nouveau framework
    est non-circulaire (les règles font toujours monter de niveau).
    """
    if not is_circular(fw):
        return fw.copy()

    heads = {h for _, h in fw.rules.values()}
    k = max(1, len(heads))
    taken = set(fw.literals)
    new = fw.copy()
    new.rules = {}

    level_name = {}
    for x in sorted(fw.non_assumptions()):
        for i in range(1, k):
            level_name[(x, i)] = _fresh(f"{x}_{i}", taken)
        level_name[(x, k)] = x
    new.literals = set(taken)

    def at(x, i):
        return x if x in fw.assumptions else level_name[(x, i)]

    for rid, (body, head) in fw.rules.items():
        only_assumptions = body <= fw.assumptions
        for i in range(1, k + 1):
            if i == 1 and not only_assumptions:
                continue
            nb = frozenset(at(b, i - 1) if i > 1 else b for b in body)
            new.rules[f"{rid}_{i}"] = (nb, at(head, i))
    return new


def to_atomic(fw):
    """
    Conversion en framework atomique (pour un framework NON-circulaire).
    Pour chaque non-hypothèse s apparaissant dans un corps de règle :
        * nouvelles hypothèses s_d (« s est dérivé ») et s_nd (« s n'est pas dérivé »)
        * contraire(s_d) = s_nd   et   contraire(s_nd) = s
        * chaque occurrence de s dans un corps est remplacée par s_d.
    Le corps de chaque règle ne contient alors plus que des hypothèses.
    """
    if is_atomic(fw):
        return fw.copy()
    if is_circular(fw):
        raise ValueError("to_atomic requiert un framework non-circulaire "
                         "(appeler to_non_circular d'abord).")

    new = fw.copy()
    taken = set(fw.literals)
    in_bodies = sorted({b for body, _ in fw.rules.values() for b in body}
                       - fw.assumptions)
    d = {}
    for s in in_bodies:
        sd = _fresh(f"{s}_d", taken)
        snd = _fresh(f"{s}_nd", taken)
        d[s] = sd
        new.assumptions |= {sd, snd}
        new.contraries[sd] = snd
        new.contraries[snd] = s
    new.literals = set(taken)
    new.rules = {rid: (frozenset(d.get(b, b) for b in body), head)
                 for rid, (body, head) in fw.rules.items()}
    return new


def convert(fw):
    """Conversion automatique : non-circulaire puis atomique. Renvoie (fw', étapes)."""
    steps = []
    if is_circular(fw):
        fw = to_non_circular(fw)
        steps.append("non-circulaire")
    if not is_atomic(fw):
        fw = to_atomic(fw)
        steps.append("atomique")
    return fw, steps


# =============================================================================
# 5. Arguments
# =============================================================================

def generate_arguments(fw):
    """
    Un argument  S ⊢ c  est un arbre de déduction de racine c dont les feuilles
    sont des hypothèses (ensemble S) ou des faits (règles à corps vide).
    On calcule, pour chaque littéral, l'ensemble des supports possibles.
    Les cycles sont évités (un littéral n'est pas réutilisé sur sa propre
    branche), ce qui rend la fonction correcte même sur un framework circulaire.
    Renvoie {(S, c): "A1", ...}.
    """
    rules_by_head = {}
    for rid, (body, head) in fw.rules.items():
        rules_by_head.setdefault(head, []).append(body)

    memo = {}

    def supports(lit, path):
        if lit in fw.assumptions:
            return {frozenset([lit])}
        if lit in path:
            return set()
        key = (lit, path)
        if key in memo:
            return memo[key]
        res = set()
        new_path = path | {lit}
        for body in rules_by_head.get(lit, []):
            parts = [supports(b, new_path) for b in sorted(body)]
            if any(not p for p in parts):
                continue
            for combo in itertools.product(*parts):
                res.add(frozenset().union(*combo) if combo else frozenset())
        memo[key] = res
        return res

    args = set()
    for lit in fw.literals:
        for S in supports(lit, frozenset()):
            args.add((S, lit))

    ordered = sorted(args, key=lambda a: (len(a[0]), sorted(a[0]), a[1]))
    return {arg: f"A{i + 1}" for i, arg in enumerate(ordered)}


# =============================================================================
# 6. Attaques ABA et ABA+
# =============================================================================

def compute_attacks(fw, args):
    """X = (S, c) attaque Y = (T, d) ssi c est le contraire d'une hypothèse de T."""
    attacks = set()
    for X in args:
        S, c = X
        for Y in args:
            T, _ = Y
            if any(fw.contraries.get(b) == c for b in T):
                attacks.add((X, Y))
    return attacks


def is_less_preferred(x, y, fw):
    """x < y  (x strictement moins préféré que y)."""
    return (x, y) in fw.less_than


def compute_aba_plus_attacks(fw, args, attacks_aba):
    """
    ABA+ (Čyras & Toni 2016), au niveau des arguments.
    Pour chaque attaque ABA  X=(S,c) -> Y=(T,·)  avec c = contraire(β), β ∈ T :
      * NORMALE  X -> Y   si aucun α ∈ S n'est moins préféré que β ;
      * INVERSE  Y -> X   s'il existe α ∈ S avec α < β
        (l'attaque est retournée : c'est Y qui attaque X).
    Les attaques inverses sont stockées DANS LEUR SENS FINAL (Y, X).
    """
    normal, reverse = set(), set()
    for (X, Y) in attacks_aba:
        S, c = X
        T, _ = Y
        for beta in T:
            if fw.contraries.get(beta) != c:
                continue
            if any(is_less_preferred(alpha, beta, fw) for alpha in S):
                reverse.add((Y, X))
            else:
                normal.add((X, Y))
    return {"normal": normal, "reverse": reverse, "all": normal | reverse}


# =============================================================================
# 7. Pipeline
# =============================================================================

@dataclass
class AnalysisResult:
    framework: ABAFramework
    arguments: Dict[Argument, str]
    attacks: Set[Attack]
    aba_plus: Dict[str, Set[Attack]]
    is_atomic_fw: bool
    is_circular_fw: bool


def analyze(fw):
    args = generate_arguments(fw)
    attacks = compute_attacks(fw, args)
    plus = compute_aba_plus_attacks(fw, args, attacks)
    return AnalysisResult(framework=fw, arguments=args, attacks=attacks,
                          aba_plus=plus, is_atomic_fw=is_atomic(fw),
                          is_circular_fw=is_circular(fw))


# =============================================================================
# 8. Affichage texte et graphe
# =============================================================================

def fmt_support(S):
    return "{" + ",".join(sorted(S)) + "}" if S else "∅"


def fmt_argument(arg):
    S, c = arg
    return f"{fmt_support(S)} ⊢ {c}"


def describe_framework(fw):
    lines = ["L: [" + ",".join(sorted(fw.literals)) + "]",
             "A: [" + ",".join(sorted(fw.assumptions)) + "]"]
    for a in sorted(fw.contraries):
        lines.append(f"C({a}): {fw.contraries[a]}")
    for rid in sorted(fw.rules, key=_natural_key):
        body, head = fw.rules[rid]
        lines.append(f"[{rid}]: {head} <- {','.join(sorted(body))}")
    if fw.less_than:
        lines.append("PREF (clôture) : " + ", ".join(
            f"{y} > {x}" for (x, y) in sorted(fw.less_than)))
    return lines


def _natural_key(s):
    return [int(t) if t.isdigit() else t for t in re.split(r"(\d+)", s)]


def render_attacks_graph(analysis, title="ABA vs ABA+ attacks", save_path=None):
    import io, base64, math
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.lines import Line2D
    from matplotlib.patches import FancyArrowPatch

    ids = analysis.arguments
    nodes = sorted(ids.values(), key=lambda s: int(s[1:]))
    label_of = {aid: fmt_argument(arg) for arg, aid in ids.items()}

    n = len(nodes)
    fig_size = min(8 + 0.35 * n, 22)
    fig, ax = plt.subplots(figsize=(fig_size, fig_size * 0.85))
    if n == 0:
        ax.text(0.5, 0.5, "Aucun argument", ha="center", va="center")
        ax.axis("off")
    else:
        R = 6.0
        pos = {v: (R * math.cos(2 * math.pi * i / n + math.pi / 2),
                   R * math.sin(2 * math.pi * i / n + math.pi / 2))
               for i, v in enumerate(nodes)}

        def edges(kind_set):
            return {(ids[X], ids[Y]) for (X, Y) in kind_set}

        layers = [
            (edges(analysis.attacks), "#9ca3af", ":", 1.4, 0.10),
            (edges(analysis.aba_plus["normal"]), "#2563eb", "-", 2.2, 0.22),
            (edges(analysis.aba_plus["reverse"]), "#dc2626", "--", 2.2, -0.22),
        ]
        for es, color, ls, lw, rad in layers:
            for (u, v) in es:
                if u == v:
                    x, y = pos[u]
                    ax.add_patch(FancyArrowPatch(
                        (x - 0.35, y + 0.45), (x + 0.35, y + 0.45),
                        connectionstyle="arc3,rad=-1.6", arrowstyle="-|>",
                        mutation_scale=16, color=color, lw=lw, linestyle=ls))
                    continue
                ax.add_patch(FancyArrowPatch(
                    pos[u], pos[v], connectionstyle=f"arc3,rad={rad}",
                    arrowstyle="-|>", mutation_scale=16, color=color, lw=lw,
                    linestyle=ls, shrinkA=26, shrinkB=26))

        for v in nodes:
            x, y = pos[v]
            ax.text(x, y, f"{v}\n{label_of[v]}", ha="center", va="center",
                    fontsize=9, fontweight="bold", zorder=5,
                    bbox=dict(boxstyle="round,pad=0.45", fc="#dbeafe", ec="#1e40af"))

        ax.set_xlim(-R - 2.2, R + 2.2)
        ax.set_ylim(-R - 1.8, R + 1.8)
        ax.set_aspect("equal")
        ax.legend(handles=[
            Line2D([0], [0], color="#9ca3af", linestyle=":", lw=1.4, label="Attaque ABA"),
            Line2D([0], [0], color="#2563eb", linestyle="-", lw=2.2, label="ABA+ normale"),
            Line2D([0], [0], color="#dc2626", linestyle="--", lw=2.2, label="ABA+ inverse"),
        ], loc="upper right", fontsize=10)
        ax.set_title(title, fontsize=14)
        ax.axis("off")

    fig.tight_layout()
    if save_path:
        fig.savefig(save_path, dpi=150, bbox_inches="tight", facecolor="white")
    buf = io.BytesIO()
    fig.savefig(buf, format="png", dpi=120, bbox_inches="tight", facecolor="white")
    plt.close(fig)
    return "data:image/png;base64," + base64.b64encode(buf.getvalue()).decode("ascii")
