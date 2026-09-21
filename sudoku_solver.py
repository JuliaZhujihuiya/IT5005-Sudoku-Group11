"""IT5005 Assignment 1: student implementation file.

Implement the functions marked below. Do not modify utils.py or logic_.py.
"""

from utils import *
from logic_ import *


# Do not change this function; it is used to create atomic propositions.
def atom(prefix, r, c, v):
    """prefix is 'Is' or 'Not'. Returns the Expr for e.g. Is3_2_4."""
    return expr(f'{prefix}{r}_{c}_{v}')


def build_general_kb(n, box_h, box_w, givens):
    """Return a PropKB encoding this n x n Sudoku's constraints plus the given
    cells, as general clauses.

    Parameters
    ----------
    n, box_h, box_w : int
    givens : dict[(int, int), int]

    Returns
    -------
    PropKB
    """
    kb = PropKB()

    # Ensure that every cell contains exactly one value.
    for r in range(1, n + 1):
        for c in range(1, n + 1):
            candidates = [atom('Is', r, c, v) for v in range(1, n + 1)]
            kb.tell(associate('|', candidates)) # Ensure at least one value per cell.
            for v in range(1, n + 1): 
                for w in range(v + 1, n + 1):
                    kb.tell(~atom('Is', r, c, v) | ~atom('Is', r, c, w)) # Ensure at most one value per cell.

    # Ensure that no value is repeated within a row.
    for r in range(1, n + 1):
        for v in range(1, n + 1):
            for c1 in range(1, n + 1):
                for c2 in range(c1 + 1, n + 1):
                    kb.tell(~atom('Is', r, c1, v) | ~atom('Is', r, c2, v))

    # Ensure that no value is repeated within a column.
    for c in range(1, n + 1):
        for v in range(1, n + 1):
            for r1 in range(1, n + 1):
                for r2 in range(r1 + 1, n + 1):
                    kb.tell(~atom('Is', r1, c, v) | ~atom('Is', r2, c, v))

    # Ensure that no value is repeated within a box.
    for r0 in range(1, n + 1, box_h):
        for c0 in range(1, n + 1, box_w):
            # Collect all cells in the current box.
            cells = []
            for r in range(r0, r0 + box_h):
                for c in range(c0, c0 + box_w):
                    cells.append((r, c))

            # Generate cell pairs after collecting the complete box.
            for i in range(len(cells)):
                for j in range(i + 1, len(cells)):
                    r1, c1 = cells[i]
                    r2, c2 = cells[j]
                    for v in range(1, n + 1):
                        kb.tell(~atom('Is', r1, c1, v) | ~atom('Is', r2, c2, v))
    # Add the given values as atomic facts.
    for (r, c), v in givens.items():
        kb.tell(atom('Is', r, c, v))

    return kb

def build_definite_kb(n, box_h, box_w, givens):
    """Return a PropDefiniteKB encoding this n x n Sudoku's constraints plus
    the given cells, using elimination + last-candidate reasoning.

    Parameters
    ----------
    n, box_h, box_w : int
    givens : dict[(int, int), int] -- {(row, col): value}, 1-indexed

    Returns
    -------
    PropDefiniteKB
    """
    kb = PropDefiniteKB()

    # If a cell contains v, eliminate every other value from that cell.
    for r in range(1, n + 1):
        for c in range(1, n + 1):
            for v in range(1, n + 1):
                for w in range(1, n + 1):
                    if v != w:
                        kb.tell(
                            atom('Is', r, c, v)
                            | '==>' |
                            atom('Not', r, c, w)
                        )
    # If a row already contains v, eliminate v from every other cell in that row.
    for r in range(1, n + 1):
        for v in range(1, n + 1):
            for c1 in range(1, n + 1):
                for c2 in range(1, n + 1):
                    if c1 != c2:
                        kb.tell(
                            atom('Is', r, c1, v)
                            | '==>' |
                            atom('Not', r, c2, v)
                        )
    # If a column already contains v, eliminate v from every other cell in that column.
    for c in range(1, n + 1):
        for v in range(1, n + 1):
            for r1 in range(1, n + 1):
                for r2 in range(1, n + 1):
                    if r1 != r2:
                        kb.tell(
                            atom('Is', r1, c, v)
                            | '==>' |
                            atom('Not', r2, c, v)
                        )
    # If a box already contains v, eliminate v from every other cell in that box.
    for r0 in range(1, n + 1, box_h):
        for c0 in range(1, n + 1, box_w):
        # Collect all cells in the current box.
            cells = []
            for r in range(r0, r0 + box_h):
                for c in range(c0, c0 + box_w):
                    cells.append((r, c))

            for i in range(len(cells)):
                for j in range(len(cells)):
                    if i != j:
                        r1, c1 = cells[i]
                        r2, c2 = cells[j]

                        for v in range(1, n + 1):
                            kb.tell(
                            atom('Is', r1, c1, v)
                            | '==>' |
                            atom('Not', r2, c2, v)
                            )
    # Infer a cell's value after all other candidates have been eliminated.
    for r in range(1, n + 1):
        for c in range(1, n + 1):
            for v in range(1, n + 1):
                premises = [
                    atom('Not', r, c, w)
                    for w in range(1, n + 1)
                    if w != v
                ]
                kb.tell(
                    associate('&', premises)
                    | '==>' |
                    atom('Is', r, c, v)
                )
    # Add the given values to the knowledge base.
    for (r, c), v in givens.items():
        kb.tell(atom('Is', r, c, v))

    return kb

def solve_full_grid_fc(n, box_h, box_w, givens):
    """Solve the whole puzzle using build_definite_kb + pl_fc_entails.

    ``logic_.py`` intentionally implements ``clauses_with_premise`` by
    scanning every rule.  A full-grid solve asks many entailment queries, so
    that repeated scan dominates the running time.  Build the same lookup
    once for this KB, then let the supplied ``pl_fc_entails`` algorithm use
    it unchanged for every query.

    Returns
    -------
    dict[(int, int), int] -- {(row, col): value} for every cell
    """
    kb = build_definite_kb(n, box_h, box_w, givens)

    # Map each premise atom to the definite clauses that contain it.  This is
    # equivalent to PropDefiniteKB.clauses_with_premise(), but avoids a full
    # scan of kb.clauses every time forward chaining derives an atom.
    rules_by_premise = {}
    for clause in kb.clauses:
        if clause.op == '==>':
            for premise in conjuncts(clause.args[0]):
                rules_by_premise.setdefault(premise, []).append(clause)

    def cached_clauses_with_premise(premise):
        return rules_by_premise.get(premise, [])

    kb.clauses_with_premise = cached_clauses_with_premise

    # Givens are unit facts in the KB, so their values are already entailed.
    solved = dict(givens)

    for r in range(1, n + 1):
        for c in range(1, n + 1):
            if (r, c) in solved:
                continue

            for v in range(1, n + 1):
                query = atom('Is', r, c, v)
                if pl_fc_entails(kb, query):
                    solved[(r, c)] = v
                    break

            if (r, c) not in solved:
                raise ValueError(
                    f'Forward chaining could not determine cell ({r}, {c}).'
                )

    return solved


def pl_bc_entails(kb, query):
    """Return whether ``query`` follows from a definite-clause KB.

    The search is goal-directed: beginning at ``query``, it follows only rules
    that could conclude the current goal and records their premise goals.  The
    resulting dependency table lets cyclic rules be resolved without unbounded
    recursive re-expansion.  Indexes and completed answers are cached on the
    supplied KB, so full-grid solving can reuse them without changing
    ``kb.clauses``.

    Parameters
    ----------
    kb : PropDefiniteKB
    query : Expr

    Returns
    -------
    bool
    """
    if not hasattr(kb, '_bc_rules_by_conclusion'):
        facts = set()
        rules_by_conclusion = {}

        for clause in kb.clauses:
            if is_prop_symbol(clause.op):
                facts.add(clause)
            elif clause.op == '==>':
                conclusion = clause.args[1]
                premises = tuple(conjuncts(clause.args[0]))
                rules_by_conclusion.setdefault(conclusion, []).append(premises)

        kb._bc_rules_by_conclusion = rules_by_conclusion
        kb._bc_true = facts
        kb._bc_false = set()

    rules_by_conclusion = kb._bc_rules_by_conclusion
    if query in kb._bc_true:
        return True
    if query in kb._bc_false:
        return False

    # Expand the AND/OR proof graph backwards from the query.  An explicit
    # stack represents recursive goal expansion, avoiding Python recursion
    # limits for the densely connected Sudoku rule graph.
    relevant_goals = set()
    relevant_rules = []
    goals_to_expand = [query]

    while goals_to_expand:
        goal = goals_to_expand.pop()
        if goal in relevant_goals:
            continue

        relevant_goals.add(goal)
        for premises in rules_by_conclusion.get(goal, []):
            relevant_rules.append((premises, goal))
            for premise in premises:
                if premise not in relevant_goals:
                    goals_to_expand.append(premise)

    # Resolve the selected proof graph by repeatedly firing a rule once all
    # of its premises are proved.  This is tabled backward chaining: it only
    # considers goals relevant to the original query, but handles cycles by
    # sharing the table rather than recursively revisiting active goals.
    proved = relevant_goals & kb._bc_true
    agenda = list(proved)
    remaining_premises = []
    rules_waiting_for = {}

    for index, (premises, conclusion) in enumerate(relevant_rules):
        missing = [premise for premise in premises if premise not in proved]
        remaining_premises.append(len(missing))

        if not missing:
            if conclusion not in proved:
                proved.add(conclusion)
                agenda.append(conclusion)
        else:
            for premise in missing:
                rules_waiting_for.setdefault(premise, []).append(index)

    while agenda:
        premise = agenda.pop()
        for rule_index in rules_waiting_for.get(premise, []):
            remaining_premises[rule_index] -= 1
            if remaining_premises[rule_index] == 0:
                conclusion = relevant_rules[rule_index][1]
                if conclusion not in proved:
                    proved.add(conclusion)
                    agenda.append(conclusion)

    # Every possible proof path for a relevant goal was included above.  With
    # an unchanged Horn KB, an unresolved relevant goal cannot become true in
    # a later query, so both successful and failed answers are safe to cache.
    kb._bc_true.update(proved)
    kb._bc_false.update(relevant_goals - proved)
    return query in proved
            


def solve_full_grid_bc(n, box_h, box_w, givens):
    """Solve the whole puzzle using build_definite_kb + your own pl_bc_entails.

    For each cell, try each candidate value until pl_bc_entails confirms one
    -- the same per-cell strategy as solve_full_grid_fc, but backed by
    backward chaining instead of a single shared forward-chaining pass.

    Returns
    -------
    dict[(int, int), int] -- {(row, col): value} for every cell
    """
    kb = build_definite_kb(n, box_h, box_w, givens)
    # Each given is a unit fact, hence already entailed without a search.
    solved = dict(givens)

    for r in range(1, n + 1):
        for c in range(1, n + 1):
            if (r, c) in solved:
                continue

            for v in range(1, n + 1):
                query = atom('Is', r, c, v)
                if pl_bc_entails(kb, query):
                    solved[(r, c)] = v
                    break

            if (r, c) not in solved:
                raise ValueError(
                    f'Backward chaining could not determine cell ({r}, {c}).'
                )

    return solved
