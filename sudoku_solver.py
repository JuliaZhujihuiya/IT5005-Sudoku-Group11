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

    # 保证每一个格子恰好有一个数字
    for r in range(1, n + 1):
        for c in range(1, n + 1):
            candidates = [atom('Is', r, c, v) for v in range(1, n + 1)]
            kb.tell(associate('|', candidates)) # 保证每个格子至少一个数字
            for v in range(1, n + 1): 
                for w in range(v + 1, n + 1):
                    kb.tell(~atom('Is', r, c, v) | ~atom('Is', r, c, w)) # 保证每个格子至多一个数字

    # 保证同一行没有重复数字
    for r in range(1, n + 1):
        for v in range(1, n + 1):
            for c1 in range(1, n + 1):
                for c2 in range(c1 + 1, n + 1):
                    kb.tell(~atom('Is', r, c1, v) | ~atom('Is', r, c2, v))

    # 保证同一列没有重复数字
    for c in range(1, n + 1):
        for v in range(1, n + 1):
            for r1 in range(1, n + 1):
                for r2 in range(r1 + 1, n + 1):
                    kb.tell(~atom('Is', r1, c, v) | ~atom('Is', r2, c, v))

    # 保证同一宫没有重复数字
    for r0 in range(1, n + 1, box_h):
        for c0 in range(1, n + 1, box_w):
            # 收集当前宫的全部格子
            cells = []
            for r in range(r0, r0 + box_h):
                for c in range(c0, c0 + box_w):
                    cells.append((r, c))

            # 每一宫收集完毕，再配对
            for i in range(len(cells)):
                for j in range(i + 1, len(cells)):
                    r1, c1 = cells[i]
                    r2, c2 = cells[j]
                    for v in range(1, n + 1):
                        kb.tell(~atom('Is', r1, c1, v) | ~atom('Is', r2, c2, v))
    # 加入已经填入数字的atom
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

    # 基本规则，对于同一个格子，如果取v，那么就不能是除v外所有的数
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
    # 对于同一行，去过已经有v，那么这一行其他格子就不能再有v
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
    # 对于同一列，去过已经有v，那么这一列其他格子就不能再有v
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
    # 对于同一宫，宫内有一个格子是v，则宫内其他格子不能再是v
    for r0 in range(1, n + 1, box_h):
        for c0 in range(1, n + 1, box_w):
        # 收集当前宫的全部格子
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
    # 通过规则确定某格数字
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
    # 将已知的格子放入知识库
    for (r, c), v in givens.items():
        kb.tell(atom('Is', r, c, v))

    return kb

def solve_full_grid_fc(n, box_h, box_w, givens):
    """Solve the whole puzzle using build_definite_kb + pl_fc_entails.

    Returns
    -------
    dict[(int, int), int] -- {(row, col): value} for every cell
    """
    kb = build_definite_kb(n, box_h, box_w, givens)
    solved = {}

    for r in range(1, n + 1):
        for c in range(1, n + 1):
            for v in range(1, n + 1):
                query = atom('Is', r, c, v)
                if pl_fc_entails(kb, query):
                    solved[(r, c)] = v
                    break

    return solved


def pl_bc_entails(kb, query):
    """Your own backward-chaining implementation.

    Parameters
    ----------
    kb : PropDefiniteKB
    query : Expr

    Returns
    -------
    bool
    """
    raise NotImplementedError(
        'pl_bc_entails: implement backward chaining, soundly'
    )


def solve_full_grid_bc(n, box_h, box_w, givens):
    """Solve the whole puzzle using build_definite_kb + your own pl_bc_entails.

    For each cell, try each candidate value until pl_bc_entails confirms one
    -- the same per-cell strategy as solve_full_grid_fc, but backed by
    backward chaining instead of a single shared forward-chaining pass.

    Returns
    -------
    dict[(int, int), int] -- {(row, col): value} for every cell
    """
    raise NotImplementedError(
        'solve_full_grid_bc: solve every cell with backward chaining'
    )
