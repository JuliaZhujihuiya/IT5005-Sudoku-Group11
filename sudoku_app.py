"""Learning step 4: explain a query with recorded inference rules.

This is a learning checkpoint, not the finished assignment application.
Run: python -m streamlit run sudoku_app.py
"""

import json
from collections import deque
from time import perf_counter
from pathlib import Path

import streamlit as st
from logic_ import conjuncts
from sudoku_solver import (
    atom, build_definite_kb, build_general_kb, pl_bc_entails,
    solve_full_grid_fc, solve_full_grid_bc,
)


def record_forward_proof(kb):
    """Tutor-only instrumentation: record the first actual proof of each atom.

    Read the existing KB clauses, never the answer grid or BC's caches.
    A conclusion is queued only after all its premises have been processed.
    """
    reasons = {}
    rules = []
    waiting = {}
    remaining = []
    for clause in kb.clauses:
        if clause.op == "==>":
            premises = tuple(dict.fromkeys(conjuncts(clause.args[0])))
            index = len(rules)
            rules.append((premises, clause.args[1]))
            remaining.append(len(premises))
            for premise in premises:
                waiting.setdefault(premise, []).append(index)
        else:
            reasons[clause] = ()
    agenda = deque(reasons)
    for premises, conclusion in rules:
        if not premises and conclusion not in reasons:
            reasons[conclusion] = ()
            agenda.append(conclusion)
    while agenda:
        fact = agenda.popleft()
        for index in waiting.get(fact, []):
            remaining[index] -= 1
            if remaining[index] == 0:
                premises, conclusion = rules[index]
                if conclusion not in reasons:
                    reasons[conclusion] = premises
                    agenda.append(conclusion)
    return reasons


def proof_steps(reasons, target):
    """Select the target's recorded dependencies, preserving firing order."""
    needed = set()
    pending = [target]
    while pending:
        goal = pending.pop()
        if goal in needed:
            continue
        needed.add(goal)
        pending.extend(reasons[goal])
    return [(goal, premises) for goal, premises in reasons.items() if goal in needed]


def explain_step(goal, premises):
    """Translate a recorded Sudoku rule into a sentence, not an invented proof."""
    prefix = "Not" if goal.op.startswith("Not") else "Is"
    r, c, v = map(int, goal.op[len(prefix):].split("_"))
    cell = f"row {r}, column {c}"
    if not premises:
        return f"Given clue: {cell} contains {v}."
    if prefix == "Is":
        excluded = sorted(int(p.op.split("_")[-1]) for p in premises)
        return f"{cell.capitalize()} must contain {v}: all other values ({', '.join(map(str, excluded))}) have been eliminated."
    source = premises[0]
    sr, sc, sv = map(int, source.op[2:].split("_"))
    if (sr, sc) == (r, c):
        return f"Eliminate {v} from {cell}: this cell already contains {sv}."
    unit = f"row {r}" if sr == r else f"column {c}" if sc == c else "the same box"
    return f"Eliminate {v} from {cell}: row {sr}, column {sc} contains {sv} in {unit}."


st.set_page_config(page_title="Sudoku Tutor", page_icon="🧩")
st.title("Sudoku Tutor")
st.caption("Step 4 · Understand why a value follows")

# Locate the data beside this file, regardless of the terminal's directory.
with Path(__file__).with_name("puzzles.json").open(encoding="utf-8") as file:
    pool = json.load(file)

puzzle_index = st.selectbox(
    "Choose a puzzle",
    options=range(len(pool["puzzles"])),
    format_func=lambda i: f"Puzzle {i + 1} · {pool['puzzles'][i]['given_count']} givens",
)
puzzle = pool["puzzles"][puzzle_index]
n = pool["n"]

# JSON stores coordinates as strings; the solver expects integer tuples.
givens = {
    tuple(map(int, coordinate.split("_"))): value
    for coordinate, value in puzzle["givens"].items()
}

def render_board(values):
    """Display values; keep given clues distinct from inferred numbers."""
    # Rows and columns in this assignment start at 1.
    board = [
        [values.get((r, c), "") for c in range(1, n + 1)]
        for r in range(1, n + 1)
    ]
    # HTML adds Sudoku box borders and 1-based coordinate labels.
    html = '<table class="sudoku"><thead><tr><th></th>'
    html += ''.join(f'<th scope="col">{c}</th>' for c in range(1, n + 1))
    html += '</tr></thead><tbody>'
    for r, row in enumerate(board, start=1):
        html += f'<tr><th scope="row">{r}</th>'
        for c, value in enumerate(row, start=1):
            style = ''
            if (r, c) not in givens and value != '':
                style += 'color:#087f5b;background:#e6fcf5;' 
            if c % pool['box_w'] == 0 and c < n:
                style += 'border-right:3px solid #526582;'
            if r % pool['box_h'] == 0 and r < n:
                style += 'border-bottom:3px solid #526582;'
            html += f'<td style="{style}">{value}</td>'
        html += '</tr>'
    html += '</tbody></table>'
    st.markdown('''<style>
    .sudoku {border-collapse:collapse; width:100%; max-width:540px; table-layout:fixed;}
    .sudoku td {height:48px; text-align:center; border:1px solid #cbd5e1;
    font-size:22px; font-weight:650; background:#f8fafc; color:#183153;}
    .sudoku th {text-align:center; font-size:13px; color:#64748b; border:0;}
    </style>''' + html, unsafe_allow_html=True)

render_board(givens)
st.caption("Numbers are given clues. Blank cells are still unknown. Rows and columns are numbered 1–9.")

with st.expander("How the data becomes a board"):
    st.write('A JSON key such as "2_1" means row 2, column 1.')
    st.write("We convert that key to (2, 1), then look up each cell in givens.")
    st.write("If a coordinate is absent, we display a blank. No solving happens yet.")

st.subheader("Solve the whole puzzle")
algorithm = st.radio("Inference algorithm", ["Forward chaining", "Backward chaining"], horizontal=True)
# Retain a result during input changes, but never show another puzzle's result.
result_key = (puzzle_index, algorithm)
if st.session_state.get("solve_key") != result_key:
    st.session_state.pop("full_result", None)
    st.session_state["solve_key"] = result_key

if st.button("Solve puzzle", type="primary"):
    st.session_state.pop("full_result", None)
    solver = solve_full_grid_fc if algorithm == "Forward chaining" else solve_full_grid_bc
    try:
        with st.spinner("Solving from the givens..."):
            start = perf_counter()
            solved = solver(n, pool["box_h"], pool["box_w"], givens)
            elapsed = perf_counter() - start
        st.session_state["full_result"] = (solved, elapsed)
    except ValueError as error:
        st.warning(f"The current inference rules could not complete this puzzle: {error}")

if "full_result" in st.session_state:
    solved, elapsed = st.session_state["full_result"]
    st.success(f"Puzzle {puzzle_index + 1} solved with {algorithm.lower()} in {elapsed:.3f} seconds.")
    render_board(solved)
    st.caption("Dark numbers: given clues. Green numbers: inferred values. Time includes building the knowledge base and solving, excluding display.")

st.subheader("Ask about a cell")
st.write("Can the puzzle's rules prove that this cell contains this value?")

# Each input change reruns the page, clearing the previous button result.
# This prevents a verdict for an old query being shown beside new inputs.
row_input, column_input, value_input = st.columns(3)
with row_input:
    query_r = st.number_input("Row", min_value=1, max_value=n, value=2, step=1)
with column_input:
    query_c = st.number_input("Column", min_value=1, max_value=n, value=2, step=1)
with value_input:
    query_v = st.number_input("Value", min_value=1, max_value=n, value=9, step=1)

if st.button("Check this value", type="primary"):
    with st.spinner("Checking the puzzle's rules..."):
        # Only the givens go into the solver; the supplied solution is not read.
        kb = build_definite_kb(n, pool["box_h"], pool["box_w"], givens)
        query = atom("Is", query_r, query_c, query_v)
        result = pl_bc_entails(kb, query)

    statement = f"Puzzle {puzzle_index + 1}: row {query_r}, column {query_c} is {query_v}."
    if result:
        st.success(f"True — {statement} This follows from the givens and rules.")
    else:
        st.info(f"False — {statement} This is not entailed by the current knowledge base.")
        st.caption("Not proved does not by itself mean the opposite has been proved.")

    st.subheader("Why? Follow the reasoning")
    st.caption("The verdict above uses backward chaining. These explanation steps come from a separate forward-chaining run on the same rules.")
    with st.spinner("Recording the inference steps..."):
        reasons = record_forward_proof(kb)
    rejected = atom("Not", query_r, query_c, query_v)
    if result != (query in reasons):
        st.error("The two inference methods disagree. A proof cannot be displayed reliably.")
    else:
        target = query if result else rejected if rejected in reasons else None
        if target is None:
            st.info("Neither this value nor its elimination was proved. The current rules leave this query unresolved.")
        else:
            if not result:
                st.write("In this case, the rules also prove that the candidate is eliminated. Here is that separate proof:")
            steps = proof_steps(reasons, target)
            st.write(f"{len(steps)} steps, starting with given clues. Each later step uses earlier facts.")
            for index, (goal, premises) in enumerate(steps, start=1):
                sentence = explain_step(goal, premises)
                with st.expander(f"{index}. {sentence}"):
                    st.write(sentence)
                    if premises:
                        st.write("This step uses:")
                        for premise in premises:
                            st.write(f"• Step {next(i for i, (g, _) in enumerate(steps, 1) if g == premise)}")
                    else:
                        st.write("This number was supplied in the selected puzzle.")
