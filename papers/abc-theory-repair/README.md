# ABC-style theory repair in IsaScheme

This directory explores a collaboration between IsaScheme and the ABC system of
Alan Bundy and colleagues, which repairs faulty logical theories with abduction,
belief revision and conceptual change (A. Bundy, *The ABC System for Repairing
Faulty Logical Theories*). It contains an extension of IsaScheme that implements
the faults and repair operations of section 5 of that chapter, the examples of the
chapter, and a pilot on recursive functions.

The extension is a separate Isabelle session based on IsaLibs. It does not change
IsaScheme itself.

## Files

- `main.tex` and `references.bib` are an article that describes the extension
  and the theories listed below. `main.pdf` is built with `latexmk -pdf main.tex`.
- `abc.ML` implements the extension. Theories are lists of Horn clauses, and terms
  may contain function symbols, so proofs by selected literal resolution are searched
  up to a depth limit, as section 8 of the chapter suggests for logics beyond
  Datalog. The file implements the two kinds of fault (incompatibilities and
  insufficiencies), the five operations that repair incompatibilities (Belief
  Revision 1 and 2, Reformation 1 to 3) and the five that repair insufficiencies
  (Abduction 1 and 2, Reformation 4 to 6), together with a breadth-first search for
  sequences of operations that leave the theory without faults.
- `ABC.thy` loads the extension and defines the commands `abc_faults` and
  `abc_repair`.
- `ABC_Examples.thy` runs the examples of the chapter, which are the black swan, the
  unique mothers, defeasible reasoning with a penguin, root cause analysis in a 5G
  network, and a student's arithmetic misconception.
- `ABC_Arithmetic.thy` recasts the arithmetic example on recursive functions over
  lists of digits. The repair, which removes the carry argument (Reformation 5), is
  written by hand there, and IsaScheme's `induct_auto` proves what the student's
  procedure computes.

## Usage

Clauses and atoms are written in Isabelle's syntax, inside quotes. Following ABC,
names that start with an upper-case letter are variables and the other ones are
constants or predicates. The text is parsed but not type-checked, so names such as
`sum` do not clash with the constants of HOL.

```
abc_repair
  axioms "german X ⟹ euro X" "euro X ∧ swan X ⟹ white X"
         "german bruce" "swan bruce"
  true "black bruce"
  false "white bruce"
```

`abc_faults` prints the faults with a proof of each incompatibility and the failed
goals of each insufficiency. `abc_repair` also prints, for each number of operations
up to `abc_max_repairs`, the fault-free theories found, with the clauses that each
repair deletes (`-`) and adds (`+`). A fault-free theory is not repaired further.

The options are

- `abc_max_depth` (default 30), the number of resolution steps of a proof;
- `abc_max_proofs` (default 5), the number of proofs kept for each atom;
- `abc_max_repairs` (default 2), the number of operations of a repair;
- `abc_max_solutions` (default 10), the number of theories shown for each number of
  operations.

The equality `X = Y` and the disequality `X ≠ Y` are built in. A goal `s = t` holds
when `s` and `t` unify, and `s ≠ t` holds when both are ground and distinct, which is
the closed world assumption of the chapter. Clauses may also have `=` or `≠` in
their heads, and these two symbols are never renamed and never change arity.

From ML, `ABC.read_clause`, `ABC.read_atom`, `ABC.faults`, `ABC.repairs`,
`ABC.search_levels` and `ABC.repair_report` give access to the same functions, which
the arithmetic example of `ABC_Examples.thy` uses to generate its 100 facts.

## Building

From the root of the repository:

```
isabelle build -d IsaLibs -d papers/abc-theory-repair ABC_Repair
```

The session takes about two minutes on 8 threads, most of it in the inductive proofs
of `ABC_Arithmetic.thy`. To read the reports, open `ABC_Examples.thy` in jEdit:

```
isabelle jedit -d IsaLibs -d papers/abc-theory-repair -l IsaLibs papers/abc-theory-repair/ABC_Examples.thy
```

## Differences from ABC

- Proofs are searched depth-first with a depth limit, and only the first proofs are
  kept, so with recursive clauses a theorem may be missed and classified as an
  insufficiency, as section 8 of the chapter warns.
- Incompatibilities are repaired on the first proof found. Its remaining proofs, if
  any, become faults of the next level of the search.
- For an insufficiency, the near misses are the clause heads with the same predicate
  that fail on the fewest arguments, and the heads with another predicate whose
  arguments unify with the goal. Reformation 4 either replaces the predicate in that
  head or merges the predicate of the goal into it in all axioms, which is the form
  used in the 5G example.
- Reformation 2 gives the targeted head a new constant. The atom that created the
  goal gets another new constant, or a new variable shared with the other occurrences
  of the predicate in its clause, as in the unique mothers example. The other facts
  get distinct new constants, and the other clauses get a new variable.
- New symbols are called `dum1`, `dum2`, ... and renamed symbols get a prime, as in
  `euro'`. Naming them meaningfully (symbol grounding) is left to the user.
- The preferred structure is never modified.
