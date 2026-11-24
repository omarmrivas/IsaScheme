# Taming divergent Knuth–Bendix completion with iterated functions

Article (prepared for the *Journal of Symbolic Computation*, Elsevier
`elsarticle` class) about the tower critic, a divergence critic of IsaScheme's
`complete` command. The critic replaces infinite families of rules such as
`f (g^n (f x)) = f (g^n x)` by a single Isabelle/HOL theorem
`f ((g ^^ Suc n) (f x)) = f ((g ^^ Suc n) x)`, proved by induction on `n`.

## Contents

| Path | What it is |
|------|------------|
| `main.tex` | The article. |
| `references.bib` | Bibliography (`elsarticle-num` style). |
| `experiments/` | The Isabelle theories of Section 5. |
| `experiments/diverging/` | Examples on which completion does not terminate (open them in jEdit and interrupt them). |

## Building the PDF

```
latexmk -pdf main.tex
```

## Running the examples

The examples need IsaLibs built for Isabelle2026 and the AProVE server
running (see the top-level `README` and `doc/IsaLibs_comandos.pdf`).
From the root of the repository:

```
isabelle build -d IsaLibs -d papers/divergent-completion-iterated-functions/experiments Divergence_Examples
```

To read the traces (`Tower critic: ...`, `Tower rule: ...`,
`Additions: ...`), open the theories in jEdit:

```
isabelle jedit -d IsaLibs -l IsaLibs papers/divergent-completion-iterated-functions/experiments/Ex1_FG.thy
```

## Before submission

- Complete the author's affiliation and e-mail in `main.tex` (marked `TODO`).
- The experiments were run with Isabelle2026 and AProVE on an 8-thread
  machine; times will differ elsewhere.
