# Exact polynomial-space algorithms for Max 2-SAT

Working repository for the paper *Accumulating Pruning Constraints: New Exact
Polynomial-Space Algorithms for Max 2-SAT*.

## Layout

- `paper/`: the paper `dense_max2sat_arxiv.tex`, its bibliography
  `pruning_2_sat.bib`, the generated `.bbl` file and the compiled PDF.
- `notes/`: research notes written along the way (`max2sat_*.tex`), each with
  its PDF, and the revision plan of the paper.
- `scripts/`: Python experiments (`explore_*.py`) and checks of the paper's
  constructions (`verify_dense_max2sat_*.py`). Each script writes its results
  (`*_checks.json`) next to itself, and several scripts import each other, so
  they belong in one folder.
- `lean/`: the Lean 4 formalization; see `lean/README.md`. Running
  `python3 lean/verify.py` builds it and compares the formalized statements with
  the theorems of `paper/dense_max2sat_arxiv.tex`.
- `archive/`: an earlier draft of the paper (`dense_max2sat_paper.tex`),
  snapshots of the Lean artifact (`lean-snapshots/`) and older PDF builds
  (`older-pdfs/`).

## Building the paper

```bash
cd paper
pdflatex dense_max2sat_arxiv
bibtex dense_max2sat_arxiv
pdflatex dense_max2sat_arxiv
pdflatex dense_max2sat_arxiv
```

The Lean build cache `lean/.lake`, which `lake build` recreates, the scratch
folder `tmp/` and LaTeX build files are not part of the repository.
