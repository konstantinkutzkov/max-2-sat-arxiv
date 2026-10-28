# Datasets

This file plans the instance sets for experiments with the pruning constraints. Nothing has been downloaded yet. For each set, the file records where to get it, what it contains, and how close it is to Max 2-SAT. Links and sizes were checked on 2026-10-28. The sizes come from directory listings, HTTP headers, or the papers.

## Storage

Download each set into the subfolder of `data/` named in the last column of the tables, for example `data/biqmac/`.

Git ignores these subfolders (see `.gitignore`), because GitHub rejects files over 100 MB and the MaxSAT collection alone has 59 GB. Git commits only the files directly in `data/` with the extensions `.md`, `.py`, `.sh` and `.csv`: this file, conversion scripts and extracted statistics.

## Formats

- **WCNF** (MaxSAT Evaluations).
  - Since 2022, a hard clause is a line `h l1 ... lk 0`, and a soft clause is a line `w l1 ... lk 0` with weight `w`.
  - Older files start with `p wcnf n m top`, and every clause line starts with its weight. Clauses of weight `top` are hard.
- **Edge lists** (Max-Cut: Biq Mac, Gset, rudy). The first line is `n m`, followed by one line `i j w` per edge.
- **WCSP** (protein design). These are cost function networks in the format of toulbar2. Converters come with the data.
- **From Max-Cut to Max 2-SAT.**
  - An edge {i, j} of weight w > 0 becomes the clauses (x<sub>i</sub> ∨ x<sub>j</sub>) and (¬x<sub>i</sub> ∨ ¬x<sub>j</sub>), each of weight w.
  - An edge of weight w < 0 becomes the clauses (x<sub>i</sub> ∨ ¬x<sub>j</sub>) and (¬x<sub>i</sub> ∨ x<sub>j</sub>), each of weight |w|.
  - The satisfied weight is then the weight of the cut plus a constant.
  - An external field h<sub>i</sub> becomes a unit clause of weight |h<sub>i</sub>|: x<sub>i</sub> or ¬x<sub>i</sub>, depending on the sign of h<sub>i</sub>.

## 1. Applications in the natural sciences

These are the applications cited in the conclusion of the paper.

### Spin glasses (statistical physics)

Ground states of Ising spin glasses are maximum cuts. After the conversion above, these instances are weighted Max 2-SAT.

| Set | Content | Size | Download | Folder |
|---|---|---|---|---|
| Biq Mac, physics instances of Liers | 2D toroidal grids with Gaussian couplings (100–400 spins). 3D toroidal grids (125–343 spins). 1D chains with long-range couplings (`ising2.5`, `ising3.0`; 100–300 spins), which are dense. Three instances per size. Optimal values are in [biqmaclib.pdf](https://biqmac.aau.at/biqmaclib.pdf) | 2.2 MB | [ising_all.tar.gz](https://biqmac.aau.at/library/tar_files/ising_all.tar.gz) | `biqmac/` |
| MaxSAT Evaluation 2016, spin glasses | Five instances, `t3pm3-5555.spn` … `t7pm3-9999.spn`, already in Max 2-SAT form (crafted track, family `maxcut`) | – | Probably in the MaxSAT Lib family [maxcut](http://www.cs.toronto.edu/maxsat-lib/maxsat-instances/downloads/unweighted/maxcut.zip) (0.8 MB). Otherwise, find them in `meta.db` (Section 2) | `mse/` |
| DIMACS Challenge 7, torus set | 3D toroidal grids with ±1 couplings (`toruspm-8-50`, `toruspm3-15-50`) and with Gaussian couplings (`torusg3-8`, `torusg3-15`), 512 and 3,375 spins. The set has graph files and a Matlab converter. Its listed values are SDP bounds, not cuts | – | [vsdp/DIMACS](https://github.com/vsdp/DIMACS), a mirror of the DIMACS archive | `dimacs/` |
| Jünger et al. (2019), quantum-annealer benchmark | 1,445 Ising instances on Chimera graphs, up to 2,032 nodes | – | The link in the paper is dead (404, not archived). Ask the authors | – |
| rudy generator (Rinaldi) | Random, planar and toroidal graphs with random weights, so new spin glasses of any size | 18 KB | [rudy.tar.gz](http://www-user.tu-chemnitz.de/~helmberg/rudy.tar.gz) | `generators/` |

### Materials science: alloys

| Set | Content | Size | Download | Folder |
|---|---|---|---|---|
| `generalized-ising` (MSE 2017, W. Huang) | Ground states of a cluster expansion fitted to DFT energies of Li<sub>x</sub>Fe<sub>1−x</sub>O on a 5×5×5 grid. About 100 cluster types (pairs, triplets, quadruplets), so the clauses are weighted and short. [Description](http://hdl.handle.net/10138/228949), p. 33 | 5.0 MB | [generalized-ising_wt.zip](http://www.cs.toronto.edu/maxsat-lib/maxsat-instances/downloads/weighted/generalized-ising_wt.zip) | `mse/` |
| maxsat-ising (Huang, Kitchaev) | Ground-state solver that builds MaxSAT instances from a cluster expansion. It includes two example expansions, one with pair terms only. Needs Gurobi and GCC 4.8 | – | [dkitch/maxsat-ising](https://github.com/dkitch/maxsat-ising) | `generators/` |

### Protein design

| Set | Content | Size | Download | Folder |
|---|---|---|---|---|
| CPD-AIJ (Allouche et al.) | 47 designs with 11–120 residues and up to 198 rotamers per residue, in WCSP format. Pairwise energies give 2-clauses. Choosing one rotamer per residue gives hard constraints. Scripts convert to MaxSAT (`wcsp2sat.py`, `wcsp2sat-support.py`), binary quadratic (`wcsp2biq.cc`) and ILP formats | 1.7 GB; single files up to 177 MB (xz) | [CPD-AIJ](https://web-genobioinfo.toulouse.inrae.fr/~tschiex/CPD-AIJ/) | `cpd/` |

### Biology

| Set | Content | Size | Download | Folder |
|---|---|---|---|---|
| Single-cell tumor phylogeny (MSE 2020; Rashidi Mehrabadi, Malikić, Sahinalp, the authors of PhISCS) | 400 simulated instances with 50–500 cells and 50–300 mutations. Soft unit clauses model sequencing errors. Hard 2- and 3-clauses enforce a perfect phylogeny | 5.2 GB | [scSequencing_Mehrabadi.zip](http://www.cs.toronto.edu/maxsat-lib/maxsat-instances/2020/weighted/scSequencing_Mehrabadi.zip) | `mse/` |
| `bio-repair` (MSE 2017) | 30 instances that repair large biological networks so that they agree with experimental data (Gebser et al., KR 2010). They were translated from ASP via pseudo-Boolean constraints, so much of their structure comes from cardinality encodings. The instances of Guerra and Lynce (2012) were not found | 58 MB | [biorepair.zip](http://www.cs.toronto.edu/maxsat-lib/maxsat-instances/downloads/unweighted/biorepair.zip) | `mse/` |
| `haplotyping-pedigrees` | Weighted instances of haplotype inference with pedigree information. The link to the 500 instances of Marques-Silva et al. (2011) is dead, and this family is very likely the same source | 558 MB | [haplotyping-pedigrees_wt.zip](http://www.cs.toronto.edu/maxsat-lib/maxsat-instances/downloads/weighted/haplotyping-pedigrees_wt.zip) | `mse/` |
| `rna-alignment` (MSE 2017), `phylogenetic-trees` (MSE 2020) | RNA alignment with pseudoknots. Maximum compatibility of phylogenetic characters: 90 Horn instances with 6–74 million clauses. Both are far from Max 2-SAT and have low priority | – | MaxSAT Lib, Zenodo (Section 2) | – |

### VLSI design

Via minimization (Barahona et al., 1988) reduces to Max-Cut. We found no public instances.

## 2. Classic benchmarks

| Set | Content | Size | Download | Folder |
|---|---|---|---|---|
| MaxSAT Evaluation collection, version 2026 | All instances of the MaxSAT Evaluations, in normalized WCNF. Each instance is one xz file, and each submission year is one zip (2007: 1 MB; 2019: 11.6 GB; 2020: 18.7 GB; 2026: 18.2 GB). Metadata is in two SQLite databases read with GBD. `meta.db` holds the family, the optimal and best-known costs, and the tracks. `base.db` holds the numbers of soft and hard clauses of each length 1–9, the weights and the degrees. License CC BY 4.0 | 58.9 GB; metadata 52 MB | [Zenodo](https://doi.org/10.5281/zenodo.21283147); [description of the metadata](https://github.com/maxsat-evaluations/data/blob/main/metadata.md) | `mse/` |
| MaxSAT Lib (Toronto) | The evaluation instances sorted by family, one zip per family: `downloads/unweighted/<family>.zip` and `downloads/weighted/<family>_wt.zip`. Newer families are under `<year>/` | per family | [unweighted](https://www.cs.toronto.edu/maxsat-lib/maxsat-instances/master-set/unweighted/), [weighted](https://www.cs.toronto.edu/maxsat-lib/maxsat-instances/master-set/weighted/) | `mse/` |
| Random tracks of the MaxSAT Evaluations 2006–2016 | Random Max-2-SAT and Max-3-SAT. The old site maxsat.udl.cat is down, and its archives are not in the Wayback Machine. Check `meta.db` for these families | – | – | – |
| Borchers and Furman (1999) | Random Max-2-SAT and Max-3-SAT test problems, unweighted and weighted. A common test set for exact Max-SAT algorithms | – | [Wayback copy of satprobs.tar.gz](http://web.archive.org/web/20060919222011/http://infohost.nmt.edu:80/~borchers/satprobs.tar.gz) (the original page is unreachable) | `borchers/` |
| Gset (Helmberg and Rendl, hosted by Y. Ye) | 71 Max-Cut graphs, G1–G81, generated by rudy: random, planar and toroidal, with 800–20,000 nodes. Only best-known cuts are available, and most are not proven optimal | 10.6 MB | [Gset](https://web.stanford.edu/~yyye/yyye/Gset/) | `gset/` |
| Biq Mac, other sets | Max-Cut on random graphs from rudy (60–100 nodes). QUBO instances from Beasley; Glover, Kochenberger and Alidaee; and Billionnet and Elloumi (20–500 variables). Optimal values or bounds are known | 9.6 MB for the whole library | [biqmac_all.tar.gz](https://biqmac.aau.at/library/tar_files/biqmac_all.tar.gz) | `biqmac/` |
| MQLib (Dunning, Gupta, Silberholz, 2018) | 3,296 Max-Cut and QUBO instances from many sources, with instance features, plus implementations of many heuristics. The repository lists the instances in `data/metrics.csv` and fetches them from an S3 bucket with `scripts/downloadGraph.py` (not checked) | – | [MQLib/MQLib](https://github.com/MQLib/MQLib) | `mqlib/` |

## 3. Generated instances

Random families of growing size show how the running time scales with n. The public sets show the behavior on real data.

- **Spin glasses and random graphs:** rudy (Section 1).
- **The classes of the paper:**
  - `make_instance` in `scripts/verify_dense_max2sat_random_models.py` generates the semirandom and biased random models.
  - `random_formula` in `scripts/explore_soft_count.py` generates random signs on G(n, p).
  - `scripts/explore_paley_maxcut.py` builds Max-Cut on Paley graphs.
  - These can be extended to regular expanders and block models.

## 4. Order of downloads

1. Small sets with known optima: Biq Mac (9.6 MB), Gset (10.6 MB), Borchers and Furman, and the MaxSAT Lib family `maxcut` (0.8 MB).
2. The MaxSAT metadata (52 MB). From `base.db`, select the instances whose soft clauses have length at most 2 and that have few hard clauses. Then download only those families.
3. The application sets, smallest first: `generalized-ising` (5 MB), `bio-repair` (58 MB), `haplotyping-pedigrees` (558 MB), protein design (1.7 GB), single-cell phylogeny (5.2 GB).
4. Generated families, for the scaling experiments.
