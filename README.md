# Kourovka

[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

This repository contains the Lean formalisation accompanying the paper *On Some Problems from the Kourovka Notebook*.

## Results

- [**3.46**](Kourovka/Problem_3_46.lean): a group with exactly two maximal locally soluble normal subgroups (`kourovka_3_46`).
- [**18.50**](Kourovka/Problem_18_50.lean): for every $1 \le k \le n!$, a group containing $n$ distinct elements whose permuted products take exactly $k$ values (`kourovka_18_50`).
- [**19.25**](Kourovka/Problem_19_25.lean): a simple and a non-simple group of order $6048$ with the same totient sum $23984$ (`kourovka_19_25`).
- [**20.125**](Kourovka/Problem_20_125.lean): a surjective, non-injective Rota-Baxter operator on a non-abelian group (`kourovka_20_125`).
- [**21.8**](Kourovka/Problem_21_8.lean): for $k \ge 4$, the horizontal class transpositions of moduli at most $k$ generate a group isomorphic to the symmetric group on $\mathrm{lcm}(2,\ldots,k)$ letters (`kourovka_21_8`).
- [**21.24**](Kourovka/Problem_21_24.lean): every cograph power graph of a finite group is chordal (`kourovka_21_24`).
- [**21.147**](Kourovka/Problem_21_147.lean): the right-relatively convex subgroups of a right-orderable group need not form a sublattice (`kourovka_21_147`).
- [**21.150**](Kourovka/Problem_21_150.lean): a $p$-group $G=A\rtimes B$ with $A$ and $B$ elementary abelian and $C_B(a)=1$ such that, for $H=\langle a,B\rangle$, $\mathrm{rank}(Z(H)\cap H')>\mathrm{rank}(B)$ (`kourovka_21_150`).

The repository also contains [`kourovka_21_149`](Kourovka/Problem_21_149.lean), which answers the original formulation of Problem 21.149 from [version 43](https://arxiv.org/abs/1401.0300v43). The strengthened formulation in [version 45](https://arxiv.org/abs/1401.0300v45) remains open.

## Structure

- [`Kourovka.lean`](Kourovka.lean) and [`Kourovka/Problem_*.lean`](Kourovka/) contain the curated formal developments.
- [`Kourovka/Mathlib/`](Kourovka/Mathlib/) contains reusable declarations intended for Mathlib.
- [`Kourovka/Util/`](Kourovka/Util/) contains project-specific supporting material.
- [`Kourovka/Aristotle.lean`](Kourovka/Aristotle.lean) and [`Kourovka/Aristotle/`](Kourovka/Aristotle/) preserve the original Aristotle submissions.

Full project metadata is recorded in [`formalization.yaml`](formalization.yaml).

## License

The repository is released under the [Apache License 2.0](LICENSE).
