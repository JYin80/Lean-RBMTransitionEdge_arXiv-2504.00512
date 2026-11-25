# Lean formalization of Fan–Stone–Yang–Yin, "Localization-delocalization transition for a random block matrix model"

This repository contains a Lean 4 / Mathlib proof of the main results of

> Jiaqi Fan, Bertrand Stone, Fan Yang and Jun Yin, *Localization-delocalization transition for a random block
> matrix model*, [arXiv:2504.00512](https://arxiv.org/abs/2504.00512).

The version of the paper that the Lean code follows is
[`paper/FanStoneYangYin_RBMTransitionEdge_Lean_version.pdf`](paper/FanStoneYangYin_RBMTransitionEdge_Lean_version.pdf) (LaTeX source
in `paper/tex/`): arXiv version 2 with the corrections listed in `docs/PAPER-VS-LEAN.md`, and the same numbering.
Equation and theorem numbers in `docs/PAPER-VS-LEAN.md` refer to it.

## Main results

The model is `H_Λ = H + Λ` of (1.2)–(1.4), complex Hermitian case: `H` has `D ≥ 2` independent `N × N` Wigner
blocks on the diagonal, with entry laws under Assumption 1 (all moments bounded by given constants), and `Λ`
places a deterministic `A` and `A*` on the cyclic off-diagonal blocks (for `D = 2`, `Λ = [[0, A], [A*, 0]]`). The
four statements are closed propositions: `MixStatement` and `LocalizedEvalStatement` are in
[`RBMTransitionEdge/MainDefs.lean`](RBMTransitionEdge/MainDefs.lean) with every definition they use, `MixEVStatement` and
`LocalizedEvecStatement` in [`RBMTransitionEdge/Main/Statements.lean`](RBMTransitionEdge/Main/Statements.lean) (further definitions in
`RBMTransitionEdge/Model/Basic.lean` and `RBMTransitionEdge/Model/Deterministic.lean`). The final theorem is

```lean
theorem main_theorems (hEI1 : LandonYauEdge) (hEI2 : ∀ C : ℕ → ℝ, EI2Hyp C) :
    MixStatement ∧ MixEVStatement ∧ LocalizedEvecStatement ∧ LocalizedEvalStatement
```

in [`RBMTransitionEdge/Main/Main.lean`](RBMTransitionEdge/Main/Main.lean) (namespace `RBMTransitionEdge`).

| Paper | Lean statement | Lean theorem | What it says |
|---|---|---|---|
| Theorem 2.1 | `MixStatement` | `mix` | Delocalized regime, eigenvectors: under `‖A‖ ≤ N^{−δ_A}` and (2.4), every unit eigenvector of `λ_k` puts mass `1/D + O(N^{−c})` on each block, with probability at least `1 − N^{−c}` (2.5). |
| Theorem 2.2 | `MixEVStatement` | `mixEV` | Delocalized regime, eigenvalues: the `n` largest (and smallest) eigenvalues, rescaled at the edge, have the law of those of a `DN × DN` GUE up to `N^{−c}`; from the external input `LandonYauEdge`. |
| Theorem 2.4 | `LocalizedEvecStatement` | `localized_evec` | Localized regime, eigenvectors: under (2.8), the eigenvector of `λ_k` concentrates on one block; from the external input `EI2Hyp`. |
| Theorem 2.5 | `LocalizedEvalStatement` | `localized_eval` | Localized regime, eigenvalues: the shift bounds (2.10), (2.11) and the comparison of the local correlation functions with those of `H` at the semicircle quantiles. |

Theorems 2.1 and 2.5 have no hypotheses other than their parameters. Each statement is in uniform form: the
constants are chosen before `N`, and the bound holds for every `N ≥ N₀`, every entry law with the given moment
constants, every admissible `A` and every `k`. `docs/PAPER-VS-LEAN.md` lists every difference between a Lean
statement and the printed one (for example the strict inequality in (2.10), and the correlation comparison of
Theorem 2.5 stated for the correlation functions `ρ^(n)`).

## External inputs

Two results from the literature are used without proof, each as an explicit hypothesis of one theorem and of
nothing else:

- `LandonYauEdge` ([`RBMTransitionEdge/Edge/Defs.lean`](RBMTransitionEdge/Edge/Defs.lean)): edge universality of Dyson Brownian
  motion for a regular initial matrix, from B. Landon and H.-T. Yau, *Edge statistics of Dyson Brownian motion*,
  [arXiv:1712.03881](https://arxiv.org/abs/1712.03881) (Definition 2.1, Theorem 2.2, Lemma 2.3). It enters only
  Theorem 2.2.
- `EI2Hyp` ([`RBMTransitionEdge/Localized/Repulsion.lean`](RBMTransitionEdge/Localized/Repulsion.lean)): the level repulsion (5.14)
  between the eigenvalues of two independent Wigner blocks, from L. Benigni and P. Lopatto, *Optimal
  delocalization for generalized Wigner matrices*, Adv. Math. 396 (2022), Lemmas B.1 and B.12, and P. Bourgade,
  *Extreme gaps between eigenvalues of Wigner matrices*, J. Eur. Math. Soc. 24 (2022), Proposition 2.10. It enters
  only Theorem 2.4.

`docs/PAPER-VS-LEAN.md` §5 states both and explains how they are used; compiled limit checks are at the end of
`RBMTransitionEdge/Edge/CVtG.lean` and `RBMTransitionEdge/Localized/Repulsion.lean`. Every other result that the paper quotes from
earlier work, including the local laws and the rigidity of Wigner matrices, is proved in the library.

## Axioms

Every declaration of the library depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`. There is
no `sorry` in the library and no declared `axiom`. `lake build` prints the axioms of `main_theorems` (the
`#print axioms` command at the end of `RBMTransitionEdge/Main/Main.lean`); `Challenge.lean` has two `sorry` by design
(see Palomar below).

## Build

The toolchain is `leanprover/lean4:v4.36.0-rc1` (file `lean-toolchain`) with Mathlib `v4.36.0-rc1`. Mathlib v4.36.0-rc1 lacks the smoothness of parametric integrals used in `RBMTransitionEdge/Edge/CountCalc.lean`; `RBMTransitionEdge/Tools/MathlibBackport.lean` copies it from Mathlib v4.37.0-rc1.

```
lake exe cache get
lake build
```

`lake exe cache get` downloads the compiled Mathlib; `lake build` builds the library, `Challenge.lean` and
`Solution.lean`.

The hypotheses of the theorems can be satisfied: compiled examples in `RBMTransitionEdge/Main/Statements.lean` and
`RBMTransitionEdge/Main/Main.lean` apply each main result at `D = 3`, `δ_A = ε_A = 1/100`, `k = 1`, with `A = N^{−1/10} I`
(delocalized regime) or `A = N^{−1/4} I` (localized regime) and an explicit entry law.

## Map of the library

Section numbers refer to the paper in `paper/`.

- `RBMTransitionEdge/Model/`, `RBMTransitionEdge/MainDefs.lean`: the model (1.2)–(1.4), Assumption 1, the deterministic objects of §2.2
  (the self-consistent equation (2.16), the density, the edges, the quantiles).
- `RBMTransitionEdge/Det/`: the deterministic analysis of §2.2 and Appendix A (Lemma A.1, the edges and their square-root
  behaviour, the expansions around the semicircle law, the shifts of the localized regime).
- `RBMTransitionEdge/Tools/`: resolvents, min–max and Weyl inequalities, eigenvalues along a line, the discrete Duhamel
  formula.
- `RBMTransitionEdge/Prob/`: complex cumulants and the cumulant expansion (Lemma 2.11), Gaussian integration by parts,
  stochastic domination (Definition 2.8), the identity (2.30), and the discrete grid of the Ornstein–Uhlenbeck flow
  with its martingale tools.
- `RBMTransitionEdge/LocalLaw/`: the local laws (Lemma 2.9 and its version for `H_t`), fluctuation averaging, rigidity of the
  eigenvalues.
- `RBMTransitionEdge/Flow/`: §3: the characteristic flow, the resolvent loops along the flow (Lemmas 3.3–3.12), the comparison
  lemma, and Theorem 2.1.
- `RBMTransitionEdge/Edge/`: §4: Lemmas 4.1–4.3 and Theorem 2.2.
- `RBMTransitionEdge/Localized/`, `RBMTransitionEdge/Localized/Expansion/`: §5: the local laws of the localized regime (Lemmas 5.2, 5.4),
  the expansion of §5.3 and Lemma 5.5, level repulsion, and Theorems 2.4 and 2.5.
- `RBMTransitionEdge/Main/`: the statements of the main theorems, their assembly, and the compiled examples.

## `docs/PAPER-VS-LEAN.md`

[`docs/PAPER-VS-LEAN.md`](docs/PAPER-VS-LEAN.md) compares the paper and the Lean proof in detail: what is proved,
every difference between the Lean statements and the printed ones, the corrections of the proofs, the external
inputs, and where the Lean proof takes a different route from the paper.

## License and authors

The code is released under the Apache License 2.0; see [`LICENSE`](LICENSE).

Paper: Jiaqi Fan, Bertrand Stone, Fan Yang and Jun Yin. Lean formalization: Jun Yin.

## Palomar

The repository is laid out for the [Palomar registry](https://palomar-registry.org/) of Lean-verified mathematics.
All source files use Lean's module system. [`RBMTransitionEdge/MainDefs.lean`](RBMTransitionEdge/MainDefs.lean) holds every
definition used by the statements of Theorems 2.1 and 2.5; [`Challenge.lean`](Challenge.lean) is the statement to
audit (it imports Mathlib only, repeats the definitions of `RBMTransitionEdge/MainDefs.lean` and states the two theorems;
Theorems 2.2 and 2.4, which have an external input as a hypothesis, are not in it), [`Solution.lean`](Solution.lean)
proves the two statements from the library, [`comparator.json`](comparator.json) names the compared theorems and
[`formalization.yaml`](formalization.yaml) holds the metadata. `lake build` also builds `Challenge.lean` (two
`sorry` warnings, by design) and `Solution.lean`. `python3 scripts/check-lean-sources.py` and
`./scripts/verify-comparator.sh` (Linux, needs `bwrap`) run the checks locally; submissions go to
<https://submit.palomar-registry.org/>.
