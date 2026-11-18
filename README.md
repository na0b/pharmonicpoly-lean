# p-harmonic homogeneous polynomials, in Lean 4

This repository contains a Lean 4 formalization, built on [Mathlib](https://github.com/leanprover-community/mathlib4), of Theorem 1.1 and Lemma 2.1 of

> Juan J. Manfredi and Aelson Sobral,
> *p-harmonic homogeneous polynomials*, https://arxiv.org/abs/2611.23136, 2026.

Both results are stated and proved, together with everything their proofs use. The development contains no `sorry` and no axioms: every result depends only on the three standard axioms of Lean (`propext`, `Classical.choice`, `Quot.sound`). The formalization follows the paper's argument; no deviation from it was needed. The Bernstein–Szegő inequality, which the paper cites and Mathlib does not contain, is proved here.

<!-- TODO: remove once both authors have read the Lean statements below against the paper. -->

## Results

| Paper | Lean declaration | File |
|---|---|---|
| Theorem 1.1, polynomial solutions of E<sub>p</sub>(u) = 0 are affine | `MainTheorem` (`PHarmonicPoly.main_theorem` in `Challenge.lean`) | [`MainTheorem.lean`](PHarmonicPoly/MainTheorem.lean) |
| Lemma 2.1, the deficit estimate at the first Chebyshev node | `DeficitBound` (`PHarmonicPoly.deficit_bound`) | [`DeficitBound.lean`](PHarmonicPoly/DeficitBound.lean) |

## The main theorem

`EpOp p u` is the operator E<sub>p</sub>(u) = |Du|²Δu + (p − 2)⟨D²u Du, Du⟩ of the paper, computed with Mathlib's gradient, Laplacian and second Fréchet derivative on `EuclideanSpace ℝ (Fin n)`. Theorem 1.1 says that for n ≥ 3 and p ≥ n − 1/13, a real polynomial in n variables whose E<sub>p</sub> vanishes everywhere is affine:

```lean
theorem MainTheorem {n : ℕ} (hn : 3 ≤ n) {p : ℝ} (hp : (n : ℝ) - 1 / 13 ≤ p)
    (P : MvPolynomial (Fin n) ℝ)
    (hE : ∀ x : EuclideanSpace ℝ (Fin n),
      EpOp p (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) x = 0) :
    ∃ (w : EuclideanSpace ℝ (Fin n)) (c : ℝ), ∀ x : EuclideanSpace ℝ (Fin n),
      MvPolynomial.eval (fun i => x i) P = inner ℝ w x + c
```

The paper's Theorem 1.1 ends with "In particular, every polynomial p-harmonic function on ℝⁿ is affine." That last sentence is **not** formalized. It passes from weak solutions of Δ<sub>p</sub>u = 0 to E<sub>p</sub>(u) ≡ 0 through regularity theory (a weak solution is classical where Du ≠ 0) that the paper cites rather than proves, and that is not in Mathlib.

Lemma 2.1, with `TrigPolyLe m T` meaning that T is a real trigonometric polynomial of degree at most m:

```lean
theorem DeficitBound {m : ℕ} (hm : 2 ≤ m) {T : ℝ → ℝ} (hT : TrigPolyLe m T)
    (hbd : ∀ t : ℝ, |T t| ≤ 1) (h0 : T 0 = 1) :
    (0 ≤ 1 + T (Real.pi / m) ∧ 0 ≤ 1 + T (-(Real.pi / m)))
      ∧ (1 + T (Real.pi / m)
            ≤ ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) * (1 - Real.cos (Real.pi / m))
          ∧ 1 + T (-(Real.pi / m))
            ≤ ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) * (1 - Real.cos (Real.pi / m)))
      ∧ ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) * (1 - Real.cos (Real.pi / m))
          ≤ Real.pi ^ 2 * ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) / (2 * (m : ℝ) ^ 2)
```

## What is and is not checked by Lean

The Lean kernel checks that the two theorems above follow from their definitions and Mathlib, using only the three standard axioms. Lean does not check that the definitions (`EpOp`, `TrigPolyLe`) and the two statements say what the paper says. That was reviewed during the formalization (see below), but readers who rely on the result should compare the statements and the definitions they use against the paper themselves. The definitions are listed in Section 1 of the blueprint.

## Blueprint

The directory [`blueprint/`](blueprint) contains a natural-language statement and a detailed proof for every Lean declaration, cross-referenced to the paper and to each other. They are collected, in dependency order, in [`blueprint/blueprint.pdf`](blueprint/blueprint.pdf). To rebuild it, run `pdflatex blueprint.tex` three times in that directory.

## Building and checking

Install Lean with [elan](https://github.com/leanprover/elan), then:

```sh
git clone <repository URL> pharmonicpoly-lean
cd pharmonicpoly-lean
lake exe cache get        # download prebuilt Mathlib
lake build
lake env lean Axioms.lean # print the axioms used by each main result
```

The project is pinned to Lean `v4.35.0-rc2` and the matching Mathlib release `v4.35.0-rc2`, and every file uses Lean's module system. Continuous integration rebuilds the project and checks the axioms on every push.

## Palomar

The repository is laid out for the [Palomar](https://palomar-registry.org/) registry. [`Challenge.lean`](Challenge.lean) is the statement of record: it imports only Mathlib, restates the definitions the main results use, and states the two results with `sorry`. [`Solution.lean`](Solution.lean) proves the same two statements from the development. [`comparator.json`](comparator.json) tells [Comparator](https://github.com/leanprover/comparator) to check that the two agree and that only the three standard axioms are used, and [`formalization.yaml`](formalization.yaml) records provenance, authorship, automation and review. To run the check locally (Linux, needs `bwrap`):

```sh
./scripts/verify-comparator.sh
ruby scripts/validate-formalization.rb
```

The definitions in `Challenge.lean` are copied verbatim into [`PHarmonicPoly/Defs.lean`](PHarmonicPoly/Defs.lean), which the development uses; keeping the two textually identical is what makes them elaborate to the same terms.

## Layout

```
PHarmonicPoly.lean         root module, imports the main results
PHarmonicPoly/             one file per lemma or theorem; the definitions used in the main
                           statements are in PHarmonicPoly/Defs.lean
Challenge.lean             Palomar statement of record (Mathlib imports only)
Solution.lean              proofs of the Challenge statements
comparator.json            Comparator configuration
formalization.yaml         Palomar metadata
Axioms.lean                #print axioms for the main results
blueprint/blueprint.tex    natural-language companion (inputs blueprint/nodes/*.tex)
```

## How this formalization was produced

The formalization was produced with [Trellis](https://github.com/wpegden/trellis), an AI-assisted formalization pipeline; the Lean proofs and the blueprint were written by AI agents (Claude, by Anthropic) under the Trellis protocol. Each node was reviewed automatically for soundness of its natural-language proof, for faithfulness to the paper, and for agreement between its Lean statement and its natural-language statement. The Lean kernel checks every proof.

## Citation

Please cite the paper; see [`CITATION.cff`](CITATION.cff).

## License

Apache License 2.0, the license of Mathlib. See [`LICENSE`](LICENSE).
