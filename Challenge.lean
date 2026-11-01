module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module

/-!
# p-harmonic homogeneous polynomials

Statement of record for a Lean 4 formalization of

> Juan J. Manfredi and Aelson Sobral, *p-harmonic homogeneous polynomials*.

Two results of the paper are stated below.

* `PHarmonicPoly.main_theorem` (Theorem 1.1): for `n ≥ 3` and `p ≥ n - 1/13`, every real
  polynomial `u` on `ℝⁿ` with `E_p(u) = |Du|² Δu + (p - 2) ⟨D²u Du, Du⟩ ≡ 0` is affine.
* `PHarmonicPoly.deficit_bound` (Lemma 2.1, the deficit estimate at the first Chebyshev node):
  for a real trigonometric polynomial `T` of degree at most `m ≥ 2` with `‖T‖∞ ≤ 1` and
  `T(0) = 1`, and `d = m² + T''(0)`, one has `0 ≤ 1 + T(±π/m) ≤ d (1 - cos(π/m)) ≤ π² d / (2 m²)`.

Theorem 1.1 of the paper ends with "In particular, every polynomial p-harmonic function on ℝⁿ
is affine." That corollary is not formalized: it passes from weak solutions of `Δ_p u = 0` to
`E_p(u) ≡ 0` through regularity theory that the paper cites rather than proves, and which is
not in Mathlib. What is formalized is the statement about `E_p` that the paper proves.

A polynomial is an element of `MvPolynomial (Fin n) ℝ`, evaluated on `EuclideanSpace ℝ (Fin n)`.
`E_p` is computed with Mathlib's `gradient`, `Laplacian.laplacian` and `iteratedFDeriv`.
Only Mathlib is imported; the definitions below are copied verbatim from the proof
development, and Comparator checks that they agree with it.
-/

@[expose] public section

section EpOp

/-- The operator `E_p` of the paper, in non-divergence form:
`E_p(u) = |Du|^2 Δu + (p-2) ⟨D²u Du, Du⟩` on `EuclideanSpace ℝ (Fin n)`. -/
noncomputable def EpOp {n : ℕ} (p : ℝ) (u : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => ‖gradient u x‖ ^ 2 * Laplacian.laplacian u x
    + (p - 2) * iteratedFDeriv ℝ 2 u x ![gradient u x, gradient u x]

end EpOp

section TrigPolyLe

/-- `TrigPolyLe m T` says that `T : ℝ → ℝ` is a real trigonometric polynomial of
degree at most `m`: there are real coefficient sequences `a` and `b` with
`T t = ∑_{k=0}^{m} (a k * cos (k t) + b k * sin (k t))` for every `t`. -/
def TrigPolyLe (m : ℕ) (T : ℝ → ℝ) : Prop :=
  ∃ a b : ℕ → ℝ, ∀ t : ℝ,
    T t = ∑ k ∈ Finset.range (m + 1), (a k * Real.cos (k * t) + b k * Real.sin (k * t))

end TrigPolyLe

namespace PHarmonicPoly

section main_theorem
open MvPolynomial

/-- **Theorem 1.1.** Let `n ≥ 3` and `p ≥ n - 1/13`. Every real polynomial `u` on `ℝⁿ`
with `E_p(u) = |Du|² Δu + (p - 2) ⟨D²u Du, Du⟩ = 0` everywhere is affine. -/
theorem main_theorem {n : ℕ} (hn : 3 ≤ n) {p : ℝ} (hp : (n : ℝ) - 1 / 13 ≤ p)
    (P : MvPolynomial (Fin n) ℝ)
    (hE : ∀ x : EuclideanSpace ℝ (Fin n),
      EpOp p (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) x = 0) :
    ∃ (w : EuclideanSpace ℝ (Fin n)) (c : ℝ), ∀ x : EuclideanSpace ℝ (Fin n),
      MvPolynomial.eval (fun i => x i) P = inner ℝ w x + c := by
  sorry

end main_theorem

section deficit_bound

/-- **Lemma 2.1 (deficit estimate).** Let `m ≥ 2` and let `T` be a real trigonometric
polynomial of degree at most `m` with `‖T‖∞ ≤ 1` and `T(0) = 1`. With `d = m² + T''(0)`,
`0 ≤ 1 + T(±π/m) ≤ d (1 - cos(π/m)) ≤ π² d / (2 m²)`. -/
theorem deficit_bound {m : ℕ} (hm : 2 ≤ m) {T : ℝ → ℝ} (hT : TrigPolyLe m T)
    (hbd : ∀ t : ℝ, |T t| ≤ 1) (h0 : T 0 = 1) :
    (0 ≤ 1 + T (Real.pi / m) ∧ 0 ≤ 1 + T (-(Real.pi / m)))
      ∧ (1 + T (Real.pi / m)
            ≤ ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) * (1 - Real.cos (Real.pi / m))
          ∧ 1 + T (-(Real.pi / m))
            ≤ ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) * (1 - Real.cos (Real.pi / m)))
      ∧ ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) * (1 - Real.cos (Real.pi / m))
          ≤ Real.pi ^ 2 * ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) / (2 * (m : ℝ) ^ 2) := by
  sorry

end deficit_bound

end PHarmonicPoly
