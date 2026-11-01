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
# Definitions used in the statements of the main results

This file is kept textually identical to the definitions section of `Challenge.lean`
(same Mathlib imports, same declarations in the same order), so that both elaborate to the
same terms, as Comparator requires.
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
