module

-- Preamble: shared imports for all files.
-- Mathlib modules only; never `import Mathlib`.

-- Calculus on real inner product spaces: gradient, iterated Frechet
-- derivatives, and the Laplacian computed from an arbitrary orthonormal basis.
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

-- Trigonometric functions: derivatives, inverses, elementary bounds, pi bounds.
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds

-- Chebyshev polynomials of the first kind, their extremal nodes, and
-- Lagrange interpolation (including the iterated-derivative formula).
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.LinearAlgebra.Lagrange

-- Smoothness of polynomial evaluation (Polynomial.contDiff_aeval).
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
-- Derivatives of polynomial evaluation (Polynomial.hasDerivAt); no longer imported transitively.
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

-- Multivariate polynomials: partial derivatives, homogeneity, Euler identity,
-- analyticity of polynomial evaluation.
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Analysis.Analytic.Polynomial

-- Symmetry of the second Frechet derivative (pm-0014): PolarInequality needs
-- the transposed Hessian entry, which FrameHessian does not supply.
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

-- Tactics actually used by the tablet's Lean proofs.
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.GCongr
-- linear_combination: needed by TraceIdentity, TopComponent and TrigPolyMul.
public import Mathlib.Tactic.LinearCombination
-- match_scalars: vector identities in TangentialLaplacianBound and PolarInequality.
public import Mathlib.Tactic.Module

@[expose] public section
