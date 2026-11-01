module

public import PHarmonicPoly.Preamble

@[expose] public section

open MvPolynomial
/-- The algebraic avatar of the operator `E_p`: the polynomial obtained by
substituting formal partial derivatives of `P` into eq:E. -/
noncomputable def EpAlg {n : ℕ} (p : ℝ) (P : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  (∑ i, (pderiv i P) ^ 2) * (∑ i, pderiv i (pderiv i P))
    + C (p - 2) * ∑ i, ∑ j, pderiv i (pderiv j P) * pderiv i P * pderiv j P
