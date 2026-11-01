module

public import PHarmonicPoly.MvPolyGradient

@[expose] public section

open MvPolynomial
/-- Pairing the gradient of a polynomial function against a vector, in partial
derivative coordinates, in both the inner-product and the linear-form form. -/
theorem MvPolyGradientInner {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (y z : EuclideanSpace ℝ (Fin n)) :
    (inner ℝ (gradient (fun q : EuclideanSpace ℝ (Fin n) =>
          MvPolynomial.eval (fun i => q i) P) y) z : ℝ)
        = ∑ i, MvPolynomial.eval (fun j => y j) (pderiv i P) * z i
      ∧ (∑ i, (MvPolynomial.eval (fun j => y j) (pderiv i P)) •
          (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) z
        = (inner ℝ (gradient (fun q : EuclideanSpace ℝ (Fin n) =>
            MvPolynomial.eval (fun i => q i) P) y) z : ℝ) := by
  have h1 : (inner ℝ (gradient (fun q : EuclideanSpace ℝ (Fin n) =>
      MvPolynomial.eval (fun i => q i) P) y) z : ℝ)
      = ∑ i, MvPolynomial.eval (fun j => y j) (pderiv i P) * z i := by
    rw [MvPolyGradient P y, PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  refine ⟨h1, ?_⟩
  rw [h1]
  simp
