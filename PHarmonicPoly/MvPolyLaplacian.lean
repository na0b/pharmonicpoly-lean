module

public import PHarmonicPoly.MvPolyHessian

@[expose] public section

open MvPolynomial
/-- The Laplacian of a polynomial function on `EuclideanSpace ℝ (Fin n)` is the
sum of its pure second partial derivatives. -/
theorem MvPolyLaplacian {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Laplacian.laplacian
        (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) x
      = ∑ i, MvPolynomial.eval (fun j => x j) (pderiv i (pderiv i P)) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin n) ℝ)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [MvPolyHessian P x _ _]
  rw [Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj; simp [hj]
    · intro h; simp at h
  · intro i _ hi
    refine Finset.sum_eq_zero (fun j _ => ?_)
    simp [hi]
  · intro h; simp at h
