module

public import PHarmonicPoly.MvPolyGradient
public import PHarmonicPoly.MvPolyFDerivEuclidean

@[expose] public section

open MvPolynomial
/-- The second derivative of a polynomial function on `EuclideanSpace ℝ (Fin n)`,
as a bilinear form, is given by the matrix of second partial derivatives. -/
theorem MvPolyHessian {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (x v w : EuclideanSpace ℝ (Fin n)) :
    iteratedFDeriv ℝ 2
        (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) x ![v, w]
      = ∑ i, ∑ j, v i * w j * MvPolynomial.eval (fun k => x k) (pderiv i (pderiv j P)) := by
  have hfd : fderiv ℝ
      (fun z : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => z i) P)
      = fun y : EuclideanSpace ℝ (Fin n) =>
        ∑ i, (MvPolynomial.eval (fun j => y j) (pderiv i P)) •
          (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := by
    funext y
    exact (MvPolyFDerivEuclidean P y).fderiv
  have hG : HasFDerivAt
      (fun y : EuclideanSpace ℝ (Fin n) =>
        ∑ i, (MvPolynomial.eval (fun j => y j) (pderiv i P)) •
          (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
      (∑ i, (∑ j, (MvPolynomial.eval (fun k => x k) (pderiv j (pderiv i P))) •
          (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)).smulRight
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) x := by
    have hterm : ∀ i : Fin n, HasFDerivAt
        (fun y : EuclideanSpace ℝ (Fin n) =>
          (MvPolynomial.eval (fun j => y j) (pderiv i P)) •
            (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
        ((∑ j, (MvPolynomial.eval (fun k => x k) (pderiv j (pderiv i P))) •
            (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)).smulRight
          (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) x :=
      fun i => (MvPolyFDerivEuclidean (pderiv i P) x).smul_const
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    have hfe : (∑ i, fun y : EuclideanSpace ℝ (Fin n) =>
          (MvPolynomial.eval (fun j => y j) (pderiv i P)) •
            (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
        = fun y : EuclideanSpace ℝ (Fin n) =>
          ∑ i, (MvPolynomial.eval (fun j => y j) (pderiv i P)) •
            (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := by
      funext y
      simp
    exact hfe ▸ HasFDerivAt.sum (fun i _ => hterm i)
  rw [iteratedFDeriv_two_apply, hfd, hG.fderiv]
  simp
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
