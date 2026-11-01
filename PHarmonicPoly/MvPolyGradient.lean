module

public import PHarmonicPoly.MvPolyFDeriv

@[expose] public section

open MvPolynomial ContinuousLinearMap InnerProductSpace
/-- The gradient of a polynomial function on `EuclideanSpace ℝ (Fin n)` is the
vector of its partial derivatives. -/
theorem MvPolyGradient {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) x
      = WithLp.toLp 2 (fun i => MvPolynomial.eval (fun j => x j) (pderiv i P)) := by
  have hcomp : (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P)
      = (fun v : Fin n → ℝ => MvPolynomial.eval v P) ∘ (EuclideanSpace.equiv (Fin n) ℝ) := rfl
  have hF : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P)
      ((∑ i, (MvPolynomial.eval (fun j => x j) (pderiv i P)) •
          (proj i : (Fin n → ℝ) →L[ℝ] ℝ)).comp
        (EuclideanSpace.equiv (Fin n) ℝ : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℝ))) x := by
    rw [hcomp]
    exact HasFDerivAt.comp x (MvPolyFDeriv P (fun j => x j))
      (EuclideanSpace.equiv (Fin n) ℝ).hasFDerivAt
  refine HasGradientAt.gradient ?_
  rw [hasGradientAt_iff_hasFDerivAt]
  refine hF.congr_fderiv ?_
  ext w
  rw [toDual_apply_apply, PiLp.inner_apply]
  simp [mul_comm]
