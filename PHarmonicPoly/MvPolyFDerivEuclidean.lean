module

public import PHarmonicPoly.MvPolyFDeriv

@[expose] public section

open MvPolynomial
/-- The `pderiv`-to-`fderiv` bridge on `EuclideanSpace ℝ (Fin n)`: the polynomial
function `z ↦ Q z` is Frechet differentiable at every point `y`, with derivative
the continuous linear form `w ↦ ∑ i, (pderiv i Q)(y) * w i`. This is
`MvPolyFDeriv` transported across the isometric linear equivalence
`EuclideanSpace.equiv`, which is the identity on coordinates. -/
theorem MvPolyFDerivEuclidean {n : ℕ} (Q : MvPolynomial (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => z i) Q)
      (∑ i, (MvPolynomial.eval (fun j => y j) (pderiv i Q)) •
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) y := by
  have hcomp : (fun z : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => z i) Q)
      = (fun u : Fin n → ℝ => MvPolynomial.eval u Q) ∘
        (EuclideanSpace.equiv (Fin n) ℝ) := rfl
  rw [hcomp]
  refine (HasFDerivAt.comp y (MvPolyFDeriv Q (fun j => y j))
    (EuclideanSpace.equiv (Fin n) ℝ).hasFDerivAt).congr_fderiv ?_
  ext z
  simp
