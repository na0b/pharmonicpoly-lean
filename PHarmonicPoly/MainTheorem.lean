module

public import PHarmonicPoly.HomogeneousCase
public import PHarmonicPoly.TopComponent
public import PHarmonicPoly.TopComponentNeZero
public import PHarmonicPoly.AffineOfTotalDegreeLeOne
public import PHarmonicPoly.EpOpEvalPoly

@[expose] public section

open MvPolynomial
/-- The paper's Theorem 1.1: for `n ≥ 3` and `p ≥ n - 1/13`, every real
polynomial on `ℝ^n` annihilated by `E_p` is affine. -/
theorem MainTheorem {n : ℕ} (hn : 3 ≤ n) {p : ℝ} (hp : (n : ℝ) - 1 / 13 ≤ p)
    (P : MvPolynomial (Fin n) ℝ)
    (hE : ∀ x : EuclideanSpace ℝ (Fin n),
      EpOp p (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) x = 0) :
    ∃ (w : EuclideanSpace ℝ (Fin n)) (c : ℝ), ∀ x : EuclideanSpace ℝ (Fin n),
      MvPolynomial.eval (fun i => x i) P = inner ℝ w x + c := by
  have halg : EpAlg p P = 0 := by
    refine MvPolynomial.funext (fun v => ?_)
    have hx := hE (WithLp.toLp 2 v)
    rw [EpOpEvalPoly p P (WithLp.toLp 2 v)] at hx
    simpa using hx
  rcases le_or_gt P.totalDegree 1 with hd | hd
  · exact AffineOfTotalDegreeLeOne hd
  · exfalso
    have hP : P ≠ 0 := by
      intro h
      rw [h] at hd
      simp at hd
    exact HomogeneousCase hn hd hp (TopComponentNeZero hP)
      (MvPolynomial.homogeneousComponent_isHomogeneous _ _) (TopComponent p hd halg)
