module

public import PHarmonicPoly.Preamble

@[expose] public section

/-- A polynomial function on `EuclideanSpace ℝ (Fin n)` is `C^k` for every
smoothness exponent `k` (so in particular real-analytic). -/
theorem MvPolyContDiff {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (k : WithTop ℕ∞) :
    ContDiff ℝ k
      (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) P) := by
  have hA : AnalyticOnNhd ℝ (fun v : Fin n → ℝ => MvPolynomial.eval v P) Set.univ :=
    AnalyticOnNhd.eval_mvPolynomial P
  have h1 : ContDiff ℝ k (fun v : Fin n → ℝ => MvPolynomial.eval v P) := by
    rw [← contDiffOn_univ]; exact hA.contDiffOn_of_completeSpace
  exact h1.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff
