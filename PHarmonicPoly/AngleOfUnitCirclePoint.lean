module

public import PHarmonicPoly.Preamble

@[expose] public section

/-- The unit-circle angle parametrization: every point `(x, y)` with
`x ^ 2 + y ^ 2 = 1` is `(cos α, sin α)` for some real angle `α`. -/
theorem AngleOfUnitCirclePoint (x y : ℝ) (hxy : x ^ 2 + y ^ 2 = 1) :
    ∃ α : ℝ, Real.cos α = x ∧ Real.sin α = y := by
  have hx1 : -1 ≤ x := by nlinarith [sq_nonneg y, sq_nonneg (x + 1)]
  have hx2 : x ≤ 1 := by nlinarith [sq_nonneg y, sq_nonneg (x - 1)]
  rcases le_or_gt 0 y with hy | hy
  · refine ⟨Real.arccos x, Real.cos_arccos hx1 hx2, ?_⟩
    rw [Real.sin_arccos, show (1 : ℝ) - x ^ 2 = y ^ 2 by linarith]
    exact Real.sqrt_sq hy
  · refine ⟨-Real.arccos x, by rw [Real.cos_neg]; exact Real.cos_arccos hx1 hx2, ?_⟩
    rw [Real.sin_neg, Real.sin_arccos, show (1 : ℝ) - x ^ 2 = y ^ 2 by linarith,
      Real.sqrt_sq_eq_abs, abs_of_neg hy]
    ring
