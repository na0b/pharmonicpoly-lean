module

public import PHarmonicPoly.Preamble

@[expose] public section

open Real
/-- Paper, Section 3: the `k = n-2` absorption step, with `p-1 = k+1-δ` and
`p-2 = k-δ` already substituted. -/
theorem AbsorbK (k δ a b s A : ℝ) (hk : 1 ≤ k) (hδ0 : 0 ≤ δ) (hA : 0 ≤ A)
    (hsa : (1 - δ) * a ≤ s) :
    s - (k + 1 - δ) * a + k * (|b| / Real.pi) + (k - δ) * A
      ≤ k * (s + |b| / Real.pi - (2 - δ) * a + A) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hk) (sub_nonneg.2 hsa), mul_nonneg hδ0 hA]
