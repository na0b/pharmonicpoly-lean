module

public import PHarmonicPoly.Preamble

@[expose] public section

/-- Paper, Section 3: `0 ≤ b^2 (s-a)/q ≤ (1-a)^2/(2a)`, where `q = a^2 + b^2`
and `s^2 + b^2 = 1`. -/
theorem ABound (a b s q : ℝ) (ha : 0 < a) (hs : a ≤ s) (hq : q = a ^ 2 + b ^ 2)
    (hsq : s ^ 2 + b ^ 2 = 1) :
    0 ≤ b ^ 2 * (s - a) / q ∧ b ^ 2 * (s - a) / q ≤ (1 - a) ^ 2 / (2 * a) := by
  have hq0 : 0 < q := by nlinarith [sq_nonneg b]
  refine ⟨div_nonneg (mul_nonneg (sq_nonneg b) (by linarith)) hq0.le, ?_⟩
  rw [div_le_div_iff₀ hq0 (by positivity)]
  nlinarith [sq_nonneg (q - a), sq_nonneg (s - a), sq_nonneg b,
    mul_nonneg ha.le (sq_nonneg (s - a)),
    mul_nonneg (sub_nonneg.2 hs) (sq_nonneg b), sq_nonneg (a * b),
    sq_nonneg (s * a - a * a)]
