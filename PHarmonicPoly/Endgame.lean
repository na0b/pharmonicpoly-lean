module

public import PHarmonicPoly.CauchySchwarzPi

@[expose] public section

open Real
/-- Paper, Section 3, the closing contradiction: under the constraints reached
there, `s + |b|/π - (2-δ)a + (1-a)^2/(2a)` is strictly negative. -/
theorem Endgame (a b s δ : ℝ)
    (_hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 13)
    (ha : 8 / 13 < a) (ha1 : a ≤ 1)
    (hs : 0 ≤ s) (hsq : s ^ 2 + b ^ 2 = 1) :
    s + |b| / Real.pi - (2 - δ) * a + (1 - a) ^ 2 / (2 * a) < 0 := by
  have ha0 : (0:ℝ) < a := by linarith
  have h1 : s + |b| / π < 17 / 16 := CauchySchwarzPi b s hs hsq
  have h2 : (200 : ℝ) / 169 < (2 - δ) * a := by nlinarith
  have h3 : (1 - a) ^ 2 / (2 * a) < 25 / 208 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have : (17:ℝ)/16 - 200/169 + 25/208 = -(1/1352) := by norm_num
  linarith
