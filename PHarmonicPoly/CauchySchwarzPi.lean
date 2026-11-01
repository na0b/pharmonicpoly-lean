module

public import PHarmonicPoly.Preamble

@[expose] public section

open Real
/-- Paper, Section 3: Cauchy-Schwarz together with `π > 3` gives
`s + |b|/π < 17/16` whenever `0 ≤ s` and `s^2 + b^2 = 1`. -/
theorem CauchySchwarzPi (b s : ℝ) (hs : 0 ≤ s) (hsq : s ^ 2 + b ^ 2 = 1) :
    s + |b| / Real.pi < 17 / 16 := by
  have hp : (0:ℝ) < π := by have := pi_gt_three; linarith
  set B := |b| with hBdef
  have hB : 0 ≤ B := abs_nonneg b
  have hB2 : B ^ 2 = b ^ 2 := sq_abs b
  have h1 : (s + B / π) ^ 2 ≤ 1 + 1 / π ^ 2 := by
    have hid : (1 + 1 / π ^ 2) - (s + B / π) ^ 2 = (B * π - s) ^ 2 / π ^ 2 := by
      rw [← hsq, ← hB2]; field_simp; ring
    nlinarith [div_nonneg (sq_nonneg (B * π - s)) (sq_nonneg π), hid]
  have h2 : 1 + 1 / π ^ 2 < (17 / 16 : ℝ) ^ 2 := by
    have h3 : (3:ℝ) < π := pi_gt_three
    have : (1 : ℝ) / π ^ 2 < 1 / 9 :=
      div_lt_div_of_pos_left one_pos (by norm_num) (by nlinarith)
    linarith
  have hsum : 0 ≤ s + B / π := add_nonneg hs (div_nonneg hB hp.le)
  nlinarith [h1, h2, hsum]
