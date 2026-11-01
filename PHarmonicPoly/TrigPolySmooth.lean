module

public import PHarmonicPoly.TrigPolyLe

@[expose] public section

open scoped ContDiff
/-- A real trigonometric polynomial of degree at most `m` is real-analytic on
`ℝ` (the smoothness exponent `ω` is analyticity). -/
theorem TrigPolySmooth {m : ℕ} {T : ℝ → ℝ} (hT : TrigPolyLe m T) :
    ContDiff ℝ ω T := by
  obtain ⟨a, b, hrep⟩ := hT
  have hfun : T = fun t => ∑ k ∈ Finset.range (m + 1),
      (a k * Real.cos (k * t) + b k * Real.sin (k * t)) := funext hrep
  rw [hfun]
  refine ContDiff.sum (fun k _ => ?_)
  have hlin : ContDiff ℝ ω (fun t : ℝ => (k : ℝ) * t) :=
    contDiff_const.mul contDiff_id
  exact (contDiff_const.mul (Real.contDiff_cos.comp hlin)).add
    (contDiff_const.mul (Real.contDiff_sin.comp hlin))
