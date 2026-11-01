module

public import PHarmonicPoly.BernsteinSzego
public import PHarmonicPoly.TrigPolyDeriv
public import PHarmonicPoly.TrigPolyLinComb
public import PHarmonicPoly.TrigPolySmooth

@[expose] public section

/-- The second form of the paper's eq:bernstein, obtained by applying the
Bernstein-Szego inequality to `T'/m`: `(T')^2/m^2 + (T'')^2/m^4 ≤ 1`. -/
theorem BernsteinSzegoSecond {m : ℕ} (hm : 1 ≤ m) {T : ℝ → ℝ}
    (hT : TrigPolyLe m T) (hbd : ∀ t : ℝ, |T t| ≤ 1) :
    ∀ t : ℝ,
      (deriv T t) ^ 2 / (m : ℝ) ^ 2
        + (iteratedDeriv 2 T t) ^ 2 / (m : ℝ) ^ 4 ≤ 1 := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hm0
  have hT' : TrigPolyLe m (deriv T) := TrigPolyDeriv hT
  -- `U = T' / m` is again a trigonometric polynomial of degree at most `m`
  have hU : TrigPolyLe m (fun t => deriv T t / (m : ℝ)) := by
    obtain ⟨a, b, h⟩ := TrigPolyLinComb hT' hT' (1 / (m : ℝ)) 0
    refine ⟨a, b, fun t => ?_⟩
    have ht := h t
    simp only [zero_mul, add_zero] at ht
    rw [← ht]
    field_simp
  -- the first inequality bounds `U` by 1 in absolute value
  have hfirst := BernsteinSzego hm hT hbd
  have hUbd : ∀ t : ℝ, |deriv T t / (m : ℝ)| ≤ 1 := by
    intro t
    have h1 := hfirst t
    have hsq : (deriv T t / (m : ℝ)) ^ 2 ≤ 1 := by
      have : deriv T t ^ 2 / (m : ℝ) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (T t)]
      calc (deriv T t / (m : ℝ)) ^ 2 = deriv T t ^ 2 / (m : ℝ) ^ 2 := by
            rw [div_pow]
        _ ≤ 1 := this
    nlinarith [sq_abs (deriv T t / (m : ℝ)), abs_nonneg (deriv T t / (m : ℝ)), hsq]
  -- the derivative of `U` is `T'' / m`
  have hsmooth : ContDiff ℝ ⊤ (deriv T) := TrigPolySmooth hT'
  have hdU : ∀ t : ℝ, deriv (fun s : ℝ => deriv T s / (m : ℝ)) t
      = iteratedDeriv 2 T t / (m : ℝ) := by
    intro t
    rw [deriv_div_const, show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  intro t
  have hsecond := BernsteinSzego hm hU hUbd t
  rw [hdU t] at hsecond
  have hexp : (deriv T t / (m : ℝ)) ^ 2
      + (iteratedDeriv 2 T t / (m : ℝ)) ^ 2 / (m : ℝ) ^ 2
      = deriv T t ^ 2 / (m : ℝ) ^ 2 + iteratedDeriv 2 T t ^ 2 / (m : ℝ) ^ 4 := by
    field_simp
  linarith [hexp ▸ hsecond]
