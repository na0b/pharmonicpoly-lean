module

public import PHarmonicPoly.TrigPolyLe

@[expose] public section

/-- The even part of a real trigonometric polynomial of degree at most `m` is a
polynomial of degree at most `m` evaluated at `cos t`. -/
theorem TrigPolyEvenPart {m : ℕ} {T : ℝ → ℝ} (hT : TrigPolyLe m T) :
    ∃ P : Polynomial ℝ, P.degree ≤ (m : ℕ) ∧
      ∀ t : ℝ, P.eval (Real.cos t) = (T t + T (-t)) / 2 := by
  obtain ⟨a, b, hrep⟩ := hT
  refine ⟨∑ k ∈ Finset.range (m + 1),
      Polynomial.C (a k) * Polynomial.Chebyshev.T ℝ (k : ℤ), ?_, ?_⟩
  · refine (Polynomial.degree_sum_le _ _).trans ?_
    refine Finset.sup_le (fun k hk => ?_)
    have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hTdeg : (Polynomial.Chebyshev.T ℝ (k : ℤ)).degree = (k : ℕ) := by
      rw [Polynomial.Chebyshev.degree_T]; simp
    refine (Polynomial.degree_mul_le _ _).trans ?_
    rw [hTdeg]
    have hC : (Polynomial.C (a k)).degree ≤ (0 : WithBot ℕ) := Polynomial.degree_C_le
    calc (Polynomial.C (a k)).degree + ((k : ℕ) : WithBot ℕ)
        ≤ (0 : WithBot ℕ) + ((k : ℕ) : WithBot ℕ) := by gcongr
      _ = ((k : ℕ) : WithBot ℕ) := by simp
      _ ≤ ((m : ℕ) : WithBot ℕ) := by exact_mod_cast hk'
  · intro t
    have hL : ∀ k ∈ Finset.range (m + 1),
        Polynomial.eval (Real.cos t)
            (Polynomial.C (a k) * Polynomial.Chebyshev.T ℝ (k : ℤ))
          = a k * Real.cos ((k : ℝ) * t) := by
      intro k _
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.Chebyshev.T_real_cos]
      norm_num
    have key : ∀ k ∈ Finset.range (m + 1),
        a k * Real.cos ((k : ℝ) * t)
          = ((a k * Real.cos ((k : ℝ) * t) + b k * Real.sin ((k : ℝ) * t))
             + (a k * Real.cos ((k : ℝ) * -t) + b k * Real.sin ((k : ℝ) * -t))) / 2 := by
      intro k _
      have h1 : ((k : ℝ) * -t) = -((k : ℝ) * t) := by ring
      rw [h1, Real.cos_neg, Real.sin_neg]
      ring
    rw [Polynomial.eval_finsetSum, Finset.sum_congr rfl hL, hrep t, hrep (-t),
      ← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl key
