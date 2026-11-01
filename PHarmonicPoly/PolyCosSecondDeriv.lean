module

public import PHarmonicPoly.Preamble

@[expose] public section

/-- For `P : ℝ[X]` and `G t = P.eval (cos t)`, one has `G'' 0 = -P'(1)`. -/
theorem PolyCosSecondDeriv (P : Polynomial ℝ) :
    iteratedDeriv 2 (fun t : ℝ => P.eval (Real.cos t)) 0
      = -(Polynomial.derivative P).eval 1 := by
  have hd1 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Polynomial.eval (Real.cos s) P)
      (-(Real.sin t) * Polynomial.eval (Real.cos t) (Polynomial.derivative P)) t := by
    intro t
    have h := (P.hasDerivAt (Real.cos t)).comp t (Real.hasDerivAt_cos t)
    have hval : Polynomial.eval (Real.cos t) (Polynomial.derivative P) * -Real.sin t
        = -(Real.sin t) * Polynomial.eval (Real.cos t) (Polynomial.derivative P) := by ring
    exact hval ▸ h
  have hG1 : deriv (fun s : ℝ => Polynomial.eval (Real.cos s) P)
      = fun t : ℝ => -(Real.sin t) * Polynomial.eval (Real.cos t) (Polynomial.derivative P) :=
    funext fun t => (hd1 t).deriv
  have hd2 : HasDerivAt
      (fun t : ℝ => -(Real.sin t) * Polynomial.eval (Real.cos t) (Polynomial.derivative P))
      (-(Real.cos 0) * Polynomial.eval (Real.cos 0) (Polynomial.derivative P)
        + -(Real.sin 0)
          * (Polynomial.eval (Real.cos 0)
              (Polynomial.derivative (Polynomial.derivative P)) * -Real.sin 0)) 0 := by
    have hf : HasDerivAt (fun s : ℝ => -(Real.sin s)) (-(Real.cos 0)) 0 :=
      (Real.hasDerivAt_sin 0).neg
    have hg : HasDerivAt
        (fun s : ℝ => Polynomial.eval (Real.cos s) (Polynomial.derivative P))
        (Polynomial.eval (Real.cos 0)
          (Polynomial.derivative (Polynomial.derivative P)) * -Real.sin 0) 0 :=
      ((Polynomial.derivative P).hasDerivAt (Real.cos 0)).comp 0 (Real.hasDerivAt_cos 0)
    exact hf.mul hg
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hG1, hd2.deriv]
  simp
