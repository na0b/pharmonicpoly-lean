module

public import PHarmonicPoly.PolarInequality
public import PHarmonicPoly.PolarContradiction
public import PHarmonicPoly.SphereMaxNormalize
public import PHarmonicPoly.LatitudeMaximizer
public import PHarmonicPoly.DeficitAtMax
public import PHarmonicPoly.GreatCircleTrigPoly
public import PHarmonicPoly.BernsteinSzegoSecond
public import PHarmonicPoly.CotBound

@[expose] public section

open MvPolynomial Real
/-- The paper's Section 3: no nonzero homogeneous polynomial of degree `m ≥ 2`
can satisfy `E_p(u) = 0` when `n ≥ 3` and `p ≥ n - 1/13`. -/
theorem HomogeneousCase {n m : ℕ} (hn : 3 ≤ n) (hm : 2 ≤ m) {p : ℝ}
    (hp : (n : ℝ) - 1 / 13 ≤ p)
    {P : MvPolynomial (Fin n) ℝ} (hP : P ≠ 0) (hhom : P.IsHomogeneous m) :
    EpAlg p P ≠ 0 := by
  intro hE0
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have : 0 < m := by omega
    exact_mod_cast this
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmR
  -- Step 1: normalizing
  obtain ⟨c0, e, hc0, he, hmax, hbd, hiff⟩ :=
    SphereMaxNormalize (n := n) (m := m) (by omega) (by omega) p hP hhom
  have hEQ : EpAlg p (c0 • P) = 0 := hiff.mpr hE0
  have hQhom : (c0 • P).IsHomogeneous m := by
    rw [MvPolynomial.smul_eq_C_mul]
    exact hhom.C_mul c0
  have hQdeg : (c0 • P).totalDegree ≤ m := hQhom.totalDegree_le
  -- Step 2: the latitude maximizer
  have hfcont : Continuous (fun v : EuclideanSpace ℝ (Fin n) =>
      MvPolynomial.eval (fun i => (Real.cos (π / m) • e + Real.sin (π / m) • v :
        EuclideanSpace ℝ (Fin n)) i) (c0 • P)) :=
    (MvPolyContDiff (c0 • P) 0).continuous.comp
      (continuous_const.add (continuous_id.const_smul (Real.sin (π / m))))
  obtain ⟨v0, hv0, hev0, hv0max⟩ := LatitudeMaximizer (n := n) (by omega) he _ hfcont
  -- Step 3: the scalars
  set G : ℝ → ℝ := fun s => MvPolynomial.eval
    (fun i => (Real.cos s • e + Real.sin s • v0 : EuclideanSpace ℝ (Fin n)) i) (c0 • P)
    with hGdef
  set a : ℝ := -(G (π / m)) with hadeff
  set b : ℝ := deriv G (π / m) / (m : ℝ) with hbdeff
  set c : ℝ := iteratedDeriv 2 G (π / m) / (m : ℝ) ^ 2 with hcdeff
  have hadef : MvPolynomial.eval (fun i => (Real.cos (π / m) • e + Real.sin (π / m) • v0 :
      EuclideanSpace ℝ (Fin n)) i) (c0 • P) = -a := by
    rw [hadeff, hGdef]; ring
  have hbdef : deriv G (π / m) = (m : ℝ) * b := by rw [hbdeff]; field_simp
  have hcdef : iteratedDeriv 2 G (π / m) = (m : ℝ) ^ 2 * c := by rw [hcdeff]; field_simp
  -- Step 4: bounds on a, and p ≤ n
  obtain ⟨hpn, hall⟩ := DeficitAtMax hn hm hp hQhom he hmax hbd hEQ
  obtain ⟨-, -, hge, -, hgt⟩ := hall v0 hv0 hev0
  rw [hadef] at hge hgt
  have ha : 8 / 13 < a := by linarith
  have ha1 : a ≤ 1 := by linarith
  have hqpos : 0 < a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg b, ha]
  -- Step 5: q ≤ 1 and b² + c² ≤ 1
  have hGTP : TrigPolyLe m G := by
    rw [hGdef]; exact GreatCircleTrigPoly hQdeg e v0
  have hGbd : ∀ t : ℝ, |G t| ≤ 1 := by
    intro t
    rw [hGdef]
    refine hbd _ ?_
    have hsq : ‖(Real.cos t • e + Real.sin t • v0 : EuclideanSpace ℝ (Fin n))‖ ^ 2 = 1 := by
      rw [norm_add_sq_real, norm_smul, norm_smul, he, hv0,
        real_inner_smul_left, real_inner_smul_right, hev0]
      simp only [Real.norm_eq_abs, mul_one, mul_zero, sq_abs]
      nlinarith [Real.sin_sq_add_cos_sq t]
    nlinarith [hsq, norm_nonneg (Real.cos t • e + Real.sin t • v0 : EuclideanSpace ℝ (Fin n))]
  have hBS := BernsteinSzego (by omega : 1 ≤ m) hGTP hGbd (π / m)
  rw [hbdef] at hBS
  have hGval : G (π / m) = -a := by rw [hadeff]; ring
  rw [hGval] at hBS
  have hq1 : a ^ 2 + b ^ 2 ≤ 1 := by
    have : ((m : ℝ) * b) ^ 2 / (m : ℝ) ^ 2 = b ^ 2 := by field_simp
    rw [this] at hBS
    nlinarith [hBS]
  have hBS2 := BernsteinSzegoSecond (by omega : 1 ≤ m) hGTP hGbd (π / m)
  rw [hbdef, hcdef] at hBS2
  have hbc : b ^ 2 + c ^ 2 ≤ 1 := by
    have h1 : ((m : ℝ) * b) ^ 2 / (m : ℝ) ^ 2 = b ^ 2 := by field_simp
    have h2 : ((m : ℝ) ^ 2 * c) ^ 2 / (m : ℝ) ^ 4 = c ^ 2 := by field_simp
    rw [h1, h2] at hBS2
    exact hBS2
  -- Step 6: the cotangent bound
  obtain ⟨hk0, hk⟩ := CotBound m hm
  -- Step 7: the two sides of eq:polar
  have hge2 := PolarInequality hn hm hp hQhom he hv0 hev0 hmax hbd hEQ hv0max
    a b c (a ^ 2 + b ^ 2) hadef hbdef hcdef rfl hqpos
  have hlt := PolarContradiction hn hm p a b c (a ^ 2 + b ^ 2)
    (Real.cos (π / m) / (Real.sin (π / m) * m)) hp hpn ha ha1 rfl hq1 hbc hk0 hk
  -- Step 8
  linarith [hge2, hlt]
