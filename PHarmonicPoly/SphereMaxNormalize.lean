module

public import PHarmonicPoly.EpAlgSmul
public import PHarmonicPoly.MvPolyContDiff

@[expose] public section

open MvPolynomial
/-- The paper's normalization: a nonzero homogeneous `P` can be rescaled by a
single nonzero constant so that it attains the value `1` at a unit vector `e`
and is bounded by `1` in absolute value on the whole unit sphere, without
changing whether `EpAlg p` vanishes. -/
theorem SphereMaxNormalize {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (p : ℝ)
    {P : MvPolynomial (Fin n) ℝ} (hP : P ≠ 0) (hhom : P.IsHomogeneous m) :
    ∃ (c : ℝ) (e : EuclideanSpace ℝ (Fin n)), c ≠ 0 ∧ ‖e‖ = 1
      ∧ MvPolynomial.eval (fun i => e i) (c • P) = 1
      ∧ (∀ y : EuclideanSpace ℝ (Fin n), ‖y‖ = 1 →
          |MvPolynomial.eval (fun i => y i) (c • P)| ≤ 1)
      ∧ (EpAlg p (c • P) = 0 ↔ EpAlg p P = 0) := by
  have hscale : ∀ (r : ℝ) (y : EuclideanSpace ℝ (Fin n)),
      MvPolynomial.eval (fun i => (r • y : EuclideanSpace ℝ (Fin n)) i) P
        = r ^ m * MvPolynomial.eval (fun i => y i) P := by
    intro r y
    rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
    refine Finset.sum_congr rfl (fun dd hdd => ?_)
    have hdegm : ∑ i, dd i = m := by
      have h := hhom (MvPolynomial.mem_support_iff.mp hdd)
      rw [Finsupp.weight_apply] at h
      simp only [Pi.one_apply, smul_eq_mul, mul_one] at h
      rw [Finsupp.sum_fintype dd (fun _ e => e) (fun _ => rfl)] at h
      exact h
    have hco : ∀ i : Fin n, (r • y : EuclideanSpace ℝ (Fin n)) i = r * y i := fun i => rfl
    simp only [hco, mul_pow]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdegm]
    ring
  have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
      |MvPolynomial.eval (fun i => y i) P|) := (MvPolyContDiff P 0).continuous.abs
  obtain ⟨e, heMem, hemax⟩ :=
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).exists_isMaxOn
      ⟨EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ), by simp⟩ hcont.continuousOn
  have henorm : ‖e‖ = 1 := mem_sphere_zero_iff_norm.mp heMem
  have hbd0 : ∀ y : EuclideanSpace ℝ (Fin n), ‖y‖ = 1 →
      |MvPolynomial.eval (fun i => y i) P| ≤ |MvPolynomial.eval (fun i => e i) P| :=
    fun y hy => hemax (mem_sphere_zero_iff_norm.mpr hy)
  have hune : MvPolynomial.eval (fun i => e i) P ≠ 0 := by
    intro h0
    have key : ∀ y : EuclideanSpace ℝ (Fin n), MvPolynomial.eval (fun i => y i) P = 0 := by
      intro y
      rcases eq_or_ne y 0 with h | h
      · have h2 := hscale 0 y
        rw [zero_smul, zero_pow (by omega : m ≠ 0), zero_mul] at h2
        rw [h]
        exact h2
      · have hr : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr h
        have hz : ‖(‖y‖⁻¹ • y : EuclideanSpace ℝ (Fin n))‖ = 1 := by
          rw [norm_smul]
          simp [hr]
        have hzz : MvPolynomial.eval
            (fun i => (‖y‖⁻¹ • y : EuclideanSpace ℝ (Fin n)) i) P = 0 := by
          have h3 := hbd0 _ hz
          rw [h0, abs_zero] at h3
          exact abs_eq_zero.mp (le_antisymm h3 (abs_nonneg _))
        have hback : (‖y‖ • (‖y‖⁻¹ • y) : EuclideanSpace ℝ (Fin n)) = y := by
          rw [smul_smul, mul_inv_cancel₀ hr, one_smul]
        have h4 := hscale ‖y‖ (‖y‖⁻¹ • y)
        rw [hback, hzz, mul_zero] at h4
        exact h4
    refine hP (MvPolynomial.funext (fun v => ?_))
    rw [map_zero]
    exact key (WithLp.toLp 2 v)
  refine ⟨(MvPolynomial.eval (fun i => e i) P)⁻¹, e, inv_ne_zero hune, henorm, ?_, ?_, ?_⟩
  · rw [MvPolynomial.smul_eval, inv_mul_cancel₀ hune]
  · intro y hy
    rw [MvPolynomial.smul_eval, abs_mul, abs_inv, inv_mul_eq_div,
      div_le_one (abs_pos.mpr hune)]
    exact hbd0 y hy
  · rw [EpAlgSmul, smul_eq_zero]
    refine ⟨fun h => ?_, fun h => Or.inr h⟩
    rcases h with h | h
    · exact absurd h (pow_ne_zero 3 (inv_ne_zero hune))
    · exact h
