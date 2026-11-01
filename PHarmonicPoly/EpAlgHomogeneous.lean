module

public import PHarmonicPoly.EpAlg

@[expose] public section

open MvPolynomial
/-- If `P` is homogeneous of degree `m ≥ 2` then `EpAlg p P` is homogeneous of
degree `3*m - 4`. -/
theorem EpAlgHomogeneous {n : ℕ} (p : ℝ) {m : ℕ} (hm : 2 ≤ m)
    {P : MvPolynomial (Fin n) ℝ} (hhom : P.IsHomogeneous m) :
    (EpAlg p P).IsHomogeneous (3 * m - 4) := by
  have h1 : ∀ i : Fin n, (pderiv i P).IsHomogeneous (m - 1) := fun i => hhom.pderiv
  have h2 : ∀ i j : Fin n, (pderiv i (pderiv j P)).IsHomogeneous (m - 2) := by
    intro i j
    have := (h1 j).pderiv (i := i)
    have he : m - 1 - 1 = m - 2 := by omega
    rwa [he] at this
  have hA : (∑ i : Fin n, (pderiv i P) ^ 2).IsHomogeneous (2 * (m - 1)) := by
    refine MvPolynomial.IsHomogeneous.sum _ _ _ (fun i _ => ?_)
    have := (h1 i).mul (h1 i)
    rw [pow_two]
    have he : m - 1 + (m - 1) = 2 * (m - 1) := by omega
    rwa [he] at this
  have hB : (∑ i : Fin n, pderiv i (pderiv i P)).IsHomogeneous (m - 2) :=
    MvPolynomial.IsHomogeneous.sum _ _ _ (fun i _ => h2 i i)
  have hAB : ((∑ i : Fin n, (pderiv i P) ^ 2)
      * (∑ i : Fin n, pderiv i (pderiv i P))).IsHomogeneous (3 * m - 4) := by
    have := hA.mul hB
    have he : 2 * (m - 1) + (m - 2) = 3 * m - 4 := by omega
    rwa [he] at this
  have hC : (∑ i : Fin n, ∑ j : Fin n,
      pderiv i (pderiv j P) * pderiv i P * pderiv j P).IsHomogeneous (3 * m - 4) := by
    refine MvPolynomial.IsHomogeneous.sum _ _ _ (fun i _ => ?_)
    refine MvPolynomial.IsHomogeneous.sum _ _ _ (fun j _ => ?_)
    have := ((h2 i j).mul (h1 i)).mul (h1 j)
    have he : m - 2 + (m - 1) + (m - 1) = 3 * m - 4 := by omega
    rwa [he] at this
  exact hAB.add (hC.C_mul _)
