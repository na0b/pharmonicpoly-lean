module

public import PHarmonicPoly.Preamble

@[expose] public section

open MvPolynomial
/-- The top homogeneous component of a nonzero polynomial is nonzero. Mathlib
has only the vanishing of components ABOVE the total degree. -/
theorem TopComponentNeZero {σ R : Type*} [CommSemiring R]
    {P : MvPolynomial σ R} (hP : P ≠ 0) :
    homogeneousComponent P.totalDegree P ≠ 0 := by
  classical
  have hsupp : P.support.Nonempty := by
    rwa [MvPolynomial.support_nonempty]
  obtain ⟨d, hd, hdeg⟩ :=
    Finset.exists_mem_eq_sup P.support hsupp (fun s => s.sum fun _ e => e)
  have hbridge : Finsupp.degree d = d.sum (fun _ e => e) := rfl
  have hcoeff : coeff d (homogeneousComponent P.totalDegree P) = coeff d P := by
    rw [MvPolynomial.coeff_homogeneousComponent, if_pos]
    rw [hbridge, MvPolynomial.totalDegree, hdeg]
  intro hzero
  rw [hzero, MvPolynomial.coeff_zero] at hcoeff
  exact (MvPolynomial.mem_support_iff.1 hd) hcoeff.symm
