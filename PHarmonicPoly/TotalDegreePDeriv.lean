module

public import PHarmonicPoly.Preamble

@[expose] public section

open MvPolynomial Finsupp
/-- Formal partial differentiation drops total degree by at least one. Missing
from Mathlib, and the sharp `- 1` is what `TopComponent` needs. -/
theorem TotalDegreePDeriv {σ : Type*} (i : σ) (φ : MvPolynomial σ ℝ) :
    (pderiv i φ).totalDegree ≤ φ.totalDegree - 1 := by
  classical
  rw [MvPolynomial.totalDegree]
  refine Finset.sup_le ?_
  intro s hs
  have hco : coeff s (pderiv i φ) ≠ 0 := by
    simpa using (MvPolynomial.mem_support_iff).1 hs
  rw [coeff_pderiv] at hco
  have hne : coeff (s + single i 1) φ ≠ 0 := by
    intro h; rw [h, zero_mul] at hco; exact hco rfl
  have hmem : s + single i 1 ∈ φ.support := MvPolynomial.mem_support_iff.2 hne
  have hle : ((s + single i 1).sum fun _ e => e) ≤ φ.totalDegree :=
    MvPolynomial.le_totalDegree hmem
  have hsum : ((s + single i 1).sum fun _ e => e) = (s.sum fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index' (by intro a; rfl) (by intro a b₁ b₂; rfl)]
    simp [Finsupp.sum_single_index]
  omega
