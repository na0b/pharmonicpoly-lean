module

public import PHarmonicPoly.TrigPolyLe

@[expose] public section

/-- Real trigonometric polynomials of degree at most `m` form a linear subspace:
a pointwise linear combination of two of them is again one. -/
theorem TrigPolyLinComb {m : ℕ} {S T : ℝ → ℝ} (hS : TrigPolyLe m S)
    (hT : TrigPolyLe m T) (c d : ℝ) :
    TrigPolyLe m (fun t => c * S t + d * T t) := by
  obtain ⟨a₁, b₁, h₁⟩ := hS
  obtain ⟨a₂, b₂, h₂⟩ := hT
  refine ⟨fun k => c * a₁ k + d * a₂ k, fun k => c * b₁ k + d * b₂ k, fun t => ?_⟩
  simp only [h₁ t, h₂ t, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => by ring)
