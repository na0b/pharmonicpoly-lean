module

public import PHarmonicPoly

/-!
# Proofs of the Challenge statements

Each declaration below has exactly the statement of its counterpart in `Challenge.lean`
and is proved by the corresponding result of the `PHarmonicPoly` development. Comparator checks
that the statements agree and that only `propext`, `Classical.choice` and `Quot.sound`
are used.
-/

@[expose] public section

namespace PHarmonicPoly

section main_theorem
open MvPolynomial

/-- **Theorem 1.1.** Let `n ≥ 3` and `p ≥ n - 1/13`. Every real polynomial `u` on `ℝⁿ`
with `E_p(u) = |Du|² Δu + (p - 2) ⟨D²u Du, Du⟩ = 0` everywhere is affine. -/
theorem main_theorem {n : ℕ} (hn : 3 ≤ n) {p : ℝ} (hp : (n : ℝ) - 1 / 13 ≤ p)
    (P : MvPolynomial (Fin n) ℝ)
    (hE : ∀ x : EuclideanSpace ℝ (Fin n),
      EpOp p (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) x = 0) :
    ∃ (w : EuclideanSpace ℝ (Fin n)) (c : ℝ), ∀ x : EuclideanSpace ℝ (Fin n),
      MvPolynomial.eval (fun i => x i) P = inner ℝ w x + c :=
  _root_.MainTheorem hn hp P hE

end main_theorem

section deficit_bound

/-- **Lemma 2.1 (deficit estimate).** Let `m ≥ 2` and let `T` be a real trigonometric
polynomial of degree at most `m` with `‖T‖∞ ≤ 1` and `T(0) = 1`. With `d = m² + T''(0)`,
`0 ≤ 1 + T(±π/m) ≤ d (1 - cos(π/m)) ≤ π² d / (2 m²)`. -/
theorem deficit_bound {m : ℕ} (hm : 2 ≤ m) {T : ℝ → ℝ} (hT : TrigPolyLe m T)
    (hbd : ∀ t : ℝ, |T t| ≤ 1) (h0 : T 0 = 1) :
    (0 ≤ 1 + T (Real.pi / m) ∧ 0 ≤ 1 + T (-(Real.pi / m)))
      ∧ (1 + T (Real.pi / m)
            ≤ ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) * (1 - Real.cos (Real.pi / m))
          ∧ 1 + T (-(Real.pi / m))
            ≤ ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) * (1 - Real.cos (Real.pi / m)))
      ∧ ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) * (1 - Real.cos (Real.pi / m))
          ≤ Real.pi ^ 2 * ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) / (2 * (m : ℝ) ^ 2) :=
  _root_.DeficitBound hm hT hbd h0

end deficit_bound

end PHarmonicPoly
