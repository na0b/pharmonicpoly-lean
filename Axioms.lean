/- Run with `lake env lean Axioms.lean` after `lake build`.
Every result below should depend only on `propext`, `Classical.choice` and `Quot.sound`. -/
import PHarmonicPoly
import Solution

#print axioms MainTheorem
#print axioms DeficitBound
#print axioms PHarmonicPoly.main_theorem
#print axioms PHarmonicPoly.deficit_bound
