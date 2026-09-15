/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Cascade
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Step.Correctness

/-!
# Full point action of the actual measured cascade on its prepared domain

The independent target composes the mathematical point actions in the
prescribed order. Its support condition checks each original prepared point
domain on the preceding mathematical density, without referring to Circuit
execution. Actual execution has precisely this full joint action, including
all resident systems and an arbitrary external reference.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Compose the independent indexed point operators in chronological execution order. -/
def cascadeTarget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (Reference : Register) :
    List (Fin count) →
      UnitaryOperator (Register.prod (readyContext p.size count).register Reference)
  | [] => 1
  | active :: remaining =>
      cascadeTarget E points Reference remaining * stepTarget E (points active) active Reference

/-- Each independent intermediate density lies in the next original prepared point domain. -/
def cascadeSupport {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (Reference : Register) :
    List (Fin count) →
      DensityOperator (Register.prod (readyContext p.size count).register Reference) →
      Prop
  | [], _ => True
  | active :: remaining, density =>
      (∀ input, ¬stepAdmissible E (points active) active input.1 → density.matrix input input = 0) ∧
      cascadeSupport E points Reference remaining
        (DensityOperator.applyUnitary (stepTarget E (points active) active Reference) density)

/-- The actual cascade realizes its complete independent point product on the prescribed domain. -/
theorem cascade_density {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    {Reference : Register} {H : Type} [Fintype H]
    (original : State (readyContext p.size count) Reference H)
    (support : cascadeSupport E points Reference order original.quantumMarginal) :
    ((cascade E points order).execute Reference original).quantumMarginal =
      DensityOperator.applyUnitary (cascadeTarget E points Reference order)
        original.quantumMarginal := by
  induction order generalizing H with
  | nil =>
      rw [cascade, Circuit.execute_id, State.skip_quantumMarginal,
        cascadeTarget, DensityOperator.applyUnitary_one]
  | cons active remaining ih =>
      have first := step_density E (points active) active original support.1
      have remainingSupport : cascadeSupport E points Reference remaining
          (((step E (points active) active).execute Reference original).quantumMarginal) := by
        rw [first]
        exact support.2
      rw [cascade, Circuit.execute_seq, State.mapHistory_quantumMarginal,
        ih _ remainingSupport, first, cascadeTarget, DensityOperator.applyUnitary_mul]

end

end MeasuredPlacement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
