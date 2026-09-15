/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Observation
import all QuantumAlg.Core.Execution.Measured.FeedForward

/-!
# Actual stored measurement blocks support their own numerator outcome

The full quantum-reference matrix selected by an actual output store has
support only on the numerator outcome read from that store. This follows
from the real Z writes, without conditioning on a separately supplied
measurement value or assuming positive branch probability. It is the
support fact needed when composing the selected literal X reset
[LYL+26, sec_point_add/sec_point_add.tex:67-81].
-/

namespace QuantumAlg.MeasuredUncompute.NumeratorMeasuredSupport

noncomputable section

open Execution NumeratorMeasurement NumeratorObservation

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- Keep the complete quantum-reference block for an actual final classical store. -/
def density (width : Nat) {Reference : Register} {History : Type} [Fintype History]
    (state : State (context width) Reference History) (stored : Store (context width)) :
    DensityOperator (Register.prod (context width).register Reference) :=
  (ExecutionState.filterClassical ((NumeratorMeasurement.measure width).execute Reference state)
    (fun entry => entry.1 = stored)).quantumMarginal

/-- The actual interpreter preserves exactly equal numerator labels and their real store writes. -/
theorem matrix_entry (width : Nat) {Reference : Register} {History : Type} [Fintype History]
    (state : State (context width) Reference History) (stored : Store (context width))
    (left right : (context width).register.Index) (leftRef rightRef : Reference.Index) :
    (density width state stored).matrix (left, leftRef) (right, rightRef) =
      if word width left = word width right then
        ExecutionState.weightedMatrixEntry state (fun original =>
          if Circuit.writeMeasurementPath (readouts width) original.1
            (Circuit.measurementBasisPath (readouts width) left) = stored then 1 else 0)
              (left, leftRef) (right, rightRef)
      else 0 := by
  rw [density, NumeratorMeasurement.measure,
    Circuit.measurementSequence_store_matrix_entry, measurement_agrees]
  by_cases same : word width left = word width right <;> simp only [same, if_true, if_false]

/-- A branch's entire row is zero unless its numerator equals that branch's actual stored result. -/
theorem row_zero (width : Nat) {Reference : Register} {History : Type} [Fintype History]
    (state : State (context width) Reference History) (stored : Store (context width))
    (left right : (context width).register.Index) (leftRef rightRef : Reference.Index)
    (different : word width left ≠ NumeratorReset.outcome (stored.read (input width))) :
    (density width state stored).matrix (left, leftRef) (right, rightRef) = 0 := by
  rw [matrix_entry]
  split
  · unfold ExecutionState.weightedMatrixEntry
    apply Finset.sum_eq_zero
    intro original _
    by_cases actual : Circuit.writeMeasurementPath (readouts width) original.1
        (Circuit.measurementBasisPath (readouts width) left) = stored
    · have result := stored_outcome width original.1 left
      rw [actual] at result
      exact False.elim (different result.symm)
    · exact mul_eq_zero_of_left (if_neg actual) _
  · rfl

/-- The locally observable support restriction is inherited from the same full reference rows. -/
theorem local_support (width : Nat) {Reference : Register} {History : Type} [Fintype History]
    (state : State (context width) Reference History) (stored : Store (context width))
    (basis : (context width).register.Index)
    (different : word width basis ≠ NumeratorReset.outcome (stored.read (input width))) :
    (density width state stored).marginalLeft.matrix basis basis = 0 := by
  rw [DensityOperator.marginalLeft_matrix]
  apply Finset.sum_eq_zero
  intro reference _
  exact row_zero width state stored basis basis reference reference different

end

end QuantumAlg.MeasuredUncompute.NumeratorMeasuredSupport
