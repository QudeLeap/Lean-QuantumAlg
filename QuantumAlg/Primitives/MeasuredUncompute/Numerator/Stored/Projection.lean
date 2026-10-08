/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.PathEquality
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Reset.Matrix

/-!
# The actual stored numerator branch as an exact Z projection

The existing Z writes determine which original stores can reach a given
actual final store. Their full quantum-reference blocks are then projected
onto precisely the word read from that final store. No measurement result
or conditional state is supplied independently of the executed circuit
[LYL+26, sec_point_add/sec_point_add.tex:67-81].
-/

namespace QuantumAlg.MeasuredUncompute.NumeratorStoredProjection

noncomputable section

open Execution MAU.Inversion.SharedEEA NumeratorMeasurement NumeratorObservation

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- A representative basis label is used only to evaluate the existing classical write function. -/
def representative (width : Nat) (value : Fin (2 ^ width)) : (context width).register.Index :=
  (frameBasis width).symm (prodEquiv ((0 : Fin (2 ^ (encoding width).width)), value))

private theorem representative_word (width : Nat) (value : Fin (2 ^ width)) :
    word width (representative width value) = value := by
  have actual : frameBasis width (representative width value) =
      prodEquiv ((0 : Fin (2 ^ (encoding width).width)), value) :=
    (frameBasis width).apply_symm_apply _
  have projected := congrArg
    (fun label : Fin (2 ^ (OutputCopy.encoding width).width) =>
      ((prodEquiv (m := (encoding width).width) (n := width)).symm label).2) actual
  exact projected.trans (congrArg Prod.snd
    ((prodEquiv (m := (encoding width).width) (n := width)).symm_apply_apply (0, value)))

private theorem writes (width : Nat) (store : Store (context width))
    (basis : (context width).register.Index) (value : Fin (2 ^ width))
    (same : word width basis = value) :
    Circuit.writeMeasurementPath (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := .empty) (classicalOracles := .empty) (readouts width) store
      (Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := .empty)
        (operations := .empty) (classicalOracles := .empty) (readouts width) basis) =
      Circuit.writeMeasurementPath (gates := AlgorithmGate.model) (oracles := .empty)
        (operations := .empty) (classicalOracles := .empty) (readouts width) store
        (Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := .empty)
          (operations := .empty) (classicalOracles := .empty)
          (readouts width) (representative width value)) := by
  apply Circuit.writeMeasurementPath_eq_of_agree (gates := AlgorithmGate.model)
    (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
  exact (measurement_agrees width basis (representative width value)).mpr
    (same.trans (representative_word width value).symm)

/-- Keep precisely the original stores whose actual Z writes produce the selected final store. -/
def source (width : Nat) {Reference : Register} {History : Type} [Fintype History]
    (state : State (context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (stored : Store (context width)) :
    DensityOperator (Register.prod (context width).register Reference) :=
  (state.filterClassical (fun entry =>
    Circuit.writeMeasurementPath (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := .empty) (classicalOracles := .empty) (readouts width) entry.1
      (Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := .empty)
        (operations := .empty) (classicalOracles := .empty) (readouts width)
        (representative width (NumeratorReset.outcome (stored.read (input width))))) =
      stored)).quantumMarginal

private theorem source_entry (width : Nat) {Reference : Register} {History : Type}
    [Fintype History] (state : State (context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (context width))
    (left right : (context width).register.Index) (leftRef rightRef : Reference.Index) :
    (source width state stored).matrix (left, leftRef) (right, rightRef) =
      ExecutionState.weightedMatrixEntry state (fun entry =>
        if Circuit.writeMeasurementPath (gates := AlgorithmGate.model) (oracles := .empty)
          (operations := .empty) (classicalOracles := .empty) (readouts width) entry.1
          (Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := .empty)
            (operations := .empty) (classicalOracles := .empty) (readouts width)
            (representative width (NumeratorReset.outcome (stored.read (input width))))) =
              stored then 1 else 0) (left, leftRef) (right, rightRef) :=
  ExecutionState.filterClassical_matrix_weighted state _ _ _

/-- The existing measurement execution equals this projection on every full reference block. -/
theorem actual_density (width : Nat) {Reference : Register} {History : Type} [Fintype History]
    (state : State (context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (stored : Store (context width)) :
    NumeratorMeasuredSupport.density width state stored =
      ZMeasurement.branch (fun entry : (Register.prod (context width).register Reference).Index =>
        word width entry.1) (NumeratorReset.outcome (stored.read (input width)))
          (source width state stored) := by
  apply DensityOperator.ext
  ext ⟨left, leftRef⟩ ⟨right, rightRef⟩
  rw [ZMeasurement.branch_matrix]
  by_cases first : word width left = NumeratorReset.outcome (stored.read (input width))
  · by_cases second : word width right = NumeratorReset.outcome (stored.read (input width))
    · rw [if_pos ⟨first, second⟩, NumeratorMeasuredSupport.matrix_entry,
        if_pos (first.trans second.symm), source_entry]
      apply congrArg (fun weight => ExecutionState.weightedMatrixEntry state weight
        (left, leftRef) (right, rightRef))
      funext original
      rw [writes width original.1 left _ first]
    · rw [if_neg (fun both => second both.2), NumeratorMeasuredSupport.matrix_entry,
        if_neg (fun same => second (same.symm.trans first))]
  · rw [if_neg (fun both => first both.1)]
    exact NumeratorMeasuredSupport.row_zero width state stored left right leftRef rightRef first

end

end QuantumAlg.MeasuredUncompute.NumeratorStoredProjection
