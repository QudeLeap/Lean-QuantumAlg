/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Guard.Phase
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Validity.Positive

/-!
# Actual full-length and source-phase conjunction with restored arbitrary Iter

Two full geometry-validity calls and two original-field phase calls
execute the dirty-work toggle cancellation. Original Ctrl is the only
output. The complete temporary geometry and all original prefixes
return unchanged; every native call is present in the actual program.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGuard

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- Validity reads the complete actual temporary length, including its physical high carry. -/
def valid (width : Nat) (state : Data width) : Bool :=
  decide (0 < (ArithmeticGeometry.targetValue width state).toNat ∧
    (ArithmeticGeometry.targetValue width state).toNat ≤ width + 3)

private def validityStep (width : Nat) : Data width → Data width :=
  predicateFlip (flag width 3) (valid width)

private lemma validityStep_pool (width : Nat) (state : Data width) :
    (validityStep width state).2 = state.2 := by
  unfold validityStep predicateFlip
  split <;> rfl

/-- Four literal actual predicate executions use one original arbitrary Iter and restore it. -/
def conjunctionProgram (width : Nat) (signed coefficient : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (GeometryValidity.fullProgram width).seq
    ((program width signed coefficient).seq
      ((GeometryValidity.fullProgram width).seq (program width signed coefficient)))

/-- Independent exact physical-length and original-field phase condition on original Ctrl. -/
def conjunctionStep (width : Nat) (signed coefficient : Bool) : Data width → Data width :=
  predicateFlip (flag width 4)
    (fun state => valid width state && condition width signed coefficient state)

private lemma conjunction_steps (width : Nat) (signed coefficient : Bool) (state : Data width) :
    step width signed coefficient
        (validityStep width (step width signed coefficient (validityStep width state))) =
      conjunctionStep width signed coefficient state := by
  have actual := dirtyPredicateConjunction_eq (flag width 3) (flag width 4)
    (iteration_output_work_ne width).1 (valid width) (condition width signed coefficient)
    (fun _ => rfl) (fun _ => rfl)
    (condition_iteration_flip width signed coefficient)
    (condition_control_flip width signed coefficient) state
  exact actual

/-- Full coherent conjunction, with no incoming Iter or Ctrl initialization assumption. -/
lemma conjunctionProgram_apply_encoded_ket (width : Nat) (signed coefficient : Bool)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width)) :
    (conjunctionProgram width signed coefficient).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (conjunctionStep width signed coefficient state))) := by
  let first := validityStep width state
  let second := step width signed coefficient first
  let third := validityStep width second
  have firstClean : first.2.2.1 = 0#(ScanMetadata.addressWidth width) :=
    (congrArg (fun value : Pool width => value.2.1) (validityStep_pool width state)).trans clean
  have secondClean : second.2.2.1 = 0#(ScanMetadata.addressWidth width) :=
    (congrArg (fun value : Pool width => value.2.1)
      (step_pool width signed coefficient first)).trans firstClean
  have firstActual := GeometryValidity.fullProgram_apply_encoded_ket width environment state clean
  have secondActual := (program_realizes width signed coefficient environment).apply_encoded_ket
    first
  have thirdActual :=
    GeometryValidity.fullProgram_apply_encoded_ket width environment second secondClean
  have fourthActual := (program_realizes width signed coefficient environment).apply_encoded_ket
    third
  change (GeometryValidity.fullProgram width).applyNormalized environment
    (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode first)) at firstActual
  change (GeometryValidity.fullProgram width).applyNormalized environment
    (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((encoding width).encode second))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode third)) at thirdActual
  have tail := UnitaryCircuit.applyNormalized_seq_of_eq thirdActual fourthActual
  have body := UnitaryCircuit.applyNormalized_seq_of_eq secondActual tail
  have complete := UnitaryCircuit.applyNormalized_seq_of_eq firstActual body
  change (conjunctionProgram width signed coefficient).applyNormalized environment
    (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (step width signed coefficient
          (validityStep width (step width signed coefficient (validityStep width state))))))
    at complete
  rw [conjunction_steps] at complete
  exact complete

/-- Every actual original prefix, temporary address and high geometry carry returns unchanged. -/
lemma conjunctionStep_pool (width : Nat) (signed coefficient : Bool) (state : Data width) :
    (conjunctionStep width signed coefficient state).2 = state.2 := by
  unfold conjunctionStep predicateFlip
  split <;> rfl

/-- The actual emitted event word includes both full validity calls and both full phase calls. -/
lemma conjunctionProgram_eventTrace (width : Nat) (signed coefficient : Bool) :
    (conjunctionProgram width signed coefficient).eventTrace =
      (GeometryValidity.fullProgram width).eventTrace ++
        ((program width signed coefficient).eventTrace ++
          ((GeometryValidity.fullProgram width).eventTrace ++
            (program width signed coefficient).eventTrace)) := by
  simp only [conjunctionProgram, UnitaryCircuit.seq_eventTrace]

/-- Quantum duration follows the same four actual sequential dependencies. -/
lemma conjunctionProgram_quantumTime (width : Nat) (signed coefficient : Bool) :
    (conjunctionProgram width signed coefficient).evaluatedEventDepth
        Resource.Event.quantumDuration =
      (GeometryValidity.fullProgram width).evaluatedEventDepth Resource.Event.quantumDuration +
        ((program width signed coefficient).evaluatedEventDepth Resource.Event.quantumDuration +
          ((GeometryValidity.fullProgram width).evaluatedEventDepth Resource.Event.quantumDuration +
            (program width signed coefficient).evaluatedEventDepth
              Resource.Event.quantumDuration)) := by
  simp only [conjunctionProgram, UnitaryCircuit.evaluatedEventDepth_seq]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGuard
