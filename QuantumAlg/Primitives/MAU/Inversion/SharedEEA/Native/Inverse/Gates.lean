/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Inverse
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.CorrectedSchedule.Gates
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint.Trace

/-! # Literal compute, copy and reverse with complete arbitrary-frame restoration -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.NativeInverse

noncomputable section

open EncodedBit GateSpec

/-- Place every complete corrected-schedule instruction before the arbitrary XOR target. -/
def forwardGates (modulus : Nat) (nontrivial : 1 < modulus) :
    List (GateSpec (OutputCopy.encoding modulus.size)) :=
  (CorrectedSchedule.gates modulus nontrivial).map
    (GateSpec.prodLeft (BinaryLabelEncoding.finIdentity modulus.size))

/-- Every forward gate, actual output CNOT and reverse gate occurs in chronological order. -/
def gates (modulus : Nat) (nontrivial : 1 < modulus) :
    List (GateSpec (OutputCopy.encoding modulus.size)) :=
  forwardGates modulus nontrivial ++
    (OutputCopy.gates modulus.size ++ (forwardGates modulus nontrivial).reverse)

/-- The whole arbitrary compute frame is restored; only the arbitrary target is xored. -/
def step (modulus : Nat) (state : OutputCopy.Data modulus.size) : OutputCopy.Data modulus.size :=
  (state.1, (OutputCopy.step (CorrectedSchedule.step modulus state.1, state.2)).2)

private theorem forwardGates_step (modulus : Nat) (nontrivial : 1 < modulus)
    (state : OutputCopy.Data modulus.size) :
    stepList (forwardGates modulus nontrivial) state =
      (CorrectedSchedule.step modulus state.1, state.2) := by
  erw [forwardGates, stepList_prodLeft, CorrectedSchedule.correctedSchedule_gates_step]

private theorem copyGates_step (width : Nat) (state : OutputCopy.Data width) :
    stepList (OutputCopy.gates width) state = OutputCopy.step state :=
  OutputCopy.gates_step width state

/-- Literal reversal restores all dirty fields for every input and arbitrary XOR target. -/
theorem nativeInverse_gates_step (modulus : Nat) (nontrivial : 1 < modulus)
    (state : OutputCopy.Data modulus.size) :
    stepList (gates modulus nontrivial) state = step modulus state := by
  rw [gates, stepList_append, stepList_append, forwardGates_step, copyGates_step]
  erw [forwardGates, ← List.map_reverse, stepList_prodLeft]
  change (stepList (CorrectedSchedule.gates modulus nontrivial).reverse
    (CorrectedSchedule.step modulus state.1), _) = _
  apply Prod.ext
  · change stepList (CorrectedSchedule.gates modulus nontrivial).reverse
      (CorrectedSchedule.step modulus state.1) = state.1
    rw [← CorrectedSchedule.correctedSchedule_gates_step modulus nontrivial state.1,
      stepList_reverse_stepList]
  · rfl

-- Generic realization laws consume this word without evaluating its recursive generator.
attribute [local irreducible] gates

/-- The original symbolic compute-copy-adjoint has the same full-frame action. -/
theorem nativeInverse_program_realizes (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit.Realizes (OutputCopy.encoding modulus.size) (program modulus nontrivial)
      (step modulus) where
  apply_encoded_ket := by
    intro state
    let computed := CorrectedSchedule.step modulus state.1
    let target := (OutputCopy.step (computed, state.2)).2
    have forward (value : Fin (2 ^ modulus.size)) :
        (forwardProgram modulus nontrivial).applyNormalized
          (NormalizedVector.ket
            ((QubitLayout.canonical (OutputCopy.encoding modulus.size).width).basisEquiv.symm
              ((OutputCopy.encoding modulus.size).encode (state.1, value)))) =
        NormalizedVector.ket
          ((QubitLayout.canonical (OutputCopy.encoding modulus.size).width).basisEquiv.symm
            ((OutputCopy.encoding modulus.size).encode (computed, value))) :=
      UnitaryCircuit.Realizes.onBinaryPrefix_applyNormalized_encoded_ket_of_eq
        (encoding modulus.size) (BinaryLabelEncoding.finIdentity modulus.size)
        (CorrectedSchedule.program modulus nontrivial) state.1 computed value
        ((CorrectedSchedule.correctedSchedule_program_realizes modulus
      nontrivial).apply_encoded_ket _)
    have copied := (OutputCopy.program_realizes modulus.size).apply_encoded_ket (computed, state.2)
    have restored :
        ((forwardProgram modulus nontrivial).dagger
          (AlgorithmGate.oracleFreeAdjoints .empty)).applyNormalized
          (NormalizedVector.ket
            ((QubitLayout.canonical (OutputCopy.encoding modulus.size).width).basisEquiv.symm
              ((OutputCopy.encoding modulus.size).encode (computed, target)))) =
        NormalizedVector.ket
          ((QubitLayout.canonical (OutputCopy.encoding modulus.size).width).basisEquiv.symm
            ((OutputCopy.encoding modulus.size).encode (state.1, target))) :=
      (congrArg (fun vector => ((forwardProgram modulus nontrivial).dagger
          (AlgorithmGate.oracleFreeAdjoints .empty)).applyNormalized vector)
        (forward target)).symm.trans
        (UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized
          (forwardProgram modulus nontrivial)
          ((forwardProgram modulus nontrivial).dagger (AlgorithmGate.oracleFreeAdjoints .empty))
          (by rw [UnitaryCircuit.dagger_matrix]; exact Unitary.star_eq_inv _) _)
    exact UnitaryCircuit.applyNormalized_seq_of_eq (forward state.2)
      (UnitaryCircuit.applyNormalized_seq_of_eq copied restored)

/-- Execute the complete standalone inverse using exactly its literal native instructions. -/
def nativeProgram (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (OutputCopy.encoding modulus.size).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (gates modulus nontrivial)

/-- Exact unrestricted phases include the complete dirty frame and arbitrary output word. -/
theorem nativeInverse_nativeProgram_realizes (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit.Realizes (OutputCopy.encoding modulus.size) (nativeProgram modulus nontrivial)
      (step modulus) :=
  realizesList_congrStep (QubitLayout.canonical _) .empty _ (nativeInverse_gates_step modulus
      nontrivial)

/-- Every complete encoded basis label has the same exact action as the original inverse. -/
theorem nativeInverse_nativeProgram_basis (modulus : Nat) (nontrivial : 1 < modulus)
    (state : OutputCopy.Data modulus.size) :
    (nativeProgram modulus nontrivial).applyNormalized
      (NormalizedVector.ket
        ((QubitLayout.canonical (OutputCopy.encoding modulus.size).width).basisEquiv.symm
        ((OutputCopy.encoding modulus.size).encode state))) =
    (program modulus nontrivial).applyNormalized
      (NormalizedVector.ket
        ((QubitLayout.canonical (OutputCopy.encoding modulus.size).width).basisEquiv.symm
        ((OutputCopy.encoding modulus.size).encode state))) :=
  ((nativeInverse_nativeProgram_realizes modulus nontrivial).apply_encoded_ket state).trans
    ((nativeInverse_program_realizes modulus nontrivial).apply_encoded_ket state).symm

/-- The original mathematical modular inverse remains the arbitrary-target XOR result. -/
theorem nativeInverse_nativeProgram_initial (modulus : Nat) (nontrivial : 1 < modulus)
    (input target : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus) :
    (nativeProgram modulus nontrivial).applyNormalized
      (NormalizedVector.ket
        ((QubitLayout.canonical (OutputCopy.encoding modulus.size).width).basisEquiv.symm
        ((OutputCopy.encoding modulus.size).encode (InitialFrame.initial modulus input, target)))) =
    NormalizedVector.ket
      ((QubitLayout.canonical (OutputCopy.encoding modulus.size).width).basisEquiv.symm
      ((OutputCopy.encoding modulus.size).encode
        (InitialFrame.initial modulus input, output modulus input.val positive bounded target))) :=
  (nativeInverse_nativeProgram_basis modulus nontrivial _).trans
    (program_initial modulus nontrivial input target coprime positive bounded)

private theorem forwardGates_trace (modulus : Nat) (nontrivial : 1 < modulus) :
    (forwardGates modulus nontrivial).map (event .empty) =
      (forwardProgram modulus nontrivial).eventTrace := by
  erw [forwardGates, map_event_prodLeft, CorrectedSchedule.correctedSchedule_gates_trace,
    forwardProgram, UnitaryCircuit.prodLeft_eventTrace]
  rfl

/-- The reverse word has exactly the actual dagger's reversed native event order. -/
theorem nativeInverse_gates_trace (modulus : Nat) (nontrivial : 1 < modulus) :
    (gates modulus nontrivial).map (event .empty) = (program modulus nontrivial).eventTrace := by
  rw [gates, List.map_append, List.map_append, List.map_reverse, forwardGates_trace,
    program, UnitaryCircuit.seq_eventTrace, UnitaryCircuit.seq_eventTrace,
    AlgorithmGate.oracleFreeAdjoints_eventTrace, OutputCopy.program, programList_eventTrace]

/-- Literal standalone execution retains the original exact chronological native trace. -/
theorem nativeInverse_nativeProgram_trace (modulus : Nat) (nontrivial : 1 < modulus) :
    (nativeProgram modulus nontrivial).eventTrace = (program modulus nontrivial).eventTrace := by
  rw [nativeProgram, programList_eventTrace, nativeInverse_gates_trace]

/-- The same emitted events support all independently stated native resource formulas. -/
theorem nativeInverse_nativeProgram_eventCost (modulus : Nat) (nontrivial : 1 < modulus) :
    (nativeProgram modulus nontrivial).eventCost = (program modulus nontrivial).eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    ← UnitaryCircuit.ofList_eventTrace_eq_eventCost, nativeInverse_nativeProgram_trace]

end

end QuantumAlg.MAU.Inversion.SharedEEA.NativeInverse
