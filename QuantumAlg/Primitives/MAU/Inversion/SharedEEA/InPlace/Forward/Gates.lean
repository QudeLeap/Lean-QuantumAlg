/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.InPlace.Forward
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.CorrectedSchedule.Gates

/-! # Complete literal in-place EEA forward, including actual load and output-port gates -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InPlaceForward

noncomputable section

open EncodedBit GateSpec

/-- Every actual load, fixed-schedule and output-port instruction at its original source address. -/
def gates (modulus : Nat) (nontrivial : 1 < modulus) : List (GateSpec (encoding modulus.size)) :=
  Work1Constant.gates modulus.size (InitialPortProgram.constant modulus) ++
    (CorrectedSchedule.gates modulus nontrivial ++ OutputPortProgram.gates modulus)

/-- Complete action, including unrestricted incoming values in the loaded and retained fields. -/
def step (modulus : Nat) (state : Registers modulus.size) : Registers modulus.size :=
  OutputPortProgram.step modulus (CorrectedSchedule.step modulus
    (stepList (Work1Constant.gates modulus.size (InitialPortProgram.constant modulus)) state))

/-- The literal whole forward acts on every original label without an extra cleanliness premise. -/
theorem inPlaceForward_gates_step (modulus : Nat) (nontrivial : 1 < modulus)
    (state : Registers modulus.size) :
    stepList (gates modulus nontrivial) state = step modulus state := by
  rw [gates, stepList_append, stepList_append, CorrectedSchedule.correctedSchedule_gates_step,
    OutputPortProgram.gates_step]
  rfl

-- Generic realization laws consume this word without evaluating its recursive generator.
attribute [local irreducible] gates

/-- The existing actual forward realizes the same complete source-frame action. -/
theorem inPlaceForward_program_realizes (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit.Realizes (encoding modulus.size) (program modulus nontrivial) (step modulus) :=
  (realizesList (QubitLayout.canonical _) .empty
    (Work1Constant.gates modulus.size (InitialPortProgram.constant modulus))).seq
      ((CorrectedSchedule.correctedSchedule_program_realizes modulus nontrivial).seq
        (OutputPortProgram.program_realizes modulus))

/-- Execute the complete forward as one literal native list. -/
def nativeProgram (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding modulus.size).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (gates modulus nontrivial)

/-- All complete input states have exact phase under the emitted forward. -/
theorem inPlaceForward_nativeProgram_realizes (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit.Realizes (encoding modulus.size) (nativeProgram modulus nontrivial)
      (step modulus) :=
  realizesList_congrStep (QubitLayout.canonical _) .empty _
    (inPlaceForward_gates_step modulus nontrivial)

/-- The emitted and original forward agree exactly at every complete logical basis label. -/
theorem inPlaceForward_nativeProgram_basis (modulus : Nat) (nontrivial : 1 < modulus)
    (state : Registers modulus.size) :
    (nativeProgram modulus nontrivial).applyNormalized
      (NormalizedVector.ket ((QubitLayout.canonical (encoding modulus.size).width).basisEquiv.symm
        ((encoding modulus.size).encode state))) =
    (program modulus nontrivial).applyNormalized
      (NormalizedVector.ket ((QubitLayout.canonical (encoding modulus.size).width).basisEquiv.symm
        ((encoding modulus.size).encode state))) :=
  ((inPlaceForward_nativeProgram_realizes modulus nontrivial).apply_encoded_ket state).trans
    ((inPlaceForward_program_realizes modulus nontrivial).apply_encoded_ket state).symm

/-- The literal list retains the established coprime-domain output and complete retained history. -/
theorem inPlaceForward_nativeProgram_initial (modulus : Nat) (nontrivial : 1 < modulus)
    (input : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus) :
    (nativeProgram modulus nontrivial).applyNormalized
      (NormalizedVector.ket ((QubitLayout.canonical (encoding modulus.size).width).basisEquiv.symm
        ((encoding modulus.size).encode (InitialPortProgram.inputFrame modulus input)))) =
    NormalizedVector.ket ((QubitLayout.canonical (encoding modulus.size).width).basisEquiv.symm
      ((encoding modulus.size).encode (result modulus input.val positive bounded))) :=
  (inPlaceForward_nativeProgram_basis modulus nontrivial _).trans
    (program_initial modulus nontrivial input coprime positive bounded)

/-- All physical events remain in their original order, including port reversal and unloading. -/
theorem inPlaceForward_gates_trace (modulus : Nat) (nontrivial : 1 < modulus) :
    (gates modulus nontrivial).map (event .empty) = (program modulus nontrivial).eventTrace := by
  simp only [gates, List.map_append, CorrectedSchedule.correctedSchedule_gates_trace,
    program, UnitaryCircuit.seq_eventTrace, InitialPortProgram.program,
    Work1Constant.program, OutputPortProgram.program, programList_eventTrace]

/-- The emitted forward has exactly the original chronological native trace. -/
theorem inPlaceForward_nativeProgram_trace (modulus : Nat) (nontrivial : 1 < modulus) :
    (nativeProgram modulus nontrivial).eventTrace = (program modulus nontrivial).eventTrace := by
  rw [nativeProgram, programList_eventTrace, inPlaceForward_gates_trace]

/-- Reversing the whole literal list restores every dirty input label, including all history. -/
theorem inPlaceForward_reverseGates_restore (modulus : Nat) (nontrivial : 1 < modulus)
    (state : Registers modulus.size) :
    stepList (gates modulus nontrivial).reverse (stepList (gates modulus nontrivial) state) =
      state :=
  stepList_reverse_stepList _ _

end

end QuantumAlg.MAU.Inversion.SharedEEA.InPlaceForward
