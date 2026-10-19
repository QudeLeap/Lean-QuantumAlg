/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Terminal.Predicate
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Phase.Gates

/-!
# Actual zero-shift phase complements with inverse predicate cleanup

The source complements both phase bits when the retained shift counter is
zero, after its ordered phase update [LYL+26, sec_EEA/sub_opt.tex:74-79].
The program below computes that zero predicate into the existing Ctrl,
executes the two declared phase CNOT gates, and reverses the complete
predicate gate list. Both arbitrary shared words and the old Ctrl are
restored exactly. Every event in both predicate passes is retained.

The complete register law holds for arbitrary Ctrl. The source-specific
formula uses the zero value established by internal initialization, not
an extra condition on the eventual EEA input. The actual predicate tests the original low
counter while divisor length is positive, and the complete existing-wire
clock after termination. Active Work1 padding is not assumed to be zero.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ZeroShiftControl

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit NativePredicate

/-- Full-register action, preserving Ctrl while using its computed predicate xor. -/
def step {width : Nat} (state : Registers width) : Registers width :=
  { state with flags :=
      ⟨if state.control ^^ TerminalPredicate.condition state then !state.flags.first
          else state.flags.first,
        if state.control ^^ TerminalPredicate.condition state then !state.flags.second
          else state.flags.second,
        state.flags.sign, state.flags.iteration⟩ }

private lemma condition_step {width : Nat} (state : Registers width) :
    TerminalPredicate.condition (step state) = TerminalPredicate.condition state := rfl

private lemma complement_computed {width : Nat} (state : Registers width) :
    PhaseGates.complementStep (xorControl (TerminalPredicate.condition state) state) =
      xorControl (TerminalPredicate.condition state) (step state) := rfl

/-- The actual compute/use/uncompute list, including both physical phase CNOTs. -/
def gates (width : Nat) (enough : 2 ≤ width.size) : List (GateSpec (encoding width)) :=
  TerminalPredicate.gates width enough ++ PhaseGates.complementGates width ++
    (TerminalPredicate.gates width enough).reverse

/-- Complete native-list semantics, including every non-target bit and the original Ctrl. -/
lemma gates_step (width : Nat) (enough : 2 ≤ width.size) (state : Registers width) :
    GateSpec.stepList (gates width enough) state = step state := by
  rw [gates, GateSpec.stepList_append, GateSpec.stepList_append, TerminalPredicate.gates_step,
    PhaseGates.complementGates_step, complement_computed, TerminalPredicate.reverse_step,
    TerminalPredicate.condition_xorControl, condition_step, xorControl_twice]

/-- Ctrl is restored for all frames, including ones with a nonzero incoming value. -/
lemma gates_control (width : Nat) (enough : 2 ≤ width.size) (state : Registers width) :
    (GateSpec.stepList (gates width enough) state).control = state.control := by
  rw [gates_step]
  rfl

/-- The literal source phase complements leave the sign and iteration parity unchanged. -/
def sourceStep {width : Nat} (state : Registers width) : Registers width :=
  { state with flags :=
      ⟨if TerminalPredicate.condition state then !state.flags.first else state.flags.first,
        if TerminalPredicate.condition state then !state.flags.second else state.flags.second,
        state.flags.sign, state.flags.iteration⟩ }

/-- The initialized Ctrl invariant specializes the complete native action to the source. -/
lemma step_eq_sourceStep {width : Nat} (state : Registers width)
    (preparedControl : state.control = false) : step state = sourceStep state := by
  simp only [step, preparedControl, Bool.false_xor, sourceStep]

/-- Compile precisely the same actual list whose full-register action is proved above. -/
def program (width : Nat) (enough : 2 ≤ width.size) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (gates width enough)

/-- Exact basis-vector action of the actual native circuit, without losing relative phases. -/
lemma program_realizes (width : Nat) (enough : 2 ≤ width.size) :
    UnitaryCircuit.Realizes (encoding width) (program width enough) environment step :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty
    (gates width enough) (gates_step width enough) environment

/-- The actual native circuit implements the source operation on internally prepared frames. -/
lemma program_apply_prepared (width : Nat) (enough : 2 ≤ width.size)
    (state : Registers width) (preparedControl : state.control = false) :
    (program width enough).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (sourceStep state))) := by
  rw [(program_realizes width enough).apply_encoded_ket, step_eq_sourceStep state preparedControl]

/-- The exact event trace includes the forward predicate, two CNOTs, and reversed predicate. -/
lemma program_eventTrace (width : Nat) (enough : 2 ≤ width.size) :
    (program width enough).eventTrace =
      (TerminalPredicate.gates width enough).map (GateSpec.event .empty) ++
        [.gate .cnot, .gate .cnot] ++
          ((TerminalPredicate.gates width enough).map (GateSpec.event .empty)).reverse := by
  rw [program, GateSpec.programList_eventTrace]
  simp only [gates, List.map_append, List.map_reverse]
  rfl

/-- Count both full predicate passes and both actual phase gates, regardless of their input. -/
lemma gates_length (width : Nat) (enough : 2 ≤ width.size) :
    (gates width enough).length = 2 * (TerminalPredicate.gates width enough).length + 2 := by
  have phaseCount : (PhaseGates.complementGates width).length = 2 := rfl
  simp only [gates, List.length_append, List.length_reverse, phaseCount]
  omega

lemma program_eventCost_card (width : Nat) (enough : 2 ≤ width.size) :
    (program width enough).eventCost.card =
      2 * (TerminalPredicate.gates width enough).length + 2 := by
  rw [program, GateSpec.programList_eventCost_card, gates_length]

lemma program_unitDepth (width : Nat) (enough : 2 ≤ width.size) :
    (program width enough).evaluatedEventDepth (fun _ => 1) =
      2 * (TerminalPredicate.gates width enough).length + 2 := by
  rw [program, GateSpec.programList_evaluatedEventDepth_unit, gates_length]

end

end QuantumAlg.MAU.Inversion.SharedEEA.ZeroShiftControl
