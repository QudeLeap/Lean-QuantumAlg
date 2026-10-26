/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Predicate
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Guard.Phase

/-!
# Actual externally selected small arithmetic phase word

Only the literal original-field phase predicate receives the native
external control. Its full source support excludes the supplied C/W
suffix by construction, including gates that use arbitrary original
Iter or original Ctrl. Full geometry validity and heavy arithmetic
remain separate actual circuits; this producer grants no free action.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledArithmeticPhase

noncomputable section

open EncodedBit ControlledFrame

/-- Same original small predicate word with a full-support-certified actual native control. -/
def program (width : Nat) (signed coefficient : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ControlledFrame.encoding width).width).toQuantum :=
  ExternalWord.program (Scanned.encoding width) (ArithmeticGuard.gates width signed coefficient)

/-- Independent original phase/Iter predicate selected by the real retained external bit. -/
def step (width : Nat) (signed coefficient : Bool) : ControlledFrame.Data width →
    ControlledFrame.Data width :=
  predicateFlip (ControlledFrame.sourceBit width (ArithmeticGuard.flag width 4))
    (fun state => state.2.1 && (ArithmeticGuard.condition width signed coefficient state.1 &&
      (ArithmeticGuard.flag width 3).get state.1))

private lemma gates_step (width : Nat) (signed coefficient : Bool)
    (state : ControlledFrame.Data width) :
    GateSpec.stepList (ExternalWord.gates (Scanned.encoding width)
        (ArithmeticGuard.gates width signed coefficient)) state =
      step width signed coefficient state := by
  rw [ExternalWord.gates_step, ExternalWord.step, ArithmeticGuard.gates_step]
  rw [step, ControlledFrame.selected_predicateFlip width (ArithmeticGuard.flag width 4)
    (fun source => ArithmeticGuard.condition width signed coefficient source &&
      (ArithmeticGuard.flag width 3).get source) state]
  rfl

/-- Every source label and arbitrary external work amplitude follows this same native word. -/
lemma program_realizes (width : Nat) (signed coefficient : Bool)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (ControlledFrame.encoding width)
      (program width signed coefficient) environment (step width signed coefficient) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (gates_step width signed coefficient) environment

/-- Inactive execution is full identity, including zero input and arbitrary original history. -/
lemma step_disabled (width : Nat) (signed coefficient : Bool)
    (state : ControlledFrame.Data width) (disabled : state.2.1 = false) :
    step width signed coefficient state = state := by
  simp only [step, predicateFlip, disabled, Bool.false_and, Bool.false_eq_true, if_false]

/-- Actual selection retains both the supplied control and its arbitrary lowering work. -/
lemma step_external (width : Nat) (signed coefficient : Bool)
    (state : ControlledFrame.Data width) : (step width signed coefficient state).2 = state.2 := by
  rw [step, ControlledFrame.selected_predicateFlip width (ArithmeticGuard.flag width 4)
    (fun source => ArithmeticGuard.condition width signed coefficient source &&
      (ArithmeticGuard.flag width 3).get source) state]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledArithmeticPhase
