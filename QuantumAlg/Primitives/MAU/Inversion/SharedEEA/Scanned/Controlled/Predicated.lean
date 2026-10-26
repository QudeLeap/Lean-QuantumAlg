/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.SourceWord

/-!
# Actual predicate preparation with only its small payload externally selected

The original preparation and its complete literal inverse execute in
both branches. The actual native selected middle word retains C/W.
Inactive execution is identity by the same native source-word inverse,
without any incoming source or pool initialization premise.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledPredicated

noncomputable section

open EncodedBit

def gates (width : Nat) (prepare middle : List (GateSpec (SharedEEA.encoding width))) :
    List (GateSpec (ControlledFrame.encoding width)) :=
  ControlledSourceWord.liftedGates width prepare ++
    ControlledSourceWord.selectedGates width middle ++
    ControlledSourceWord.liftedGates width prepare.reverse

def step (width : Nat) (prepare middle : List (GateSpec (SharedEEA.encoding width)))
    (state : ControlledFrame.Data width) : ControlledFrame.Data width :=
  ((if state.2.1 then GateSpec.stepList (prepare ++ middle ++ prepare.reverse) state.1.1
    else state.1.1, state.1.2), state.2)

private lemma gates_step (width : Nat) (prepare middle : List (GateSpec (SharedEEA.encoding width)))
    (state : ControlledFrame.Data width) :
    GateSpec.stepList (gates width prepare middle) state = step width prepare middle state := by
  simp only [gates, GateSpec.stepList_append, ControlledSourceWord.liftedGates_step,
    ControlledSourceWord.selectedGates_step]
  cases selected : state.2.1 with
  | false =>
      simp only [selected, Bool.false_eq_true, if_false, step]
      exact congrArg (fun source => ((source, state.1.2), state.2))
        (GateSpec.stepList_reverse_stepList prepare state.1.1)
  | true =>
      simp only [selected, ↓reduceIte, step, GateSpec.stepList_append]

def program (width : Nat) (prepare middle : List (GateSpec (SharedEEA.encoding width))) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ControlledFrame.encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (gates width prepare middle)

/-- All-label native semantics keep the same full prefix, original pool and external work. -/
lemma program_realizes (width : Nat) (prepare middle : List (GateSpec (SharedEEA.encoding width)))
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (ControlledFrame.encoding width) (program width prepare middle)
      environment (step width prepare middle) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (gates_step width prepare middle) environment

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledPredicated
