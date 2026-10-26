/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Boundary.Program

/-!
# Same actual full terminal body, before adding external predicate selection

The full original-word exchange, all four ordered scanned length writes
and original Ctrl-to-Iter CNOT execute without extra external controls.
Their complete source action returns the same full initialized pool.
When original Ctrl is false every actual component has identity action.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledBoundaryBody

noncomputable section

open NumberTheory.SharedEEA

def program (width : Nat) (enough : 2 ≤ width.size) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (Scanned.encoding width).width).toQuantum :=
  (BoundaryExchange.program width).seq
    ((LengthRefresh.program width (TerminalBoundary.capacity width enough)).seq
      (TerminalBoundary.parityProgram width))

/-- The same full physical body has the complete independent original source action. -/
lemma program_apply_encoded_ket (width : Nat) (enough : 2 ≤ width.size)
    (environment : OracleModel.empty.Interpretation) (state : Scanned.Data width)
    (prefixZero : state.2.2.1 = 0) (addressZero : state.2.1 = 0)
    (borrowZero : state.2.2.2 = false) :
    (program width enough).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((Scanned.encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((Scanned.encoding width).encode (SharedEEA.TerminalBoundary.body state.1, state.2))) := by
  let exchanged : Scanned.Data width := (WorkWordExchange.step state.1, state.2)
  let refreshed : Scanned.Data width :=
    (if exchanged.1.control then SharedEEA.LengthRefresh.step exchanged.1 else exchanged.1,
      state.2)
  have first := (BoundaryExchange.program_realizes width environment).apply_encoded_ket state
  have second := LengthRefresh.program_apply_source width (TerminalBoundary.capacity width enough)
    environment exchanged prefixZero addressZero borrowZero
    (TerminalBoundary.sentinel_fits width enough)
  have third := (TerminalBoundary.parityProgram_realizes width environment).apply_encoded_ket
    refreshed
  have actual := UnitaryCircuit.applyNormalized_seq_of_eq first
    (UnitaryCircuit.applyNormalized_seq_of_eq second third)
  exact actual

/-- Inactive original Ctrl restores all original finite fields, including zero input and Iter. -/
lemma source_disabled {width : Nat} (state : Registers width) (control : state.control = false) :
    SharedEEA.TerminalBoundary.body state = state :=
  SharedEEA.TerminalBoundary.body_false state control

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledBoundaryBody
