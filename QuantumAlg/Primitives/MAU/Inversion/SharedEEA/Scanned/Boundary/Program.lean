/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Boundary.Prefix
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Boundary.Exchange
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Refresh

/-!
# Complete actual scanned terminal boundary with the original full action

The actual predicate, one-Toffoli word exchanges, four scanned length
writes, paid Iter CNOT and literal reversed predicate execute in the
original order. The last predicate toggle remains part of the exact
all-original-label result. Cleanup on reachable selected trajectories
is not asserted for arbitrary unreachable input labels.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.TerminalBoundary

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- All actual boundary instructions remain on the same complete physical frame. -/
def program (width : Nat) (enough : 2 ≤ width.size) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (predicateProgram width enough false).seq
    ((BoundaryExchange.program width).seq
      ((LengthRefresh.program width (capacity width enough)).seq
        ((parityProgram width).seq (predicateProgram width enough true))))

/-- Exact complete original boundary action, with the same pool clean and returned in full. -/
lemma program_apply_source (width : Nat) (enough : 2 ≤ width.size)
    (environment : OracleModel.empty.Interpretation)
    (state : Data width) (prefixZero : state.2.2.1 = 0) (addressZero : state.2.1 = 0)
    (borrowZero : state.2.2.2 = false) :
    (program width enough).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (SharedEEA.TerminalBoundary.step state.1, state.2))) := by
  let toggled : Data width :=
    (NativePredicate.xorControl (BoundaryPredicate.condition state.1) state.1, state.2)
  let exchanged : Data width := (WorkWordExchange.step toggled.1, state.2)
  let refreshed : Data width :=
    (if exchanged.1.control then SharedEEA.LengthRefresh.step exchanged.1 else exchanged.1,
      state.2)
  let iterated : Data width := (SharedEEA.BoundaryExchange.parityStep refreshed.1, state.2)
  let final : Data width :=
    (NativePredicate.xorControl (BoundaryPredicate.condition iterated.1) iterated.1, state.2)
  let ket (value : Data width) := NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
    ((encoding width).encode value))
  have predicateActual :=
    (predicateProgram_realizes width enough false environment).apply_encoded_ket state
  have exchangeActual := (BoundaryExchange.program_realizes width environment).apply_encoded_ket
    toggled
  have refreshActual := LengthRefresh.program_apply_source width (capacity width enough) environment
    exchanged prefixZero addressZero borrowZero (sentinel_fits width enough)
  have parityActual := (parityProgram_realizes width environment).apply_encoded_ket refreshed
  have inverseActual := (predicateProgram_realizes width enough true environment).apply_encoded_ket
    iterated
  change (predicateProgram width enough false).applyNormalized environment (ket state) =
    ket toggled at predicateActual
  change (BoundaryExchange.program width).applyNormalized environment (ket toggled) =
    ket exchanged at exchangeActual
  change (LengthRefresh.program width (capacity width enough)).applyNormalized environment
    (ket exchanged) = ket refreshed at refreshActual
  change (parityProgram width).applyNormalized environment (ket refreshed) =
    ket iterated at parityActual
  change (predicateProgram width enough true).applyNormalized environment (ket iterated) =
    ket final at inverseActual
  change (program width enough).applyNormalized environment (ket state) =
    ket (SharedEEA.TerminalBoundary.step state.1, state.2)
  rw [program, UnitaryCircuit.applyNormalized_seq, predicateActual,
    UnitaryCircuit.applyNormalized_seq, exchangeActual, UnitaryCircuit.applyNormalized_seq,
    refreshActual, UnitaryCircuit.applyNormalized_seq, parityActual, inverseActual]
  rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.TerminalBoundary
