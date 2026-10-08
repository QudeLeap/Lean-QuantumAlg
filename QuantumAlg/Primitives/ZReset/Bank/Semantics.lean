/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ZReset.Bank
import all QuantumAlg.Primitives.ZReset.Sequence.Frame

/-!
# Reusing the same bank while preserving earlier classical observations

The bank's constructed wire enumeration satisfies complete reset coverage.
Its one scratch key determines exactly which classical reads can be retained
unchanged. The actual final quantum register is zero within each retained
classical-reference block, including arbitrary initial entanglement and
classical correlations. No initial zero state or independent-state premise
is needed. The scratch result and all physical systems remain live.
-/

namespace QuantumAlg.ZReset.Bank

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {ctx : RuntimeCtx .quantum} {oracles : OracleModel}

/-- Every actual bank reset produces zero with the unchanged complete reference marginal. -/
theorem zResetBank_complete_entry (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference
      ((ExecutionModel.quantum AlgorithmGate.model oracles).HiddenState × History))
    (left right : ctx.quantumLayout.Basis)
    (leftRef rightRef : Reference.Index) :
    ((code (oracles := oracles) qubits scratch).execute Reference state).quantumMarginal.matrix
        (left, leftRef) (right, rightRef) =
      if left = ctx.quantumLayout.zeroLabel ∧ right = ctx.quantumLayout.zeroLabel then
        ∑ basis : ctx.register.Index,
          state.quantumMarginal.matrix (basis, leftRef) (basis, rightRef)
      else 0 :=
  zReset_sequence_complete_entry (implementations (oracles := oracles) qubits)
    (readouts qubits scratch)
    (zResetBank_readouts_cover qubits scratch) state left right leftRef rightRef

/-- The bank becomes zero separately within every observation avoiding the real scratch key. -/
theorem zResetBank_complete_read_entry (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2)) {shape : CShape}
    (observed : CInputRef ctx shape) (separate : scratch.key ∉ observed.storageKeys)
    (value : shape.Value) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference
      ((ExecutionModel.quantum AlgorithmGate.model oracles).HiddenState × History))
    (left right : ctx.quantumLayout.Basis)
    (leftRef rightRef : Reference.Index) :
    (((code (oracles := oracles) qubits scratch).execute Reference state).filterClassical
      (fun entry => entry.1.read observed = value)).quantumMarginal.matrix
        (left, leftRef) (right, rightRef) =
      if left = ctx.quantumLayout.zeroLabel ∧ right = ctx.quantumLayout.zeroLabel then
        ∑ basis : ctx.register.Index,
          (state.filterClassical
            (fun entry => entry.1.read observed = value)).quantumMarginal.matrix
            (basis, leftRef) (basis, rightRef)
      else 0 := by
  exact zReset_sequence_complete_read_entry
    (implementations (oracles := oracles) qubits) (readouts qubits scratch)
    (zResetBank_readouts_cover qubits scratch) observed
    (fun item present => by
      rw [zResetBank_readouts_key qubits scratch item present]
      exact separate)
    value state left right leftRef rightRef

end

end QuantumAlg.ZReset.Bank
