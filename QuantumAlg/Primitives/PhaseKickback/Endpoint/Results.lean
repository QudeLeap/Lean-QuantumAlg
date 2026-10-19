/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.PhaseKickback.Endpoint
import all QuantumAlg.Primitives.PhaseKickback.Endpoint
import all QuantumAlg.Primitives.PhaseKickback.Endpoint.Execution

public import QuantumAlg.Primitives.PhaseKickback.Construction
public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Core.Execution.Owned.Qubits
import all QuantumAlg.Primitives.PhaseKickback.Construction
import all QuantumAlg.Primitives.PhaseKickback.Basic
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Unitary.Requirement
import all QuantumAlg.Core.Execution.Owned.Qubits
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Algorithm.Unitary.Borrowed

/-!
# Complete XOR-oracle phase kickback

The actual query has an independent full-operator target and a complete
supplied register. The original exact phase identity is retained alongside
the common execution contract.
-/

namespace QuantumAlg.PhaseKickback

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution.OwnedQubits NormalizedVector

variable {n : Nat}

/-- Complete Output keeps every supplied system. -/
public lemma algorithm_output_listing (n : Nat) :
    (algorithm n).run.output.listing = (context (n + 1)).keys := output_listing n


/-- The actual complete query solves its independent execution problem and
preserves the original exact phase-kickback identity [dW19, qcnotes.tex:1145-1173]. -/
public lemma phaseKickback_completeContract (f : Fin (2 ^ n) → Bool) (x : Fin (2 ^ n)) :
    ∃ candidate, Algorithm.Solves (allowAllocation := true) candidate (problem n) ∧
    (xorOracleOp f).applyVec
        (((ket x : NormalizedVector (Qubits n)).tensor ketMinus :
          NormalizedVector (Qubits (n + 1))) : HilbertVector (Qubits (n + 1)))
      = (if f x then (-1 : ℂ) else 1)
          • (((ket x : NormalizedVector (Qubits n)).tensor ketMinus :
              NormalizedVector (Qubits (n + 1))) : HilbertVector (Qubits (n + 1))) := by
  exact ⟨algorithm n, algorithm_solves n, xor_action f x⟩
end

end QuantumAlg.PhaseKickback
