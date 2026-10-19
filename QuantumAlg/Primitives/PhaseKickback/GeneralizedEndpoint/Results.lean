/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.PhaseKickback.GeneralizedEndpoint
import all QuantumAlg.Primitives.PhaseKickback.GeneralizedEndpoint
import all QuantumAlg.Primitives.PhaseKickback.GeneralizedEndpoint.Execution

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
# Complete eigenvalue phase kickback

The actual query has an independent full-operator target and a complete
supplied register. The original exact phase identity is retained alongside
the common execution contract.
-/

namespace QuantumAlg.GeneralizedPhaseKickback

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution.OwnedQubits NormalizedVector

variable {n : Nat}

/-- Complete Output keeps every supplied system. -/
public lemma algorithm_output_listing (n : Nat) :
    (algorithm n).run.output.listing = (context (1 + n)).keys := output_listing n


/-- The actual complete query solves its independent execution problem and
preserves the original exact phase-kickback identity [CEMM98, cemm6.tex:140-166]. -/
public lemma generalizedPhaseKickback_completeContract (U : UnitaryOperator (Qubits n))
    (u : NormalizedVector (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      Complex.exp (θ * Complex.I) • (u : HilbertVector (Qubits n))) (a b : ℂ) :
    ∃ candidate, Algorithm.Solves (allowAllocation := true) candidate (problem n) ∧
    (UnitaryOperator.controlledQubits U).applyVec
        (HilbertVector.tensor
          ((a • ket0 + b • ket1 : HilbertVector (Qubits 1))) (u : HilbertVector (Qubits n)))
      =
      HilbertVector.tensor
        ((a • ket0 + (Complex.exp (θ * Complex.I) * b) • ket1 : HilbertVector (Qubits 1)))
        (u : HilbertVector (Qubits n)) := by
  exact ⟨algorithm n, algorithm_solves n, eigenvalue_action U u θ hu a b⟩
end

end QuantumAlg.GeneralizedPhaseKickback
