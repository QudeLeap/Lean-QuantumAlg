/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.LCU.Endpoint
import all QuantumAlg.Primitives.LCU.Endpoint
import all QuantumAlg.Primitives.LCU.Endpoint.Execution

public import QuantumAlg.Primitives.LCU.Construction
public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Core.Execution.Owned.Qubits
import all QuantumAlg.Primitives.LCU.Construction
import all QuantumAlg.Primitives.LCU.Basic
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Unitary.Requirement
import all QuantumAlg.Core.Execution.Owned.Qubits
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Components.Oracle.LCU
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Algorithm.Unitary.Borrowed

/-!
# Complete LCU execution and the original exact projected block

The same placed three-query circuit implements the source LCU operator,
retains the complete supplied input and obeys independent native budgets
[Lin22, hermfunc.tex:531-554]. Its exact projected block keeps the original
nonnegative-coefficient domain, including zero coefficients with positive sum.
-/

namespace QuantumAlg.LinearCombinationOfUnitaries

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution.OwnedQubits

variable {a n : Nat}

/-- Complete Output keeps every supplied system. -/
public lemma algorithm_output_listing (a n : Nat) :
    (algorithm a n).run.output.listing = (context (a + n)).keys := output_listing a n


/-- The complete native circuit solves its independent execution problem and
has the original exact normalized linear-combination block. -/
public lemma lcu_completeContract (V : UnitaryOperator (Qubits a))
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n))
    (α : Fin (2 ^ a) → ℝ) (halpha : ∀ i, 0 ≤ α i) (hlam : 0 < lcuNorm α)
    (hV : ∀ i, V i 0 = ((Real.sqrt (α i / lcuNorm α) : ℝ) : ℂ)) :
    ∃ candidate, Algorithm.Solves (allowAllocation := true) candidate (problem a n) ∧
      ExactBlockEncoding a n ((circuit a n).binaryMatrix (LCUOracle.interpretation V U))
        (((lcuNorm α : ℂ))⁻¹ • lcuCombination α U) := by
  refine ⟨algorithm a n, algorithm_solves a n, ?_⟩
  rw [circuit_matrix]
  exact lcuWalk_exactBlockEncoding V U α halpha hlam hV
end

end QuantumAlg.LinearCombinationOfUnitaries
