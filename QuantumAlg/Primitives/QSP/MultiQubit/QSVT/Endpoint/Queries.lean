/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Endpoint.Real
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Endpoint.Complex
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Endpoint.Real
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Endpoint.Complex
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Queries
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Real
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Complex

/-!
# Explicit source-query counts of the complete Hermitian endpoints

The public existence theorems identify the actual word's event pool with its
independent problem budget. These lemmas expose the source-access consequences
of that same equality, without an additional query-accounting witness.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Witness
noncomputable section

namespace HermitianRealParity

variable {m n L : Nat}
  (word : UnitaryCircuit AlgorithmGate.model (UnitarySource.model (m + n) false true false)
    (UnitaryExecution.Owned.Binary.layout ((1 + m) + n)))
  (cost : word.eventCost = Execution.realBudget m n L)

include cost

/-- Actual source access obtained from the complete endpoint event equality. -/
public lemma realEndpoint_source_queries :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) false true false))
      (.oracle UnitarySource.Coordinate.ordinary) word.eventCost +
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) false true false))
      (.oracle UnitarySource.Coordinate.inverse) word.eventCost = L := by
  rw [cost]
  exact Execution.realBudget_source_queries m n L

/-- Actual source access obtained from the complete endpoint event equality. -/
public lemma realEndpoint_controlled_queries :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) false true false))
      (.oracle UnitarySource.Coordinate.controlled) word.eventCost = 0 := by
  rw [cost]
  exact Execution.realBudget_controlled_queries m n L

/-- Actual source access obtained from the complete endpoint event equality. -/
public lemma realEndpoint_controlled_inverse_queries :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) false true false))
      (.oracle UnitarySource.Coordinate.controlledInverse) word.eventCost = 0 := by
  rw [cost]
  exact Execution.realBudget_controlled_inverse_queries m n L

end HermitianRealParity

namespace HermitianComplex

variable {m n L a : Nat}
  (word : UnitaryCircuit AlgorithmGate.model (UnitarySource.model (m + n) true true false)
    (UnitaryExecution.Owned.Binary.layout (a + n)))
  (cost : word.eventCost = Execution.complexBudget m n L)

include cost

/-- Actual source access obtained from the complete endpoint event equality. -/
public lemma complexEndpoint_source_queries :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) true true false))
      (.oracle UnitarySource.Coordinate.ordinary) word.eventCost +
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) true true false))
      (.oracle UnitarySource.Coordinate.inverse) word.eventCost ≤ L := by
  rw [cost]
  exact Execution.complexBudget_source_queries m n L

/-- Actual source access obtained from the complete endpoint event equality. -/
public lemma complexEndpoint_controlled_queries :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) true true false))
      (.oracle UnitarySource.Coordinate.controlled) word.eventCost = if L = 0 then 0 else 1 := by
  rw [cost]
  exact Execution.complexBudget_controlled_queries m n L

/-- Actual source access obtained from the complete endpoint event equality. -/
public lemma complexEndpoint_controlled_inverse_queries :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) true true false))
      (.oracle UnitarySource.Coordinate.controlledInverse) word.eventCost = 0 := by
  rw [cost]
  exact Execution.complexBudget_controlled_inverse_queries m n L

end HermitianComplex

end
end QuantumAlg.QSP.MultiQubit.QSVT.Witness
