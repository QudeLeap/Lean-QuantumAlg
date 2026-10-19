/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Core.Base.UnitaryCircuit.Refinement
import all QuantumAlg.Core.Base.UnitaryCircuit.Refinement
import all QuantumAlg.Core.Base.UnitaryCircuit.Realization.Native
import all QuantumAlg.Components.Gates.Toffoli.Semantics
import all QuantumAlg.Components.Gates.Toffoli.Resources
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Gate.Placement
import all QuantumAlg.Core.Base.Oracle.Placement

/-!
# Replacing actual Toffoli occurrences by one- and two-qubit words

Every Toffoli expands on the original three physical systems. CNOT and arbitrary
one-qubit applications retain their original tokens and placements. Queries are
copied as granted, with no inferred control or inverse access.
-/

namespace QuantumAlg.Gate.Toffoli
noncomputable section

/-- Expand a Toffoli application and retain each other native gate exactly as applied. -/
public def nativeExpansion (oracles : OracleModel) {count : Nat} {ambient : QuantumLayout count}
    (application : GateModel.Application AlgorithmGate.model ambient) :
    UnitaryCircuit.ExactRealization AlgorithmGate.model oracles ambient (fun _
      => application.operator) := by
  rcases application with ⟨⟨token, placement⟩, embedding⟩
  cases token with
  | toffoli =>
      exact UnitaryCircuit.realizeNativeApplication
        (sourceGates := AlgorithmGate.model) (targetGates := AlgorithmGate.model)
        (oracles := oracles) ⟨⟨.toffoli, placement⟩, embedding⟩ (realization oracles)
  | cnot =>
      exact ⟨UnitaryCircuit.native ⟨⟨.cnot, placement⟩, embedding⟩,
        fun environment => UnitaryCircuit.native_matrix environment _⟩
  | singleQubit operator =>
      exact ⟨UnitaryCircuit.native ⟨⟨.singleQubit operator, placement⟩, embedding⟩,
        fun environment => UnitaryCircuit.native_matrix environment _⟩

/-- The substitution uses exactly the original oracle applications and access model. -/
public def expansionInstructions (oracles : OracleModel) :
    UnitaryCircuit.InstructionRealizations AlgorithmGate.model oracles AlgorithmGate.model oracles
      where
  interpretation := id
  native := nativeExpansion oracles
  query application := ⟨UnitaryCircuit.query application,
    fun environment => UnitaryCircuit.query_matrix environment application⟩

/-- Expand all Toffoli occurrences throughout the actual circuit construction. -/
public def expand {oracles : OracleModel} {count : Nat} {ambient : QuantumLayout count}
    (source : UnitaryCircuit AlgorithmGate.model oracles ambient) :
    UnitaryCircuit AlgorithmGate.model oracles ambient :=
  source.refine (expansionInstructions oracles)

/-- The expanded circuit has exactly the source operator on the same full physical layout. -/
public lemma toffoliExpansion_preserves_matrix {oracles : OracleModel} {count : Nat}
    {ambient : QuantumLayout count} (source : UnitaryCircuit AlgorithmGate.model oracles ambient)
      (environment : oracles.Interpretation) :
    ((expand source).matrix environment) = (source.matrix environment) :=
  UnitaryCircuit.refine_matrix source (expansionInstructions oracles) environment

end
end QuantumAlg.Gate.Toffoli
