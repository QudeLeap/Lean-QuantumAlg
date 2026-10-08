/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Placement.Entries
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement.Entries
import all QuantumAlg.Core.Base.UnitaryCircuit.Realization
import all QuantumAlg.Core.Base.Gate.Placement
import all QuantumAlg.Core.Base.Gate.Model
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.Control.Operator

/-!
# Placing exact local token implementations at their original occurrences

A canonical local construction is moved to the argument positions of the
original application. The coordinate casts preserve all local basis values;
every complementary physical system retains its identity action.
-/

namespace QuantumAlg.UnitaryCircuit
noncomputable section

variable {sourceGates targetGates : GateModel} {oracles : OracleModel}
variable {count : Nat} {ambient : QuantumLayout count}

/-- Original placement certifies the dimensions required to relocate a local native word. -/
public theorem nativeDimensions (application : GateModel.Application sourceGates ambient) :
    ∀ index,
      (((sourceGates.signature application.occurrence.token).canonicalPlacement.layout).wire
        index).dimension = (ambient.wire (application.embedding.position index)).dimension := by
  intro index
  rw [application.embedding.wire_eq]
  exact (application.occurrence.placement.dimension_eq index).symm

/-- Canonical placement of the model operator agrees with the full original application. -/
public theorem nativeApplication_operatorAt
    (application : GateModel.Application sourceGates ambient) :
    operatorAt (sourceGates.signature application.occurrence.token).canonicalPlacement.layout
      ambient application.embedding.position (nativeDimensions application)
      (sourceGates.operator application.occurrence.token) = application.operator := by
  apply Subtype.ext
  ext row column
  rw [operatorAt_entry, GateModel.Application.application_operator_entry]
  have selected (basis : ambient.Basis) :
      selectedInput (sourceGates.signature application.occurrence.token).canonicalPlacement.layout
        ambient application.embedding.position (nativeDimensions application) basis =
      application.occurrence.placement.indexEquiv
        (application.embedding.splitBasis basis).1 := by
    funext index
    apply Fin.ext
    rfl
  rw [selected row, selected column]
  rfl

/-- Execute a certified local word at exactly the original occurrence's physical positions. -/
public def realizeNativeApplication (application : GateModel.Application sourceGates ambient)
    (localWord : ExactRealization targetGates oracles
      (sourceGates.signature application.occurrence.token).canonicalPlacement.layout
      (sourceGates.operator application.occurrence.token)) :
    ExactRealization targetGates oracles ambient application.operator where
  circuit := placeAt
    (sourceGates.signature application.occurrence.token).canonicalPlacement.layout
    ambient application.embedding.position (nativeDimensions application) localWord.circuit
  matrix_eq := by
    rw [placeAt_matrix, localWord.matrix_eq, nativeApplication_operatorAt]

end
end QuantumAlg.UnitaryCircuit
