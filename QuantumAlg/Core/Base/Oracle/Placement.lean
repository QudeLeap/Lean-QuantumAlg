/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Oracle.Model
import all QuantumAlg.Core.Base.Oracle.Model
public import QuantumAlg.Core.Base.Layout.Quantum.Embedding
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding
import all QuantumAlg.Core.Base.Layout.Quantum.Selection
import all QuantumAlg.Core.Base.Control.Operator
public import QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Applying declared queries to actual ambient wires

An application embeds the occurrence's own physical wires in the ambient
layout. Its operator acts on those ordered wires and tensors with identity on
their full complement. The embedding does not supply an arbitrary basis change.
-/

namespace QuantumAlg.OracleModel

/-- A granted query occurrence on exactly the selected physical wires of an ambient layout. -/
public structure Application (model : OracleModel) {count : Nat}
    (layout : QuantumLayout count) where
  /-- The actual token and its dimension-correct physical placement. -/
  occurrence : Occurrence model
  /-- These same physical wires occur at the selected ambient positions. -/
  embedding : QuantumLayout.Embedding occurrence.placement.layout layout

namespace Application

variable {model : OracleModel} {count : Nat} {layout : QuantumLayout count}

/-- The query event coordinate remains fixed by the original query instance. -/
@[expose]
public def coordinate (application : Application model layout) : model.Coordinate :=
  application.occurrence.coordinate

/-- Act on the selected systems and preserve the complete complementary subsystem. -/
@[expose]
public noncomputable def operator (application : Application model layout) :
    UnitaryOperator layout.register :=
  UnitaryOperator.reindex application.embedding.splitBasis.symm
    (UnitaryOperator.prodTensor application.occurrence.operator
      (1 : UnitaryOperator (layout.complementRegister application.embedding.selection)))

/-- Query accounting cannot be detached from the applied query instance. -/
public theorem oracle_application_coordinate (application : Application model layout) :
    application.coordinate = model.coordinate application.occurrence.query := rfl

/-- Application retains the original physical identity at every gate argument. -/
public theorem oracle_application_wire_identity (application : Application model layout)
    (index : Fin (model.signature application.occurrence.query).systemCount) :
    (layout.wire (application.embedding.position index)).identity =
      (application.occurrence.placement.layout.wire index).identity :=
  congrArg QuantumWire.identity (application.embedding.wire_eq index)

/-- Each matrix entry factors through the actual query and identity on its full complement. -/
public theorem oracle_application_operator_entry (application : Application model layout)
    (row column : layout.Basis) :
    application.operator row column =
      application.occurrence.operator
        (application.embedding.splitBasis row).1
        (application.embedding.splitBasis column).1 *
      (if (application.embedding.splitBasis row).2 =
          (application.embedding.splitBasis column).2 then 1 else 0) := by
  change UnitaryOperator.prodTensor application.occurrence.operator
    (1 : UnitaryOperator (layout.complementRegister application.embedding.selection))
    (application.embedding.splitBasis row) (application.embedding.splitBasis column) = _
  rw [UnitaryOperator.unitaryOperator_prodTensor_apply]
  rfl

end Application

end QuantumAlg.OracleModel
