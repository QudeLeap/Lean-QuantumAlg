/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Gate.Placement
import all QuantumAlg.Core.Base.Gate.Placement

/-!
# Applying a declared gate instance at actual wire positions

A finite injection selects distinct ambient wires in argument order. Each
selected wire must have the declared dimension. The local layout and its
embedding are derived from these same positions, with no independent operator
or physical-identity claim.
-/

namespace QuantumAlg.GateModel.Application

/-- Construct the actual local layout and embedding from dimension-correct ambient positions. -/
@[expose]
public def ofPositions (model : GateModel) (token : model.Token)
    {count : Nat} (layout : QuantumLayout count)
    (position : Fin (model.signature token).systemCount ↪ Fin count)
    (dimensions : ∀ index,
      (layout.wire (position index)).dimension = (model.signature token).dimension index) :
    Application model layout where
  occurrence :=
    { token := token
      placement :=
        { layout :=
            { wire := fun index => layout.wire (position index)
              identityInjective := fun _ _ same =>
                position.injective (layout.identityInjective same) }
          dimension_eq := dimensions } }
  embedding := { position := position, wire_eq := fun _ => rfl }

/-- The placement constructor retains the exact declared instance. -/
public theorem gateApplication_ofPositions_instance
    (model : GateModel) (token : model.Token)
    {count : Nat} (layout : QuantumLayout count)
    (position : Fin (model.signature token).systemCount ↪ Fin count)
    (dimensions : ∀ index,
      (layout.wire (position index)).dimension = (model.signature token).dimension index) :
    (ofPositions model token layout position dimensions).occurrence.token = token := rfl

/-- The original instance fixes the emitted coordinate after actual placement. -/
public theorem gateApplication_ofPositions_coordinate
    (model : GateModel) (token : model.Token)
    {count : Nat} (layout : QuantumLayout count)
    (position : Fin (model.signature token).systemCount ↪ Fin count)
    (dimensions : ∀ index,
      (layout.wire (position index)).dimension = (model.signature token).dimension index) :
    (ofPositions model token layout position dimensions).coordinate =
      model.coordinate token := rfl

end QuantumAlg.GateModel.Application
