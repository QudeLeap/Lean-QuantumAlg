/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Oracle.Placement
import all QuantumAlg.Core.Base.Oracle.Placement
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding.Operator

/-!
# Applying a declared query instance at actual wire positions

A finite injection selects distinct ambient wires in argument order. Each
selected wire must have the declared dimension. The local layout and its
embedding are derived from these same positions, with no independent operator
or physical-identity claim.
-/

namespace QuantumAlg.OracleModel.Application

/-- Construct the actual local layout and embedding from dimension-correct ambient positions. -/
@[expose]
public def ofPositions (model : OracleModel) (query : model.Query)
    {count : Nat} (layout : QuantumLayout count)
    (position : Fin (model.signature query).systemCount ↪ Fin count)
    (dimensions : ∀ index,
      (layout.wire (position index)).dimension = (model.signature query).dimension index) :
    Application model layout where
  occurrence :=
    { query := query
      placement :=
        { layout :=
            { wire := fun index => layout.wire (position index)
              identityInjective := fun _ _ same =>
                position.injective (layout.identityInjective same) }
          dimension_eq := dimensions } }
  embedding := { position := position, wire_eq := fun _ => rfl }

/-- The placement constructor retains the exact declared instance. -/
public lemma queryApplication_ofPositions_instance
    (model : OracleModel) (query : model.Query)
    {count : Nat} (layout : QuantumLayout count)
    (position : Fin (model.signature query).systemCount ↪ Fin count)
    (dimensions : ∀ index,
      (layout.wire (position index)).dimension = (model.signature query).dimension index) :
    (ofPositions model query layout position dimensions).occurrence.query = query := rfl

/-- The original instance fixes the emitted coordinate after actual placement. -/
public lemma queryApplication_ofPositions_coordinate
    (model : OracleModel) (query : model.Query)
    {count : Nat} (layout : QuantumLayout count)
    (position : Fin (model.signature query).systemCount ↪ Fin count)
    (dimensions : ∀ index,
      (layout.wire (position index)).dimension = (model.signature query).dimension index) :
    (ofPositions model query layout position dimensions).coordinate =
      model.coordinate query := rfl

/-- Apply a granted query to its complete dimension-correct physical placement. -/
@[expose]
public def onPlacement (model : OracleModel) (query : model.Query)
    (placement : (model.signature query).Placement) : Application model placement.layout where
  occurrence := { query := query, placement := placement }
  embedding := { position := Function.Embedding.refl _, wire_eq := fun _ => rfl }

/-- Whole-placement execution retains the exact declaration-owned query coordinate. -/
public lemma queryApplication_onPlacement_coordinate (model : OracleModel) (query : model.Query)
    (placement : (model.signature query).Placement) :
    (onPlacement model query placement).coordinate = model.coordinate query := rfl

/-- Using every physical wire adds no complementary state or extra operator action. -/
public lemma queryApplication_onPlacement_operator (model : OracleModel)
    (environment : Interpretation model) (query : model.Query)
    (placement : (model.signature query).Placement) :
    (onPlacement model query placement).operator environment =
      (⟨query, placement⟩ : Occurrence model).operator environment := by
  let embedding : QuantumLayout.Embedding placement.layout placement.layout :=
    { position := Function.Embedding.refl _, wire_eq := fun _ => rfl }
  let operator : UnitaryOperator placement.layout.register :=
    (⟨query, placement⟩ : Occurrence model).operator environment
  change embedding.liftOperator operator = operator
  apply Subtype.ext
  funext row column
  rw [QuantumLayout.Embedding.liftOperator_entry_of_surjective embedding
    (fun index => ⟨index, rfl⟩)]
  have selected (basis : placement.layout.Basis) : (embedding.splitBasis basis).1 = basis := by
    funext index
    apply Fin.ext
    rfl
  rw [selected, selected]

end QuantumAlg.OracleModel.Application
