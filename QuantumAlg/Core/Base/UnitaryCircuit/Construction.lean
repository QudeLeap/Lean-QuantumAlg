/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Sequence
import all QuantumAlg.Core.Base.UnitaryCircuit.Sequence

/-!
# Constructing circuits in a selected physical operation language

A circuit contains only its actual construction tree. Its type fixes the gate
model, granted oracle access and full physical layout. Every constructor keeps
those indices coherent; parallel execution additionally requires disjoint
physical subsystems. Operators and resource projections are not input fields.
-/

namespace QuantumAlg

/-- One model-relative construction on a fixed physical layout. -/
public structure UnitaryCircuit (gates : GateModel) (oracles : OracleModel)
    {count : Nat} (layout : QuantumLayout count) where
  private mk ::
  /-- The actual construction tree, observable without supplying separate semantics or costs. -/
  sequence : UnitarySequence gates oracles layout

namespace UnitaryCircuit

variable {gates : GateModel} {oracles : OracleModel}
variable {count : Nat} {layout : QuantumLayout count}

/-- Execute the zero-event identity on the complete supplied layout. -/
public def identity (gates : GateModel) (oracles : OracleModel) {count : Nat}
    (layout : QuantumLayout count) : UnitaryCircuit gates oracles layout :=
  ⟨.id layout⟩

/-- Execute one model-owned native or query application. -/
public def ofLeaf (leaf : UnitaryLeaf gates oracles layout) :
    UnitaryCircuit gates oracles layout := ⟨.leaf leaf⟩

/-- Execute a native token on its certified physical placement. -/
public def native (application : GateModel.Application gates layout) :
    UnitaryCircuit gates oracles layout := ofLeaf (.gate application)

/-- Execute only a query value granted by the selected oracle declaration. -/
public def query (application : OracleModel.Application oracles layout) :
    UnitaryCircuit gates oracles layout := ofLeaf (.oracle application)

/-- Sequential composition keeps the same language and actual physical systems. -/
public def seq (left right : UnitaryCircuit gates oracles layout) :
    UnitaryCircuit gates oracles layout := ⟨.seq left.sequence right.sequence⟩

/-- Extend an actual construction by identity on every complementary wire. -/
public def embed {small large : Nat} {source : QuantumLayout small}
    {target : QuantumLayout large} (placement : QuantumLayout.Embedding source target)
    (body : UnitaryCircuit gates oracles source) : UnitaryCircuit gates oracles target :=
  ⟨.embed placement body.sequence⟩

/-- Execute two constructions in parallel on certified disjoint physical subsystems. -/
public def parallel {leftCount rightCount count : Nat}
    {leftLayout : QuantumLayout leftCount} {rightLayout : QuantumLayout rightCount}
    {layout : QuantumLayout count} (left : UnitaryCircuit gates oracles leftLayout)
    (right : UnitaryCircuit gates oracles rightLayout)
    (leftPlacement : QuantumLayout.Embedding leftLayout layout)
    (rightPlacement : QuantumLayout.Embedding rightLayout layout)
    (disjoint : Disjoint leftPlacement.selection rightPlacement.selection) :
    UnitaryCircuit gates oracles layout :=
  ⟨.parallel left.sequence right.sequence leftPlacement rightPlacement disjoint⟩

/-- Repeat exactly the actual construction, retaining the same physical workspace. -/
public def iterate (repetitions : Nat) (body : UnitaryCircuit gates oracles layout) :
    UnitaryCircuit gates oracles layout := ⟨.iterate repetitions body.sequence⟩

/-- Execute a finite list of constructions in the listed order. -/
public def sequenceList (start : UnitaryCircuit gates oracles layout)
    (steps : List (UnitaryCircuit gates oracles layout)) :
    UnitaryCircuit gates oracles layout := steps.foldl seq start

/-- Execute the start and each indexed step; the label only describes the construction. -/
public def indexedProduct (label : String) (steps : Nat)
    (start : UnitaryCircuit gates oracles layout)
    (step : Fin steps → UnitaryCircuit gates oracles layout) :
    UnitaryCircuit gates oracles layout :=
  ⟨.indexedProduct label steps start.sequence (fun index => (step index).sequence)⟩

/-- Record a descriptive macro occurrence containing its complete actual expansion. -/
public def macroCall (name : String) (body : UnitaryCircuit gates oracles layout) :
    UnitaryCircuit gates oracles layout := ⟨.macroCall name body.sequence⟩

end UnitaryCircuit

end QuantumAlg
