/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Placement
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Sequence

/-!
# Descriptive macro counts under composition and placement

These observations count names in the actual construction tree. They neither
replace the retained native expansion nor determine its resource cost.
-/

namespace QuantumAlg.UnitaryCircuit

variable {gates : GateModel} {oracles : OracleModel}
variable {count : Nat} {layout : QuantumLayout count}

/-- Sequential execution retains every descriptive macro occurrence of both operands. -/
public theorem macroCount_seq (name : String) (left right : UnitaryCircuit gates oracles layout) :
    (left.seq right).macroCount name = left.macroCount name + right.macroCount name := by
  simp only [macroCount, seq, UnitarySequence.macroTrace, List.count_append]

/-- Parallel words retain the descriptive macro occurrences of both disjoint operands. -/
public theorem macroCount_parallel {leftCount rightCount count : Nat}
    {leftLayout : QuantumLayout leftCount} {rightLayout : QuantumLayout rightCount}
    {layout : QuantumLayout count} (name : String)
    (left : UnitaryCircuit gates oracles leftLayout)
    (right : UnitaryCircuit gates oracles rightLayout)
    (leftPlacement : QuantumLayout.Embedding leftLayout layout)
    (rightPlacement : QuantumLayout.Embedding rightLayout layout)
    (disjoint : Disjoint leftPlacement.selection rightPlacement.selection) :
    (parallel left right leftPlacement rightPlacement disjoint).macroCount name =
      left.macroCount name + right.macroCount name := by
  simp only [macroCount, parallel, UnitarySequence.macroTrace, List.count_append]

/-- Extending by untouched systems retains all descriptive occurrences of the actual word. -/
public theorem macroCount_embed {small large : Nat}
    {source : QuantumLayout small} {target : QuantumLayout large}
    (placement : QuantumLayout.Embedding source target)
    (body : UnitaryCircuit gates oracles source) (name : String) :
    (body.embed placement).macroCount name = body.macroCount name := by
  simp only [macroCount, embed, UnitarySequence.macroTrace]

/-- Placing a complete word preserves its descriptive macro counts as well as its native events. -/
public theorem placeAt_macroCount {small large : Nat}
    (source : QuantumLayout small) (target : QuantumLayout large)
    (position : Fin small ↪ Fin large)
    (dimensions : ∀ index,
      (source.wire index).dimension = (target.wire (position index)).dimension)
    (body : UnitaryCircuit gates oracles source) (name : String) :
    (placeAt source target position dimensions body).macroCount name = body.macroCount name := by
  rw [placeAt, macroCount_embed, relabel_macroCount]

end QuantumAlg.UnitaryCircuit
