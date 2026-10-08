/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Suffix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Suffix
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical

/-!
# Parallel native words on consecutive binary registers

Both words retain their actual physical placements. The right word is shifted
behind the left register; their disjoint supports permit a parallel dependency
node while preserving both executed native and declared-query ledgers.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

private theorem binaryPlacements_disjoint (leftWidth rightWidth : Nat) :
    Disjoint (binaryPrefixEmbedding leftWidth rightWidth).selection
      (binarySuffixEmbedding leftWidth rightWidth).selection := by
  apply Finset.disjoint_left.mpr
  intro position inLeft inRight
  obtain ⟨left, _, leftEq⟩ := Finset.mem_map.mp inLeft
  obtain ⟨right, _, rightEq⟩ := Finset.mem_map.mp inRight
  have leftVal := congrArg Fin.val leftEq
  have rightVal := congrArg Fin.val rightEq
  change left.val = position.val at leftVal
  change leftWidth + right.val = position.val at rightVal
  have bound : left.val < leftWidth := left.isLt
  omega

/-- Execute both original words in parallel on their consecutive registers. -/
public def parallelBinary {gates : GateModel} {oracles : OracleModel}
    {leftWidth rightWidth : Nat}
    (left : UnitaryCircuit gates oracles
      (QuantumSignature.qubits leftWidth).canonicalPlacement.layout)
    (right : UnitaryCircuit gates oracles
      (QuantumSignature.qubits rightWidth).canonicalPlacement.layout) :
    UnitaryCircuit gates oracles
      (QuantumSignature.qubits (leftWidth + rightWidth)).canonicalPlacement.layout :=
  parallel left (right.relabel (binarySuffixShift leftWidth))
    (binaryPrefixEmbedding leftWidth rightWidth)
    (binarySuffixEmbedding leftWidth rightWidth)
    (binaryPlacements_disjoint leftWidth rightWidth)

/-- Parallel placement preserves both complete event ledgers. -/
public theorem parallelBinary_eventCost {gates : GateModel} {oracles : OracleModel}
    {leftWidth rightWidth : Nat}
    (left : UnitaryCircuit gates oracles
      (QuantumSignature.qubits leftWidth).canonicalPlacement.layout)
    (right : UnitaryCircuit gates oracles
      (QuantumSignature.qubits rightWidth).canonicalPlacement.layout) :
    (parallelBinary left right).eventCost = left.eventCost + right.eventCost := by
  rw [parallelBinary, parallel_eventCost, relabel_eventCost]

/-- The two actual disjoint branches take the maximum of their depths. -/
public theorem parallelBinary_evaluatedEventDepth
    {gates : GateModel} {oracles : OracleModel} {leftWidth rightWidth : Nat}
    (duration : Resource.Event (.quantum gates oracles) → Nat)
    (left : UnitaryCircuit gates oracles
      (QuantumSignature.qubits leftWidth).canonicalPlacement.layout)
    (right : UnitaryCircuit gates oracles
      (QuantumSignature.qubits rightWidth).canonicalPlacement.layout) :
    (parallelBinary left right).evaluatedEventDepth duration =
      max (left.evaluatedEventDepth duration) (right.evaluatedEventDepth duration) := by
  rw [parallelBinary, evaluatedEventDepth_parallel, relabel_evaluatedEventDepth]

end

end QuantumAlg.UnitaryCircuit
