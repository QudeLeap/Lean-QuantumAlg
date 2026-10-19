/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit
public import QuantumAlg.Core.Base.Layout.Quantum.Append.Embedding
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Sequence
import all QuantumAlg.Core.Base.Layout.Quantum.Append.Embedding
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding.Operator

/-!
# Parallel execution on appended disjoint physical layouts

The two original words execute on their own unchanged systems. The resulting
word records both event traces and a parallel dependency expression. It does
not infer disjointness from equal dimensions or allocate additional systems.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

variable {gates : GateModel} {oracles : OracleModel}
variable {leftCount rightCount : Nat}
variable {leftLayout : QuantumLayout leftCount} {rightLayout : QuantumLayout rightCount}

/-- Execute two actual words in parallel on the append of their disjoint physical layouts. -/
public def tensor (left : UnitaryCircuit gates oracles leftLayout)
    (right : UnitaryCircuit gates oracles rightLayout)
    (disjoint : List.Disjoint leftLayout.identities rightLayout.identities) :
    UnitaryCircuit gates oracles (QuantumLayout.append leftLayout rightLayout disjoint) :=
  parallel left right
    (QuantumLayout.appendLeftEmbedding leftLayout rightLayout disjoint)
    (QuantumLayout.appendRightEmbedding leftLayout rightLayout disjoint)
    (QuantumLayout.appendEmbedding_selections_disjoint leftLayout rightLayout disjoint)

/-- The complete operator consists of the two actual disjoint subsystem embeddings. -/
public lemma tensor_embedded_matrix (left : UnitaryCircuit gates oracles leftLayout)
    (right : UnitaryCircuit gates oracles rightLayout)
    (disjoint : List.Disjoint leftLayout.identities rightLayout.identities) (environment :
      oracles.Interpretation) :
    ((tensor left right disjoint).matrix environment) =
      (QuantumLayout.appendRightEmbedding leftLayout rightLayout disjoint).liftOperator
        (right.matrix environment) *
      (QuantumLayout.appendLeftEmbedding leftLayout rightLayout disjoint).liftOperator
        (left.matrix environment) := by rfl

/-- Both event sequences are retained in deterministic traversal order. -/
public lemma tensor_native_eventTrace (left : UnitaryCircuit gates oracles leftLayout)
    (right : UnitaryCircuit gates oracles rightLayout)
    (disjoint : List.Disjoint leftLayout.identities rightLayout.identities) :
    (tensor left right disjoint).eventTrace = left.eventTrace ++ right.eventTrace := by rfl

/-- Parallel placement preserves the sum of actual event multiplicities. -/
public lemma tensor_native_eventCost (left : UnitaryCircuit gates oracles leftLayout)
    (right : UnitaryCircuit gates oracles rightLayout)
    (disjoint : List.Disjoint leftLayout.identities rightLayout.identities) :
    (tensor left right disjoint).eventCost = left.eventCost + right.eventCost := by rfl

/-- Disjoint execution has the maximum of the two actual dependency depths. -/
public lemma tensor_native_evaluatedEventDepth
    (left : UnitaryCircuit gates oracles leftLayout)
    (right : UnitaryCircuit gates oracles rightLayout)
    (disjoint : List.Disjoint leftLayout.identities rightLayout.identities)
    (duration : Resource.Event (.quantum gates oracles) → Nat) :
    (tensor left right disjoint).evaluatedEventDepth duration =
      max (left.evaluatedEventDepth duration) (right.evaluatedEventDepth duration) := by rfl

end

end QuantumAlg.UnitaryCircuit
