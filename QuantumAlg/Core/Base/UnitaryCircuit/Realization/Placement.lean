/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Realization
import all QuantumAlg.Core.Base.UnitaryCircuit.Realization
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Sequence
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding.Operator

/-!
# Exact realizations on a larger physical layout

Embedding an actual native word preserves its operator equality and all native
occurrences. The target operator acts by identity on the complementary systems.
No initialized-spectator assumption or additional native capability is needed.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

variable {gates : GateModel} {oracles : OracleModel}
variable {small large : Nat} {source : QuantumLayout small} {target : QuantumLayout large}

/-- The embedded circuit acts by the physical embedding of its original operator. -/
public lemma embed_matrix (placement : QuantumLayout.Embedding source target)
    (body : UnitaryCircuit gates oracles source) (environment : oracles.Interpretation) :
    ((body.embed placement).matrix environment) = placement.liftOperator (body.matrix environment)
      := by
  simp only [embed, matrix, UnitarySequence.toUnitary]

/-- Embedding retains every native occurrence, including expanded macro bodies. -/
public lemma embed_eventTrace (placement : QuantumLayout.Embedding source target)
    (body : UnitaryCircuit gates oracles source) :
    (body.embed placement).eventTrace = body.eventTrace := by
  simp only [embed, eventTrace, UnitarySequence.eventTrace]

/-- Physical placement does not insert or remove any dependency in the native word. -/
public lemma embed_eventDepth (placement : QuantumLayout.Embedding source target)
    (body : UnitaryCircuit gates oracles source) :
    (body.embed placement).eventDepth = body.eventDepth := by
  simp only [embed, eventDepth, UnitarySequence.eventDepth]

namespace ExactRealization

/-- Place the complete exact implementation with identity on every complementary system. -/
public def embed {operator : oracles.Interpretation → UnitaryOperator source.register}
    (placement : QuantumLayout.Embedding source target)
    (realized : ExactRealization gates oracles source operator) :
    ExactRealization gates oracles target (fun environment => placement.liftOperator (operator
      environment)) where
  circuit := realized.circuit.embed placement
  matrix_eq := by
    intro environment
    rw [embed_matrix, realized.matrix_eq]

end ExactRealization

end

end QuantumAlg.UnitaryCircuit
