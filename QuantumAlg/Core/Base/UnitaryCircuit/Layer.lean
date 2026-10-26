/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Tensor
public import QuantumAlg.Core.Base.Layout.Quantum.Embedding.Append
import all QuantumAlg.Core.Base.UnitaryCircuit.Tensor
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding.Append
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding.Operator
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Actual parallel words on their certified physical supports

A part stores an actual circuit on its unchanged subsystem and the inclusion of
that subsystem into the ambient layout. Joining parts constructs a real parallel
node, requiring disjoint positions after placement. All event, depth and operator
laws follow from that same construction; no separate resource witness is used.
-/

namespace QuantumAlg.UnitaryCircuit

/-- One actual word together with its unchanged physical subsystem. -/
public structure LayerPart (gates : GateModel) (oracles : OracleModel)
    {count : Nat} (ambient : QuantumLayout count) where
  /-- Number of original systems used by this word. -/
  count : Nat
  /-- The actual ordered subsystem, including its physical identities. -/
  layout : QuantumLayout count
  /-- These same systems occur at the certified ambient positions. -/
  placement : QuantumLayout.Embedding layout ambient
  /-- The actual native/query construction on that subsystem. -/
  body : UnitaryCircuit gates oracles layout

namespace LayerPart

noncomputable section

variable {gates : GateModel} {oracles : OracleModel} {count : Nat}
  {ambient : QuantumLayout count}

/-- Extend this actual word by identity on its complete physical complement. -/
public def program (part : LayerPart gates oracles ambient) :
    UnitaryCircuit gates oracles ambient := embed part.placement part.body

/-- An empty part touches no physical system and executes no operation. -/
public def empty : LayerPart gates oracles ambient where
  count := 0
  layout := { wire := Fin.elim0, identityInjective := fun i => Fin.elim0 i }
  placement :=
    { position := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
      wire_eq := fun i => Fin.elim0 i }
  body := UnitaryCircuit.identity gates oracles _

/-- Retain exactly the native occurrence's own wires as its compact subsystem. -/
public def native (application : GateModel.Application gates ambient) :
    LayerPart gates oracles ambient where
  count := (gates.signature application.occurrence.token).systemCount
  layout := application.occurrence.placement.layout
  placement := application.embedding
  body := UnitaryCircuit.native
    { occurrence := application.occurrence
      embedding := { position := Function.Embedding.refl _, wire_eq := fun _ => rfl } }

/-- The empty actual word has no native/query events. -/
public lemma layerPart_empty_eventCost :
    (empty (gates := gates) (oracles := oracles) (ambient := ambient)).program.eventCost = 0 := by
  rfl

/-- The empty part has no physical support. -/
public lemma layerPart_empty_selection :
    (empty (gates := gates) (oracles := oracles) (ambient := ambient)).placement.selection = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro index present
  obtain ⟨original, _, _⟩ := Finset.mem_map.mp present
  exact Fin.elim0 original

/-- The original native coordinate is unchanged by compact subsystem construction. -/
public lemma layerPart_native_eventCost (application : GateModel.Application gates ambient) :
    (native (oracles := oracles) application).program.eventCost =
      ResourcePool.singleton (model := .quantum gates oracles) (.gate application.coordinate) := by
  rfl

/-- Compacting a native application preserves its actual single-event trace. -/
public lemma layerPart_native_eventTrace (application : GateModel.Application gates ambient) :
    (native (oracles := oracles) application).program.eventTrace =
      [.gate application.coordinate] := by rfl

/-- The original native instruction remains one actual dependency step. -/
public lemma layerPart_native_depth (application : GateModel.Application gates ambient)
    (duration : Resource.Event (.quantum gates oracles) → Nat) :
    (native (oracles := oracles) application).program.evaluatedEventDepth duration =
      duration (.gate application.coordinate) := by rfl

/-- Compacting and re-embedding retains the complete original native operator. -/
public lemma layerPart_native_matrix (application : GateModel.Application gates ambient)
    (environment : oracles.Interpretation) :
    (native (oracles := oracles) application).program.matrix environment =
      (UnitaryCircuit.native application).matrix environment := by
  change application.embedding.liftOperator
    (({ position := Function.Embedding.refl _, wire_eq := fun _ => rfl } :
      QuantumLayout.Embedding application.occurrence.placement.layout
        application.occurrence.placement.layout).liftOperator application.occurrence.operator) =
    application.embedding.liftOperator application.occurrence.operator
  rw [QuantumLayout.Embedding.embedding_lift_compose]
  congr 1

/-- Join only words with disjoint actual ambient supports. -/
public def join (first second : LayerPart gates oracles ambient)
    (separate : Disjoint first.placement.selection second.placement.selection) :
    LayerPart gates oracles ambient where
  count := first.count + second.count
  layout := QuantumLayout.append first.layout second.layout
    (QuantumLayout.Embedding.embedding_identities_disjoint
      first.placement second.placement separate)
  placement := QuantumLayout.Embedding.append first.placement second.placement separate
  body := first.body.tensor second.body
    (QuantumLayout.Embedding.embedding_identities_disjoint
      first.placement second.placement separate)

/-- The joined part uses exactly the two actual supports and no extra system. -/
public lemma layerPart_join_selection (first second : LayerPart gates oracles ambient)
    (separate : Disjoint first.placement.selection second.placement.selection) :
    (join first second separate).placement.selection =
      first.placement.selection ∪ second.placement.selection :=
  QuantumLayout.Embedding.embedding_append_selection first.placement second.placement separate

/-- Real parallel execution retains both complete native/query ledgers. -/
public lemma layerPart_join_eventCost (first second : LayerPart gates oracles ambient)
    (separate : Disjoint first.placement.selection second.placement.selection) :
    (join first second separate).program.eventCost =
      first.program.eventCost + second.program.eventCost := by
  rfl

/-- Traversing both parallel branches retains every original native/query event. -/
public lemma layerPart_join_eventTrace (first second : LayerPart gates oracles ambient)
    (separate : Disjoint first.placement.selection second.placement.selection) :
    (join first second separate).program.eventTrace =
      first.program.eventTrace ++ second.program.eventTrace := by rfl

/-- Parallel words take the maximum of their actual dependency depths. -/
public lemma layerPart_join_depth (first second : LayerPart gates oracles ambient)
    (separate : Disjoint first.placement.selection second.placement.selection)
    (duration : Resource.Event (.quantum gates oracles) → Nat) :
    (join first second separate).program.evaluatedEventDepth duration =
      max (first.program.evaluatedEventDepth duration)
        (second.program.evaluatedEventDepth duration) := by
  rfl

/-- The parallel word has the same full ambient operator as the two words in order. -/
public lemma layerPart_join_matrix (first second : LayerPart gates oracles ambient)
    (separate : Disjoint first.placement.selection second.placement.selection)
    (environment : oracles.Interpretation) :
    (join first second separate).program.matrix environment =
      (first.program.seq second.program).matrix environment := by
  change (QuantumLayout.Embedding.append first.placement second.placement separate).liftOperator
    ((first.body.tensor second.body _).matrix environment) =
      second.placement.liftOperator (second.body.matrix environment) *
        first.placement.liftOperator (first.body.matrix environment)
  rw [tensor_embedded_matrix, QuantumLayout.Embedding.embedding_lift_mul,
    QuantumLayout.Embedding.embedding_lift_compose,
    QuantumLayout.Embedding.embedding_lift_compose,
    QuantumLayout.Embedding.embedding_append_right,
    QuantumLayout.Embedding.embedding_append_left]

end

end LayerPart

end QuantumAlg.UnitaryCircuit
