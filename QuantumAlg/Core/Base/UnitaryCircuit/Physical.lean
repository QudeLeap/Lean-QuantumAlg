/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Sequence
public import QuantumAlg.Core.Base.Layout.Quantum.Relabeling
import all QuantumAlg.Core.Base.Layout.Quantum.Relabeling
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding.Operator
import all QuantumAlg.Core.Base.Gate.Placement
public import QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Base.Oracle.Placement

/-!
# Relocating the complete physical construction

An injective physical-address map relocates every actual wire, gate occurrence
and query occurrence in the same construction tree. Logical positions,
dimensions and basis values stay fixed. Disjoint subsystems remain disjoint;
native instances, exact operators, resource counts, dependencies and macro
observations are preserved. The new circuit's type records the relocated layout.
-/

namespace QuantumAlg

namespace QuantumLayout.Embedding

/-- Relocate source and target wires with the same injective physical-address map. -/
def relabel {small large : Nat} {source : QuantumLayout small} {target : QuantumLayout large}
    (placement : Embedding source target) (physical : Nat ↪ Nat) :
    Embedding (source.relabel physical) (target.relabel physical) where
  position := placement.position
  wire_eq index := congrArg (QuantumWire.relabel physical) (placement.wire_eq index)

/-- The same local operator acts on the same coordinate values after physical relocation. -/
@[simp] theorem liftOperator_relabel {small large : Nat}
    {source : QuantumLayout small} {target : QuantumLayout large}
    (placement : Embedding source target) (physical : Nat ↪ Nat)
    (operator : UnitaryOperator source.register) :
    (placement.relabel physical).liftOperator operator = placement.liftOperator operator := by
  rfl

end QuantumLayout.Embedding

namespace GateModel.Application

/-- Relocate the actual native token and its complete physical embedding together. -/
def relabel {model : GateModel} {count : Nat} {layout : QuantumLayout count}
    (application : Application model layout) (physical : Nat ↪ Nat) :
    Application model (layout.relabel physical) where
  occurrence :=
    { token := application.occurrence.token
      placement :=
        { layout := application.occurrence.placement.layout.relabel physical
          dimension_eq := application.occurrence.placement.dimension_eq } }
  embedding := application.embedding.relabel physical

end GateModel.Application

namespace OracleModel.Application

/-- Relocation preserves the actual query instance and cannot grant a new access form. -/
def relabel {model : OracleModel} {count : Nat} {layout : QuantumLayout count}
    (application : Application model layout) (physical : Nat ↪ Nat) :
    Application model (layout.relabel physical) where
  occurrence :=
    { query := application.occurrence.query
      placement :=
        { layout := application.occurrence.placement.layout.relabel physical
          dimension_eq := application.occurrence.placement.dimension_eq } }
  embedding := application.embedding.relabel physical

end OracleModel.Application

namespace UnitaryLeaf

/-- Relocate the actual leaf without changing its declared operation instance. -/
def relabel {gates : GateModel} {oracles : OracleModel} {count : Nat}
    {layout : QuantumLayout count} (leaf : UnitaryLeaf gates oracles layout)
    (physical : Nat ↪ Nat) : UnitaryLeaf gates oracles (layout.relabel physical) :=
  match leaf with
  | .gate application => .gate (application.relabel physical)
  | .oracle application => .oracle (application.relabel physical)

end UnitaryLeaf

namespace UnitarySequence

variable {gates : GateModel} {oracles : OracleModel}

/-- Relocate every leaf and intermediate subsystem with one injective physical-address map. -/
def relabel (physical : Nat ↪ Nat) : {count : Nat} → {layout : QuantumLayout count} →
    UnitarySequence gates oracles layout →
      UnitarySequence gates oracles (layout.relabel physical)
  | _, layout, .id _ => .id (layout.relabel physical)
  | _, _, .leaf atom => .leaf (atom.relabel physical)
  | _, _, .seq left right => .seq (left.relabel physical) (right.relabel physical)
  | _, _, .embed placement body => .embed (placement.relabel physical) (body.relabel physical)
  | _, _, .parallel left right leftPlacement rightPlacement disjoint =>
      .parallel (left.relabel physical) (right.relabel physical)
        (leftPlacement.relabel physical) (rightPlacement.relabel physical) disjoint
  | _, _, .iterate repetitions body => .iterate repetitions (body.relabel physical)
  | _, _, .indexedProduct label steps start step =>
      .indexedProduct label steps (start.relabel physical)
        (fun index => (step index).relabel physical)
  | _, _, .macroCall name body => .macroCall name (body.relabel physical)

variable {count : Nat} {layout : QuantumLayout count}

/-- Logical operators are unchanged because relocation preserves every coordinate value. -/
@[simp] theorem toUnitary_relabel (physical : Nat ↪ Nat)
    (sequence : UnitarySequence gates oracles layout) :
    (sequence.relabel physical).toUnitary = sequence.toUnitary := by
  induction sequence with
  | id => rfl
  | leaf atom => cases atom <;> rfl
  | seq left right leftIH rightIH =>
      simp only [relabel, toUnitary, leftIH, rightIH]
      rfl
  | embed placement body bodyIH =>
      simp only [relabel, toUnitary, QuantumLayout.Embedding.liftOperator_relabel, bodyIH]
      rfl
  | parallel left right leftPlacement rightPlacement disjoint leftIH rightIH =>
      simp only [relabel, toUnitary, QuantumLayout.Embedding.liftOperator_relabel, leftIH, rightIH]
      rfl
  | iterate repetitions body bodyIH =>
      simp only [relabel, toUnitary, bodyIH]
      rfl
  | indexedProduct label steps start step startIH stepIH =>
      simp only [relabel, toUnitary, startIH, stepIH]
      rfl
  | macroCall name body bodyIH => simpa [relabel, toUnitary] using bodyIH

/-- Relocation retains each original native and query occurrence in execution order. -/
@[simp] theorem eventTrace_relabel (physical : Nat ↪ Nat)
    (sequence : UnitarySequence gates oracles layout)
    (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    (sequence.relabel physical).eventTrace operations classicalOracles =
      sequence.eventTrace operations classicalOracles := by
  induction sequence with
  | id => rfl
  | leaf atom => cases atom <;> rfl
  | seq left right leftIH rightIH => simp [relabel, eventTrace, leftIH, rightIH]
  | embed placement body bodyIH => simpa [relabel, eventTrace] using bodyIH
  | parallel left right leftPlacement rightPlacement disjoint leftIH rightIH =>
      simp [relabel, eventTrace, leftIH, rightIH]
  | iterate repetitions body bodyIH => simp [relabel, eventTrace, bodyIH]
  | indexedProduct label steps start step startIH stepIH =>
      simp [relabel, eventTrace, startIH, stepIH]
  | macroCall name body bodyIH => simpa [relabel, eventTrace] using bodyIH

/-- Exact native costs follow the same unchanged occurrence trace. -/
@[simp] theorem eventCost_relabel (physical : Nat ↪ Nat)
    (sequence : UnitarySequence gates oracles layout)
    (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    (sequence.relabel physical).eventCost operations classicalOracles =
      sequence.eventCost operations classicalOracles := by
  rw [← ofList_eventTrace_eq_eventCost (sequence.relabel physical) operations classicalOracles,
    eventTrace_relabel physical sequence operations classicalOracles,
    ofList_eventTrace_eq_eventCost sequence operations classicalOracles]

/-- Relocation preserves every sequential and parallel dependency. -/
@[simp] theorem eventDepth_relabel (physical : Nat ↪ Nat)
    (sequence : UnitarySequence gates oracles layout)
    (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    (sequence.relabel physical).eventDepth operations classicalOracles =
      sequence.eventDepth operations classicalOracles := by
  induction sequence with
  | id => rfl
  | leaf atom => cases atom <;> rfl
  | seq left right leftIH rightIH => simp [relabel, eventDepth, leftIH, rightIH]
  | embed placement body bodyIH => simpa [relabel, eventDepth] using bodyIH
  | parallel left right leftPlacement rightPlacement disjoint leftIH rightIH =>
      simp [relabel, eventDepth, leftIH, rightIH]
  | iterate repetitions body bodyIH => simp [relabel, eventDepth, bodyIH]
  | indexedProduct label steps start step startIH stepIH =>
      simp [relabel, eventDepth, startIH, stepIH]
  | macroCall name body bodyIH => simpa [relabel, eventDepth] using bodyIH

/-- Descriptive macro observations still refer to the same complete expansion tree. -/
@[simp] theorem macroTrace_relabel (physical : Nat ↪ Nat)
    (sequence : UnitarySequence gates oracles layout) :
    (sequence.relabel physical).macroTrace = sequence.macroTrace := by
  induction sequence with
  | id => rfl
  | leaf => rfl
  | seq left right leftIH rightIH => simp [relabel, macroTrace, leftIH, rightIH]
  | embed placement body bodyIH => simpa [relabel, macroTrace] using bodyIH
  | parallel left right leftPlacement rightPlacement disjoint leftIH rightIH =>
      simp [relabel, macroTrace, leftIH, rightIH]
  | iterate repetitions body bodyIH => simp [relabel, macroTrace, bodyIH]
  | indexedProduct label steps start step startIH stepIH =>
      simp [relabel, macroTrace, startIH, stepIH]
  | macroCall name body bodyIH => simp [relabel, macroTrace, bodyIH]

end UnitarySequence

namespace UnitaryCircuit

variable {gates : GateModel} {oracles : OracleModel}
variable {count : Nat} {layout : QuantumLayout count}

/-- Relocate the actual circuit and expose its new physical layout in the result type. -/
public def relabel (circuit : UnitaryCircuit gates oracles layout) (physical : Nat ↪ Nat) :
    UnitaryCircuit gates oracles (layout.relabel physical) :=
  ⟨circuit.sequence.relabel physical⟩

private theorem relabel_matrix_internal (circuit : UnitaryCircuit gates oracles layout)
    (physical : Nat ↪ Nat) : (circuit.relabel physical).matrix = circuit.matrix :=
  UnitarySequence.toUnitary_relabel physical circuit.sequence

@[simp] public theorem relabel_matrix (circuit : UnitaryCircuit gates oracles layout)
    (physical : Nat ↪ Nat) : (circuit.relabel physical).matrix = circuit.matrix :=
  relabel_matrix_internal circuit physical

/-- Physical-address relabelling retains the action on the unchanged logical values. -/
@[simp] public theorem relabel_applyVec (circuit : UnitaryCircuit gates oracles layout)
    (physical : Nat ↪ Nat) (state : HilbertVector layout.register) :
    (circuit.relabel physical).applyVec state = circuit.applyVec state := by
  unfold applyVec
  rw [relabel_matrix]
  rfl

/-- Relocating both the circuit and its vector coordinates preserves their
complete action. -/
@[simp] public theorem relabel_applyVec_reindex
    (circuit : UnitaryCircuit gates oracles layout)
    (physical : Nat ↪ Nat) (state : HilbertVector layout.register) :
    (circuit.relabel physical).applyVec
        (HilbertVector.reindex (QuantumLayout.relabelBasis layout physical) state) =
      HilbertVector.reindex (QuantumLayout.relabelBasis layout physical)
        (circuit.applyVec state) := by
  unfold applyVec
  rw [relabel_matrix]
  rfl

private theorem relabel_eventTrace_internal
    (circuit : UnitaryCircuit gates oracles layout) (physical : Nat ↪ Nat)
    (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    (circuit.relabel physical).eventTrace operations classicalOracles =
      circuit.eventTrace operations classicalOracles :=
  UnitarySequence.eventTrace_relabel physical circuit.sequence operations classicalOracles

@[simp] public theorem relabel_eventTrace (circuit : UnitaryCircuit gates oracles layout)
    (physical : Nat ↪ Nat) (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    (circuit.relabel physical).eventTrace operations classicalOracles =
      circuit.eventTrace operations classicalOracles :=
  relabel_eventTrace_internal circuit physical operations classicalOracles

private theorem relabel_eventCost_internal
    (circuit : UnitaryCircuit gates oracles layout) (physical : Nat ↪ Nat)
    (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    (circuit.relabel physical).eventCost operations classicalOracles =
      circuit.eventCost operations classicalOracles :=
  UnitarySequence.eventCost_relabel physical circuit.sequence operations classicalOracles

@[simp] public theorem relabel_eventCost (circuit : UnitaryCircuit gates oracles layout)
    (physical : Nat ↪ Nat) (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    (circuit.relabel physical).eventCost operations classicalOracles =
      circuit.eventCost operations classicalOracles :=
  relabel_eventCost_internal circuit physical operations classicalOracles

private theorem relabel_eventDepth_internal
    (circuit : UnitaryCircuit gates oracles layout) (physical : Nat ↪ Nat)
    (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    (circuit.relabel physical).eventDepth operations classicalOracles =
      circuit.eventDepth operations classicalOracles :=
  UnitarySequence.eventDepth_relabel physical circuit.sequence operations classicalOracles

@[simp] public theorem relabel_eventDepth (circuit : UnitaryCircuit gates oracles layout)
    (physical : Nat ↪ Nat) (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    (circuit.relabel physical).eventDepth operations classicalOracles =
      circuit.eventDepth operations classicalOracles :=
  relabel_eventDepth_internal circuit physical operations classicalOracles

private theorem relabel_evaluatedEventDepth_internal
    (circuit : UnitaryCircuit gates oracles layout) (physical : Nat ↪ Nat)
    (duration : Resource.Event (.quantum gates oracles) → Nat) :
    (circuit.relabel physical).evaluatedEventDepth duration =
      circuit.evaluatedEventDepth duration := by
  unfold evaluatedEventDepth
  rw [relabel_eventDepth_internal]

/-- Relocation preserves evaluated dependency depth under every event-duration assignment. -/
@[simp] public theorem relabel_evaluatedEventDepth
    (circuit : UnitaryCircuit gates oracles layout) (physical : Nat ↪ Nat)
    (duration : Resource.Event (.quantum gates oracles) → Nat) :
    (circuit.relabel physical).evaluatedEventDepth duration =
      circuit.evaluatedEventDepth duration := by
  exact relabel_evaluatedEventDepth_internal circuit physical duration

private theorem relabel_macroCount_internal
    (circuit : UnitaryCircuit gates oracles layout) (physical : Nat ↪ Nat)
    (name : String) :
    (circuit.relabel physical).macroCount name = circuit.macroCount name := by
  simp only [macroCount, relabel, UnitarySequence.macroTrace_relabel]

@[simp] public theorem relabel_macroCount (circuit : UnitaryCircuit gates oracles layout)
    (physical : Nat ↪ Nat) (name : String) :
    (circuit.relabel physical).macroCount name = circuit.macroCount name := by
  exact relabel_macroCount_internal circuit physical name

end UnitaryCircuit

end QuantumAlg
