/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Dirty.Control
import all QuantumAlg.Components.Encoded.BitGates.QubitPrimitive
import all QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Components.Encoded.BitGates.QuantumTime

/-!
# Actual native control with a separate retained source and restored work coordinate

Both appended systems are actual supplied physical wires. Every source
gate is lifted into its original complete prefix, so the external control
and arbitrary borrowed work are disjoint from its whole support. The
literal dirty-work lowering restores work inside each controlled gate.
This component allocates no systems and requires no source-value domain.
-/

namespace QuantumAlg.EncodedBit.ExternalWord

noncomputable section

open BinaryLabelEncoding

abbrev Registers (Data : Type) := Data × (Bool × Bool)

def flags : BinaryLabelEncoding (Bool × Bool) := .prod .bool .bool

def encoding {Data : Type} (source : BinaryLabelEncoding Data) :
    BinaryLabelEncoding (Registers Data) := .prod source flags

variable {Data : Type} (source : BinaryLabelEncoding Data)

/-- The first actual suffix coordinate is the supplied retained control. -/
def controlBit : EncodedBit (encoding source) :=
  prodRightBit source flags (prodLeftBit .bool .bool boolBit)

/-- The second actual suffix coordinate is arbitrary restored lowering work. -/
def workBit : EncodedBit (encoding source) :=
  prodRightBit source flags (prodRightBit .bool .bool boolBit)

lemma control_work : (controlBit source).wire ≠ (workBit source).wire := by
  intro same
  have values := congrArg Fin.val same
  change source.width + 0 = source.width + (1 + 0) at values
  omega

private def lifted (body : List (GateSpec source)) : List (GateSpec (encoding source)) :=
  body.map (GateSpec.prodLeft flags)

private lemma control_disjoint (body : List (GateSpec source))
    (gate : GateSpec (encoding source)) (present : gate ∈ lifted source body) :
    GateSpec.bitDisjoint (controlBit source) gate := by
  obtain ⟨original, _member, rfl⟩ := List.mem_map.mp present
  exact GateSpec.bitDisjoint_prodLeft_rightBit source flags _ original

private lemma work_disjoint (body : List (GateSpec source))
    (gate : GateSpec (encoding source)) (present : gate ∈ lifted source body) :
    GateSpec.bitDisjoint (workBit source) gate := by
  obtain ⟨original, _member, rfl⟩ := List.mem_map.mp present
  exact GateSpec.bitDisjoint_prodLeft_rightBit source flags _ original

/-- Every actual source instruction is lowered using these same certified external coordinates. -/
def gates (body : List (GateSpec source)) : List (GateSpec (encoding source)) :=
  GateSpec.listWithDirtyControl (controlBit source) (workBit source) (lifted source body)
    (control_disjoint source body) (work_disjoint source body) (control_work source)

/-- Independent complete action preserves both original external coordinates. -/
def step (body : List (GateSpec source)) (state : Registers Data) : Registers Data :=
  (if state.2.1 then GateSpec.stepList body state.1 else state.1, state.2)

/-- Inactive execution is exact identity on all source labels and arbitrary borrowed work. -/
lemma gates_step (body : List (GateSpec source)) (state : Registers Data) :
    GateSpec.stepList (gates source body) state = step source body state := by
  rw [gates, GateSpec.listWithDirtyControl_step]
  change (if state.2.1 then GateSpec.stepList (body.map (GateSpec.prodLeft flags)) state
    else state) = _
  rw [GateSpec.stepList_prodLeft, step]
  cases state.2.1 <;> rfl

/-- Literal native control uses the supplied physical systems without fresh allocation. -/
def program (body : List (GateSpec source)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding source).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (gates source body)

/-- Coherent native semantics include every source, control and arbitrary work amplitude. -/
lemma program_realizes (body : List (GateSpec source))
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding source) (program source body) environment
      (step source body) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (gates_step source body) environment

private lemma lifted_events (body : List (GateSpec source)) :
    (lifted source body).map (GateSpec.event .empty) = body.map (GateSpec.event .empty) :=
  GateSpec.map_event_prodLeft flags body

/-- Source CNOTs become Toffolis and actual source Toffolis pay their four-gate native lowering. -/
lemma program_toffoli_count (body : List (GateSpec source)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program source body).eventCost =
        (body.map GateSpec.cnotMultiplicity).sum +
          4 * (body.map GateSpec.toffoliMultiplicity).sum := by
  rw [program, GateSpec.programList_toffoli_count_eq_sum, gates,
    GateSpec.listWithDirtyControl_toffoliMultiplicity_sum,
    GateSpec.sum_cnotMultiplicity_eq_of_events_eq .empty (lifted_events source body),
    GateSpec.sum_toffoliMultiplicity_eq_of_events_eq .empty (lifted_events source body)]

/-- Only literal source X instructions become CNOTs under this actual control. -/
lemma program_cnot_count (body : List (GateSpec source)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program source body).eventCost = (body.map GateSpec.xMultiplicity).sum := by
  rw [program, GateSpec.programList_cnot_count_eq_sum, gates,
    GateSpec.listWithDirtyControl_cnotMultiplicity_sum,
    GateSpec.sum_xMultiplicity_eq_of_events_eq .empty (lifted_events source body)]

/-- Each actual dirty-control lowering has no single-qubit gate. -/
lemma program_singleQubit_count (body : List (GateSpec source)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program source body).eventCost = 0 := by
  rw [program, GateSpec.programList_x_count_eq_sum, gates,
    GateSpec.listWithDirtyControl_xMultiplicity_sum]

/-- Actual duration is the emitted small word's true sequential native duration. -/
lemma program_quantumTime (body : List (GateSpec source)) :
    (program source body).evaluatedEventDepth Resource.Event.quantumDuration =
      (body.map GateSpec.xMultiplicity).sum + (body.map GateSpec.cnotMultiplicity).sum +
        4 * (body.map GateSpec.toffoliMultiplicity).sum := by
  have native := GateSpec.primitiveEventCount_programList
    (layout := QubitLayout.canonical _) (oracles := .empty) (gates source body)
  change GateSpec.primitiveEventCount (program source body) = _ at native
  rw [GateSpec.primitiveEventCount, program_singleQubit_count, program_cnot_count,
    program_toffoli_count] at native
  rw [program, GateSpec.programList_quantumTime, ← native]
  omega

end

end QuantumAlg.EncodedBit.ExternalWord
