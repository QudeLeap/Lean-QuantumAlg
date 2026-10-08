/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Registers
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Small.Gates
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Small

/-!
# Small-width accumulation stages without borrowed bits

Each actual X or CNOT of the small modular offset becomes a CNOT or Toffoli
selected by the original source bit. The complete two-word carrier contains
no additional work bit [VBE95, 9511018.tex:333-367; G17, paper.tex:319-334].
-/

namespace QuantumAlg.MAU.Multiplication.Accumulate.Gidney

noncomputable section

open Nat.FixedWidth EncodedBit.GateSpec

/-- The standard source bit uses the little-endian-to-wire conversion. -/
def sourceBit (width : Nat) (selected : Fin width) :
    EncodedBit (BinaryLabelEncoding.finIdentity width) :=
  BinaryLabelEncoding.finIdentityBit width (WireAddress.littleEndianWire selected)

/-- The addressed source bit is exactly the selected little-endian binary digit. -/
theorem gidneySourceBit_get (width : Nat) (selected : Fin width) (source : Fin (2 ^ width)) :
    (sourceBit width selected).get source = source.val.testBit selected.val := by
  change source.val.testBit (WireAddress.bitIndex (WireAddress.littleEndianWire selected)).val = _
  rw [WireAddress.bitIndex_littleEndianWire]

/-- Actual CNOT and Toffoli instructions on the original two-word carrier. -/
def smallStageGates (width : Nat) (small : width ≤ 2) (selected : Fin width)
    (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1)) :
    List (EncodedBit.GateSpec (encoding width)) :=
  (Addition.Gidney.Small.modularOffsetGates width small modulus constant).map
    (controlSmall (sourceBit width selected) small)

/-- Execute the actual selected list, without an abstract controlled-gate label. -/
def smallStageProgram (width : Nat) (small : width ≤ 2) (selected : Fin width)
    (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty
    (smallStageGates width small selected modulus constant)

/-- Exact coherent semantics includes both control branches and every target label. -/
theorem gidneySmallStage_realizes (width : Nat) (small : width ≤ 2) (selected : Fin width)
    (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1)) :
    UnitaryCircuit.Realizes (encoding width)
      (smallStageProgram width small selected modulus constant)
      (selectedOutput selected modulus constant) := by
  apply (controlSmallList_realizes (sourceBit width selected) small
    (QubitLayout.canonical _) .empty
    (Addition.Gidney.Small.modularOffsetGates width small modulus constant)).congrStep
  intro state
  rw [gidneySourceBit_get, Addition.Gidney.Small.modularOffsetGates_step]
  rfl

/-- The typed layout contains exactly the two original words, including at width zero. -/
theorem gidneySmallStage_interface (width : Nat) :
    (encoding width).width = 2 * width ∧
      (QubitLayout.canonical (encoding width).width).systemIdx = List.range (2 * width) := by
  have size : (encoding width).width = 2 * width := by
    change width + width = 2 * width
    omega
  exact ⟨size, (QubitLayout.canonical_systemIdx _).trans (congrArg List.range size)⟩

/-- The native ledger records the emitted CNOT/Toffoli list, in the default model. -/
theorem gidneySmallStage_eventCost (width : Nat) (small : width ≤ 2) (selected : Fin width)
    (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1)) :
    (smallStageProgram width small selected modulus constant).eventCost =
      ResourcePool.ofList
        ((smallStageGates width small selected modulus constant).map (event .empty)) :=
  programList_eventCost _ _ _

/-- Every source instruction becomes exactly one native controlled instruction. -/
theorem gidneySmallStage_event_count_bound (width : Nat) (small : width ≤ 2)
    (selected : Fin width) (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) :
    (smallStageProgram width small selected modulus constant).eventCost.card ≤ 9 := by
  exact (controlSmallList_resources (sourceBit width selected) small
    (QubitLayout.canonical _) .empty
    (Addition.Gidney.Small.modularOffsetGates width small modulus constant)).1.trans_le
      (Addition.Gidney.Small.modularOffsetGates_length width small modulus constant)

/-- The literal gate list has the same serial depth as its actual native instruction count. -/
theorem gidneySmallStage_depth_eq_events (width : Nat) (small : width ≤ 2)
    (selected : Fin width) (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) :
    (smallStageProgram width small selected modulus constant).evaluatedEventDepth (fun _ => 1) =
      (smallStageProgram width small selected modulus constant).eventCost.card := by
  rw [smallStageProgram, programList_evaluatedEventDepth_unit, programList_eventCost_card]

/-- The emitted circuit uses no single-qubit gates, at most six CNOTs and three Toffolis. -/
theorem gidneySmallStage_native_bounds (width : Nat) (small : width ≤ 2)
    (selected : Fin width) (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (smallStageProgram width small selected modulus constant).eventCost = 0 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (smallStageProgram width small selected modulus constant).eventCost ≤ 6 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (smallStageProgram width small selected modulus constant).eventCost ≤ 3 := by
  dsimp only [smallStageProgram, smallStageGates, encoding]
  simp only [programList_x_count_eq_sum, programList_cnot_count_eq_sum,
    programList_toffoli_count_eq_sum, List.map_map, Function.comp_def,
    controlSmall_xMultiplicity, controlSmall_cnotMultiplicity, controlSmall_toffoliMultiplicity]
  refine ⟨by simp, ?_, ?_⟩
  · exact Addition.Gidney.Small.modularOffsetGates_x_bound width small modulus constant
  · exact Addition.Gidney.Small.modularOffsetGates_cnot_bound width small modulus constant

end

end QuantumAlg.MAU.Multiplication.Accumulate.Gidney
