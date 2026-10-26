/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Cycle.Circuit
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Lookup.Resources
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Resources.Complete
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Resources.Measurement
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Cycle.Report

/-!
# Separate actual runtime CNOT and native-classical ledgers

The complete runtime-array pair retains its selected native masked-X loader,
real H/MZ/reset, paid AND/XOR feedback and native unary inverse. CNOTs and
native classical operations are bounded independently on the same actual
path. No combined quantity is treated as an exact count or exchange rate.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeTable

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {wordWidth lowWidth highRemaining : Nat}
  (frame : UnlookupFrame encoding wordWidth lowWidth highRemaining)
  (lookup : SelectorFrame encoding (highRemaining + lowWidth))
  (outsideAddress : ∀ bit label,
    (frame.result.bit bit).wire ≠ (lookup.address label).wire)
  (outsideStack : ∀ bit label,
    (frame.result.bit bit).wire ≠ (lookup.stack label).wire)
  (physical : QubitLayout encoding.width)
  (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
  (source : CInputRef ctx
    (.fixedVector (2 ^ (highRemaining + lowWidth + 1)) (.unsignedWord wordWidth)))
  (height : Nat) (output : Fin wordWidth → CWriteRef ctx (.finite 2))
  (mask : CWriteRef ctx (.bits wordWidth))
  (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)

local notation "code" => cycleCircuit (services := services) frame lookup outsideAddress
  outsideStack physical sameWires source height output mask parity temporary
local notation "loader" => lookupCircuit (oracles := OracleModel.empty) (services := services)
  source lookup (frame.cycleTarget lookup outsideAddress outsideStack) physical sameWires height
local notation "tailCode" => RuntimeUnlookup.circuit frame physical sameWires output mask parity
  temporary (splitInputs source)

/-- The selected loader and full measured feedback retain their original separate pools. -/
lemma cycleCircuit_resourcePool (path : (code).Path) :
    (code).resourcePool path = (loader).resourcePool path.1 +
      (tailCode).resourcePool path.2 := by
  change ResourcePool.ofList (_ ++ _) = _
  rw [ResourcePool.ofList_append]
  rfl

/-- Actual runtime table parity adds classical instructions and no quantum CNOT conversion. -/
lemma cycleCircuit_cnot_count_le (covered : wordWidth ≤ 2 ^ height) (path : (code).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .cnot)
      ((code).resourcePool path) ≤ staticCycleCnotLimit wordWidth highRemaining lowWidth := by
  have first := lookupCircuit_cnot_count_le source lookup
    (frame.cycleTarget lookup outsideAddress outsideStack) physical sameWires height covered path.1
  have last := RuntimeUnlookup.circuit_cnot_count_le frame physical sameWires output mask
    parity temporary (splitInputs source) path.2
  rw [cycleCircuit_resourcePool, ResourcePool.count_add]
  exact Nat.add_le_add first last

/-- All paid per-bit AND/XOR instructions and the real packed-mask operation remain classical. -/
lemma cycleCircuit_classical_weight_le (path : (code).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((code).resourcePool path) ≤
        1 + 2 ^ (highRemaining + 1) * 2 ^ lowWidth * (2 * wordWidth + 1) := by
  have last := RuntimeUnlookup.circuit_classical_weight_le frame physical sameWires output mask
    parity temporary (splitInputs source) path.2
  rw [cycleCircuit_resourcePool, ResourcePool.weightedCount_add,
    lookupCircuit_classical_weight, Nat.zero_add]
  exact last

/-- The actual pair measures exactly its original result systems once each. -/
lemma cycleCircuit_measurement_count (path : (code).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.measurement (2 : ℕ+))
      ((code).resourcePool path) = wordWidth := by
  have last := RuntimeUnlookup.circuit_measurement_count frame physical sameWires
    parity temporary (splitInputs source) output mask path.2
  rw [cycleCircuit_resourcePool, ResourcePool.count_add, lookupCircuit_resourcePool,
    UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  simpa only [Nat.zero_add] using last

/-- The actual caller-owned table and all reused quantum systems remain in the exact peak. -/
lemma cycleCircuit_spaces (path : (code).Path) :
    (code).peakResidentSpace path = ctx.residentSpace ∧
      (code).peakAuxiliarySpace path = ctx.auxiliarySpace :=
  ⟨Circuit.fixed_peakResidentSpace _ _, Circuit.fixed_peakAuxiliarySpace _ _⟩

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeTable
