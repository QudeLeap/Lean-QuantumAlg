/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Cycle.Resources

/-!
# Separate runtime CNOT and paid classical coordinates

The concrete full sixteen-bit and four-bit tail bounds project the actual
runtime-array load/reset/feedback pool. All per-bit AND/XOR instructions
remain in the separate native-classical coordinate. These upper bounds
include no conversion between quantum CNOTs and classical operations.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeTable

/-- Native-classical ceiling for paid full-width runtime table/mask parity. -/
def runtimeCycleClassicalLimit (wordWidth highRemaining lowWidth : Nat) : Nat :=
  1 + 2 ^ (highRemaining + 1) * 2 ^ lowWidth * (2 * wordWidth + 1)

/-- Full sixteen-bit runtime cycle bounds retain their two original distinct coordinates. -/
lemma runtimeCycle_full16_limits :
    staticCycleCnotLimit 256 7 8 = 33686010 ∧
      runtimeCycleClassicalLimit 256 7 8 = 33619969 := by
  norm_num [staticCycleCnotLimit, runtimeCycleClassicalLimit]

/-- The actual four-bit tail has the same paid per-bit classical interpretation. -/
lemma runtimeCycle_tail4_limits :
    staticCycleCnotLimit 256 1 2 = 8226 ∧
      runtimeCycleClassicalLimit 256 1 2 = 8209 := by
  norm_num [staticCycleCnotLimit, runtimeCycleClassicalLimit]

/-- Three rounds of six calls across both streams have separate original coordinate ceilings. -/
lemma runtimeCycle_threeRound_limits :
    18 * (2 * (16 * staticCycleCnotLimit 256 7 8 +
      staticCycleCnotLimit 256 1 2)) = 19403437896 ∧
    18 * (2 * (16 * runtimeCycleClassicalLimit 256 7 8 +
      runtimeCycleClassicalLimit 256 1 2)) = 19365397668 := by
  norm_num [staticCycleCnotLimit, runtimeCycleClassicalLimit]

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {wordWidth lowWidth highRemaining : Nat}

/-- Both reporting bounds are derived from the same actual runtime circuit and path. -/
lemma cycleCircuit_separate_coordinates
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
    (covered : wordWidth ≤ 2 ^ height)
    (path : (cycleCircuit (services := services) frame lookup outsideAddress outsideStack
      physical sameWires source height output mask parity temporary).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .cnot)
      ((cycleCircuit frame lookup outsideAddress outsideStack physical sameWires source height
        output mask parity temporary).resourcePool path) ≤
          staticCycleCnotLimit wordWidth highRemaining lowWidth ∧
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((cycleCircuit frame lookup outsideAddress outsideStack physical sameWires source height
        output mask parity temporary).resourcePool path) ≤
          runtimeCycleClassicalLimit wordWidth highRemaining lowWidth :=
  ⟨cycleCircuit_cnot_count_le frame lookup outsideAddress outsideStack physical sameWires
      source height output mask parity temporary covered path,
    cycleCircuit_classical_weight_le frame lookup outsideAddress outsideStack physical sameWires
      source height output mask parity temporary path⟩

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeTable
