/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Cycle.Resources

/-!
# Original quantum resources of the actual runtime load/unlookup pair

The paid runtime parity changes the classical coordinate. Native selector,
masked-X, physical reset and restored unary feedback retain their original
Toffoli, single-qubit and parallel dependence depth bounds on every path.
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

/-- The real selected native loader and both actual unary traversals pay every Toffoli. -/
lemma cycleCircuit_toffoli_count_le (covered : wordWidth ≤ 2 ^ height) (path : (code).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .toffoli)
      ((code).resourcePool path) ≤
        (2 * 2 ^ (highRemaining + lowWidth + 1) - 4) +
          (2 * (2 ^ lowWidth - 1) + (2 * 2 ^ (highRemaining + 1) - 4)) := by
  have first := lookupCircuit_toffoli_count source lookup
    (frame.cycleTarget lookup outsideAddress outsideStack) physical sameWires height covered path.1
  have last := RuntimeUnlookup.circuit_toffoli_count_le frame physical sameWires output mask
    parity temporary (splitInputs source) path.2
  rw [cycleCircuit_resourcePool, ResourcePool.count_add, first]
  exact Nat.add_le_add_left last _

/-- All actual selector X, H, selected reset X and restored unary seed gates remain quantum. -/
lemma cycleCircuit_singleQubit_count_le (covered : wordWidth ≤ 2 ^ height)
    (path : (code).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .singleQubit)
      ((code).resourcePool path) ≤
        (2 * 2 ^ (highRemaining + lowWidth + 1) - 2) +
          (2 * wordWidth + 2 + (4 * 2 ^ (highRemaining + 1) - 2)) := by
  have first := lookupCircuit_singleQubit_count source lookup
    (frame.cycleTarget lookup outsideAddress outsideStack) physical sameWires height covered path.1
  have last := RuntimeUnlookup.circuit_singleQubit_count_le frame physical sameWires output mask
    parity temporary (splitInputs source) path.2
  rw [cycleCircuit_resourcePool, ResourcePool.count_add, first]
  exact Nat.add_le_add_left last _

/-- The actual runtime branch retains all internal native parallel layers and exact order. -/
lemma cycleCircuit_quantumTime_le (path : (code).Path) :
    (code).depth Resource.Event.quantumDuration path ≤
      (2 + 10 * (2 ^ (highRemaining + lowWidth) - 1) +
        2 * 2 ^ (highRemaining + lowWidth) * (2 * height + 1)) +
        (2 + 2 * (2 ^ lowWidth + lowWidth) +
          ((2 * lowWidth + 8) * 2 ^ (highRemaining + 1) - 8)) := by
  have first := lookupCircuit_quantumTime_le source lookup
    (frame.cycleTarget lookup outsideAddress outsideStack) physical sameWires height path.1
  have last := RuntimeUnlookup.circuit_quantumTime_le frame physical sameWires output mask
    parity temporary (splitInputs source) path.2
  exact (Circuit.depth_seq (loader) (tailCode)
    Resource.Event.quantumDuration path.1 path.2).trans_le
    (Nat.add_le_add first last)

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeTable
