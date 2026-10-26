/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Circuit
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Row.Count
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Circuit.Count
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Circuit.Resources

/-!
# Actual high-half feedback ledger

Every retained high leaf runs its real paid parity row and native masked
phase on the reused result systems. The complete static selector contributes
its actual forks. Counts and quantum depth come from these same actual paths,
without assuming clean unary values or an ideal phase implementation.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {resultWidth lowWidth highRemaining : Nat}
  (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)
  (physical : QubitLayout encoding.width)
  (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
  (measured : CInputRef ctx (.bits resultWidth))
  (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit)
  (temporary : CWriteRef ctx .bit)
  (table : Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) →
    CInputRef ctx (.unsignedWord resultWidth))

private lemma halfCircuit_gate_count_le (coordinate : AlgorithmGate.Coordinate) (bound : Nat)
    (callbackBound : ∀ label path, ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate coordinate)
      ((halfCallback frame (services := services)
        physical sameWires measured parity temporary table label).resourcePool path) ≤ bound)
    (path : (halfCircuit frame (services := services)
      physical sameWires measured parity temporary table).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate coordinate)
      ((halfCircuit frame physical sameWires measured parity temporary table).resourcePool path) ≤
        (2 ^ highRemaining - 1) * SelectorFrame.hybridGateForkCount coordinate +
          2 ^ highRemaining * bound := by
  have actual := frame.high.circuitAt_gate_count_le physical sameWires
    (halfCallback frame (services := services) physical sameWires measured parity temporary table)
    coordinate bound callbackBound (SelectorTrie.full highRemaining) 0 (by omega) 0 (by omega) path
  simpa only [halfCircuit, SelectorFrame.circuit, SelectorTrie.full_forks,
    SelectorTrie.full_leaves] using actual

/-- The actual unitary selector is the only source of native Toffoli events in a paid half. -/
lemma halfCircuit_toffoli_count_le
    (path : (halfCircuit frame (services := services)
      physical sameWires measured parity temporary table).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .toffoli)
      ((halfCircuit frame physical sameWires measured parity temporary table).resourcePool path) ≤
        2 * (2 ^ highRemaining - 1) := by
  have actual := halfCircuit_gate_count_le frame physical sameWires measured parity temporary table
    .toffoli 0
    (fun label current => Nat.le_of_eq (RuntimeRow.rowCircuit_toffoli_count physical sameWires
      measured parity temporary (table label) frame.lowWord frame.low.targetDistinct
      (frame.high.stack ⟨highRemaining, by omega⟩) (frame.highStack_lowWord _) lowWidth current))
    path
  simpa [SelectorFrame.hybridGateForkCount, Nat.mul_comm] using actual

/-- Actual masked fan-in and inverse charge their original CNOTs at every high leaf. -/
lemma halfCircuit_cnot_count_le
    (path : (halfCircuit frame (services := services)
      physical sameWires measured parity temporary table).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .cnot)
      ((halfCircuit frame physical sameWires measured parity temporary table).resourcePool path) ≤
        (2 ^ highRemaining - 1) + 2 ^ highRemaining * (2 * 2 ^ lowWidth - 1) := by
  have actual := halfCircuit_gate_count_le frame physical sameWires
    measured parity temporary table .cnot
    (2 * 2 ^ lowWidth - 1)
    (fun label current => RuntimeRow.rowCircuit_cnot_count_le physical sameWires
      measured parity temporary
      (table label) frame.lowWord frame.low.targetDistinct
      (frame.high.stack ⟨highRemaining, by omega⟩) (frame.highStack_lowWord _) lowWidth
      (Nat.le_refl _) current) path
  simpa [SelectorFrame.hybridGateForkCount] using actual

/-- The real selector X and feedback H events retain
their complete native single-qubit bound. -/
lemma halfCircuit_singleQubit_count_le
    (path : (halfCircuit frame (services := services)
      physical sameWires measured parity temporary table).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .singleQubit)
      ((halfCircuit frame physical sameWires measured parity temporary table).resourcePool path) ≤
        2 * (2 ^ highRemaining - 1) + 2 * 2 ^ highRemaining := by
  have actual := halfCircuit_gate_count_le frame physical sameWires measured parity temporary table
    .singleQubit
    2 (fun label current => RuntimeRow.rowCircuit_singleQubit_count_le physical sameWires
      measured parity temporary (table label) frame.lowWord frame.low.targetDistinct
      (frame.high.stack ⟨highRemaining, by omega⟩) (frame.highStack_lowWord _) lowWidth current)
    path
  simpa [SelectorFrame.hybridGateForkCount, Nat.mul_comm] using actual

/-- Every high leaf pays its real column clears and full-width AND/XOR pairs. -/
lemma halfCircuit_classical_weight_le
    (path : (halfCircuit frame (services := services)
      physical sameWires measured parity temporary table).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((halfCircuit frame physical sameWires measured parity temporary table).resourcePool path) ≤
        2 ^ highRemaining * 2 ^ lowWidth * (2 * resultWidth + 1) := by
  have actual := frame.high.circuitAt_weight_le physical sameWires
    (halfCallback frame (services := services) physical sameWires measured parity temporary table)
    Resource.Event.classicalOperationWeight (2 ^ lowWidth * (2 * resultWidth + 1))
    (fun label current => RuntimeRow.rowCircuit_classical_weight_le physical sameWires
      measured parity temporary
      (table label) frame.lowWord frame.low.targetDistinct
      (frame.high.stack ⟨highRemaining, by omega⟩) (frame.highStack_lowWord _) lowWidth current)
    (SelectorTrie.full highRemaining) 0 (by omega) 0 (by omega) path
  simpa [halfCircuit, SelectorFrame.circuit, SelectorTrie.full_leaves,
    SelectorFrame.hybridForkWeight,
    Resource.Event.classicalOperationWeight, Nat.mul_assoc] using actual

/-- Physical fan-in layers keep their actual parallel quantum depth at every retained high leaf. -/
lemma halfCircuit_quantumTime_le
    (path : (halfCircuit frame (services := services)
      physical sameWires measured parity temporary table).Path) :
    (halfCircuit frame physical sameWires measured parity temporary table).depth
      Resource.Event.quantumDuration path ≤
        5 * (2 ^ highRemaining - 1) + 2 ^ highRemaining * (2 * lowWidth + 3) := by
  have actual := frame.high.circuitAt_quantumTime_le physical sameWires
    (halfCallback frame (services := services) physical sameWires measured parity temporary table)
    (2 * lowWidth + 3)
    (fun label current => RuntimeRow.rowCircuit_quantumTime_le physical sameWires
      measured parity temporary
      (table label) frame.lowWord frame.low.targetDistinct
      (frame.high.stack ⟨highRemaining, by omega⟩) (frame.highStack_lowWord _) lowWidth current)
    (SelectorTrie.full highRemaining) 0 (by omega) 0 (by omega) path
  simpa only [halfCircuit, SelectorFrame.circuit, SelectorTrie.full_forks,
    SelectorTrie.full_leaves] using actual

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup
