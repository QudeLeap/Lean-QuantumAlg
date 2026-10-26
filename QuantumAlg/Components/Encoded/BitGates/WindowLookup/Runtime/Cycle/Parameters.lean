/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Cycle.Report
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Cycle.Quantum

/-!
# Literal existing placements of actual runtime window circuits

Parameters contain actual physical frames, existing classical storage and
the native mask-tree height. No table value, operator or resource witness
is supplied. The circuit and every path's bounds follow from these literal
placements; clean-state and graph semantics remain separate proved laws.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeTable

open Execution

variable {Data : Type} (encoding : BinaryLabelEncoding Data)

/-- Existing real systems and storage for one runtime load and paid measured unlookup. -/
structure CycleParameters (ctx : RuntimeCtx .quantum)
    (wordWidth lowWidth highRemaining : Nat) where
  frame : UnlookupFrame encoding wordWidth lowWidth highRemaining
  lookup : SelectorFrame encoding (highRemaining + lowWidth)
  outsideAddress : ∀ bit label, (frame.result.bit bit).wire ≠ (lookup.address label).wire
  outsideStack : ∀ bit label, (frame.result.bit bit).wire ≠ (lookup.stack label).wire
  physical : QubitLayout encoding.width
  sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires
  source : CInputRef ctx
    (.fixedVector (2 ^ (highRemaining + lowWidth + 1)) (.unsignedWord wordWidth))
  output : Fin wordWidth → CWriteRef ctx (.finite 2)
  mask : CWriteRef ctx (.bits wordWidth)
  parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit
  temporary : CWriteRef ctx .bit
  height : Nat
  covered : wordWidth ≤ 2 ^ height

namespace CycleParameters

noncomputable section

variable {encoding} {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {wordWidth lowWidth highRemaining : Nat}
  (parameters : CycleParameters encoding ctx wordWidth lowWidth highRemaining)

/-- The actual runtime circuit is determined entirely by the literal existing placement. -/
def circuit : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  cycleCircuit parameters.frame parameters.lookup parameters.outsideAddress parameters.outsideStack
    parameters.physical parameters.sameWires parameters.source parameters.height parameters.output
    parameters.mask parameters.parity parameters.temporary

/-- Both bounds project the same real circuit's event pool, without combining coordinates. -/
lemma separate_coordinates (path : (parameters.circuit (services := services)).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .cnot)
      (parameters.circuit.resourcePool path) ≤
        staticCycleCnotLimit wordWidth highRemaining lowWidth ∧
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (parameters.circuit.resourcePool path) ≤
        runtimeCycleClassicalLimit wordWidth highRemaining lowWidth :=
  cycleCircuit_separate_coordinates parameters.frame parameters.lookup parameters.outsideAddress
    parameters.outsideStack parameters.physical parameters.sameWires parameters.source
    parameters.height parameters.output parameters.mask parameters.parity parameters.temporary
    parameters.covered path

/-- The complete actual result word is physically measured once per supplied circuit. -/
lemma measurement_count (path : (parameters.circuit (services := services)).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.measurement (2 : ℕ+))
      (parameters.circuit.resourcePool path) = wordWidth :=
  cycleCircuit_measurement_count parameters.frame parameters.lookup parameters.outsideAddress
    parameters.outsideStack parameters.physical parameters.sameWires parameters.source
    parameters.height parameters.output parameters.mask parameters.parity parameters.temporary path

/-- The actual native Toffolis follow directly from the supplied physical circuit placement. -/
lemma toffoli_count_le (path : (parameters.circuit (services := services)).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .toffoli)
      (parameters.circuit.resourcePool path) ≤
        (2 * 2 ^ (highRemaining + lowWidth + 1) - 4) +
          (2 * (2 ^ lowWidth - 1) + (2 * 2 ^ (highRemaining + 1) - 4)) :=
  cycleCircuit_toffoli_count_le parameters.frame parameters.lookup parameters.outsideAddress
    parameters.outsideStack parameters.physical parameters.sameWires parameters.source
    parameters.height parameters.output parameters.mask parameters.parity parameters.temporary
    parameters.covered path

/-- Native dependence depth uses the actual supplied tree height and retains parallel layers. -/
lemma quantumTime_le (path : (parameters.circuit (services := services)).Path) :
    parameters.circuit.depth Resource.Event.quantumDuration path ≤
      (2 + 10 * (2 ^ (highRemaining + lowWidth) - 1) +
        2 * 2 ^ (highRemaining + lowWidth) * (2 * parameters.height + 1)) +
        (2 + 2 * (2 ^ lowWidth + lowWidth) +
          ((2 * lowWidth + 8) * 2 ^ (highRemaining + 1) - 8)) :=
  cycleCircuit_quantumTime_le parameters.frame parameters.lookup parameters.outsideAddress
    parameters.outsideStack parameters.physical parameters.sameWires parameters.source
    parameters.height parameters.output parameters.mask parameters.parity parameters.temporary path

end

end CycleParameters

end QuantumAlg.EncodedBit.WindowLookup.RuntimeTable
