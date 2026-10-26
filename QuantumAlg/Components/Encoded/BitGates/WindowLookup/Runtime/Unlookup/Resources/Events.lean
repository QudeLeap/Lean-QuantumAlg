/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Resources.Complete
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Row.Events
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Circuit.Events
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Events

/-!
# Independent complete event allowance for actual measured runtime unlookup

Each high-address leaf includes every paid parity column and selected physical
phase. Both high halves, the native unary preparation and inverse, and the
original H/MZ/pack/X reset retain their complete literal native coordinates.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup

noncomputable section

/-- Complete independent allowance for one original high-address traversal. -/
def halfEnvelope (services : ClassicalOracleModel) (resultWidth lowWidth highRemaining : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services) :=
  (2 ^ highRemaining - 1) • SelectorFrame.hybridForkEnvelope .empty BitWord.model services +
    2 ^ highRemaining • RuntimeRow.rowEnvelope services resultWidth (2 ^ lowWidth)

/-- The original pair of high halves includes both real top-bit flips. -/
def phaseEnvelope (services : ClassicalOracleModel) (resultWidth lowWidth highRemaining : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services) :=
  ResourcePool.singleton
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .singleQubit) +
    (halfEnvelope services resultWidth lowWidth highRemaining +
      (ResourcePool.singleton
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .singleQubit) +
        halfEnvelope services resultWidth lowWidth highRemaining))

/-- Independent complete allowance for native unary preparation and its inverse. -/
def unaryEnvelope (services : ClassicalOracleModel) (width : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services) :=
  AlgorithmGate.gateEnvelope BitWord.model services 1 (2 ^ width - 1) (2 ^ width - 1)

/-- Original unary preparation, paid feedback and true unary inverse. -/
def restorationEnvelope (services : ClassicalOracleModel)
    (resultWidth lowWidth highRemaining : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services) :=
  unaryEnvelope services lowWidth +
    (phaseEnvelope services resultWidth lowWidth highRemaining + unaryEnvelope services lowWidth)

/-- Complete finite allowance for the same measured/reset/restoration program. -/
def envelope (services : ClassicalOracleModel) (resultWidth lowWidth highRemaining : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services) :=
  measuredResetWordEnvelope services resultWidth +
    restorationEnvelope services resultWidth lowWidth highRemaining

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {resultWidth lowWidth highRemaining : Nat}
  (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)
  (physical : QubitLayout encoding.width)
  (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)

/-- Every actual high leaf pays its complete finite row pool. -/
lemma halfCircuit_pool_le (measured : CInputRef ctx (.bits resultWidth))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (table : Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) →
      CInputRef ctx (.unsignedWord resultWidth))
    (path : (halfCircuit frame (services := services)
      physical sameWires measured parity temporary table).Path) :
    (halfCircuit frame physical sameWires measured parity temporary table).resourcePool path ≤
      halfEnvelope services resultWidth lowWidth highRemaining := by
  have actual := frame.high.circuitAt_pool_le physical sameWires
    (halfCallback frame physical sameWires measured parity temporary table)
    (RuntimeRow.rowEnvelope services resultWidth (2 ^ lowWidth))
    (fun label selected => RuntimeRow.rowCircuit_pool_le physical sameWires
      measured parity temporary (table label) frame.lowWord frame.low.targetDistinct
      (frame.high.stack ⟨highRemaining, by omega⟩) (frame.highStack_lowWord _) lowWidth
      (Nat.le_refl _) selected)
    (SelectorTrie.full highRemaining) 0 (by omega) 0 (by omega) path
  simpa only [halfCircuit, SelectorFrame.circuit, SelectorTrie.full_forks,
    SelectorTrie.full_leaves, halfEnvelope] using actual

/-- Both chronological high halves retain every native coordinate and both top-bit flips. -/
lemma phaseCircuit_pool_le (measured : CInputRef ctx (.bits resultWidth))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) →
      CInputRef ctx (.unsignedWord resultWidth))
    (path : (phaseCircuit frame (services := services)
      physical sameWires measured parity temporary table).Path) :
    (phaseCircuit frame physical sameWires measured parity temporary table).resourcePool path ≤
      phaseEnvelope services resultWidth lowWidth highRemaining := by
  rw [phaseCircuit_resourcePool]
  exact add_le_add le_rfl
    (add_le_add (halfCircuit_pool_le frame physical sameWires measured parity temporary
      (table false) path.2.1) (add_le_add le_rfl
        (halfCircuit_pool_le frame physical sameWires measured parity temporary
          (table true) path.2.2.2)))

/-- The original native unary pair surrounds the complete paid feedback pool. -/
lemma restorationCircuit_pool_le (measured : CInputRef ctx (.bits resultWidth))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) →
      CInputRef ctx (.unsignedWord resultWidth))
    (path : (restorationCircuit frame (services := services)
      physical sameWires measured parity temporary table).Path) :
    (restorationCircuit frame physical sameWires measured parity temporary table).resourcePool
      path ≤ restorationEnvelope services resultWidth lowWidth highRemaining := by
  rw [restorationCircuit_resourcePool]
  apply add_le_add
  · apply AlgorithmGate.algorithmGate_unitary_pool_le
    intro coordinate
    cases coordinate with
    | singleQubit => exact (frame.low.program_singleQubit_count physical .empty).le
    | cnot => exact (frame.low.program_cnot_count physical .empty).le
    | toffoli => exact (frame.low.program_toffoli_count physical .empty).le
  · apply add_le_add
    · exact phaseCircuit_pool_le frame physical sameWires measured parity temporary table path.2.1
    · apply AlgorithmGate.algorithmGate_unitary_pool_le
      intro coordinate
      rw [frame.low.uncomputeProgram_event_count]
      cases coordinate with
      | singleQubit => exact (frame.low.program_singleQubit_count physical .empty).le
      | cnot => exact (frame.low.program_cnot_count physical .empty).le
      | toffoli => exact (frame.low.program_toffoli_count physical .empty).le

/-- Every actual complete unlookup path obeys the independent finite native event allowance. -/
lemma circuit_pool_le (output : Fin resultWidth → CWriteRef ctx (.finite 2))
    (mask : CWriteRef ctx (.bits resultWidth)) (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit)
    (temporary : CWriteRef ctx .bit)
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) →
      CInputRef ctx (.unsignedWord resultWidth))
    (path : (circuit frame (services := services)
      physical sameWires output mask parity temporary table).Path) :
    (circuit frame physical sameWires output mask parity temporary table).resourcePool path ≤
      envelope services resultWidth lowWidth highRemaining := by
  rw [circuit_resourcePool]
  exact add_le_add
    (measuredResetWordCircuit_pool_le physical sameWires frame.result frame.resultDistinct
      output mask path.1)
    (restorationCircuit_pool_le frame physical sameWires (.storage mask.toCStorageRef)
      parity temporary table path.2)

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup
