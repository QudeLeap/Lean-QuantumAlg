/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Row.Count
import all QuantumAlg.Components.GateModel.Algorithm.Resources.Events

/-!
# Complete native pools for real stored-table parity rows

Every column keeps its actual XOR clear and all AND/XOR pairs. The selected
physical phase is bounded by its original native gate counts. Both parts are
combined without replacing the finite native alphabet by a scalar weight.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeRow

open Execution

noncomputable section

/-- The independent exact trace pool of one width-indexed classical parity column. -/
def parityEnvelope (services : ClassicalOracleModel) (width : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services) :=
  ResourcePool.ofList (.classicalOperation (.bit .xor) ::
    (List.replicate width [.classicalOperation (.bit .and),
      .classicalOperation (.bit .xor)]).flatten)

/-- All real classical columns plus the selected native physical feedback allowance. -/
def rowEnvelope (services : ClassicalOracleModel) (width columns : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services) :=
  columns • parityEnvelope services width +
    AlgorithmGate.gateEnvelope BitWord.model services 2 (2 * columns - 1) 0

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel} {wordWidth columns : Nat}

/-- The real parity program has exactly its independent width-indexed classical pool. -/
lemma rowProgram_pool (measured : CInputRef ctx (.bits wordWidth))
    (parity : Fin columns → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (table : Fin columns → CInputRef ctx (.unsignedWord wordWidth))
    (indices : List (Fin columns))
    (path : (rowProgram (oracles := .empty) (services := services)
      measured parity temporary table indices).Path) :
    (rowProgram measured parity temporary table indices).resourcePool path =
      indices.length • parityEnvelope services wordWidth := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      dsimp only [rowProgram, Circuit.Path] at path
      change ResourcePool.ofList (_ ++ _) = _
      rw [ResourcePool.ofList_append]
      have first := RuntimeParity.program_eventTrace (oracles := .empty) (services := services)
        (parity index) temporary (RuntimeParity.inputs (table index) measured) path.1
      simp only [RuntimeParity.inputs, List.length_ofFn] at first ⊢
      rw [first]
      change parityEnvelope services wordWidth +
        (rowProgram (oracles := .empty) (services := services)
          measured parity temporary table rest).resourcePool path.2 = _
      rw [ih]
      simp only [List.length_cons, add_nsmul, one_nsmul, parityEnvelope, add_comm]

/-- All actual parity reads and the original stored-mask phase obey the complete finite pool. -/
lemma rowCircuit_pool_le (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits wordWidth))
    (parity : Fin columns → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (table : Fin columns → CInputRef ctx (.unsignedWord wordWidth)) (target : Word encoding columns)
    (distinct : Function.Injective fun index => (target.bit index).wire)
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire)
    (height : Nat) (covered : columns ≤ 2 ^ height)
    (path : (rowCircuit (oracles := .empty) (services := services) physical sameWires
      measured parity temporary table target distinct selector outside height).Path) :
    (rowCircuit physical sameWires measured parity temporary table target distinct
      selector outside height).resourcePool path ≤ rowEnvelope services wordWidth columns := by
  dsimp only [rowCircuit, Circuit.Path] at path
  have first := rowProgram_pool measured parity temporary table (List.ofFn fun index => index)
    path.1
  simp only [List.length_ofFn] at first
  have native := AlgorithmGate.algorithmGate_unitary_pool_le
    (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
      (wordMaskParityPhaseProgram physical .empty target distinct selector outside
        (MaskParity.storedConstant path.2.1) height)) BitWord.model services 2 (2 * columns - 1) 0
    (by
      intro coordinate
      rw [unitaryOfEqualWires_cost]
      cases coordinate with
      | toffoli => exact (wordPhase_toffoli_count physical target distinct selector outside _ _).le
      | singleQubit =>
          have actual := maskedParityPhaseProgram_singleQubit_count physical .empty
            (constantMaskTarget target (MaskParity.storedConstant path.2.1))
            (constantMaskTarget_distinct target distinct _) selector
            (fun index => outside ((Word.constantOneIndices _).get index)) height
          change ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
            (.gate .singleQubit)
            (wordMaskParityPhaseProgram physical .empty target distinct selector outside _
              height).eventCost = _ at actual
          rw [actual]
          change _ ≤ 2
          split <;> omega
      | cnot =>
          have selected := Word.constantOneIndices_length_le (MaskParity.storedConstant path.2.1)
          have actual := maskedParityPhaseProgram_cnot_count physical .empty
            (constantMaskTarget target (MaskParity.storedConstant path.2.1))
            (constantMaskTarget_distinct target distinct _) selector
            (fun index => outside ((Word.constantOneIndices _).get index)) height
            (selected.trans covered)
          change ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
            (.gate .cnot)
            (wordMaskParityPhaseProgram physical .empty target distinct selector outside _
              height).eventCost = _ at actual
          rw [actual]
          change _ ≤ 2 * columns - 1
          split <;> omega)
  change ResourcePool.ofList (_ ++ _) ≤ _
  rw [ResourcePool.ofList_append]
  change (rowProgram (oracles := .empty) (services := services)
    measured parity temporary table (List.ofFn fun index => index)).resourcePool path.1 + _ ≤ _
  rw [first]
  change columns • parityEnvelope services wordWidth + ResourcePool.ofList
    ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
      (wordMaskParityPhaseProgram physical .empty target distinct selector outside
        (MaskParity.storedConstant path.2.1) height)).eventTrace BitWord.model services) ≤ _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost _ BitWord.model services]
  exact add_le_add le_rfl native

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeRow
