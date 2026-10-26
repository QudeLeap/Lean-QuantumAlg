/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Lookup
import all QuantumAlg.Core.Base.Accounting.ClassicalWeight
import all QuantumAlg.Core.Base.Accounting.Weighted

/-!
# Actual runtime-table lookup quantum and classical coordinates

The real stored-array read selects a fixed native template. Its original
parallel dependence depth and gate counts survive the selection. Structural
reads do not introduce a classical computation; paid runtime AND/XOR parity
belongs to the subsequent actual unlookup program.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeTable

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {width wordWidth : Nat}
  (source : CInputRef ctx (.fixedVector (2 ^ (width + 1)) (.unsignedWord wordWidth)))
  (frame : SelectorFrame encoding width) (target : LookupTarget frame wordWidth)
  (physical : QubitLayout encoding.width)
  (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires) (height : Nat)

local notation "code" => lookupCircuit (oracles := oracles) (services := services)
  source frame target physical sameWires height

/-- Actual runtime selection preserves the original selector's exact native Toffoli count. -/
lemma lookupCircuit_toffoli_count (covered : wordWidth ≤ 2 ^ height) (path : (code).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles BitWord.model services) (.gate .toffoli)
      ((code).resourcePool path) = 2 * 2 ^ (width + 1) - 4 := by
  rw [lookupCircuit_resourcePool,
    UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  exact splitLookupProgram_toffoli_count frame physical oracles target
    (tableValue path.1) height covered

/-- Actual runtime selection preserves the original selector's exact native X count. -/
lemma lookupCircuit_singleQubit_count (covered : wordWidth ≤ 2 ^ height) (path : (code).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles BitWord.model services) (.gate .singleQubit)
      ((code).resourcePool path) = 2 * 2 ^ (width + 1) - 2 := by
  rw [lookupCircuit_resourcePool,
    UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  exact splitLookupProgram_singleQubit_count frame physical oracles target
    (tableValue path.1) height covered

/-- The fixed actual loader branch contains only the selected native unitary's quantum events. -/
lemma lookupCircuit_classical_weight (path : (code).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((code).resourcePool path) = 0 := by
  rw [lookupCircuit_resourcePool]
  apply ResourcePool.weightedCount_eq_zero_of_mem
  intro event present
  cases event with
  | classicalOperation coordinate =>
      have absent := UnitaryCircuit.unitaryCircuit_event_count_classical_context
        (splitLookupProgram frame physical oracles target (tableValue path.1) height)
        BitWord.model services (.classicalOperation coordinate)
      exact False.elim ((Multiset.count_eq_zero.mp absent) present)
  | _ => rfl

/-- Actual runtime selection retains the original physical parallel mask depth. -/
lemma lookupCircuit_quantumTime_le (path : (code).Path) :
    (code).depth Resource.Event.quantumDuration path ≤
      2 + 10 * (2 ^ width - 1) + 2 * 2 ^ width * (2 * height + 1) := by
  rcases path with ⟨stored, selected⟩
  change DepthExpr.depthEval Resource.Event.quantumDuration
    ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
      (splitLookupProgram frame physical oracles target (tableValue stored) height)).eventDepth
        BitWord.model services) ≤ _
  rw [unitaryOfEqualWires_depth, UnitaryCircuit.unitaryCircuit_quantumDuration_classical_context]
  exact splitLookupProgram_quantumTime_le frame physical oracles target (tableValue stored) height

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeTable
