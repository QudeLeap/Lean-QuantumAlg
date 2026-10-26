/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Cardinality
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Shared.Add.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Shared.Sub.Resources
import all QuantumAlg.Components.Classical.Modular.NativePower.Resources
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Path
import all QuantumAlg.Core.Base.Accounting.ClassicalWeight
import all QuantumAlg.Core.Base.Accounting.Weighted

/-!
# Actual native instruction accounting for five-table construction

The arithmetic costs below project the real instruction traces and real
XGCD/reduction envelope. Indexed composition sums each selected component
path. Quantum CNOT coordinates and native classical-operation weights stay
distinct; these lemmas introduce no conversion between them.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Accounting

open Execution Modular.NativePower ClassicalAlgorithms.Modular
open scoped BigOperators

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Actual shared-modulus multiplication emits its three original native instructions. -/
lemma multiply_eventCount (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (scopedMultiply (model := model) left right modulus output).Path) :
    ((scopedMultiply (model := model) left right modulus output).eventTrace path).length = 3 := by
  have counted := congrArg Multiset.card (nativePower_scopedMultiply_pool left right modulus
    output path)
  simpa only [Circuit.resourcePool, ResourcePool.ofList, Multiset.coe_card, multiplyEnvelope,
    Multiset.card_add, ResourcePool.singleton, Multiset.card_replicate] using counted

/-- The total coefficient uses its actual loaded XGCD and unconditional signed reduction. -/
lemma coefficient_eventCount_le (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (Field.Native.coefficientIntoWord (model := model) spec denominator output).Path) :
    ((Field.Native.coefficientIntoWord (model := model) spec denominator output).eventTrace
      path).length ≤ 30 * width + 70 := by
  have actual := Multiset.card_le_card
    (Field.Native.coefficientIntoWord_pool_le spec denominator output path)
  have counted :
      ((Field.Native.coefficientIntoWord (model := model) spec denominator output).eventTrace
        path).length ≤ (Field.Native.coefficientEnvelope model spec).card := by
    simpa only [Circuit.resourcePool, ResourcePool.ofList, Multiset.coe_card] using actual
  exact counted.trans (Field.Native.coefficientEnvelope_card_le model spec)

omit [BitWord.Selected model] in
/-- Every actual loop path sums its own per-index component ceilings. -/
lemma range_eventCount_le {allocate : Bool} (count : Nat)
    (body : Fin count → Circuit model ctx ctx allocate) (budget : Fin count → Nat)
    (bounded : ∀ index path, ((body index).eventTrace path).length ≤ budget index)
    (path : (Circuit.forRange count body).Path) :
    ((Circuit.forRange count body).eventTrace path).length ≤ ∑ index, budget index := by
  rw [Circuit.forRange_eventCount_eq_sum]
  exact Finset.sum_le_sum fun index _ => bounded index _

/-- A single closed native instruction emits one event of its declared coordinate. -/
lemma instruction_eventCount {input output : CShape} (op : ClassicalOp input output ctx ctx)
    (path : (BitWord.instruction (execution := model) op).Path) :
    ((BitWord.instruction (execution := model) op).eventTrace path).length = 1 := by
  rw [BitWord.bitWord_instruction_eventTrace]
  rfl

omit [BitWord.Selected model] in
/-- Native classical operation weight is bounded by the real event count, without gate exchange. -/
lemma classical_weight_le_eventCount {allocate : Bool} (code : Circuit model ctx ctx allocate)
    (path : code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight (code.resourcePool path) ≤
      (code.eventTrace path).length := by
  rw [Circuit.resourcePool, ResourcePool.weightedCount_ofList]
  generalize code.eventTrace path = events
  induction events with
  | nil => rfl
  | cons event rest ih =>
      have unit : Resource.Event.classicalOperationWeight event ≤ 1 := by
        cases event <;> simp [Resource.Event.classicalOperationWeight]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Accounting
