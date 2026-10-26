/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Parity
import all QuantumAlg.Core.Base.Accounting.ClassicalWeight
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Execution.Circuit.Allocation

/-!
# Exact native classical work for runtime table parity

The real trace contains one initial XOR clear, one AND per original table
bit and one XOR per original table bit. These classical coordinates remain
separate from quantum CNOTs. Their quantum duration is zero, while their
native-operation weight and their caller-owned storage are retained.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeParity

open Execution

noncomputable section

variable {ctx : RuntimeCtx .quantum} {oracles : OracleModel}
  {services : ClassicalOracleModel}

/-- The exact ordered native operations of every actual fixed pair traversal. -/
lemma foldProgram_eventTrace (parity temporary : CWriteRef ctx .bit)
    (pairs : List (CInputRef ctx .bit × CInputRef ctx .bit))
    (path : (foldProgram (oracles := oracles) (services := services)
      parity temporary pairs).Path) :
    (foldProgram parity temporary pairs).eventTrace path =
      (List.replicate pairs.length
        [.classicalOperation (.bit .and), .classicalOperation (.bit .xor)]).flatten := by
  induction pairs with
  | nil => rfl
  | cons input rest ih =>
      change [.classicalOperation (.bit .and), .classicalOperation (.bit .xor)] ++
        (foldProgram parity temporary rest).eventTrace path.2 = _
      rw [ih, List.length_cons, List.replicate_succ, List.flatten_cons]

/-- The actual parity program pays its real clear before every AND/XOR pair. -/
lemma program_eventTrace (parity temporary : CWriteRef ctx .bit)
    (pairs : List (CInputRef ctx .bit × CInputRef ctx .bit))
    (path : (program (oracles := oracles) (services := services)
      parity temporary pairs).Path) :
    (program parity temporary pairs).eventTrace path =
      .classicalOperation (.bit .xor) ::
        (List.replicate pairs.length
          [.classicalOperation (.bit .and), .classicalOperation (.bit .xor)]).flatten := by
  change [.classicalOperation (.bit .xor)] ++
    (foldProgram parity temporary pairs).eventTrace path.2 = _
  rw [foldProgram_eventTrace]
  rfl

private lemma fold_weight (parity temporary : CWriteRef ctx .bit)
    (pairs : List (CInputRef ctx .bit × CInputRef ctx .bit))
    (path : (foldProgram (oracles := oracles) (services := services)
      parity temporary pairs).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((foldProgram parity temporary pairs).resourcePool path) = 2 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons input rest ih =>
      change ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (ResourcePool.ofList
          ([.classicalOperation (.bit .and), .classicalOperation (.bit .xor)] ++
            (foldProgram parity temporary rest).eventTrace path.2)) = _
      rw [ResourcePool.ofList_append, ResourcePool.weightedCount_add]
      change 2 + ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        ((foldProgram parity temporary rest).resourcePool path.2) = _
      rw [ih, List.length_cons]
      omega

/-- A W-bit runtime row pays exactly 2W+1 native classical operations on every actual path. -/
lemma program_classical_weight (parity temporary : CWriteRef ctx .bit)
    (pairs : List (CInputRef ctx .bit × CInputRef ctx .bit))
    (path : (program (oracles := oracles) (services := services)
      parity temporary pairs).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((program parity temporary pairs).resourcePool path) = 2 * pairs.length + 1 := by
  change ResourcePool.weightedCount Resource.Event.classicalOperationWeight
    (ResourcePool.ofList ([.classicalOperation (.bit .xor)] ++
      (foldProgram parity temporary pairs).eventTrace path.2)) = _
  rw [ResourcePool.ofList_append, ResourcePool.weightedCount_add]
  change 1 + ResourcePool.weightedCount Resource.Event.classicalOperationWeight
    ((foldProgram parity temporary pairs).resourcePool path.2) = _
  rw [fold_weight]
  omega

/-- Native AND/XOR instructions remain classical in the actual dependency schedule. -/
lemma foldProgram_quantumTime (parity temporary : CWriteRef ctx .bit)
    (pairs : List (CInputRef ctx .bit × CInputRef ctx .bit))
    (path : (foldProgram (oracles := oracles) (services := services)
      parity temporary pairs).Path) :
    (foldProgram parity temporary pairs).depth Resource.Event.quantumDuration path = 0 := by
  induction pairs with
  | nil => rfl
  | cons input rest ih =>
      change (0 + 0) + (foldProgram parity temporary rest).depth
        Resource.Event.quantumDuration path.2 = 0
      rw [ih]

/-- The initial clear has zero quantum duration and remains a paid classical coordinate. -/
lemma program_quantumTime (parity temporary : CWriteRef ctx .bit)
    (pairs : List (CInputRef ctx .bit × CInputRef ctx .bit))
    (path : (program (oracles := oracles) (services := services)
      parity temporary pairs).Path) :
    (program parity temporary pairs).depth Resource.Event.quantumDuration path = 0 := by
  change 0 + (foldProgram parity temporary pairs).depth Resource.Event.quantumDuration path.2 = 0
  rw [foldProgram_quantumTime]

/-- Supplied table, mask, parity and temporary cells remain included in resident space. -/
lemma program_peakResidentSpace (parity temporary : CWriteRef ctx .bit)
    (pairs : List (CInputRef ctx .bit × CInputRef ctx .bit))
    (path : (program (oracles := oracles) (services := services)
      parity temporary pairs).Path) :
    (program parity temporary pairs).peakResidentSpace path = ctx.residentSpace :=
  Circuit.fixed_peakResidentSpace _ _

/-- Auxiliary storage follows the unchanged roles of the same caller-owned cells. -/
lemma program_peakAuxiliarySpace (parity temporary : CWriteRef ctx .bit)
    (pairs : List (CInputRef ctx .bit × CInputRef ctx .bit))
    (path : (program (oracles := oracles) (services := services)
      parity temporary pairs).Path) :
    (program parity temporary pairs).peakAuxiliarySpace path = ctx.auxiliarySpace :=
  Circuit.fixed_peakAuxiliarySpace _ _

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeParity
