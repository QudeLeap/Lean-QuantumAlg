/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Layout
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scope.Resources
import all QuantumAlg.Components.Classical.FirstAccepted.Resources

/-!
# Actual native events and serial dependencies of the complete factor scan

Each stored tuple runs its full factor-recovery scope, actual option unpack
and actual first-accepted selector. The finite scan counts every such visit
in order, together with the real initial latch clear and final option pack.
The four enclosing workspace cells are true lexical allocations; their live
capacity is proved separately and their entry or release creates no hidden
arithmetic instruction.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeFactorScan

open ClassicalRoutines

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {N : Nat}

/-- One real nominal unpack precedes the existing native first-accepted selector allowance. -/
def selectionEnvelope (model : ExecutionModel) [BitWord.Selected model] (N : Nat) : ResourcePool
  model :=
  ResourcePool.singleton
    (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.nominalEncoding (.unpackOption (modulusBits N))))) +
      FirstAccepted.nativeEnvelope model (modulusBits N)

/-- Complete factor recovery and actual latch selection are included for each retained tuple. -/
def visitEnvelope (model : ExecutionModel) [BitWord.Selected model] (N : Nat) : ResourcePool model
  :=
  FactorRecovery.NativeFactorTail.eventEnvelope model N + selectionEnvelope model N

/-- The full independent finite-scan ledger counts both real boundary operations. -/
def eventEnvelope (model : ExecutionModel) [BitWord.Selected model] (N count : Nat) : ResourcePool
  model :=
  ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.bit .xor))) +
    (ResourcePool.scale count (visitEnvelope model N) +
      ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.nominalEncoding (.packOption (modulusBits N))))))

/-- The full serial allowance includes initialization, every complete visit and final packing. -/
def depthBound (N count : Nat) : Nat :=
  2 + count * (FactorRecovery.NativeFactorTail.depthBound N + 5)

private theorem selection_pool_le (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (selection (model := model) cells result).Path) :
    (selection (model := model) cells result).resourcePool path ≤ selectionEnvelope model N := by
  change ResourcePool.ofList ((BitWord.instruction (execution := model) (unpackOp cells
    result)).eventTrace path.1 ++
    (FirstAccepted.circuit (model := model) (selectorInputs cells) (selectorRefs cells)).eventTrace
      path.2) ≤ _
  rw [BitWord.bitWord_instruction_eventTrace, ResourcePool.ofList_append]
  exact add_le_add le_rfl
    (FirstAccepted.firstAccepted_pool_le (selectorInputs cells) (selectorRefs cells) path.2)

/-- The actual visit retains every native recovery event before its stored-result selection. -/
theorem visit_pool_le (source : Input N) (inputs : Inputs ctx N) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (visit (model := model) source inputs cells result).Path) :
    (visit (model := model) source inputs cells result).resourcePool path ≤ visitEnvelope model N
      := by
  change ResourcePool.ofList
    ((FactorRecovery.NativeFactorScope.code (model := model) source inputs.parameter inputs.phase
      result).eventTrace
      path.1 ++ (selection (model := model) cells result).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add
    (FactorRecovery.NativeFactorScope.code_pool_le
      source inputs.parameter inputs.phase result path.1)
    (selection_pool_le cells result path.2)

/-- Finite actual visits contribute at most the corresponding multiplicity of the native ledger. -/
theorem scan_pool_le (source : Input N) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (inputs : List (Inputs ctx N)) : ∀ path : (scan (model := model) source cells result
      inputs).Path,
    (scan (model := model) source cells result inputs).resourcePool path ≤
      ResourcePool.scale inputs.length (visitEnvelope model N) := by
  induction inputs with
  | nil => intro path; exact (show (0 : ResourcePool model) ≤ 0 from le_rfl)
  | cons input rest ih =>
      intro path
      change ResourcePool.ofList ((visit (model := model) source input cells result).eventTrace
        path.1 ++
        (scan (model := model) source cells result rest).eventTrace path.2) ≤ _
      rw [ResourcePool.ofList_append]
      simp only [List.length_cons, ResourcePool.scale_succ]
      exact add_le_add (visit_pool_le source input cells result path.1) (ih path.2)

/-- Both boundary instructions and every actual retained-tuple visit fit the independent budget. -/
theorem code_pool_le (source : Input N) (inputs : List (Inputs ctx N)) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code (model := model) source inputs cells result).Path) :
    (code (model := model) source inputs cells result).resourcePool path ≤ eventEnvelope model N
      inputs.length := by
  change ResourcePool.ofList ((BitWord.instruction (execution := model) (clearAcceptedOp
    cells)).eventTrace path.1 ++
    ((scan (model := model) source cells result inputs).eventTrace path.2.1 ++ (BitWord.instruction
      (execution := model) (packOp cells result)).eventTrace path.2.2)) ≤ _
  simp only [BitWord.bitWord_instruction_eventTrace]
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add le_rfl (add_le_add (scan_pool_le source cells result inputs path.2.1) le_rfl)

private theorem selection_unitDepth_le (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (selection (model := model) cells result).Path) :
    (selection (model := model) cells result).depth (fun _ => 1) path ≤ 5 := by
  change 1 + (FirstAccepted.circuit (model := model) (selectorInputs cells) (selectorRefs
    cells)).depth
    (fun _ => 1) path.2 ≤ 5
  rw [FirstAccepted.firstAccepted_unit_depth]
  split <;> omega

/-- Each actual visit includes complete recovery followed by all selected packaging dependencies. -/
theorem visit_unitDepth_le (source : Input N) (inputs : Inputs ctx N) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (visit (model := model) source inputs cells result).Path) :
    (visit (model := model) source inputs cells result).depth (fun _ => 1) path ≤
      FactorRecovery.NativeFactorTail.depthBound N + 5 :=
  Nat.add_le_add
    (FactorRecovery.NativeFactorScope.code_unitDepth_le
      source inputs.parameter inputs.phase result path.1)
    (selection_unitDepth_le cells result path.2)

/-- The real serial fold is bounded by its actual finite reference-list length. -/
theorem scan_unitDepth_le (source : Input N) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (inputs : List (Inputs ctx N)) : ∀ path : (scan (model := model) source cells result
      inputs).Path,
    (scan (model := model) source cells result inputs).depth (fun _ => 1) path ≤
      inputs.length * (FactorRecovery.NativeFactorTail.depthBound N + 5) := by
  induction inputs with
  | nil => intro path; exact Nat.zero_le _
  | cons input rest ih =>
      intro path
      have first := visit_unitDepth_le source input cells result path.1
      have later := ih path.2
      change (visit (model := model) source input cells result).depth (fun _ => 1) path.1 +
        (scan (model := model) source cells result rest).depth (fun _ => 1) path.2 ≤ _
      simp only [List.length_cons, Nat.succ_mul]
      omega

/-- All complete visits and both actual boundary operations contribute to the native unit depth. -/
theorem code_unitDepth_le (source : Input N) (inputs : List (Inputs ctx N)) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code (model := model) source inputs cells result).Path) :
    (code (model := model) source inputs cells result).depth (fun _ => 1) path ≤ depthBound N
      inputs.length := by
  have scanned := scan_unitDepth_le source cells result inputs path.2.1
  change 1 + ((scan (model := model) source cells result inputs).depth (fun _ => 1) path.2.1 + 1) ≤
    _
  unfold depthBound
  omega

namespace Scope

/-- Genuine lexical placement preserves the complete native finite-scan event bound. -/
theorem code_pool_le (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code (model := model) source inputs result).Path) :
    (code (model := model) source inputs result).resourcePool path ≤ eventEnvelope model N
      inputs.length := by
  have placed : (code (model := model) source inputs result).resourcePool path =
      (NativeFactorScan.code (model := model) source (inputs.map liftInputs) (cells ctx N)
        (liftWrite result)).resourcePool path := rfl
  refine placed.le.trans ?_
  simpa only [List.length_map] using
    NativeFactorScan.code_pool_le source (inputs.map liftInputs) (cells ctx N)
      (liftWrite result) path

/-- Every serial native dependency remains in the same scoped finite-scan execution. -/
theorem code_unitDepth_le (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code (model := model) source inputs result).Path) :
    (code (model := model) source inputs result).depth (fun _ => 1) path ≤ depthBound N
      inputs.length := by
  have placed : (code (model := model) source inputs result).depth (fun _ => 1) path =
      (NativeFactorScan.code (model := model) source (inputs.map liftInputs) (cells ctx N)
        (liftWrite result)).depth (fun _ => 1) path := rfl
  refine placed.le.trans ?_
  simpa only [List.length_map] using
    NativeFactorScan.code_unitDepth_le source (inputs.map liftInputs) (cells ctx N)
      (liftWrite result) path

end Scope

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeFactorScan
