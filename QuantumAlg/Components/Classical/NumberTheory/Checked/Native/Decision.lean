/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace
import all QuantumAlg.Components.Classical.Model.BitWord.Execution
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Actual raw-gcd unit decision

The original widened one word is genuinely allocated at zero, incremented
once and compared with the actual raw gcd. Its matching release precedes
signed reduction. This component establishes only the gcd-equals-one stored
bit; the raw engine and number-theoretic theorem supply its unit meaning.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.Checked.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Original widened comparison-one lexical cell. -/
@[reducible] def unitDecisionCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh

/-- Structural read of an actual writable result. -/
def decisionRead {shape : CShape} (cell : CWriteRef ctx shape) : CInputRef ctx shape :=
  .storage cell.toCStorageRef

/-- Original stored values retain their identities beneath the one-word scope. -/
def underUnitDecision {shape : CShape} (input : CInputRef ctx shape) (width : Nat) :
    CInputRef (unitDecisionCtx ctx width) shape :=
  input.underWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh

/-- Original writable status remains the same caller cell. -/
def writeUnderUnitDecision {shape : CShape} (output : CWriteRef ctx shape) (width : Nat) :
    CWriteRef (unitDecisionCtx ctx width) shape :=
  output.underWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh

/-- The actual initialized one-word scratch head. -/
def unitOneCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (unitDecisionCtx ctx width) (.unsignedWord (width + 1)) :=
  CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh

/-- One actual increment materializes the comparison constant. -/
def unitOneIncrement (one : CWriteRef ctx (.unsignedWord (width + 1))) :
    ClassicalOp (.unsignedWord (width + 1)) (.unsignedWord (width + 1)) ctx ctx :=
  .wordUnary .increment (width + 1) ctx (decisionRead one) one

/-- Original actual raw-gcd equality instruction. -/
def unitGcdEqual (gcd : CInputRef ctx (.unsignedWord (width + 1)))
    (one : CWriteRef ctx (.unsignedWord (width + 1))) (success : CWriteRef ctx .bit) :
    ClassicalOp (.product (.unsignedWord (width + 1)) (.unsignedWord (width + 1))) .bit ctx ctx :=
  .wordBinary .equal (width + 1) ctx (.product gcd (decisionRead one)) success

/-- Actual original increment followed by gcd-equals-one comparison. -/
def unitDecisionBody {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (gcd : CInputRef ctx (.unsignedWord (width + 1)))
    (one : CWriteRef ctx (.unsignedWord (width + 1))) (success : CWriteRef ctx .bit) :
    Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (unitOneIncrement one)) (BitWord.instruction
      (execution := model) (unitGcdEqual gcd one success))

/-- Literal chronological update and true native path. -/
def unitDecisionBodyStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (gcd : CInputRef ctx (.unsignedWord (width + 1)))
    (one : CWriteRef ctx (.unsignedWord (width + 1))) (success : CWriteRef ctx .bit)
    (store : Store ctx) : Store ctx × (unitDecisionBody (model := model) gcd one success).Path :=
  let seeded := BitWord.instructionStep (execution := model) (unitOneIncrement one) store
  let compared := BitWord.instructionStep (execution := model)
    (unitGcdEqual gcd one success) seeded.1
  (compared.1, (seeded.2, compared.2))

/-- Actual placement uses the real fresh one word and original stored gcd/status cells. -/
def unitDecisionPlaced {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (gcd : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) :
    Circuit model (unitDecisionCtx ctx width) (unitDecisionCtx ctx width) :=
  unitDecisionBody (model := model) (underUnitDecision gcd width) (unitOneCell ctx width)
    (writeUnderUnitDecision success width)

/-- The original decision fully allocates and releases its one-word temporary. -/
def withUnitDecision {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (gcd : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) : Circuit model ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh
    (unitDecisionPlaced (model := model) gcd success)

/-- Actual caller-store result and native path after the one-word release. -/
def withUnitDecisionStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (gcd : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (store : Store ctx) :
    Store ctx × (withUnitDecision (model := model) gcd success).Path :=
  let result := unitDecisionBodyStep (model := model) (underUnitDecision gcd width)
      (unitOneCell ctx width)
    (writeUnderUnitDecision success width) (store.pushWorkspace ctx.canonicalFreshKey
      (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh result.1, result.2)

/-- The two real instructions preserve every complete quantum-reference block and old history. -/
theorem unitDecisionBody_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (gcd : CInputRef ctx (.unsignedWord (width + 1)))
    (one : CWriteRef ctx (.unsignedWord (width + 1))) (success : CWriteRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (unitDecisionBody (model := model) gcd one success).execute Reference state =
        state.mapClassical (fun entry =>
      let result := unitDecisionBodyStep (model := model) gcd one success entry.1
      (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  simp only [unitDecisionBody, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual allocation, decision and release retain the full reference-correlated execution state. -/
theorem withUnitDecision_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (gcd : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (withUnitDecision (model := model) gcd success).execute Reference state =
        state.mapClassical (fun entry =>
      let result := withUnitDecisionStep (model := model) gcd success entry.1
      (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_workspace_mapClassical ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh (unitDecisionPlaced (model := model) gcd success)
    (fun before =>
      let result := unitDecisionBodyStep (model := model) (underUnitDecision gcd width)
        (unitOneCell ctx width) (writeUnderUnitDecision success width) before.1
      ((result.1, before.2), result.2)) ?_ Reference state).trans ?_
  · intro reference history _ initial
    exact (unitDecisionBody_execute (underUnitDecision gcd width) (unitOneCell ctx width)
      (writeUnderUnitDecision success width) reference initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Fresh initialization makes the stored decision exactly equality of the original gcd to one. -/
theorem withUnitDecision_value {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (gcd : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (store : Store ctx) :
    (withUnitDecisionStep (model := model) gcd success store).1.read (decisionRead success) =
      .bit (decide ((store.read gcd).toNat = 1)) := by
  let entered := store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh
  let one := unitOneCell ctx width
  let stepped := entered.applyOp (unitOneIncrement one)
  have gcdFree : one.key ∉ (underUnitDecision gcd width).storageKeys := by
    rw [underUnitDecision, CInputRef.storageKeys_underWorkspace]
    exact fun present => ctx.canonicalFreshKey_fresh (gcd.storageKeys_subset_context present)
  have oldGcd : stepped.read (underUnitDecision gcd width) = store.read gcd :=
    (Store.read_applyOp_of_not_mem_storageKeys entered (unitOneIncrement one)
      (underUnitDecision gcd width) gcdFree).trans
        (Store.read_pushWorkspace_underWorkspace store _ _ _ gcd)
  have oneValue : (stepped.read (decisionRead one)).toNat = 1 := by
    have written : stepped.read (decisionRead one) =
        (unitOneIncrement one).eval (entered.read (decisionRead one)) :=
      Store.read_applyOp_output entered (unitOneIncrement one)
    rw [written]
    have capacity : 1 < 2 ^ (width + 1) := by
      have positive : 0 < 2 ^ width := Nat.two_pow_pos width
      rw [pow_succ]
      omega
    change (0 + 1) % 2 ^ (width + 1) = 1
    exact Nat.mod_eq_of_lt capacity
  have result : (stepped.applyOp (unitGcdEqual (underUnitDecision gcd width) one
      (writeUnderUnitDecision success width))).read
      (decisionRead (writeUnderUnitDecision success width)) =
        .bit (decide ((stepped.read (underUnitDecision gcd width)).toNat =
          (stepped.read (decisionRead one)).toNat)) :=
    Store.read_applyOp_output stepped (unitGcdEqual (underUnitDecision gcd width) one
      (writeUnderUnitDecision success width))
  unfold withUnitDecisionStep
  rw [Store.read_popWorkspace_underWorkspace _ _ _ _ (decisionRead success)]
  change (stepped.applyOp (unitGcdEqual (underUnitDecision gcd width) one
    (writeUnderUnitDecision success width))).read
      (decisionRead (writeUnderUnitDecision success width)) = _
  rw [result, oldGcd, oneValue]

/-- Both real writes preserve every structural caller read outside the status output. -/
theorem withUnitDecision_read_other {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (gcd : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) {shape : CShape} (other : CInputRef ctx shape)
    (separate : success.key ∉ other.storageKeys) (store : Store ctx) :
    (withUnitDecisionStep (model := model) gcd success store).1.read other = store.read other := by
  have fresh : (unitOneCell ctx width).key ∉ (underUnitDecision other width).storageKeys := by
    rw [underUnitDecision, CInputRef.storageKeys_underWorkspace]
    exact fun present => ctx.canonicalFreshKey_fresh (other.storageKeys_subset_context present)
  have outputFree : (writeUnderUnitDecision success width).key ∉
      (underUnitDecision other width).storageKeys := by
    change success.key ∉ (underUnitDecision other width).storageKeys
    simpa only [underUnitDecision, CInputRef.storageKeys_underWorkspace] using separate
  unfold withUnitDecisionStep unitDecisionBodyStep
  rw [Store.read_popWorkspace_underWorkspace _ _ _ _ other]
  change (((store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh).applyOp (unitOneIncrement (unitOneCell ctx width))).applyOp
    (unitGcdEqual (underUnitDecision gcd width) (unitOneCell ctx width)
      (writeUnderUnitDecision success width))).read (underUnitDecision other width) = _
  rw [Store.read_applyOp_of_not_mem_storageKeys _
    (unitGcdEqual (underUnitDecision gcd width) (unitOneCell ctx width)
      (writeUnderUnitDecision success width)) _ outputFree,
    Store.read_applyOp_of_not_mem_storageKeys _ (unitOneIncrement (unitOneCell ctx width)) _ fresh]
  exact Store.read_pushWorkspace_underWorkspace _ _ _ _ other

/-- The exact original increment-then-equality trace at the widened operand width. -/
theorem withUnitDecision_eventTrace {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (gcd : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (path : (withUnitDecision (model := model) gcd success).Path) :
    (withUnitDecision (model := model) gcd success).eventTrace path =
      [.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary
          .increment (width + 1))),
        .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordBinary
            .equal (width + 1)))] := by
  change (BitWord.instruction (execution := model) (unitOneIncrement (unitOneCell ctx
      width))).eventTrace
     path.1 ++
      (BitWord.instruction (execution := model)
        (unitGcdEqual (underUnitDecision gcd width) (unitOneCell ctx width)
          (writeUnderUnitDecision success width))).eventTrace path.2 = _
  rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace]
  rfl

/-- Actual native durations preserve both chronological dependencies. -/
theorem withUnitDecision_durationDepth {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (gcd : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (duration : Resource.Event model → Nat)
    (path : (withUnitDecision (model := model) gcd success).Path) :
    (withUnitDecision (model := model) gcd success).depth duration path =
      duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordUnary .increment (width + 1)))) +
        duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
            (.wordBinary .equal (width + 1)))) := by
  change (BitWord.instruction (execution := model) (unitOneIncrement (unitOneCell ctx width))).depth
    duration path.1 +
      (BitWord.instruction (execution := model)
        (unitGcdEqual (underUnitDecision gcd width) (unitOneCell ctx width)
          (writeUnderUnitDecision success width))).depth duration path.2 = _
  rw [BitWord.bitWord_instruction_depth, BitWord.bitWord_instruction_depth]
  rfl

/-- Exactly two original native instructions execute. -/
theorem withUnitDecision_depth {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (gcd : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (path : (withUnitDecision (model := model) gcd success).Path) :
    (withUnitDecision (model := model) gcd success).depth (fun _ => 1) path = 2 := rfl


/-- Exactly the original two event multiplicities, with no hidden coefficient computation. -/
theorem withUnitDecision_resourcePool {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (gcd : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (path : (withUnitDecision (model := model) gcd success).Path) :
    (withUnitDecision (model := model) gcd success).resourcePool path = ResourcePool.ofList
      [.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary
          .increment (width + 1))),
        .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordBinary
            .equal (width + 1)))] :=
  congrArg ResourcePool.ofList (withUnitDecision_eventTrace gcd success path)

/-- Exact resident peak includes the actual widened one word and all original context entries. -/
theorem withUnitDecision_resident {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (gcd : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (path : (withUnitDecision (model := model) gcd success).Path) :
    (withUnitDecision (model := model) gcd success).peakResidentSpace path =
      SpacePool.ofShape (.unsignedWord (width + 1)) + ctx.residentSpace := by
  have bodyPeak : (unitDecisionPlaced (model := model) gcd success).peakResidentSpace path =
      (unitDecisionCtx ctx width).residentSpace := by
    change SpacePool.max (unitDecisionCtx ctx width).residentSpace
      (SpacePool.max (unitDecisionCtx ctx width).residentSpace 0) = _
    simp only [SpacePool.max_zero, SpacePool.max_self]
  refine (Circuit.peakResidentSpace_workspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh (unitDecisionPlaced (model := model) gcd success) path).trans
      ((congrArg (SpacePool.max ctx.residentSpace) bodyPeak).trans ?_)
  exact SpacePool.max_eq_right le_add_self

/-- Exact auxiliary peak includes the actual widened one word and all original context entries. -/
theorem withUnitDecision_auxiliary {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (gcd : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (path : (withUnitDecision (model := model) gcd success).Path) :
    (withUnitDecision (model := model) gcd success).peakAuxiliarySpace path =
      SpacePool.ofShape (.unsignedWord (width + 1)) + ctx.auxiliarySpace := by
  have bodyPeak : (unitDecisionPlaced (model := model) gcd success).peakAuxiliarySpace path =
      (unitDecisionCtx ctx width).auxiliarySpace := by
    change SpacePool.max (unitDecisionCtx ctx width).auxiliarySpace
      (SpacePool.max (unitDecisionCtx ctx width).auxiliarySpace 0) = _
    simp only [SpacePool.max_zero, SpacePool.max_self]
  refine (Circuit.peakAuxiliarySpace_workspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh (unitDecisionPlaced (model := model) gcd success) path).trans
      ((congrArg (SpacePool.max ctx.auxiliarySpace) bodyPeak).trans ?_)
  exact SpacePool.max_eq_right le_add_self

end

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.Native
