/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Allocation
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Resources
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Space

/-!
# Native costs and complete borrowed restoration of optional first-success folding

Each optional step pays for unpacking and up to two actual copies. One final
pack writes the caller's existing output. The three lexical cells occupy
exactly twice the word width plus two classical bits; their space is reused
for every candidate and introduces no quantum systems.
-/

namespace QuantumAlg.ClassicalRoutines.FirstAccepted.Direct.Optional

noncomputable section

open Execution ClassicalWorkspace

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width count : Nat}

namespace Fold

/-- Every chronological optional step contributes its independent native allowance. -/
lemma into_pool_le (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (refs : Optional.Refs ctx width) (path : (into (model := model) inputs refs).Path) :
    (into (model := model) inputs refs).resourcePool path ≤
      ResourcePool.scale count (Optional.eventEnvelope model width) :=
  Circuit.forRange_pool_le count (fun index => Optional.into (model := model) (inputs index) refs)
    (Optional.eventEnvelope model width)
    (fun index => Optional.into_pool_le (inputs index) refs) path

/-- Each actual candidate adds at most three sequential native instruction events. -/
lemma into_depth_le (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (refs : Optional.Refs ctx width) (path : (into (model := model) inputs refs).Path) :
    (into (model := model) inputs refs).depth (fun _ => 1) path ≤ 3 * count := by
  exact (Circuit.forRange_depth_le count (fun index => Optional.into (model := model) (inputs
    index) refs) 3
    (fun index => Optional.into_depth_le (inputs index) refs) path).trans_eq (Nat.mul_comm count 3)

/-- The loop reuses the same three destinations and allocates no further resident storage. -/
lemma into_resident_le (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (refs : Optional.Refs ctx width) (path : (into (model := model) inputs refs).Path) :
    (into (model := model) inputs refs).peakResidentSpace path ≤ ctx.residentSpace :=
  Circuit.forRange_resident_le count (fun index => Optional.into (model := model) (inputs index)
    refs)
    ctx.residentSpace le_rfl (fun index => Optional.into_resident_le (inputs index) refs) path

/-- The loop preserves the existing auxiliary capacity through all actual branches. -/
lemma into_auxiliary_le (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (refs : Optional.Refs ctx width) (path : (into (model := model) inputs refs).Path) :
    (into (model := model) inputs refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace :=
  Circuit.forRange_auxiliary_le count (fun index => Optional.into (model := model) (inputs index)
    refs)
    ctx.auxiliarySpace le_rfl (fun index => Optional.into_auxiliary_le (inputs index) refs) path

/-- Complete borrowed systems and arbitrary external correlations survive every real loop step. -/
lemma into_borrowedRestored
    (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (refs : Optional.Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (into (model := model) inputs refs).BorrowedRestored Reference state
      ((into (model := model) inputs refs).execute environment Reference state) :=
  Circuit.forRange_borrowedRestored
    (environment := environment) count (fun index => Optional.into (model := model) (inputs
    index) refs) Reference
    (fun index => Optional.into_borrowedRestored (inputs index) refs Reference) state

end Fold

namespace Allocation

/-- The independent native envelope pays for every optional step and exactly one final pack. -/
def eventEnvelope (model : ExecutionModel) [BitWord.Selected model]
    (width count : Nat) : ResourcePool model :=
  ResourcePool.scale count (Optional.eventEnvelope model width) +
    ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.nominalEncoding (.packOption width))))

/-- Three actual lexical shapes require only this classical scratch capacity. -/
def scratchSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.ofShape (.bits (2 * width + 2))

/-- The scratch formula is exactly the sum of the three physically allocated shapes. -/
lemma shapes_space (kind : ProblemKind) (width : Nat) :
    ((shapes width).map (SpacePool.ofShape (kind := kind))).sum = scratchSpace kind width := by
  apply SpacePool.ext
  intro axis
  cases axis <;> simp [shapes, scratchSpace, SpacePool.ofShape]
  omega

/-- None of the actual selector workspaces contributes a quantum system in any dimension. -/
lemma scratchSpace_quantum (width : Nat) (dimension : ℕ+) :
    scratchSpace .quantum width (.quantumSystems dimension) = 0 := rfl

/-- The complete body charges the actual optional loop and final encoding instruction. -/
lemma body_pool_le (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) {inner : RuntimeCtx model.kind}
    (cells : Cells inner (shapes width)) (transport : Transport ctx inner)
    (path : (body (model := model) inputs output cells transport).Path) :
    (body (model := model) inputs output cells transport).resourcePool path ≤ eventEnvelope model
      width count := by
  change ResourcePool.ofList
    ((Fold.into (model := model) (fun index => transport.liftInput (inputs index)) (refs
      cells)).eventTrace path.1 ++
      (BitWord.instruction (execution := model)
        (packOp (refs cells) (transport.liftWrite output))).eventTrace path.2) ≤ _
  rw [BitWord.bitWord_instruction_eventTrace, ResourcePool.ofList_append]
  exact add_le_add (Fold.into_pool_le _ _ path.1) le_rfl

/-- The single final pack follows the entire actual selection dependency chain. -/
lemma body_depth_le (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) {inner : RuntimeCtx model.kind}
    (cells : Cells inner (shapes width)) (transport : Transport ctx inner)
    (path : (body (model := model) inputs output cells transport).Path) :
    (body (model := model) inputs output cells transport).depth (fun _ => 1) path ≤ 3 * count + 1 :=
  Nat.add_le_add (Fold.into_depth_le _ _ path.1) (Nat.le_refl 1)

/-- Every body branch retains exactly the already live caller and three-workspace context. -/
lemma body_resident_le (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) {inner : RuntimeCtx model.kind}
    (cells : Cells inner (shapes width)) (transport : Transport ctx inner)
    (path : (body (model := model) inputs output cells transport).Path) :
    (body (model := model) inputs output cells transport).peakResidentSpace path ≤
      inner.residentSpace := by
  refine (Circuit.peakResidentSpace_seq
    (Fold.into (model := model) (fun index => transport.liftInput (inputs index)) (refs cells))
    (BitWord.instruction (execution := model) (packOp (refs cells) (transport.liftWrite output)))
      path).le.trans ?_
  exact SpacePool.max_le (Fold.into_resident_le _ _ path.1)
    (Circuit.peakResidentSpace_classical
      (BitWord.selectedApplication (execution := model)
        (packOp (refs cells) (transport.liftWrite output))) path.2).le

/-- The same actual body context bounds the auxiliary roles in every selected branch. -/
lemma body_auxiliary_le (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) {inner : RuntimeCtx model.kind}
    (cells : Cells inner (shapes width)) (transport : Transport ctx inner)
    (path : (body (model := model) inputs output cells transport).Path) :
    (body (model := model) inputs output cells transport).peakAuxiliarySpace path ≤
      inner.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq
    (Fold.into (model := model) (fun index => transport.liftInput (inputs index)) (refs cells))
    (BitWord.instruction (execution := model) (packOp (refs cells) (transport.liftWrite output)))
      path).le.trans ?_
  exact SpacePool.max_le (Fold.into_auxiliary_le _ _ path.1)
    (Circuit.peakAuxiliarySpace_classical
      (BitWord.selectedApplication (execution := model)
        (packOp (refs cells) (transport.liftWrite output))) path.2).le

/-- Actual body restoration holds for arbitrary borrowed systems and arbitrary external
references. -/
lemma body_borrowedRestored
    (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) {inner : RuntimeCtx model.kind}
    (cells : Cells inner (shapes width)) (transport : Transport ctx inner)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State inner Reference (model.HiddenState × History)) :
    (body (model := model) inputs output cells transport).BorrowedRestored Reference state
      ((body (model := model) inputs output cells transport).execute
        environment Reference state) := by
  apply Circuit.borrowedRestored_seq (environment := environment)
  · exact Fold.into_borrowedRestored _ _ Reference state
  · exact Circuit.borrowedRestored_classical (environment := environment) _ _

/-- Lexical entry and release leave the complete actual native event budget unchanged. -/
lemma into_pool_le (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) (path : (into (model := model) inputs
      output).Path) :
    (into (model := model) inputs output).resourcePool path ≤ eventEnvelope model width count :=
  withCellsFrom_pool_le (Transport.id ctx) (shapes width)
    (fun cells _distinct transport _separated => body (model := model) inputs output cells
      transport)
    (eventEnvelope model width count)
    (fun cells _distinct transport _separated => body_pool_le inputs output cells transport) path

/-- The complete actual selection has at most three events per candidate and one final pack. -/
lemma eventEnvelope_card (model : ExecutionModel) [BitWord.Selected model]
    (width count : Nat) :
    (eventEnvelope model width count).card = 3 * count + 1 := by
  simp [eventEnvelope, ResourcePool.scale, ResourcePool.singleton, Optional.eventEnvelope,
    Direct.copyTrace, ResourcePool.ofList, Nat.mul_comm]

/-- Event count is bounded from the same complete native path ledger. -/
lemma into_eventCount_le (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) (path : (into (model := model) inputs
      output).Path) :
    ((into (model := model) inputs output).eventTrace path).length ≤ 3 * count + 1 := by
  have bound := Multiset.card_le_card (into_pool_le inputs output path)
  exact bound.trans_eq (eventEnvelope_card model width count)

/-- Lexical allocation preserves the complete actual chronological instruction depth. -/
lemma into_depth_le (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) (path : (into (model := model) inputs
      output).Path) :
    (into (model := model) inputs output).depth (fun _ => 1) path ≤ 3 * count + 1 :=
  withCellsFrom_depth_le (Transport.id ctx) (shapes width)
    (fun cells _distinct transport _separated => body (model := model) inputs output cells
      transport)
    (fun _ => 1) (3 * count + 1)
    (fun cells _distinct transport _separated => body_depth_le inputs output cells transport) path

/-- Resident accounting includes the caller-owned output and exactly the three reused workspaces. -/
lemma into_resident_le (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) (path : (into (model := model) inputs
      output).Path) :
    (into (model := model) inputs output).peakResidentSpace path ≤ ctx.residentSpace +
      scratchSpace model.kind width := by
  have bound := withCellsFrom_resident_le (Transport.id ctx) (shapes width)
    (fun cells _distinct transport _separated => body (model := model) inputs output cells
      transport) 0
    (fun cells _distinct transport _separated selected => by
      simpa only [zero_add] using body_resident_le inputs output cells transport selected) path
  exact bound.trans_eq (by rw [shapes_space, add_zero]; exact add_comm _ _)

/-- Auxiliary accounting charges precisely the same actual reused lexical shapes. -/
lemma into_auxiliary_le (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) (path : (into (model := model) inputs
      output).Path) :
    (into (model := model) inputs output).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + scratchSpace model.kind width := by
  have bound := withCellsFrom_auxiliary_le (Transport.id ctx) (shapes width)
    (fun cells _distinct transport _separated => body (model := model) inputs output cells
      transport) 0
    (fun cells _distinct transport _separated selected => by
      simpa only [zero_add] using body_auxiliary_le inputs output cells transport selected) path
  exact bound.trans_eq (by rw [shapes_space, add_zero]; exact add_comm _ _)

/-- Actual workspace release restores the complete arbitrary-reference borrowed interface. -/
lemma into_borrowedRestored
    (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (into (model := model) inputs output).BorrowedRestored Reference state
      ((into (model := model) inputs output).execute environment Reference state) :=
  withCellsFrom_borrowedRestored (environment := environment) (Transport.id ctx) (shapes width)
    (fun cells _distinct transport _separated => body (model := model) inputs output cells
      transport) Reference
    (fun cells _distinct transport _separated => body_borrowedRestored inputs output cells transport
      Reference) state

end Allocation

end

end QuantumAlg.ClassicalRoutines.FirstAccepted.Direct.Optional
