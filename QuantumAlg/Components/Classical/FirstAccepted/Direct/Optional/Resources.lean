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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width count : Nat}

namespace Fold

/-- Every chronological optional step contributes its independent native allowance. -/
theorem into_pool_le (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (refs : Optional.Refs ctx width) (path : (into inputs refs).Path) :
    (into inputs refs).resourcePool path ≤
      ResourcePool.scale count (Optional.eventEnvelope kind width) :=
  Circuit.forRange_pool_le count (fun index => Optional.into (inputs index) refs)
    (Optional.eventEnvelope kind width)
    (fun index => Optional.into_pool_le (inputs index) refs) path

/-- Each actual candidate adds at most three sequential native instruction events. -/
theorem into_depth_le (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (refs : Optional.Refs ctx width) (path : (into inputs refs).Path) :
    (into inputs refs).depth (fun _ => 1) path ≤ 3 * count := by
  exact (Circuit.forRange_depth_le count (fun index => Optional.into (inputs index) refs) 3
    (fun index => Optional.into_depth_le (inputs index) refs) path).trans_eq (Nat.mul_comm count 3)

/-- The loop reuses the same three destinations and allocates no further resident storage. -/
theorem into_resident_le (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (refs : Optional.Refs ctx width) (path : (into inputs refs).Path) :
    (into inputs refs).peakResidentSpace path ≤ ctx.residentSpace :=
  Circuit.forRange_resident_le count (fun index => Optional.into (inputs index) refs)
    ctx.residentSpace le_rfl (fun index => Optional.into_resident_le (inputs index) refs) path

/-- The loop preserves the existing auxiliary capacity through all actual branches. -/
theorem into_auxiliary_le (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (refs : Optional.Refs ctx width) (path : (into inputs refs).Path) :
    (into inputs refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace :=
  Circuit.forRange_auxiliary_le count (fun index => Optional.into (inputs index) refs)
    ctx.auxiliarySpace le_rfl (fun index => Optional.into_auxiliary_le (inputs index) refs) path

/-- Complete borrowed systems and arbitrary external correlations survive every real loop step. -/
theorem into_borrowedRestored
    (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (refs : Optional.Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (into inputs refs).BorrowedRestored Reference state
      ((into inputs refs).execute Reference state) :=
  Circuit.forRange_borrowedRestored count (fun index => Optional.into (inputs index) refs) Reference
    (fun index => Optional.into_borrowedRestored (inputs index) refs Reference) state

end Fold

namespace Allocation

/-- The independent native envelope pays for every optional step and exactly one final pack. -/
def eventEnvelope (kind : ProblemKind) (width count : Nat) : ResourcePool kind :=
  ResourcePool.scale count (Optional.eventEnvelope kind width) +
    ResourcePool.singleton (.classicalOperation (.nominalEncoding (.packOption width)))

/-- Three actual lexical shapes require only this classical scratch capacity. -/
def scratchSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.ofShape (.bits (2 * width + 2))

/-- The scratch formula is exactly the sum of the three physically allocated shapes. -/
theorem shapes_space (kind : ProblemKind) (width : Nat) :
    ((shapes width).map (SpacePool.ofShape (kind := kind))).sum = scratchSpace kind width := by
  apply SpacePool.ext
  intro axis
  cases axis <;> simp [shapes, scratchSpace, SpacePool.ofShape]
  omega

/-- None of the actual selector workspaces contributes a quantum system in any dimension. -/
theorem scratchSpace_quantum (width : Nat) (dimension : ℕ+) :
    scratchSpace .quantum width (.quantumSystems dimension) = 0 := rfl

/-- The complete body charges the actual optional loop and final encoding instruction. -/
theorem body_pool_le (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) {inner : RuntimeCtx kind}
    (cells : Cells inner (shapes width)) (transport : Transport ctx inner)
    (path : (body inputs output cells transport).Path) :
    (body inputs output cells transport).resourcePool path ≤ eventEnvelope kind width count := by
  change ResourcePool.ofList
    ((Fold.into (fun index => transport.liftInput (inputs index)) (refs cells)).eventTrace path.1 ++
      [.classicalOperation (.nominalEncoding (.packOption width))]) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (Fold.into_pool_le _ _ path.1) le_rfl

/-- The single final pack follows the entire actual selection dependency chain. -/
theorem body_depth_le (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) {inner : RuntimeCtx kind}
    (cells : Cells inner (shapes width)) (transport : Transport ctx inner)
    (path : (body inputs output cells transport).Path) :
    (body inputs output cells transport).depth (fun _ => 1) path ≤ 3 * count + 1 :=
  Nat.add_le_add (Fold.into_depth_le _ _ path.1) (Nat.le_refl 1)

/-- Every body branch retains exactly the already live caller and three-workspace context. -/
theorem body_resident_le (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) {inner : RuntimeCtx kind}
    (cells : Cells inner (shapes width)) (transport : Transport ctx inner)
    (path : (body inputs output cells transport).Path) :
    (body inputs output cells transport).peakResidentSpace path ≤ inner.residentSpace := by
  refine (Circuit.peakResidentSpace_seq
    (Fold.into (fun index => transport.liftInput (inputs index)) (refs cells))
    (.classical (packOp (refs cells) (transport.liftWrite output))) path).le.trans ?_
  exact SpacePool.max_le (Fold.into_resident_le _ _ path.1)
    (Circuit.peakResidentSpace_classical
      (packOp (refs cells) (transport.liftWrite output)) path.2).le

/-- The same actual body context bounds the auxiliary roles in every selected branch. -/
theorem body_auxiliary_le (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) {inner : RuntimeCtx kind}
    (cells : Cells inner (shapes width)) (transport : Transport ctx inner)
    (path : (body inputs output cells transport).Path) :
    (body inputs output cells transport).peakAuxiliarySpace path ≤ inner.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq
    (Fold.into (fun index => transport.liftInput (inputs index)) (refs cells))
    (.classical (packOp (refs cells) (transport.liftWrite output))) path).le.trans ?_
  exact SpacePool.max_le (Fold.into_auxiliary_le _ _ path.1)
    (Circuit.peakAuxiliarySpace_classical
      (packOp (refs cells) (transport.liftWrite output)) path.2).le

/-- Actual body restoration holds for arbitrary borrowed systems and arbitrary external
references. -/
theorem body_borrowedRestored
    (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) {inner : RuntimeCtx kind}
    (cells : Cells inner (shapes width)) (transport : Transport ctx inner)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State inner Reference History) :
    (body inputs output cells transport).BorrowedRestored Reference state
      ((body inputs output cells transport).execute Reference state) := by
  apply Circuit.borrowedRestored_seq
  · exact Fold.into_borrowedRestored _ _ Reference state
  · exact Circuit.borrowedRestored_classical _ _

/-- Lexical entry and release leave the complete actual native event budget unchanged. -/
theorem into_pool_le (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) (path : (into inputs output).Path) :
    (into inputs output).resourcePool path ≤ eventEnvelope kind width count :=
  withCellsFrom_pool_le (Transport.id ctx) (shapes width)
    (fun cells _distinct transport _separated => body inputs output cells transport)
    (eventEnvelope kind width count)
    (fun cells _distinct transport _separated => body_pool_le inputs output cells transport) path

/-- The complete actual selection has at most three events per candidate and one final pack. -/
theorem eventEnvelope_card (kind : ProblemKind) (width count : Nat) :
    (eventEnvelope kind width count).card = 3 * count + 1 := by
  simp [eventEnvelope, ResourcePool.scale, ResourcePool.singleton, Optional.eventEnvelope,
    Direct.copyTrace, ResourcePool.ofList, Nat.mul_comm]

/-- Event count is bounded from the same complete native path ledger. -/
theorem into_eventCount_le (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) (path : (into inputs output).Path) :
    ((into inputs output).eventTrace path).length ≤ 3 * count + 1 := by
  have bound := Multiset.card_le_card (into_pool_le inputs output path)
  exact bound.trans_eq (eventEnvelope_card kind width count)

/-- Lexical allocation preserves the complete actual chronological instruction depth. -/
theorem into_depth_le (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) (path : (into inputs output).Path) :
    (into inputs output).depth (fun _ => 1) path ≤ 3 * count + 1 :=
  withCellsFrom_depth_le (Transport.id ctx) (shapes width)
    (fun cells _distinct transport _separated => body inputs output cells transport)
    (fun _ => 1) (3 * count + 1)
    (fun cells _distinct transport _separated => body_depth_le inputs output cells transport) path

/-- Resident accounting includes the caller-owned output and exactly the three reused workspaces. -/
theorem into_resident_le (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) (path : (into inputs output).Path) :
    (into inputs output).peakResidentSpace path ≤ ctx.residentSpace + scratchSpace kind width := by
  have bound := withCellsFrom_resident_le (Transport.id ctx) (shapes width)
    (fun cells _distinct transport _separated => body inputs output cells transport) 0
    (fun cells _distinct transport _separated selected => by
      simpa only [zero_add] using body_resident_le inputs output cells transport selected) path
  exact bound.trans_eq (by rw [shapes_space, add_zero]; exact add_comm _ _)

/-- Auxiliary accounting charges precisely the same actual reused lexical shapes. -/
theorem into_auxiliary_le (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) (path : (into inputs output).Path) :
    (into inputs output).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + scratchSpace kind width := by
  have bound := withCellsFrom_auxiliary_le (Transport.id ctx) (shapes width)
    (fun cells _distinct transport _separated => body inputs output cells transport) 0
    (fun cells _distinct transport _separated selected => by
      simpa only [zero_add] using body_auxiliary_le inputs output cells transport selected) path
  exact bound.trans_eq (by rw [shapes_space, add_zero]; exact add_comm _ _)

/-- Actual workspace release restores the complete arbitrary-reference borrowed interface. -/
theorem into_borrowedRestored
    (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (into inputs output).BorrowedRestored Reference state
      ((into inputs output).execute Reference state) :=
  withCellsFrom_borrowedRestored (Transport.id ctx) (shapes width)
    (fun cells _distinct transport _separated => body inputs output cells transport) Reference
    (fun cells _distinct transport _separated => body_borrowedRestored inputs output cells transport
      Reference) state

end Allocation

end

end QuantumAlg.ClassicalRoutines.FirstAccepted.Direct.Optional
