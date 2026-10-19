/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent
import all QuantumAlg.Core.Execution.Trace.Boundary

/-!
# Actual one-time persistent allocation resources

The original seven retained cells are counted once beside every original
caller entry. Their literal retain instructions emit no operation events or
dependency duration. Every actual allocation path reaches the complete final
context, whose resident and auxiliary pools are therefore the exact peaks.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {kind : ProblemKind}

/-- The seven actual shapes in final head-to-tail order, each counted once. -/
def persistentCellSpace (kind : ProblemKind) (width scalarWidth : Nat) : SpacePool kind :=
  SpacePool.ofShape (PointShape width) + SpacePool.ofShape .bit + SpacePool.ofShape .bit +
    SpacePool.ofShape (.unsignedWord scalarWidth) + SpacePool.ofShape .bit +
      SpacePool.ofShape (.unsignedWord scalarWidth) + SpacePool.ofShape .bit

/-- The actual final resident pool contains exactly seven new cells and the caller pool. -/
lemma persistentCtx_residentSpace (ctx : RuntimeCtx kind) (width scalarWidth : Nat) :
    (persistentCtx ctx width scalarWidth).residentSpace =
      persistentCellSpace kind width scalarWidth + ctx.residentSpace := by
  simp only [persistentCtx, retainedCtx, acceptedCtx, persistentBaseCtx, persistentCandidateCtx,
    persistentInverseCtx, persistentSelectedCtx, persistentLatchCtx,
    RuntimeCtx.residentSpace_addRetained, persistentCellSpace, add_assoc]

/-- The actual final auxiliary pool contains exactly seven new cells and the caller pool. -/
lemma persistentCtx_auxiliarySpace (ctx : RuntimeCtx kind) (width scalarWidth : Nat) :
    (persistentCtx ctx width scalarWidth).auxiliarySpace =
      persistentCellSpace kind width scalarWidth + ctx.auxiliarySpace := by
  simp only [persistentCtx, retainedCtx, acceptedCtx, persistentBaseCtx, persistentCandidateCtx,
    persistentInverseCtx, persistentSelectedCtx, persistentLatchCtx,
    RuntimeCtx.auxiliarySpace_addRetained, persistentCellSpace, add_assoc]

/-- Literal retention of the seven cells emits no native operation events. -/
lemma retainPersistent_eventTrace {model : ExecutionModel}
    (ctx : RuntimeCtx model.kind) (width scalarWidth : Nat)
    (path : (retainPersistent ctx width scalarWidth).Path) :
    (retainPersistent ctx width scalarWidth).eventTrace path = [] := rfl

/-- The actual event multiset of the one-time allocation is empty. -/
lemma retainPersistent_resourcePool {model : ExecutionModel}
    (ctx : RuntimeCtx model.kind) (width scalarWidth : Nat)
    (path : (retainPersistent ctx width scalarWidth).Path) :
    (retainPersistent ctx width scalarWidth).resourcePool path = 0 := rfl

/-- The actual allocation dependency duration is zero for every native duration model. -/
lemma retainPersistent_depth {model : ExecutionModel}
    (ctx : RuntimeCtx model.kind) (width scalarWidth : Nat)
    (duration : Resource.Event model → Nat)
    (path : (retainPersistent ctx width scalarWidth).Path) :
    (retainPersistent ctx width scalarWidth).depth duration path = 0 := rfl

private lemma persistentPeak_le {s0 s1 s2 s3 s4 s5 s6 s7 : SpacePool kind}
    (h0 : s0 ≤ s1) (h1 : s1 ≤ s2) (h2 : s2 ≤ s3) (h3 : s3 ≤ s4)
    (h4 : s4 ≤ s5) (h5 : s5 ≤ s6) (h6 : s6 ≤ s7) :
    SpacePool.max s0 (SpacePool.max s1 (SpacePool.max s1 (SpacePool.max s2 (SpacePool.max s2
      (SpacePool.max s3 (SpacePool.max s3 (SpacePool.max s4 (SpacePool.max s4 (SpacePool.max s5
      (SpacePool.max s5 (SpacePool.max s6 (SpacePool.max s6 (SpacePool.max s7 (0)))))))))))))) ≤
      s7 := by
  have b5 := h5.trans h6
  have b4 := h4.trans b5
  have b3 := h3.trans b4
  have b2 := h2.trans b3
  have b1 := h1.trans b2
  have b0 := h0.trans b1
  rw [SpacePool.max_zero]
  exact SpacePool.max_le b0 (SpacePool.max_le b1 (SpacePool.max_le b1 (SpacePool.max_le b2
    (SpacePool.max_le b2 (SpacePool.max_le b3 (SpacePool.max_le b3 (SpacePool.max_le b4
    (SpacePool.max_le b4 (SpacePool.max_le b5 (SpacePool.max_le b5 (SpacePool.max_le h6
    (SpacePool.max_le h6 (le_rfl)))))))))))))

/-- The exact resident peak is the complete final context, including all original entries. -/
lemma retainPersistent_resident {model : ExecutionModel}
    (ctx : RuntimeCtx model.kind) (width scalarWidth : Nat)
    (path : (retainPersistent ctx width scalarWidth).Path) :
    (retainPersistent ctx width scalarWidth).peakResidentSpace path =
      (persistentCtx ctx width scalarWidth).residentSpace := by
  apply le_antisymm ?_ ((retainPersistent ctx width scalarWidth).output_residentSpace_le_peak path)
  change SpacePool.max ctx.residentSpace (SpacePool.max (persistentLatchCtx ctx).residentSpace
    (SpacePool.max (persistentLatchCtx ctx).residentSpace (SpacePool.max (persistentSelectedCtx
    ctx scalarWidth).residentSpace (SpacePool.max (persistentSelectedCtx ctx
    scalarWidth).residentSpace (SpacePool.max (persistentInverseCtx ctx
    scalarWidth).residentSpace (SpacePool.max (persistentInverseCtx ctx
    scalarWidth).residentSpace (SpacePool.max (persistentCandidateCtx ctx
    scalarWidth).residentSpace (SpacePool.max (persistentCandidateCtx ctx
    scalarWidth).residentSpace (SpacePool.max (persistentBaseCtx ctx scalarWidth).residentSpace
    (SpacePool.max (persistentBaseCtx ctx scalarWidth).residentSpace (SpacePool.max (acceptedCtx
    (persistentBaseCtx ctx scalarWidth)).residentSpace (SpacePool.max (acceptedCtx
    (persistentBaseCtx ctx scalarWidth)).residentSpace (SpacePool.max (persistentCtx ctx width
    scalarWidth).residentSpace (0)))))))))))))) ≤ _
  exact persistentPeak_le
    (show ctx.residentSpace ≤ (persistentLatchCtx ctx).residentSpace from le_add_self)
    (show (persistentLatchCtx ctx).residentSpace ≤ (persistentSelectedCtx ctx
      scalarWidth).residentSpace from le_add_self)
    (show (persistentSelectedCtx ctx scalarWidth).residentSpace ≤ (persistentInverseCtx ctx
      scalarWidth).residentSpace from le_add_self)
    (show (persistentInverseCtx ctx scalarWidth).residentSpace ≤ (persistentCandidateCtx ctx
      scalarWidth).residentSpace from le_add_self)
    (show (persistentCandidateCtx ctx scalarWidth).residentSpace ≤ (persistentBaseCtx ctx
      scalarWidth).residentSpace from le_add_self)
    (show (persistentBaseCtx ctx scalarWidth).residentSpace ≤ (acceptedCtx (persistentBaseCtx
      ctx scalarWidth)).residentSpace from le_add_self)
    (show (acceptedCtx (persistentBaseCtx ctx scalarWidth)).residentSpace ≤ (persistentCtx ctx
      width scalarWidth).residentSpace from le_add_self)

/-- The exact auxiliary peak is the complete final context, including all original entries. -/
lemma retainPersistent_auxiliary {model : ExecutionModel}
    (ctx : RuntimeCtx model.kind) (width scalarWidth : Nat)
    (path : (retainPersistent ctx width scalarWidth).Path) :
    (retainPersistent ctx width scalarWidth).peakAuxiliarySpace path =
      (persistentCtx ctx width scalarWidth).auxiliarySpace := by
  apply le_antisymm ?_ ((retainPersistent ctx width scalarWidth).output_auxiliarySpace_le_peak path)
  change SpacePool.max ctx.auxiliarySpace (SpacePool.max (persistentLatchCtx ctx).auxiliarySpace
    (SpacePool.max (persistentLatchCtx ctx).auxiliarySpace (SpacePool.max (persistentSelectedCtx
    ctx scalarWidth).auxiliarySpace (SpacePool.max (persistentSelectedCtx ctx
    scalarWidth).auxiliarySpace (SpacePool.max (persistentInverseCtx ctx
    scalarWidth).auxiliarySpace (SpacePool.max (persistentInverseCtx ctx
    scalarWidth).auxiliarySpace (SpacePool.max (persistentCandidateCtx ctx
    scalarWidth).auxiliarySpace (SpacePool.max (persistentCandidateCtx ctx
    scalarWidth).auxiliarySpace (SpacePool.max (persistentBaseCtx ctx
    scalarWidth).auxiliarySpace (SpacePool.max (persistentBaseCtx ctx
    scalarWidth).auxiliarySpace (SpacePool.max (acceptedCtx (persistentBaseCtx ctx
    scalarWidth)).auxiliarySpace (SpacePool.max (acceptedCtx (persistentBaseCtx ctx
    scalarWidth)).auxiliarySpace (SpacePool.max (persistentCtx ctx width
    scalarWidth).auxiliarySpace (0)))))))))))))) ≤ _
  exact persistentPeak_le
    (show ctx.auxiliarySpace ≤ (persistentLatchCtx ctx).auxiliarySpace from le_add_self)
    (show (persistentLatchCtx ctx).auxiliarySpace ≤ (persistentSelectedCtx ctx
      scalarWidth).auxiliarySpace from le_add_self)
    (show (persistentSelectedCtx ctx scalarWidth).auxiliarySpace ≤ (persistentInverseCtx ctx
      scalarWidth).auxiliarySpace from le_add_self)
    (show (persistentInverseCtx ctx scalarWidth).auxiliarySpace ≤ (persistentCandidateCtx ctx
      scalarWidth).auxiliarySpace from le_add_self)
    (show (persistentCandidateCtx ctx scalarWidth).auxiliarySpace ≤ (persistentBaseCtx ctx
      scalarWidth).auxiliarySpace from le_add_self)
    (show (persistentBaseCtx ctx scalarWidth).auxiliarySpace ≤ (acceptedCtx (persistentBaseCtx
      ctx scalarWidth)).auxiliarySpace from le_add_self)
    (show (acceptedCtx (persistentBaseCtx ctx scalarWidth)).auxiliarySpace ≤ (persistentCtx ctx
      width scalarWidth).auxiliarySpace from le_add_self)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
