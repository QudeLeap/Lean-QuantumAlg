/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Core.Base.Accounting.Context

/-!
# Sealed live-space flows

`SpaceFlow pre post` records the typed runtime contexts visited by one liveness
flow. A single private trace is interpreted once to obtain both resident and
auxiliary peaks. Sequential and alternative paths take pointwise maxima;
genuinely parallel flows add their peaks after a trace-wide identity and
physical-placement disjointness check.

The public API has no raw transition or claimed-peak constructor. Workspace
release is the typed inverse of one exact allocation, branches share the same
endpoints, and invariant loops must return to the same context. Progressive
repetition is represented by a chain of actual compatible flows, so retained
storage grows through its real intermediate contexts rather than a multiplier.
-/

section

namespace QuantumAlg

private inductive SpaceTrace {kind : ProblemKind} :
    RuntimeCtx kind → RuntimeCtx kind → Type where
  | stay (ctx : RuntimeCtx kind) : SpaceTrace ctx ctx
  | checkedStep (pre post : RuntimeCtx kind) : SpaceTrace pre post
  | seq {pre mid post : RuntimeCtx kind}
      (first : SpaceTrace pre mid) (second : SpaceTrace mid post) :
      SpaceTrace pre post
  | branch {pre post : RuntimeCtx kind}
      (left right : SpaceTrace pre post) : SpaceTrace pre post
  | loopInvariant (ctx : RuntimeCtx kind) (count : Nat)
      (body : SpaceTrace ctx ctx) : SpaceTrace ctx ctx
  | tensor {leftPre leftPost rightPre rightPost : RuntimeCtx kind}
      (left : SpaceTrace leftPre leftPost)
      (right : SpaceTrace rightPre rightPost)
      (preDisjoint : RuntimeCtx.StorageDisjoint leftPre rightPre)
      (postDisjoint : RuntimeCtx.StorageDisjoint leftPost rightPost) :
      SpaceTrace
        (RuntimeCtx.disjointUnion leftPre rightPre preDisjoint)
        (RuntimeCtx.disjointUnion leftPost rightPost postDisjoint)

private abbrev SpacePeaks (kind : ProblemKind) :=
  SpacePool kind × SpacePool kind

private def contextPeaks {kind : ProblemKind}
    (ctx : RuntimeCtx kind) : SpacePeaks kind :=
  (ctx.residentSpace, ctx.auxiliarySpace)

private def maxPeaks {kind : ProblemKind}
    (left right : SpacePeaks kind) : SpacePeaks kind :=
  (SpacePool.max left.1 right.1, SpacePool.max left.2 right.2)

private def addPeaks {kind : ProblemKind}
    (left right : SpacePeaks kind) : SpacePeaks kind :=
  (left.1 + right.1, left.2 + right.2)

private def SpaceTrace.spacePeaks {kind : ProblemKind}
    {pre post : RuntimeCtx kind} : SpaceTrace pre post → SpacePeaks kind
  | .stay ctx => contextPeaks ctx
  | .checkedStep pre post => maxPeaks (contextPeaks pre) (contextPeaks post)
  | .seq first second => maxPeaks first.spacePeaks second.spacePeaks
  | .branch left right => maxPeaks left.spacePeaks right.spacePeaks
  | .loopInvariant ctx 0 _body => contextPeaks ctx
  | .loopInvariant _ctx (_count + 1) body => body.spacePeaks
  | .tensor left right _preDisjoint _postDisjoint =>
      addPeaks left.spacePeaks right.spacePeaks

private def SpaceTrace.usedKeys {kind : ProblemKind}
    {pre post : RuntimeCtx kind} : SpaceTrace pre post → List StorageKey
  | .stay ctx => ctx.keys
  | .checkedStep pre post => pre.keys ++ post.keys
  | .seq first second => first.usedKeys ++ second.usedKeys
  | .branch left right => left.usedKeys ++ right.usedKeys
  | .loopInvariant ctx 0 _body => ctx.keys
  | .loopInvariant _ctx (_count + 1) body => body.usedKeys
  | .tensor left right _preDisjoint _postDisjoint =>
      left.usedKeys ++ right.usedKeys

private def SpaceTrace.usedPhysicalIdx {kind : ProblemKind}
    {pre post : RuntimeCtx kind} : SpaceTrace pre post → List Nat
  | .stay ctx => ctx.physicalIdx
  | .checkedStep pre post => pre.physicalIdx ++ post.physicalIdx
  | .seq first second => first.usedPhysicalIdx ++ second.usedPhysicalIdx
  | .branch left right => left.usedPhysicalIdx ++ right.usedPhysicalIdx
  | .loopInvariant ctx 0 _body => ctx.physicalIdx
  | .loopInvariant _ctx (_count + 1) body => body.usedPhysicalIdx
  | .tensor left right _preDisjoint _postDisjoint =>
      left.usedPhysicalIdx ++ right.usedPhysicalIdx

/-- A sealed liveness flow between two exact runtime contexts. -/
structure SpaceFlow {kind : ProblemKind} (pre post : RuntimeCtx kind) where
  private mk ::
  /-- The single source of visited contexts and both peak projections. -/
  private trace : SpaceTrace pre post

-- Intentional declaration-scoped exception: the linter cannot resolve the
-- private projection, while its value is computational trace data, not a proof.
attribute [nolint structureInType] SpaceFlow

namespace SpaceFlow

/-- A flow that visits one context and performs no transition. -/
def stay {kind : ProblemKind} (ctx : RuntimeCtx kind) : SpaceFlow ctx ctx where
  trace := .stay ctx

private def checkedStep {kind : ProblemKind}
    (pre post : RuntimeCtx kind) : SpaceFlow pre post where
  trace := .checkedStep pre post

/-- Allocate classical workspace through the checked context constructor.

This raw transition is deliberately file-private. Public callers construct a
balanced `workspaceRegion`, never a detached push. -/
private def allocateWorkspace {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    SpaceFlow ctx (ctx.addWorkspace key shape fresh) :=
  checkedStep ctx (ctx.addWorkspace key shape fresh)

/-- Release exactly the most recently described workspace allocation.

This raw transition is deliberately file-private. Public callers construct a
balanced `workspaceRegion`, never a detached pop. -/
private def releaseWorkspace {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    SpaceFlow (ctx.addWorkspace key shape fresh) ctx :=
  checkedStep (ctx.addWorkspace key shape fresh) ctx

/-- Retain one intermediate classical value in the post-context. -/
def retain {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    SpaceFlow ctx (ctx.addRetained key shape fresh) :=
  checkedStep ctx (ctx.addRetained key shape fresh)

/-- Terminally promote one retained head cell to final-output storage.

The pre- and post-contexts are rebuilt from the same base context, key, shape,
and freshness witness.  The transition therefore changes only the storage
role: it neither allocates a second cell nor permits a detached final-output
scratch region.  The typed run interpreter is the only layer that pairs this
flow with the corresponding value-preserving store transition. -/
def promoteRetained {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    SpaceFlow (ctx.addRetained key shape fresh)
      (ctx.addFinalOutput key shape fresh) :=
  checkedStep (ctx.addRetained key shape fresh)
    (ctx.addFinalOutput key shape fresh)

/-- Prepare one algorithm-owned typed layout through the checked ownership
constructor.

This liveness transition fixes the owned placement and derives its resident and
auxiliary contribution from the post-context. The typed run layer separately
fixes the known prepared state and its resource event; callers cannot attach a
space claim to this flow. -/
def prepareOwned (ctx : RuntimeCtx .quantum) (key : StorageKey)
    {systemCount : Nat} (layout : QuantumLayout systemCount)
    (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
    SpaceFlow ctx (ctx.addOwnedLayout key layout fresh disjoint) :=
  checkedStep ctx (ctx.addOwnedLayout key layout fresh disjoint)

/-- Execute two compatible flows sequentially. -/
def seq {kind : ProblemKind} {pre mid post : RuntimeCtx kind}
    (first : SpaceFlow pre mid) (second : SpaceFlow mid post) :
    SpaceFlow pre post where
  trace := .seq first.trace second.trace

/-- Join two alternative paths only when both have identical endpoints. -/
def branch {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (left right : SpaceFlow pre post) : SpaceFlow pre post where
  trace := .branch left.trace right.trace

/-- Repeat an invariant body an exact number of times. Zero visits only the
invariant context; positive counts retain the body's actual peak once. -/
def loopInvariant {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (count : Nat) (body : SpaceFlow ctx ctx) : SpaceFlow ctx ctx where
  trace := .loopInvariant ctx count body.trace

/-- Execute a lexical workspace body and release its exact head allocation.

The single public constructor packages allocation, body, and release. Its type
forces the body to preserve the extended context, so empty, double, or
non-LIFO release has no public representation. -/
def workspaceRegion {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (body : SpaceFlow
      (ctx.addWorkspace key shape fresh)
      (ctx.addWorkspace key shape fresh)) : SpaceFlow ctx ctx :=
  seq (allocateWorkspace ctx key shape fresh)
    (seq body (releaseWorkspace ctx key shape fresh))

/-- Every storage key visited anywhere in a sealed flow. -/
def allStorageKeys {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (flow : SpaceFlow pre post) : Finset StorageKey :=
  flow.trace.usedKeys.toFinset

/-- Every physical system visited anywhere in a sealed flow. -/
def allPhysicalIdx {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (flow : SpaceFlow pre post) : Finset Nat :=
  flow.trace.usedPhysicalIdx.toFinset

/-- Trace-wide separation required for true-parallel composition. -/
structure GloballyDisjoint {kind : ProblemKind}
    {leftPre leftPost rightPre rightPost : RuntimeCtx kind}
    (left : SpaceFlow leftPre leftPost)
    (right : SpaceFlow rightPre rightPost) : Prop where
  /-- No storage identity occurs in both traces. -/
  keys : Disjoint left.allStorageKeys right.allStorageKeys
  /-- No physical quantum system occurs in both traces. -/
  physical : Disjoint left.allPhysicalIdx right.allPhysicalIdx

instance instDecidableGloballyDisjoint {kind : ProblemKind}
    {leftPre leftPost rightPre rightPost : RuntimeCtx kind}
    (left : SpaceFlow leftPre leftPost)
    (right : SpaceFlow rightPre rightPost) :
    Decidable (GloballyDisjoint left right) :=
  decidable_of_iff
    (Disjoint left.allStorageKeys right.allStorageKeys ∧
      Disjoint left.allPhysicalIdx right.allPhysicalIdx)
    ⟨fun evidence => ⟨evidence.1, evidence.2⟩,
      fun evidence => ⟨evidence.keys, evidence.physical⟩⟩

private theorem SpaceTrace.pre_key_mem_used {kind : ProblemKind}
    {pre post : RuntimeCtx kind} (trace : SpaceTrace pre post)
    {key : StorageKey} (member : key ∈ pre.keys) : key ∈ trace.usedKeys := by
  induction trace with
  | stay ctx => exact member
  | checkedStep pre post => exact List.mem_append_left post.keys member
  | seq first second ihFirst _ =>
      exact List.mem_append_left second.usedKeys (ihFirst member)
  | branch left right ihLeft _ =>
      exact List.mem_append_left right.usedKeys (ihLeft member)
  | loopInvariant ctx count body ih =>
      cases count with
      | zero => exact member
      | succ count => exact ih member
  | tensor left right preDisjoint postDisjoint ihLeft ihRight =>
      rw [RuntimeCtx.keys_disjointUnion] at member
      rcases List.mem_append.mp member with inLeft | inRight
      · exact List.mem_append_left right.usedKeys (ihLeft inLeft)
      · exact List.mem_append_right left.usedKeys (ihRight inRight)

private theorem SpaceTrace.post_key_mem_used {kind : ProblemKind}
    {pre post : RuntimeCtx kind} (trace : SpaceTrace pre post)
    {key : StorageKey} (member : key ∈ post.keys) : key ∈ trace.usedKeys := by
  induction trace with
  | stay ctx => exact member
  | checkedStep pre post => exact List.mem_append_right pre.keys member
  | seq first second _ ihSecond =>
      exact List.mem_append_right first.usedKeys (ihSecond member)
  | branch left right ihLeft _ =>
      exact List.mem_append_left right.usedKeys (ihLeft member)
  | loopInvariant ctx count body ih =>
      cases count with
      | zero => exact member
      | succ count => exact ih member
  | tensor left right preDisjoint postDisjoint ihLeft ihRight =>
      rw [RuntimeCtx.keys_disjointUnion] at member
      rcases List.mem_append.mp member with inLeft | inRight
      · exact List.mem_append_left right.usedKeys (ihLeft inLeft)
      · exact List.mem_append_right left.usedKeys (ihRight inRight)

private theorem SpaceTrace.pre_physical_mem_used {kind : ProblemKind}
    {pre post : RuntimeCtx kind} (trace : SpaceTrace pre post)
    {physical : Nat} (member : physical ∈ pre.physicalIdx) :
    physical ∈ trace.usedPhysicalIdx := by
  induction trace with
  | stay ctx => exact member
  | checkedStep pre post => exact List.mem_append_left post.physicalIdx member
  | seq first second ihFirst _ =>
      exact List.mem_append_left second.usedPhysicalIdx (ihFirst member)
  | branch left right ihLeft _ =>
      exact List.mem_append_left right.usedPhysicalIdx (ihLeft member)
  | loopInvariant ctx count body ih =>
      cases count with
      | zero => exact member
      | succ count => exact ih member
  | tensor left right preDisjoint postDisjoint ihLeft ihRight =>
      rw [RuntimeCtx.physicalIdx_disjointUnion] at member
      rcases List.mem_append.mp member with inLeft | inRight
      · exact List.mem_append_left right.usedPhysicalIdx (ihLeft inLeft)
      · exact List.mem_append_right left.usedPhysicalIdx (ihRight inRight)

private theorem SpaceTrace.post_physical_mem_used {kind : ProblemKind}
    {pre post : RuntimeCtx kind} (trace : SpaceTrace pre post)
    {physical : Nat} (member : physical ∈ post.physicalIdx) :
    physical ∈ trace.usedPhysicalIdx := by
  induction trace with
  | stay ctx => exact member
  | checkedStep pre post => exact List.mem_append_right pre.physicalIdx member
  | seq first second _ ihSecond =>
      exact List.mem_append_right first.usedPhysicalIdx (ihSecond member)
  | branch left right ihLeft _ =>
      exact List.mem_append_left right.usedPhysicalIdx (ihLeft member)
  | loopInvariant ctx count body ih =>
      cases count with
      | zero => exact member
      | succ count => exact ih member
  | tensor left right preDisjoint postDisjoint ihLeft ihRight =>
      rw [RuntimeCtx.physicalIdx_disjointUnion] at member
      rcases List.mem_append.mp member with inLeft | inRight
      · exact List.mem_append_left right.usedPhysicalIdx (ihLeft inLeft)
      · exact List.mem_append_right left.usedPhysicalIdx (ihRight inRight)

/-- Trace-wide separation implies disjoint entry contexts. -/
theorem GloballyDisjoint.pre {kind : ProblemKind}
    {leftPre leftPost rightPre rightPost : RuntimeCtx kind}
    {left : SpaceFlow leftPre leftPost} {right : SpaceFlow rightPre rightPost}
    (separate : GloballyDisjoint left right) :
    RuntimeCtx.StorageDisjoint leftPre rightPre := by
  constructor
  · rw [RuntimeCtx.keysDisjoint_iff_listDisjoint]
    intro key inLeft inRight
    exact Finset.disjoint_left.mp separate.keys
      (by simpa [allStorageKeys] using SpaceTrace.pre_key_mem_used left.trace inLeft)
      (by simpa [allStorageKeys] using SpaceTrace.pre_key_mem_used right.trace inRight)
  · rw [RuntimeCtx.physicallyDisjoint_iff_listDisjoint]
    intro physical inLeft inRight
    exact Finset.disjoint_left.mp separate.physical
      (by simpa [allPhysicalIdx] using
        SpaceTrace.pre_physical_mem_used left.trace inLeft)
      (by simpa [allPhysicalIdx] using
        SpaceTrace.pre_physical_mem_used right.trace inRight)

/-- Trace-wide separation implies disjoint exit contexts. -/
theorem GloballyDisjoint.post {kind : ProblemKind}
    {leftPre leftPost rightPre rightPost : RuntimeCtx kind}
    {left : SpaceFlow leftPre leftPost} {right : SpaceFlow rightPre rightPost}
    (separate : GloballyDisjoint left right) :
    RuntimeCtx.StorageDisjoint leftPost rightPost := by
  constructor
  · rw [RuntimeCtx.keysDisjoint_iff_listDisjoint]
    intro key inLeft inRight
    exact Finset.disjoint_left.mp separate.keys
      (by simpa [allStorageKeys] using SpaceTrace.post_key_mem_used left.trace inLeft)
      (by simpa [allStorageKeys] using SpaceTrace.post_key_mem_used right.trace inRight)
  · rw [RuntimeCtx.physicallyDisjoint_iff_listDisjoint]
    intro physical inLeft inRight
    exact Finset.disjoint_left.mp separate.physical
      (by simpa [allPhysicalIdx] using
        SpaceTrace.post_physical_mem_used left.trace inLeft)
      (by simpa [allPhysicalIdx] using
        SpaceTrace.post_physical_mem_used right.trace inRight)

/-- Compose genuinely parallel flows only after checking every identity and
physical system visited by either trace. -/
def tensor {kind : ProblemKind}
    {leftPre leftPost rightPre rightPost : RuntimeCtx kind}
    (left : SpaceFlow leftPre leftPost) (right : SpaceFlow rightPre rightPost)
    (separate : GloballyDisjoint left right) :
    SpaceFlow
      (RuntimeCtx.disjointUnion leftPre rightPre separate.pre)
      (RuntimeCtx.disjointUnion leftPost rightPost separate.post) where
  trace := .tensor left.trace right.trace separate.pre separate.post

/-- Resident and auxiliary peaks derived together from the sealed trace. -/
private def peaks {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (flow : SpaceFlow pre post) : SpacePeaks kind :=
  flow.trace.spacePeaks

/-- Peak resident live space over every state/path in the flow. -/
def peakResidentSpace {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (flow : SpaceFlow pre post) : SpacePool kind :=
  flow.peaks.1

/-- Peak auxiliary live space derived from the same trace traversal. -/
def peakAuxiliarySpace {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (flow : SpaceFlow pre post) : SpacePool kind :=
  flow.peaks.2

private theorem SpaceTrace.residentSpace_pre_le {kind : ProblemKind}
    {pre post : RuntimeCtx kind} (trace : SpaceTrace pre post) :
    pre.residentSpace ≤ trace.spacePeaks.1 := by
  induction trace with
  | stay ctx => exact le_rfl
  | checkedStep pre post =>
      exact SpacePool.le_max_left pre.residentSpace post.residentSpace
  | seq first second ihFirst _ =>
      exact ihFirst.trans (SpacePool.le_max_left _ _)
  | branch left right ihLeft _ =>
      exact ihLeft.trans (SpacePool.le_max_left _ _)
  | loopInvariant ctx count body ih =>
      cases count with
      | zero => exact le_rfl
      | succ count => exact ih
  | tensor left right preDisjoint postDisjoint ihLeft ihRight =>
      rw [RuntimeCtx.residentSpace_disjointUnion]
      intro axis
      exact Nat.add_le_add (ihLeft axis) (ihRight axis)

private theorem SpaceTrace.residentSpace_post_le {kind : ProblemKind}
    {pre post : RuntimeCtx kind} (trace : SpaceTrace pre post) :
    post.residentSpace ≤ trace.spacePeaks.1 := by
  induction trace with
  | stay ctx => exact le_rfl
  | checkedStep pre post =>
      exact SpacePool.le_max_right pre.residentSpace post.residentSpace
  | seq first second _ ihSecond =>
      exact ihSecond.trans (SpacePool.le_max_right _ _)
  | branch left right ihLeft _ =>
      exact ihLeft.trans (SpacePool.le_max_left _ _)
  | loopInvariant ctx count body ih =>
      cases count with
      | zero => exact le_rfl
      | succ count => exact ih
  | tensor left right preDisjoint postDisjoint ihLeft ihRight =>
      rw [RuntimeCtx.residentSpace_disjointUnion]
      intro axis
      exact Nat.add_le_add (ihLeft axis) (ihRight axis)

private theorem SpaceTrace.auxiliarySpace_pre_le {kind : ProblemKind}
    {pre post : RuntimeCtx kind} (trace : SpaceTrace pre post) :
    pre.auxiliarySpace ≤ trace.spacePeaks.2 := by
  induction trace with
  | stay ctx => exact le_rfl
  | checkedStep pre post =>
      exact SpacePool.le_max_left pre.auxiliarySpace post.auxiliarySpace
  | seq first second ihFirst _ =>
      exact ihFirst.trans (SpacePool.le_max_left _ _)
  | branch left right ihLeft _ =>
      exact ihLeft.trans (SpacePool.le_max_left _ _)
  | loopInvariant ctx count body ih =>
      cases count with
      | zero => exact le_rfl
      | succ count => exact ih
  | tensor left right preDisjoint postDisjoint ihLeft ihRight =>
      rw [RuntimeCtx.auxiliarySpace_disjointUnion]
      intro axis
      exact Nat.add_le_add (ihLeft axis) (ihRight axis)

private theorem SpaceTrace.auxiliarySpace_post_le {kind : ProblemKind}
    {pre post : RuntimeCtx kind} (trace : SpaceTrace pre post) :
    post.auxiliarySpace ≤ trace.spacePeaks.2 := by
  induction trace with
  | stay ctx => exact le_rfl
  | checkedStep pre post =>
      exact SpacePool.le_max_right pre.auxiliarySpace post.auxiliarySpace
  | seq first second _ ihSecond =>
      exact ihSecond.trans (SpacePool.le_max_right _ _)
  | branch left right ihLeft _ =>
      exact ihLeft.trans (SpacePool.le_max_left _ _)
  | loopInvariant ctx count body ih =>
      cases count with
      | zero => exact le_rfl
      | succ count => exact ih
  | tensor left right preDisjoint postDisjoint ihLeft ihRight =>
      rw [RuntimeCtx.auxiliarySpace_disjointUnion]
      intro axis
      exact Nat.add_le_add (ihLeft axis) (ihRight axis)

/-- The entry context participates in the resident peak. -/
theorem residentSpace_pre_le_peak {kind : ProblemKind}
    {pre post : RuntimeCtx kind} (flow : SpaceFlow pre post) :
    pre.residentSpace ≤ flow.peakResidentSpace :=
  SpaceTrace.residentSpace_pre_le flow.trace

/-- The exit context participates in the resident peak. -/
theorem residentSpace_post_le_peak {kind : ProblemKind}
    {pre post : RuntimeCtx kind} (flow : SpaceFlow pre post) :
    post.residentSpace ≤ flow.peakResidentSpace :=
  SpaceTrace.residentSpace_post_le flow.trace

/-- The entry context participates in the auxiliary peak. -/
theorem auxiliarySpace_pre_le_peak {kind : ProblemKind}
    {pre post : RuntimeCtx kind} (flow : SpaceFlow pre post) :
    pre.auxiliarySpace ≤ flow.peakAuxiliarySpace :=
  SpaceTrace.auxiliarySpace_pre_le flow.trace

/-- The exit context participates in the auxiliary peak. -/
theorem auxiliarySpace_post_le_peak {kind : ProblemKind}
    {pre post : RuntimeCtx kind} (flow : SpaceFlow pre post) :
    post.auxiliarySpace ≤ flow.peakAuxiliarySpace :=
  SpaceTrace.auxiliarySpace_post_le flow.trace

@[simp] theorem peakResidentSpace_stay {kind : ProblemKind}
    (ctx : RuntimeCtx kind) :
    (stay ctx).peakResidentSpace = ctx.residentSpace := rfl

@[simp] theorem peakAuxiliarySpace_stay {kind : ProblemKind}
    (ctx : RuntimeCtx kind) :
    (stay ctx).peakAuxiliarySpace = ctx.auxiliarySpace := rfl

/-- Retaining one classical cell visits exactly the entry and retained
contexts. -/
@[simp] theorem peakResidentSpace_retain {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys) :
    (retain ctx key shape fresh).peakResidentSpace =
      SpacePool.max ctx.residentSpace
        (ctx.addRetained key shape fresh).residentSpace :=
  rfl

/-- The auxiliary projection of the same retained-cell transition visits the
same two contexts. -/
@[simp] theorem peakAuxiliarySpace_retain {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys) :
    (retain ctx key shape fresh).peakAuxiliarySpace =
      SpacePool.max ctx.auxiliarySpace
        (ctx.addRetained key shape fresh).auxiliarySpace :=
  rfl

@[simp] theorem peakResidentSpace_seq {kind : ProblemKind}
    {pre mid post : RuntimeCtx kind} (first : SpaceFlow pre mid)
    (second : SpaceFlow mid post) :
    (seq first second).peakResidentSpace =
      SpacePool.max first.peakResidentSpace second.peakResidentSpace := rfl

@[simp] theorem peakAuxiliarySpace_seq {kind : ProblemKind}
    {pre mid post : RuntimeCtx kind} (first : SpaceFlow pre mid)
    (second : SpaceFlow mid post) :
    (seq first second).peakAuxiliarySpace =
      SpacePool.max first.peakAuxiliarySpace second.peakAuxiliarySpace := rfl

@[simp] theorem peakResidentSpace_branch {kind : ProblemKind}
    {pre post : RuntimeCtx kind} (left right : SpaceFlow pre post) :
    (branch left right).peakResidentSpace =
      SpacePool.max left.peakResidentSpace right.peakResidentSpace := rfl

@[simp] theorem peakAuxiliarySpace_branch {kind : ProblemKind}
    {pre post : RuntimeCtx kind} (left right : SpaceFlow pre post) :
    (branch left right).peakAuxiliarySpace =
      SpacePool.max left.peakAuxiliarySpace right.peakAuxiliarySpace := rfl

@[simp] theorem peakResidentSpace_loopInvariant_zero {kind : ProblemKind}
    {ctx : RuntimeCtx kind} (body : SpaceFlow ctx ctx) :
    (loopInvariant 0 body).peakResidentSpace = ctx.residentSpace := rfl

@[simp] theorem peakAuxiliarySpace_loopInvariant_zero {kind : ProblemKind}
    {ctx : RuntimeCtx kind} (body : SpaceFlow ctx ctx) :
    (loopInvariant 0 body).peakAuxiliarySpace = ctx.auxiliarySpace := rfl

@[simp] theorem peakResidentSpace_loopInvariant_succ {kind : ProblemKind}
    {ctx : RuntimeCtx kind} (count : Nat) (body : SpaceFlow ctx ctx) :
    (loopInvariant (count + 1) body).peakResidentSpace = body.peakResidentSpace := rfl

@[simp] theorem peakAuxiliarySpace_loopInvariant_succ {kind : ProblemKind}
    {ctx : RuntimeCtx kind} (count : Nat) (body : SpaceFlow ctx ctx) :
    (loopInvariant (count + 1) body).peakAuxiliarySpace = body.peakAuxiliarySpace := rfl

@[simp] theorem peakResidentSpace_tensor {kind : ProblemKind}
    {leftPre leftPost rightPre rightPost : RuntimeCtx kind}
    (left : SpaceFlow leftPre leftPost) (right : SpaceFlow rightPre rightPost)
    (separate : GloballyDisjoint left right) :
    (tensor left right separate).peakResidentSpace =
      left.peakResidentSpace + right.peakResidentSpace := rfl

@[simp] theorem peakAuxiliarySpace_tensor {kind : ProblemKind}
    {leftPre leftPost rightPre rightPost : RuntimeCtx kind}
    (left : SpaceFlow leftPre leftPost) (right : SpaceFlow rightPre rightPost)
    (separate : GloballyDisjoint left right) :
    (tensor left right separate).peakAuxiliarySpace =
      left.peakAuxiliarySpace + right.peakAuxiliarySpace := rfl

/-- Extending a valid flow on the right cannot lower its resident peak. -/
theorem peakResidentSpace_le_seq_left {kind : ProblemKind}
    {pre mid post : RuntimeCtx kind} (first : SpaceFlow pre mid)
    (second : SpaceFlow mid post) :
    first.peakResidentSpace ≤ (seq first second).peakResidentSpace :=
  SpacePool.le_max_left _ _

/-- Extending a valid flow on the left cannot lower its resident peak. -/
theorem peakResidentSpace_le_seq_right {kind : ProblemKind}
    {pre mid post : RuntimeCtx kind} (first : SpaceFlow pre mid)
    (second : SpaceFlow mid post) :
    second.peakResidentSpace ≤ (seq first second).peakResidentSpace :=
  SpacePool.le_max_right _ _

/-- Extending a valid flow on the right cannot lower its auxiliary peak. -/
theorem peakAuxiliarySpace_le_seq_left {kind : ProblemKind}
    {pre mid post : RuntimeCtx kind} (first : SpaceFlow pre mid)
    (second : SpaceFlow mid post) :
    first.peakAuxiliarySpace ≤ (seq first second).peakAuxiliarySpace :=
  SpacePool.le_max_left _ _

/-- Extending a valid flow on the left cannot lower its auxiliary peak. -/
theorem peakAuxiliarySpace_le_seq_right {kind : ProblemKind}
    {pre mid post : RuntimeCtx kind} (first : SpaceFlow pre mid)
    (second : SpaceFlow mid post) :
    second.peakAuxiliarySpace ≤ (seq first second).peakAuxiliarySpace :=
  SpacePool.le_max_right _ _

theorem peakResidentSpace_le_branch_left {kind : ProblemKind}
    {pre post : RuntimeCtx kind} (left right : SpaceFlow pre post) :
    left.peakResidentSpace ≤ (branch left right).peakResidentSpace :=
  SpacePool.le_max_left _ _

theorem peakResidentSpace_le_branch_right {kind : ProblemKind}
    {pre post : RuntimeCtx kind} (left right : SpaceFlow pre post) :
    right.peakResidentSpace ≤ (branch left right).peakResidentSpace :=
  SpacePool.le_max_right _ _

theorem peakAuxiliarySpace_le_branch_left {kind : ProblemKind}
    {pre post : RuntimeCtx kind} (left right : SpaceFlow pre post) :
    left.peakAuxiliarySpace ≤ (branch left right).peakAuxiliarySpace :=
  SpacePool.le_max_left _ _

theorem peakAuxiliarySpace_le_branch_right {kind : ProblemKind}
    {pre post : RuntimeCtx kind} (left right : SpaceFlow pre post) :
    right.peakAuxiliarySpace ≤ (branch left right).peakAuxiliarySpace :=
  SpacePool.le_max_right _ _

end SpaceFlow

/-- A finite chain of compatible attempt flows. Each intermediate context is
real, so retained values grow through actual states rather than a count field. -/
inductive SpaceRepetition {kind : ProblemKind} :
    RuntimeCtx kind → Nat → RuntimeCtx kind → Type where
  | zero (ctx : RuntimeCtx kind) : SpaceRepetition ctx 0 ctx
  | succ {pre mid post : RuntimeCtx kind} {attempts : Nat}
      (attempt : SpaceFlow pre mid)
      (rest : SpaceRepetition mid attempts post) :
      SpaceRepetition pre (attempts + 1) post

namespace SpaceFlow

/-- Interpret an actual compatible repetition chain as one sealed flow. -/
def repetition {kind : ProblemKind} {pre post : RuntimeCtx kind} {attempts : Nat} :
    SpaceRepetition pre attempts post → SpaceFlow pre post
  | .zero ctx => stay ctx
  | .succ attempt rest => seq attempt (repetition rest)

@[simp] theorem repetition_zero {kind : ProblemKind} (ctx : RuntimeCtx kind) :
    repetition (.zero ctx) = stay ctx := rfl

@[simp] theorem repetition_succ {kind : ProblemKind}
    {pre mid post : RuntimeCtx kind} {attempts : Nat}
    (attempt : SpaceFlow pre mid) (rest : SpaceRepetition mid attempts post) :
    repetition (.succ attempt rest) = seq attempt (repetition rest) := rfl

end SpaceFlow

namespace AccountingFlowFixtures

/-!
These executable fixtures pin the space algebra to actual typed transitions.
They intentionally use small closed shapes and layouts so every expected peak
reduces without a caller-provided bound.
-/

private def key0 : StorageKey := ⟨0⟩
private def key1 : StorageKey := ⟨1⟩
private def key2 : StorageKey := ⟨2⟩
private def key10 : StorageKey := ⟨10⟩
private def key11 : StorageKey := ⟨11⟩

private def emptyClassical : RuntimeCtx .classical := RuntimeCtx.empty

private def workspace32 : RuntimeCtx .classical :=
  emptyClassical.addWorkspace key0 (.bits 32) (by decide)

private def workspace40 : RuntimeCtx .classical :=
  workspace32.addWorkspace key1 (.bits 8) (by decide)

/-- An allocation makes the exit context the unique nonzero maximum. -/
private def exitOnlyAllocation : SpaceFlow emptyClassical workspace32 :=
  SpaceFlow.allocateWorkspace emptyClassical key0 (.bits 32) (by decide)

/-- A release makes the entry context the unique nonzero maximum. -/
private def entryOnlyRelease : SpaceFlow workspace32 emptyClassical :=
  SpaceFlow.releaseWorkspace emptyClassical key0 (.bits 32) (by decide)

private def nestedAllocation : SpaceFlow workspace32 workspace40 :=
  SpaceFlow.allocateWorkspace workspace32 key1 (.bits 8) (by decide)

example : SpaceFlow.peakResidentSpace exitOnlyAllocation .classicalBits = 32 := rfl
example : SpaceFlow.peakAuxiliarySpace exitOnlyAllocation .classicalBits = 32 := rfl
example : SpaceFlow.peakResidentSpace entryOnlyRelease .classicalBits = 32 := rfl
example : SpaceFlow.peakAuxiliarySpace entryOnlyRelease .classicalBits = 32 := rfl

private def workspaceRoundTrip8 : SpaceFlow emptyClassical emptyClassical :=
  let fresh : key0 ∉ emptyClassical.keys := by decide
  SpaceFlow.workspaceRegion emptyClassical key0 (.bits 8) fresh
    (SpaceFlow.stay (emptyClassical.addWorkspace key0 (.bits 8) fresh))

private def workspaceRoundTrip32 : SpaceFlow emptyClassical emptyClassical :=
  let fresh : key0 ∉ emptyClassical.keys := by decide
  SpaceFlow.workspaceRegion emptyClassical key0 (.bits 32) fresh
    (SpaceFlow.stay (emptyClassical.addWorkspace key0 (.bits 32) fresh))

private def finalOne : RuntimeCtx .classical :=
  emptyClassical.addFinalOutput key1 (.bits 1) (by decide)

/-- Sequential composition takes a maximum: eight transient bits dominate one
bit of final output. -/
private def sequentialMax : SpaceFlow emptyClassical finalOne :=
  SpaceFlow.seq workspaceRoundTrip8
    (SpaceFlow.seq
      (SpaceFlow.retain emptyClassical key1 (.bits 1) (by decide))
      (SpaceFlow.promoteRetained emptyClassical key1 (.bits 1) (by decide)))

example : SpaceFlow.peakResidentSpace sequentialMax .classicalBits = 8 := rfl
example : SpaceFlow.peakAuxiliarySpace sequentialMax .classicalBits = 8 := rfl

/-- Alternative paths take their actual pointwise maximum. -/
private def branchMax : SpaceFlow emptyClassical emptyClassical :=
  SpaceFlow.branch workspaceRoundTrip8 workspaceRoundTrip32

example : SpaceFlow.peakResidentSpace branchMax .classicalBits = 32 := rfl
example : SpaceFlow.peakAuxiliarySpace branchMax .classicalBits = 32 := rfl

/-- A zero-count loop visits only its invariant context. -/
example : SpaceFlow.peakAuxiliarySpace
    (SpaceFlow.loopInvariant 0 workspaceRoundTrip32) .classicalBits = 0 := rfl

/-- Reusable workspace is not multiplied by three invariant attempts. -/
example : SpaceFlow.peakAuxiliarySpace
    (SpaceFlow.loopInvariant 3 workspaceRoundTrip32) .classicalBits = 32 := rfl

private def oneQubitAt (physical : Nat) : QuantumLayout 1 :=
  QuantumLayout.uniform 1 2 (fun _ => physical) (fun _ _ _ => Subsingleton.elim _ _)

private def ownedLeft : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addOwnedLayout key10 (oneQubitAt 0) (by decide)
    (by simp [RuntimeCtx.physicalIdx, RuntimeCtx.quantumWires])

private def ownedRight : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addOwnedLayout key11 (oneQubitAt 1) (by decide)
    (by simp [RuntimeCtx.physicalIdx, RuntimeCtx.quantumWires])

/-- A distinct storage identity deliberately placed on the left system. -/
private def ownedOverlap : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addOwnedLayout key11 (oneQubitAt 0) (by decide)
    (by simp [RuntimeCtx.physicalIdx, RuntimeCtx.quantumWires])

private def preparedOwnedLeft : SpaceFlow RuntimeCtx.empty ownedLeft :=
  SpaceFlow.prepareOwned RuntimeCtx.empty key10 (oneQubitAt 0) (by decide)
    (by simp [RuntimeCtx.physicalIdx, RuntimeCtx.quantumWires])

example : ownedLeft.systemCount = 1 := by decide
example : ownedLeft.quantumLayout.identities = [0] := by decide
example : SpaceFlow.peakAuxiliarySpace preparedOwnedLeft (.quantumSystems 2) = 1 := by
  decide

private def disjointTensor :=
  SpaceFlow.tensor (SpaceFlow.stay ownedLeft) (SpaceFlow.stay ownedRight) (by decide)

example : SpaceFlow.GloballyDisjoint
    (SpaceFlow.stay ownedLeft) (SpaceFlow.stay ownedRight) := by decide
example : SpaceFlow.peakResidentSpace disjointTensor (.quantumSystems 2) = 2 := rfl
example : SpaceFlow.peakAuxiliarySpace disjointTensor (.quantumSystems 2) = 2 := rfl

private def retainedOne : RuntimeCtx .classical :=
  emptyClassical.addRetained key1 (.bits 1) (by decide)

private def retainedTwo : RuntimeCtx .classical :=
  retainedOne.addRetained key2 (.bits 1) (by decide)

private def firstAttempt : SpaceFlow emptyClassical retainedOne :=
  let workspaceFresh : key0 ∉ emptyClassical.keys := by decide
  SpaceFlow.seq
    (SpaceFlow.workspaceRegion emptyClassical key0 (.bits 32) workspaceFresh
      (SpaceFlow.stay
        (emptyClassical.addWorkspace key0 (.bits 32) workspaceFresh)))
    (SpaceFlow.retain emptyClassical key1 (.bits 1) (by decide))

private def secondAttempt : SpaceFlow retainedOne retainedTwo :=
  let workspaceFresh : key0 ∉ retainedOne.keys := by decide
  SpaceFlow.seq
    (SpaceFlow.workspaceRegion retainedOne key0 (.bits 32) workspaceFresh
      (SpaceFlow.stay
        (retainedOne.addWorkspace key0 (.bits 32) workspaceFresh)))
    (SpaceFlow.retain retainedOne key2 (.bits 1) (by decide))

private def retainedAttempts : SpaceRepetition emptyClassical 2 retainedTwo :=
  .succ firstAttempt (.succ secondAttempt (.zero retainedTwo))

/-- The second attempt reuses 32 workspace bits while one retained bit remains
live, so the actual peak is 33 rather than 64; the exit contains two retained
samples. -/
private def retainedGrowth : SpaceFlow emptyClassical retainedTwo :=
  SpaceFlow.repetition retainedAttempts

example : SpaceFlow.peakAuxiliarySpace retainedGrowth .classicalBits = 33 := rfl
example : retainedTwo.auxiliarySpace .classicalBits = 2 := rfl

/- Empty release is rejected: a release must start at the exact allocated context. -/
/-- error: Type mismatch -/
#guard_msgs(error, drop info, substring := true) in
example : SpaceFlow emptyClassical emptyClassical :=
  SpaceFlow.releaseWorkspace emptyClassical key0 (.bits 32) (by decide)

/- Double release is rejected because the first release no longer leaves the
allocated context required by the second. -/
/-- error: Application type mismatch -/
#guard_msgs(error, drop info, substring := true) in
#check SpaceFlow.seq entryOnlyRelease entryOnlyRelease

/- A non-LIFO release is rejected: after allocating the inner workspace, the
outer release cannot consume a context whose inner head is still live. -/
/-- error: Application type mismatch -/
#guard_msgs(error, drop info, substring := true) in
#check SpaceFlow.seq nestedAllocation entryOnlyRelease

/- An incompatible branch cannot join paths with distinct post-contexts. -/
/-- error: Application type mismatch -/
#guard_msgs(error, drop info, substring := true) in
#check SpaceFlow.branch exitOnlyAllocation (SpaceFlow.stay emptyClassical)

/- A loop with net allocation cannot inhabit the invariant `ctx → ctx` body type. -/
/-- error: Application type mismatch -/
#guard_msgs(error, drop info, substring := true) in
#check SpaceFlow.loopInvariant 2 exitOnlyAllocation

/- An overlapping tensor layout fails even when the storage keys differ. -/
/-- error: Tactic `decide` proved that the proposition -/
#guard_msgs(error, drop info, substring := true) in
example : SpaceFlow.GloballyDisjoint
    (SpaceFlow.stay ownedLeft) (SpaceFlow.stay ownedOverlap) := by decide

/- Trace-wide tensor separation cannot be weakened to endpoint checking: both
round trips start and end empty, but their intermediate workspace key overlaps. -/
/-- error: Tactic `decide` proved that the proposition -/
#guard_msgs(error, drop info, substring := true) in
example : SpaceFlow.GloballyDisjoint workspaceRoundTrip32 workspaceRoundTrip32 := by decide

end AccountingFlowFixtures

end QuantumAlg

end
