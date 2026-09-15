/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.Trivial.Native
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Exact actual order-one recovery resources

The original word equality and option pack are the only native events.
The candidate word is allocated before the inner tag and both remain live
through packing. Retention precedes both scopes and keeps the original
optional result live afterward, including when the word width is zero.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.Trivial.Native

open Execution ClassicalWorkspace

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The two original native operations retain their exact widths and chronological order. -/
def zeroEvents (kind : ProblemKind) (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordBinary .equal width),
    .classicalOperation (.nominalEncoding (.packOption width))]

/-- Actual allocation and release preserve the original two-event trace. -/
theorem zeroInto_eventTrace (output : CWriteRef ctx (.option (.unsignedWord width)))
    (path : (zeroInto output).Path) :
    (zeroInto output).eventTrace path = zeroEvents kind width := rfl

/-- The exact native pool is derived from the same actual two-event trace. -/
theorem zeroInto_resourcePool (output : CWriteRef ctx (.option (.unsignedWord width)))
    (path : (zeroInto output).Path) :
    (zeroInto output).resourcePool path = ResourcePool.ofList (zeroEvents kind width) := rfl

/-- The actual dependency chain charges equality followed by the original option pack. -/
theorem zeroInto_durationDepth (output : CWriteRef ctx (.option (.unsignedWord width)))
    (duration : Resource.Event kind → Nat) (path : (zeroInto output).Path) :
    (zeroInto output).depth duration path =
      duration (.classicalOperation (.wordBinary .equal width)) +
        duration (.classicalOperation (.nominalEncoding (.packOption width))) := rfl

/-- Exactly two actual native instructions execute, also at width zero. -/
theorem zeroInto_eventCount (output : CWriteRef ctx (.option (.unsignedWord width)))
    (path : (zeroInto output).Path) : ((zeroInto output).eventTrace path).length = 2 := rfl

/-- The original candidate word and inner tag are simultaneously live scratch cells. -/
def zeroScratchSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.ofShape .bit + SpacePool.ofShape (.unsignedWord width)

private def candidateCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh

private def tagCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (candidateCtx ctx width).addWorkspace (candidateCtx ctx width).canonicalFreshKey .bit
    (candidateCtx ctx width).canonicalFreshKey_fresh

private theorem zeroInto_visitedContexts (output : CWriteRef ctx (.option (.unsignedWord width)))
    (path : (zeroInto output).Path) :
    (zeroInto output).visitedContexts path =
      [ctx, candidateCtx ctx width, tagCtx ctx width, tagCtx ctx width,
        candidateCtx ctx width, ctx] := rfl

/-- Resident peak includes the exact two lexical cells and every original caller entry. -/
theorem zeroInto_resident (output : CWriteRef ctx (.option (.unsignedWord width)))
    (path : (zeroInto output).Path) :
    (zeroInto output).peakResidentSpace path = zeroScratchSpace kind width + ctx.residentSpace := by
  rw [Circuit.peakResidentSpace, zeroInto_visitedContexts]
  apply SpacePool.ext
  intro axis
  cases axis <;> simp (disch := omega) [Circuit.peak, candidateCtx, tagCtx, zeroScratchSpace,
    SpacePool.ofShape, SpacePool.max]
  omega

/-- Auxiliary peak uses the same actual candidate and tag lifetimes. -/
theorem zeroInto_auxiliary (output : CWriteRef ctx (.option (.unsignedWord width)))
    (path : (zeroInto output).Path) :
    (zeroInto output).peakAuxiliarySpace path =
      zeroScratchSpace kind width + ctx.auxiliarySpace := by
  rw [Circuit.peakAuxiliarySpace, zeroInto_visitedContexts]
  apply SpacePool.ext
  intro axis
  cases axis <;> simp (disch := omega) [Circuit.peak, candidateCtx, tagCtx, zeroScratchSpace,
    SpacePool.ofShape, SpacePool.max]
  omega

/-- The original optional output remains live beside the candidate word and inner tag. -/
def zeroRetainedSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.ofShape (.option (.unsignedWord width)) + zeroScratchSpace kind width

/-- Actual retention adds no native operation to the original two-instruction program. -/
theorem zeroRetained_eventTrace (ctx : RuntimeCtx kind) (width : Nat)
    (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (zeroRetained ctx width key fresh).Path) :
    (zeroRetained ctx width key fresh).eventTrace path = zeroEvents kind width := rfl

/-- The retained endpoint's exact pool comes from its actual equality and option pack. -/
theorem zeroRetained_resourcePool (ctx : RuntimeCtx kind) (width : Nat)
    (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (zeroRetained ctx width key fresh).Path) :
    (zeroRetained ctx width key fresh).resourcePool path =
      ResourcePool.ofList (zeroEvents kind width) := rfl

/-- Actual retained execution preserves both original serial duration charges. -/
theorem zeroRetained_durationDepth (ctx : RuntimeCtx kind) (width : Nat)
    (key : StorageKey) (fresh : key ∉ ctx.keys) (duration : Resource.Event kind → Nat)
    (path : (zeroRetained ctx width key fresh).Path) :
    (zeroRetained ctx width key fresh).depth duration path =
      duration (.classicalOperation (.wordBinary .equal width)) +
        duration (.classicalOperation (.nominalEncoding (.packOption width))) := by
  change 0 + (zeroInto (CWriteRef.retainedHead ctx key
    (.option (.unsignedWord width)) fresh)).depth duration path.2 = _
  rw [zero_add, zeroInto_durationDepth]

private theorem zeroRetained_visitedContexts (ctx : RuntimeCtx kind) (width : Nat)
    (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (zeroRetained ctx width key fresh).Path) :
    let retained := ctx.addRetained key (.option (.unsignedWord width)) fresh
    (zeroRetained ctx width key fresh).visitedContexts path =
      [ctx, retained, retained, candidateCtx retained width, tagCtx retained width,
        tagCtx retained width, candidateCtx retained width, retained] := rfl

/-- Exact resident peak includes the retained output and both original lexical cells. -/
theorem zeroRetained_resident (ctx : RuntimeCtx kind) (width : Nat)
    (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (zeroRetained ctx width key fresh).Path) :
    (zeroRetained ctx width key fresh).peakResidentSpace path =
      zeroRetainedSpace kind width + ctx.residentSpace := by
  rw [Circuit.peakResidentSpace, zeroRetained_visitedContexts]
  apply SpacePool.ext
  intro axis
  cases axis <;> simp (disch := omega) [Circuit.peak, candidateCtx, tagCtx,
    zeroRetainedSpace, zeroScratchSpace,
    SpacePool.ofShape, SpacePool.max]
  omega

/-- Exact auxiliary peak includes the same retained result and original lexical scopes. -/
theorem zeroRetained_auxiliary (ctx : RuntimeCtx kind) (width : Nat)
    (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (zeroRetained ctx width key fresh).Path) :
    (zeroRetained ctx width key fresh).peakAuxiliarySpace path =
      zeroRetainedSpace kind width + ctx.auxiliarySpace := by
  rw [Circuit.peakAuxiliarySpace, zeroRetained_visitedContexts]
  apply SpacePool.ext
  intro axis
  cases axis <;> simp (disch := omega) [Circuit.peak, candidateCtx, tagCtx,
    zeroRetainedSpace, zeroScratchSpace,
    SpacePool.ofShape, SpacePool.max]
  omega

/-- The actual retained result and two original work cells occupy exactly twice width plus two. -/
theorem zeroRetainedSpace_classicalBits (kind : ProblemKind) (width : Nat) :
    zeroRetainedSpace kind width .classicalBits = 2 * width + 2 := by
  simp [zeroRetainedSpace, zeroScratchSpace, SpacePool.ofShape, CShape.bitWidth]
  omega

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.Trivial.Native
