/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Decode
import all QuantumAlg.Components.Classical.TerminalDecode.Resources
import all QuantumAlg.Core.Execution.Trace.Boundary

/-!
# Actual resources of measured-value decoding

Every path contains one packing event followed by the native decoder's real
shift and selected increment events. Its exact peak includes the fresh packed
bit cell while the lexical body executes; that cell is released on return.
All widths, including zero, use the same actual instruction accounting.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {count : Nat}

/-- Native event of the literal finite-binary packing instruction. -/
def measuredPackEvent (count : Nat) : Resource.Event model :=
  .classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.nominalEncoding (.packFiniteBits count)))

/-- Independent coordinatewise allowance for the pack and complete decoder. -/
def measuredDecodeEnvelope (count : Nat) : ResourcePool model :=
  ResourcePool.singleton (measuredPackEvent (model := model) count) +
    TerminalDecode.envelope (model := model) count

/-- Actual chronological trace begins with its one charged packing operation. -/
theorem measuredDecodeInto_eventTrace
    (input : CInputRef ctx (.fixedVector count (.finite 2)))
    (decoded : CWriteRef ctx (.unsignedWord count))
    (path : (measuredDecodeInto (model := model) input decoded).Path) :
    (measuredDecodeInto (model := model) input decoded).eventTrace path =
      measuredPackEvent (model := model) count ::
        (TerminalDecode.into (model := model) .bigEndian (packedInput ctx count)
          (writeUnderDecode decoded count)).eventTrace path.2 := by
  change (BitWord.instruction (execution := model) (measuredPackOp input)).eventTrace path.1 ++
    (TerminalDecode.into (model := model) .bigEndian (packedInput ctx count)
      (writeUnderDecode decoded count)).eventTrace path.2 = _
  rw [BitWord.bitWord_instruction_eventTrace]
  rfl

/-- The native budget charges the same literal packing and decoder instructions. -/
theorem measuredDecodeInto_resourcePool_le
    (input : CInputRef ctx (.fixedVector count (.finite 2)))
    (decoded : CWriteRef ctx (.unsignedWord count))
    (path : (measuredDecodeInto (model := model) input decoded).Path) :
    (measuredDecodeInto (model := model) input decoded).resourcePool path ≤
      measuredDecodeEnvelope (model := model) count := by
  change ResourcePool.ofList
    ((measuredDecodeInto (model := model) input decoded).eventTrace path) ≤ _
  rw [measuredDecodeInto_eventTrace, ResourcePool.ofList_cons]
  exact add_le_add le_rfl (TerminalDecode.terminalDecode_intoFromBitRefs_pool_le .bigEndian
    (fun index => CInputRef.bitsGet (packedInput ctx count) index)
    (writeUnderDecode decoded count) path.2)

/-- Packing precedes every actual serial shift and selected increment. -/
theorem measuredDecodeInto_depth_le
    (input : CInputRef ctx (.fixedVector count (.finite 2)))
    (decoded : CWriteRef ctx (.unsignedWord count))
    (duration : Resource.Event model → Nat)
    (path : (measuredDecodeInto (model := model) input decoded).Path) :
    (measuredDecodeInto (model := model) input decoded).depth duration path ≤
      duration (measuredPackEvent (model := model) count) + count *
        (duration (TerminalDecode.shiftEvent (model := model) count) +
          duration (TerminalDecode.incrementEvent (model := model) count)) := by
  change (BitWord.instruction (execution := model) (measuredPackOp input)).depth duration path.1 +
    (TerminalDecode.into (model := model) .bigEndian (packedInput ctx count)
      (writeUnderDecode decoded count)).depth duration path.2 ≤ _
  rw [BitWord.bitWord_instruction_depth]
  exact Nat.add_le_add_left (TerminalDecode.terminalDecode_intoFromBitRefs_depth_le .bigEndian
    (fun index => CInputRef.bitsGet (packedInput ctx count) index)
    (writeUnderDecode decoded count) duration path.2) _

private theorem measuredDecodeBody_resident
    (input : CInputRef ctx (.fixedVector count (.finite 2)))
    (decoded : CWriteRef ctx (.unsignedWord count))
    (path : (measuredDecodeBody (model := model) input decoded).Path) :
    (measuredDecodeBody (model := model) input decoded).peakResidentSpace path =
      (decodeCtx ctx count).residentSpace := by
  have decoder := le_antisymm
    (TerminalDecode.terminalDecode_intoFromBitRefs_resident_le .bigEndian
      (fun index => CInputRef.bitsGet (packedInput ctx count) index)
      (writeUnderDecode decoded count) path.2)
    ((TerminalDecode.into (model := model) .bigEndian (packedInput ctx count)
      (writeUnderDecode decoded count)).input_residentSpace_le_peak path.2)
  exact (Circuit.peakResidentSpace_seq
    (BitWord.instruction (execution := model) (measuredPackOp input))
    (TerminalDecode.into (model := model) .bigEndian (packedInput ctx count)
      (writeUnderDecode decoded count)) path).trans
    ((congrArg₂ SpacePool.max
      (Circuit.peakResidentSpace_classical
        (BitWord.selectedApplication (execution := model) (measuredPackOp input)) path.1)
      decoder).trans
        (SpacePool.max_eq_right le_rfl))

private theorem measuredDecodeBody_auxiliary
    (input : CInputRef ctx (.fixedVector count (.finite 2)))
    (decoded : CWriteRef ctx (.unsignedWord count))
    (path : (measuredDecodeBody (model := model) input decoded).Path) :
    (measuredDecodeBody (model := model) input decoded).peakAuxiliarySpace path =
      (decodeCtx ctx count).auxiliarySpace := by
  have decoder := le_antisymm
    (TerminalDecode.terminalDecode_intoFromBitRefs_auxiliary_le .bigEndian
      (fun index => CInputRef.bitsGet (packedInput ctx count) index)
      (writeUnderDecode decoded count) path.2)
    ((TerminalDecode.into (model := model) .bigEndian (packedInput ctx count)
      (writeUnderDecode decoded count)).input_auxiliarySpace_le_peak path.2)
  exact (Circuit.peakAuxiliarySpace_seq
    (BitWord.instruction (execution := model) (measuredPackOp input))
    (TerminalDecode.into (model := model) .bigEndian (packedInput ctx count)
      (writeUnderDecode decoded count)) path).trans
    ((congrArg₂ SpacePool.max
      (Circuit.peakAuxiliarySpace_classical
        (BitWord.selectedApplication (execution := model) (measuredPackOp input)) path.1)
      decoder).trans
        (SpacePool.max_eq_right le_rfl))

/-- Exact resident peak adds the one real packed bit cell to all existing storage. -/
theorem measuredDecodeInto_resident
    (input : CInputRef ctx (.fixedVector count (.finite 2)))
    (decoded : CWriteRef ctx (.unsignedWord count))
    (path : (measuredDecodeInto (model := model) input decoded).Path) :
    (measuredDecodeInto (model := model) input decoded).peakResidentSpace path =
      SpacePool.ofShape (.bits count) + ctx.residentSpace := by
  have body := measuredDecodeBody_resident (model := model) input decoded path
  exact (Circuit.peakResidentSpace_workspace ctx.canonicalFreshKey (.bits count)
    ctx.canonicalFreshKey_fresh (measuredDecodeBody (model := model) input decoded) path).trans
    ((congrArg (SpacePool.max ctx.residentSpace) body).trans
      (SpacePool.max_eq_right (fun axis => Nat.le_add_left _ _)))

/-- Exact auxiliary peak charges that same lexical cell, which is absent on return. -/
theorem measuredDecodeInto_auxiliary
    (input : CInputRef ctx (.fixedVector count (.finite 2)))
    (decoded : CWriteRef ctx (.unsignedWord count))
    (path : (measuredDecodeInto (model := model) input decoded).Path) :
    (measuredDecodeInto (model := model) input decoded).peakAuxiliarySpace path =
      SpacePool.ofShape (.bits count) + ctx.auxiliarySpace := by
  have body := measuredDecodeBody_auxiliary (model := model) input decoded path
  exact (Circuit.peakAuxiliarySpace_workspace ctx.canonicalFreshKey (.bits count)
    ctx.canonicalFreshKey_fresh (measuredDecodeBody (model := model) input decoded) path).trans
    ((congrArg (SpacePool.max ctx.auxiliarySpace) body).trans
      (SpacePool.max_eq_right (fun axis => Nat.le_add_left _ _)))

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
