/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Retained
import all QuantumAlg.Components.Classical.GF2.Native.State.Resources
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Actual resources of retained GF(2) recovery

The real retained output allocation preserves every native body event and
its duration. Resident and auxiliary allowances include the optional output,
all seven original workspaces, the active scratch allowance, and the complete
caller context. No repeated matrix or sample count multiplies live workspace.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

noncomputable section

variable (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
  (key : StorageKey) (fresh : key ∉ ctx.keys)

/-- Actual output retention preserves the complete original native event allowance. -/
theorem gf2Retained_pool_le (path : (retainedCircuit input key fresh).Path) :
    (retainedCircuit input key fresh).resourcePool path ≤ intoEnvelope kind rowCount width :=
  gf2WithState_pool_le (input.underRetained key (.option (.unsignedWord width)) fresh)
    (CWriteRef.retainedHead ctx key (.option (.unsignedWord width)) fresh) path.2

/-- Every arbitrary event duration is charged through the original retained invocation. -/
theorem gf2Retained_depth_le (duration : Resource.Event kind → Nat)
    (path : (retainedCircuit input key fresh).Path) :
    (retainedCircuit input key fresh).depth duration path ≤
      intoDepthLimit rowCount width duration := by
  change 0 + (withState (input.underRetained key (.option (.unsignedWord width)) fresh)
    (CWriteRef.retainedHead ctx key (.option (.unsignedWord width)) fresh)).depth
      duration path.2 ≤ _
  simpa only [Nat.zero_add] using
    gf2WithState_depth_le (input.underRetained key (.option (.unsignedWord width)) fresh)
    (CWriteRef.retainedHead ctx key (.option (.unsignedWord width)) fresh) duration path.2

/-- Actual retention and lexical scopes preserve the same-path serial event-duration equation. -/
theorem gf2Retained_duration_eventTrace (duration : Resource.Event kind → Nat)
    (path : (retainedCircuit input key fresh).Path) :
    (retainedCircuit input key fresh).depth duration path =
      (((retainedCircuit input key fresh).eventTrace path).map duration).sum := by
  have trace : (retainedCircuit input key fresh).eventTrace path =
      (withState (input.underRetained key (.option (.unsignedWord width)) fresh)
        (CWriteRef.retainedHead ctx key (.option (.unsignedWord width)) fresh)).eventTrace
          path.2 := rfl
  rw [trace]
  change 0 + (withState (input.underRetained key (.option (.unsignedWord width)) fresh)
    (CWriteRef.retainedHead ctx key (.option (.unsignedWord width)) fresh)).depth
      duration path.2 = _
  simpa only [Nat.zero_add] using
    gf2WithState_duration_eventTrace
      (input.underRetained key (.option (.unsignedWord width)) fresh)
      (CWriteRef.retainedHead ctx key (.option (.unsignedWord width)) fresh) duration path.2

/-- Every actual native instruction remains counted at the retained endpoint. -/
theorem gf2Retained_eventCount_le (path : (retainedCircuit input key fresh).Path) :
    ((retainedCircuit input key fresh).eventTrace path).length ≤
      intoDepthLimit (kind := kind) rowCount width (fun _ => 1) :=
  gf2WithState_eventCount_le (input.underRetained key (.option (.unsignedWord width)) fresh)
    (CWriteRef.retainedHead ctx key (.option (.unsignedWord width)) fresh) path.2

/-- Result, original workspaces and active scratch retain all resident roles. -/
theorem gf2Retained_resident_le (path : (retainedCircuit input key fresh).Path) :
    (retainedCircuit input key fresh).peakResidentSpace path ≤
      ((stateShapes rowCount width).map SpacePool.ofShape).sum +
        intoScratchSpace kind rowCount width +
          (SpacePool.ofShape (.option (.unsignedWord width)) + ctx.residentSpace) := by
  refine (Circuit.peakResidentSpace_seq
    (.retain ctx key (.option (.unsignedWord width)) fresh)
    (withState (input.underRetained key (.option (.unsignedWord width)) fresh)
    (CWriteRef.retainedHead ctx key (.option (.unsignedWord width)) fresh)) path).le.trans ?_
  refine SpacePool.max_le ?_ (gf2WithState_resident_le
    (input.underRetained key (.option (.unsignedWord width)) fresh)
    (CWriteRef.retainedHead ctx key (.option (.unsignedWord width)) fresh) path.2)
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  change visited ∈ [ctx, retainedCtx ctx width key fresh] at present
  rcases List.mem_cons.mp present with first | later
  · subst visited
    intro axis
    change ctx.residentSpace axis ≤
      (((stateShapes rowCount width).map SpacePool.ofShape).sum) axis +
        intoScratchSpace kind rowCount width axis +
          (SpacePool.ofShape (.option (.unsignedWord width)) axis + ctx.residentSpace axis)
    omega
  · have last := List.mem_singleton.mp later
    subst visited
    intro axis
    change SpacePool.ofShape (.option (.unsignedWord width)) axis + ctx.residentSpace axis ≤
      (((stateShapes rowCount width).map SpacePool.ofShape).sum) axis +
        intoScratchSpace kind rowCount width axis +
          (SpacePool.ofShape (.option (.unsignedWord width)) axis + ctx.residentSpace axis)
    omega

/-- Result, original workspaces and active scratch retain all auxiliary roles. -/
theorem gf2Retained_auxiliary_le (path : (retainedCircuit input key fresh).Path) :
    (retainedCircuit input key fresh).peakAuxiliarySpace path ≤
      ((stateShapes rowCount width).map SpacePool.ofShape).sum +
        intoScratchSpace kind rowCount width +
          (SpacePool.ofShape (.option (.unsignedWord width)) + ctx.auxiliarySpace) := by
  refine (Circuit.peakAuxiliarySpace_seq
    (.retain ctx key (.option (.unsignedWord width)) fresh)
    (withState (input.underRetained key (.option (.unsignedWord width)) fresh)
    (CWriteRef.retainedHead ctx key (.option (.unsignedWord width)) fresh)) path).le.trans ?_
  refine SpacePool.max_le ?_ (gf2WithState_auxiliary_le
    (input.underRetained key (.option (.unsignedWord width)) fresh)
    (CWriteRef.retainedHead ctx key (.option (.unsignedWord width)) fresh) path.2)
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  change visited ∈ [ctx, retainedCtx ctx width key fresh] at present
  rcases List.mem_cons.mp present with first | later
  · subst visited
    intro axis
    change ctx.auxiliarySpace axis ≤
      (((stateShapes rowCount width).map SpacePool.ofShape).sum) axis +
        intoScratchSpace kind rowCount width axis +
          (SpacePool.ofShape (.option (.unsignedWord width)) axis + ctx.auxiliarySpace axis)
    omega
  · have last := List.mem_singleton.mp later
    subst visited
    intro axis
    change SpacePool.ofShape (.option (.unsignedWord width)) axis + ctx.auxiliarySpace axis ≤
      (((stateShapes rowCount width).map SpacePool.ofShape).sum) axis +
        intoScratchSpace kind rowCount width axis +
          (SpacePool.ofShape (.option (.unsignedWord width)) axis + ctx.auxiliarySpace axis)
    omega

end

end QuantumAlg.ClassicalRoutines.GF2.Native
