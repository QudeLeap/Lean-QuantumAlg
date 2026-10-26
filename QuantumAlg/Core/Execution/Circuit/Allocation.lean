/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Circuit
public import QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Trace.Boundary

/-!
# Complete live context of an allocation-free execution

The allocation index rules out every instruction that introduces runtime
storage. Consequently each visited context is the original context, including
nested calls and explicit parallel children. Space is therefore the actual
complete caller context; it is not reconstructed from a child's event count.
-/

namespace QuantumAlg.Circuit

private lemma endpoints_of_fixed {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {allowAllocation : Bool}
    (code : Circuit model pre post allowAllocation) (fixed : allowAllocation = false) :
    pre = post := by
  induction code with
  | id | classical | classicalQuery | unitary | measureZ | iterate
  | embed | ownedLayoutView | parallelClassical | parallelQuantum => rfl
  | retain | prepareZero | workspace => cases fixed
  | seq first second firstIH secondIH => exact (firstIH fixed).trans (secondIH fixed)
  | branch input body bodyIH => exact bodyIH (CShape.initialValue _) fixed

/-- The false allocation index enforces exactly identical input and output contexts. -/
public lemma fixed_endpoints {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post false) : pre = post :=
  endpoints_of_fixed code rfl

private lemma visited_of_fixed {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {allowAllocation : Bool}
    (code : Circuit model pre post allowAllocation) (fixed : allowAllocation = false)
    (path : code.Path) (visited : RuntimeCtx model.kind)
    (present : visited ∈ code.visitedContexts path) : visited = pre := by
  induction code with
  | id | classical | classicalQuery | unitary | measureZ
  | embed | ownedLayoutView | parallelClassical | parallelQuantum =>
      exact List.mem_singleton.mp present
  | retain | prepareZero | workspace => cases fixed
  | seq first second firstIH secondIH =>
      rcases List.mem_append.mp present with before | after
      · exact firstIH fixed path.1 visited before
      · exact (secondIH fixed path.2 visited after).trans (endpoints_of_fixed first fixed).symm
  | branch input body bodyIH => exact bodyIH path.1 fixed path.2 visited present
  | iterate count body bodyIH =>
      rcases List.mem_cons.mp present with same | later
      · exact same
      · obtain ⟨part, inParts, inPart⟩ := List.mem_flatten.mp later
        obtain ⟨index, rfl⟩ := List.mem_ofFn.mp inParts
        exact bodyIH fixed (path index) visited inPart

/-- No supported or unsupported path of a fixed child introduces hidden resident storage. -/
public lemma fixed_visitedContexts {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post false) (path : code.Path) (visited : RuntimeCtx model.kind)
    (present : visited ∈ code.visitedContexts path) : visited = pre :=
  visited_of_fixed code rfl path visited present

/-- The resident peak of a fixed child is exactly its full physical input storage. -/
public lemma fixed_peakResidentSpace {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post false) (path : code.Path) :
    code.peakResidentSpace path = pre.residentSpace := by
  apply le_antisymm
  · exact code.peakResidentSpace_le_of_visited path _ fun visited present =>
      (congrArg RuntimeCtx.residentSpace (code.fixed_visitedContexts path visited present)).le
  · exact code.input_residentSpace_le_peak path

/-- Auxiliary roles are charged on that same complete fixed context. -/
public lemma fixed_peakAuxiliarySpace {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post false) (path : code.Path) :
    code.peakAuxiliarySpace path = pre.auxiliarySpace := by
  apply le_antisymm
  · exact code.peakAuxiliarySpace_le_of_visited path _ fun visited present =>
      (congrArg RuntimeCtx.auxiliarySpace (code.fixed_visitedContexts path visited present)).le
  · exact code.input_auxiliarySpace_le_peak path

end QuantumAlg.Circuit
