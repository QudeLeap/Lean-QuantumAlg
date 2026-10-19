/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Actual live input and output boundaries contribute to peak space

Every selected execution path visits its typed input and output contexts.
Their actual resident and auxiliary storage therefore contribute to that
same path's measured peak, including empty loops and lexical workspaces.
-/

namespace QuantumAlg.Circuit

variable {allowAllocation : Bool}

variable {model : ExecutionModel} {pre post : RuntimeCtx model.kind}

/-- Every actual path visits its complete original live context. -/
lemma input_mem_visitedContexts (code : Circuit model pre post allowAllocation) (path : code.Path)
    :
    pre ∈ code.visitedContexts path := by
  induction code with
  | id | classical | classicalQuery | unitary | measureZ | retain | prepareZero =>
      exact List.mem_cons_self
  | seq first second firstIH _ =>
      exact List.mem_append_left _ (firstIH path.1)
  | branch input body bodyIH =>
      exact bodyIH path.1 path.2
  | iterate => exact List.mem_cons_self
  | workspace | embed | parallelClassical | parallelQuantum => exact List.mem_cons_self

/-- Every actual path visits its complete final live context. -/
lemma output_mem_visitedContexts (code : Circuit model pre post allowAllocation) (path :
    code.Path) :
    post ∈ code.visitedContexts path := by
  induction code with
  | id | classical | classicalQuery | unitary | measureZ =>
      exact List.mem_cons_self
  | retain | prepareZero => exact List.mem_cons_of_mem _ List.mem_cons_self
  | seq first second _ secondIH =>
      exact List.mem_append_right _ (secondIH path.2)
  | branch input body bodyIH =>
      exact bodyIH path.1 path.2
  | iterate => exact List.mem_cons_self
  | workspace | embed | parallelClassical | parallelQuantum => exact List.mem_cons_self

/-- The real supplied input storage is bounded by the same actual resident peak. -/
lemma input_residentSpace_le_peak (code : Circuit model pre post allowAllocation) (path :
    code.Path) :
    pre.residentSpace ≤ code.peakResidentSpace path :=
  code.residentSpace_le_peak_of_visited path pre (code.input_mem_visitedContexts path)

/-- The real supplied input roles are bounded by the same actual auxiliary peak. -/
lemma input_auxiliarySpace_le_peak (code : Circuit model pre post allowAllocation) (path :
    code.Path) :
    pre.auxiliarySpace ≤ code.peakAuxiliarySpace path :=
  code.auxiliarySpace_le_peak_of_visited path pre (code.input_mem_visitedContexts path)

/-- The real retained output storage contributes to the same actual resident peak. -/
lemma output_residentSpace_le_peak (code : Circuit model pre post allowAllocation) (path :
    code.Path) :
    post.residentSpace ≤ code.peakResidentSpace path :=
  code.residentSpace_le_peak_of_visited path post (code.output_mem_visitedContexts path)

/-- The real retained output roles contribute to the same actual auxiliary peak. -/
lemma output_auxiliarySpace_le_peak (code : Circuit model pre post allowAllocation) (path :
    code.Path) :
    post.auxiliarySpace ≤ code.peakAuxiliarySpace path :=
  code.auxiliarySpace_le_peak_of_visited path post (code.output_mem_visitedContexts path)

end QuantumAlg.Circuit
