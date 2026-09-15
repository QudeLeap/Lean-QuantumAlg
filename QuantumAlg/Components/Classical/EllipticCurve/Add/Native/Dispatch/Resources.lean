/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native
import all QuantumAlg.Core.Execution.Trace

/-!
# Actual resource-path selection by complete addition dispatch

The original five stored predicates select one actual arm. Its native events,
dependency expression and complete visited contexts are exactly those of the
same actual dispatch path; branching introduces no detached accounting model.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Each real dispatch path retains one real arm's events, dependencies and visited contexts. -/
theorem dispatch_selectedTrace (classifier : Classifier ctx width)
    (arms : Case → Circuit ctx ctx) (path : (dispatch classifier arms).Path) :
    ∃ selected, ∃ armPath : (arms selected).Path,
      (dispatch classifier arms).eventTrace path = (arms selected).eventTrace armPath ∧
      (dispatch classifier arms).eventDepth path = (arms selected).eventDepth armPath ∧
      (dispatch classifier arms).visitedContexts path =
        (arms selected).visitedContexts armPath := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit flag =>
    cases flag
    · rcases path with ⟨value, path⟩
      cases value with
      | bit flag =>
        cases flag
        · rcases path with ⟨value, path⟩
          cases value with
          | bit flag =>
            cases flag
            · exact ⟨.generic, path, rfl, rfl, rfl⟩
            · rcases path with ⟨value, path⟩
              cases value with
              | bit flag =>
                cases flag
                · exact ⟨.vertical, path, rfl, rfl, rfl⟩
                · rcases path with ⟨value, path⟩
                  cases value with
                  | bit flag =>
                    cases flag
                    · exact ⟨.doubling, path, rfl, rfl, rfl⟩
                    · exact ⟨.vertical, path, rfl, rfl, rfl⟩
        · exact ⟨.rightInfinity, path, rfl, rfl, rfl⟩
    · exact ⟨.leftInfinity, path, rfl, rfl, rfl⟩

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
