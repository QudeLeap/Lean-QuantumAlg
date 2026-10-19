/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Layout
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Execution
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Actual complete store records through the first-success scan scope

Four literal pushes allocate the selector's actual cells. Its real ordered
scan runs on those stores and its four matching pops release only those
heads. Each original retained tuple and the surviving optional output are
read through the actual structural lifts, including arbitrary outer frames.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeFactorScan.Scope

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Enter the four genuine selector workspace heads in their real allocation order. -/
def enter (N : Nat) (store : Store ctx) : Store (context ctx N) :=
  let candidate := store.pushWorkspace ctx.canonicalFreshKey
    (.product .bit (.unsignedWord (modulusBits N))) ctx.canonicalFreshKey_fresh
  let accepted := candidate.pushWorkspace (candidateContext ctx N).canonicalFreshKey .bit
    (candidateContext ctx N).canonicalFreshKey_fresh
  let selected := accepted.pushWorkspace (acceptedContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (acceptedContext ctx N).canonicalFreshKey_fresh
  selected.pushWorkspace (selectedContext ctx N).canonicalFreshKey .bit
    (selectedContext ctx N).canonicalFreshKey_fresh

/-- Release precisely those four heads, exposing the actual original store entries. -/
def leave (N : Nat) (store : Store (context ctx N)) : Store ctx :=
  let selected := Store.popWorkspace (selectedContext ctx N).canonicalFreshKey .bit
    (selectedContext ctx N).canonicalFreshKey_fresh store
  let accepted := Store.popWorkspace (acceptedContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N)) (acceptedContext ctx N).canonicalFreshKey_fresh selected
  let candidate := Store.popWorkspace (candidateContext ctx N).canonicalFreshKey .bit
    (candidateContext ctx N).canonicalFreshKey_fresh accepted
  Store.popWorkspace ctx.canonicalFreshKey (.product .bit (.unsignedWord (modulusBits N)))
    ctx.canonicalFreshKey_fresh candidate

section Selected

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- The literal inner scan uses its already derived actual store and path update. -/
def bodyStep (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Store (context ctx N) → Store (context ctx N) × (body (model := model) source inputs
      result).Path :=
  NativeFactorScan.step (model := model) source (inputs.map liftInputs) (cells ctx N) (liftWrite
    result)

/-- Actual entry, the full scan and actual release retain the body's real path. -/
def step (source : Input N) (inputs : List (Inputs ctx N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (code (model := model) source inputs result).Path :=
  let selected := bodyStep (model := model) source inputs result (enter N store)
  (leave N selected.1, selected.2)

end Selected

/-- The four real allocations preserve every original structural input value. -/
lemma enter_read {shape : CShape} (input : CInputRef ctx shape) (store : Store ctx) :
    (enter N store).read (liftInput input) = store.read input := by
  simp only [enter, liftInput, Store.read_pushWorkspace_underWorkspace]

/-- The actual release reads each surviving original operand from the inner final store. -/
lemma leave_read {shape : CShape} (input : CInputRef ctx shape)
    (store : Store (context ctx N)) :
    (leave N store).read input = store.read (liftInput input) := by
  simp only [leave, liftInput, Store.read_popWorkspace_underWorkspace]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeFactorScan.Scope
