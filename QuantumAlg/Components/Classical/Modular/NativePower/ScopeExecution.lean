/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Modular.NativePower.BodyExecution
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Complete execution through the actual modular-power scopes

Three applications of the existing workspace execution law initialize and
release exactly the modulus, raw base and accumulator cells. The complete
body record keeps the original quantum-reference block and its actual path.
-/

namespace QuantumAlg.ClassicalRoutines.Modular.NativePower

open Execution ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width exponentWidth : Nat}

/-- Native modular power has the exact entered-body-exited store update on every full block. -/
theorem nativePower_into_execute (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (into (model := model) spec base exponent output).execute Reference state =
      state.mapClassical (fun entry =>
        ((intoStep (model := model) spec base exponent output entry.1).1,
          (entry.2.1, (entry.2.2,
            (intoStep (model := model) spec base exponent output entry.1).2)))) := by
  let inner := powerBody (model := model) spec base exponent output
  let innerUpdate := powerBodyStep (model := model) spec base exponent output
  let baseScope := Circuit.workspace (baseCtx ctx width) (baseCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (baseCtx ctx width).canonicalFreshKey_fresh inner
  let baseUpdate : Store (baseCtx ctx width) → Store (baseCtx ctx width) × baseScope.Path :=
    fun store =>
      let next := innerUpdate (store.pushWorkspace (baseCtx ctx width).canonicalFreshKey
        (.unsignedWord width) (baseCtx ctx width).canonicalFreshKey_fresh)
      (Store.popWorkspace (baseCtx ctx width).canonicalFreshKey (.unsignedWord width)
        (baseCtx ctx width).canonicalFreshKey_fresh next.1, next.2)
  let modulusScope := Circuit.workspace (modulusCtx ctx width)
    (modulusCtx ctx width).canonicalFreshKey (.unsignedWord width)
    (modulusCtx ctx width).canonicalFreshKey_fresh baseScope
  let modulusUpdate : Store (modulusCtx ctx width) →
      Store (modulusCtx ctx width) × modulusScope.Path := fun store =>
    let next := baseUpdate (store.pushWorkspace (modulusCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (modulusCtx ctx width).canonicalFreshKey_fresh)
    (Store.popWorkspace (modulusCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (modulusCtx ctx width).canonicalFreshKey_fresh next.1, next.2)
  refine (Circuit.execute_workspace_mapClassical ctx.canonicalFreshKey
    (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh modulusScope
    (fun entry => let next := modulusUpdate entry.1; ((next.1, entry.2), next.2))
    (fun reference {_} _ initial => ?_) Reference state).trans ?_
  · refine (Circuit.execute_workspace_mapClassical (modulusCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (modulusCtx ctx width).canonicalFreshKey_fresh baseScope
      (fun entry => let next := baseUpdate entry.1; ((next.1, entry.2), next.2))
      (fun reference' {_} _ initial' => ?_) reference initial).trans ?_
    · refine (Circuit.execute_workspace_mapClassical (baseCtx ctx width).canonicalFreshKey
        (.unsignedWord width) (baseCtx ctx width).canonicalFreshKey_fresh inner
        (fun entry => let next := innerUpdate entry.1; ((next.1, entry.2), next.2))
        (fun reference'' {_} _ initial'' => nativePower_body_execute spec base exponent output
          reference'' initial'') reference' initial').trans ?_
      congr 1
    · congr 1
  · congr 1

end

end QuantumAlg.ClassicalRoutines.Modular.NativePower
