/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.OwnedLayoutView
import all QuantumAlg.Core.Execution.Composition.Effect

/-!
# Observations through exact owned-layout grouping coordinates

These pullbacks use only the certified identical ordered physical wires and
unchanged classical cells. They describe the same complete interpreter state.
-/

namespace QuantumAlg.OwnedLayoutView

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {original viewed : RuntimeCtx .quantum}
  (view : OwnedLayoutView original viewed) (Reference : Register)

/-- Pull an observable through the exact view entry coordinates. -/
def splitEffectPullback {H : Type}
    (effects : Store viewed × H → Effect (viewed.register.prod Reference))
    (record : Store original × H) : Effect (original.register.prod Reference) :=
  Effect.compress (view.referenceBasis Reference) (view.referenceBasis Reference).injective
    (effects (view.record H record))

/-- Pull an observable through restoration of the original grouping. -/
def joinEffectPullback {H : Type}
    (effects : Store original × H → Effect (original.register.prod Reference))
    (record : Store viewed × H) : Effect (viewed.register.prod Reference) :=
  Effect.compress (view.referenceBasis Reference).symm
    (view.referenceBasis Reference).symm.injective (effects ((view.record H).symm record))

/-- Entering the scope preserves every complete observable weight. -/
lemma effectWeight_split {H : Type} [Fintype H] (state : State original Reference H)
    (effects : Store viewed × H → Effect (viewed.register.prod Reference)) :
    (view.split state).effectWeight effects =
      state.effectWeight (view.splitEffectPullback Reference effects) := by
  unfold split
  rw [ExecutionState.effectWeight_reindex, ExecutionState.effectWeight_mapClassical_decision]
  rfl

/-- Restoring the original grouping preserves every complete observable weight. -/
lemma effectWeight_join {H : Type} [Fintype H] (state : State viewed Reference H)
    (effects : Store original × H → Effect (original.register.prod Reference)) :
    (view.join state).effectWeight effects =
      state.effectWeight (view.joinEffectPullback Reference effects) := by
  unfold join
  rw [ExecutionState.effectWeight_reindex, ExecutionState.effectWeight_mapClassical_decision]
  rfl

end

end QuantumAlg.OwnedLayoutView
