/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Execution
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Execution
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Classical.Pushforward

/-!
# Complete state map of one actual retained recovery stage

The finite recovery body consumes the original borrowed base and measured
phase word, preserving the selected persistent service state and every
external reference block.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution
open ClassicalRoutines.OrderRecovery.Native

/-- The actual retained recovery stage maps each complete weighted block. -/
lemma recoveryStage_execute {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width) (t : Nat)
    (environment : (Sampling.Native.model t width).Environment) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (SourceNativeSampling.post t width) Reference
      ((Sampling.Native.Framed.model t width).HiddenState × History)) :
    (recoveryStage spec t).execute environment Reference state =
      state.mapClassical (fun entry =>
        ((recoveryStep spec t entry.1).1,
          (entry.2.1, (entry.2.2, (recoveryStep spec t entry.1).2)))) := by
  simp only [recoveryStage, Circuit.execute_seq, recoveryCode]
  rw [nativeRecovery_into_execute (model := Sampling.Native.Framed.model t width)
    (environment := environment)
    (⟨spec⟩ : ClassicalAlgorithms.OrderRecovery.Spec width t) (baseInput t width)
    (sampleInput t width) (resultRef t width)]
  simp only [Circuit.execute_retain, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint
