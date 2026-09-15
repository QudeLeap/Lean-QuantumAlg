/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.CheckedSelection.Semantics
import all
  QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation.Placement.Semantics
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# Complete actual single raw recovery

The original measured input passes through preparation, the shared checked
inverse and the selected candidate computation. All actual lexical workspaces
are released. One execution record proves both the complete quantum-reference
equation and the exact single caller-store write of the original optional
recovery result. The caller supplies no scratch initialization or separation.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual single recovery writes the original optional result and preserves the caller frame. -/
theorem singleIntoResult_actualRecord (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (result : CWriteRef ctx (OutputShape width)) :
    ∃ record : Store ctx → Store ctx × (singleIntoResult spec input result).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (singleIntoResult spec input result).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx, (record before).1 = before.write result
        (encodedRawOutput spec
          (RawRecovery.outputOf spec (preparationInput (before.read input)))) := by
  unfold singleIntoResult
  apply withPreparation_actualRecord_post spec input
    (fun refs transport => withCheckedSelection spec refs (transport.liftWrite result))
    (fun before after => after = before.write result
      (encodedRawOutput spec (RawRecovery.outputOf spec (preparationInput (before.read input)))))
  intro inner cells _distinct transport _separated
  obtain ⟨record, equation, correct⟩ := withCheckedSelection_actualRecord spec
    (preparationRefs cells) (transport.liftWrite result)
  refine ⟨record, equation, ?_⟩
  intro source prepared reads modulusValue leftValue rightValue
  let final := (record prepared).1
  let returned := transport.restrict final
  have returnedReads : transport.ReadsAs returned final :=
    transport.workspaceTransport_restrict_readsAs final
  have exactOutput := (correct prepared).2 (preparationInput (source.read input))
    modulusValue leftValue rightValue
  refine ⟨returned, ?_, returnedReads⟩
  apply Store.store_eq_write_of_read_frame source returned result
  · have resultRead : final.read (scaleRead (transport.liftWrite result)) =
        returned.read (scaleRead result) := by
      simpa only [scaleRead, transport.liftWrite_input] using returnedReads (scaleRead result)
    exact resultRead.symm.trans exactOutput
  · intro shape other resultFree
    have unchanged := (correct prepared).1 (transport.liftInput (.storage other))
      (by simpa only [transport.liftWrite_key, transport.liftInput_storageKeys,
        CInputRef.storageKeys, List.mem_singleton] using resultFree)
    exact (returnedReads (.storage other)).symm.trans
      (unchanged.trans (reads (.storage other)))

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
