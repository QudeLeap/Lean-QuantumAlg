/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Retained.Correctness
import all QuantumAlg.Core.Execution.Classical.Support

/-!
# Original GF(2) recovery as one complete actual run

The retained circuit is the sole program. Its output lists every caller cell
and quantum wire together with the actual optional result. The final state
and result distribution come from the same executed recovery and retain all
quantum-reference correlations, including correlations with the input rows.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

/-- Execute the original retained recovery and list every live final resource. -/
def run (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (key : StorageKey) (fresh : key ∉ ctx.keys) :
    AlgorithmRun ctx (retainedCtx ctx width key fresh) (.option (.unsignedWord width)) where
  code := retainedCircuit input key fresh
  output := Output.all (retainedCtx ctx width key fresh) (.read (retainedRead ctx width key fresh))

/-- The actual recovery result does not hide any caller entry or surviving quantum wire. -/
theorem gf2Run_output_listing (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (key : StorageKey) (fresh : key ∉ ctx.keys) :
    (run input key fresh).output.listing = (retainedCtx ctx width key fresh).keys := rfl

/-- Forgetting only path histories leaves the actual retained write and all old correlations. -/
theorem gf2Run_finalState (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (key : StorageKey) (fresh : key ∉ ctx.keys) (Reference : Register)
    (state : ExecutionState (Store ctx) (Register.prod ctx.register Reference)) :
    (run input key fresh).finalState Reference state =
      state.mapClassical (fun before =>
        (before.pushRetained key (.option (.unsignedWord width)) fresh).write
          (CWriteRef.retainedHead ctx key (.option (.unsignedWord width)) fresh)
          (gf2RecoveryValue (before.read input))) := by
  obtain ⟨record, executed, correct⟩ := gf2Retained_actualRecord_correct input key fresh
  change ((retainedCircuit input key fresh).execute Reference
    (state.mapClassical (fun before => (before, before)))).mapClassical Prod.fst = _
  rw [executed]
  erw [ExecutionState.executionState_mapClassical_comp,
    ExecutionState.executionState_mapClassical_comp]
  congr 1
  funext before
  exact correct before

/-- Reading the actual result groups the complete input state by its original recovery value. -/
theorem gf2Run_readoutState (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (key : StorageKey) (fresh : key ∉ ctx.keys) (Reference : Register)
    (state : ExecutionState (Store ctx) (Register.prod ctx.register Reference)) :
    ((run input key fresh).execute Reference state).mapClassical
      (run input key fresh).result =
      state.mapClassical (fun before => gf2RecoveryValue (before.read input)) := by
  change ((run input key fresh).execute Reference state).mapClassical
    (fun entry => (run input key fresh).output.eval entry.1) = _
  rw [← AlgorithmRun.finalState_readout, gf2Run_finalState]
  erw [ExecutionState.executionState_mapClassical_comp]
  congr 1

/-- The actual output PMF is the original recovery applied to the input's own block weights. -/
theorem gf2Run_outputDistribution
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (key : StorageKey) (fresh : key ∉ ctx.keys) {Reference : Register}
    (original : Execution.Input ctx Reference) :
    (run input key fresh).outputDistribution original =
      (original.state.toPMF original.normalized).map
        (fun before => gf2RecoveryValue (before.read input)) := by
  apply PMF.ext
  intro value
  have actual := congrArg (fun probability : PMF (CShape.Value (.option (.unsignedWord width))) =>
      probability value)
    (ExecutionState.toPMF_mapClassical
      ((run input key fresh).execute Reference original.state)
      ((run input key fresh).execute_normalized original) (run input key fresh).result)
  change (((run input key fresh).execute Reference original.state).toPMF
    ((run input key fresh).execute_normalized original)).map
      (run input key fresh).result value = _
  refine actual.symm.trans ?_
  rw [ExecutionState.toPMF_apply, gf2Run_readoutState]
  exact congrArg (fun probability : PMF (CShape.Value (.option (.unsignedWord width))) =>
    probability value) (ExecutionState.toPMF_mapClassical original.state original.normalized
      (fun before => gf2RecoveryValue (before.read input)))

end

end QuantumAlg.ClassicalRoutines.GF2.Native
