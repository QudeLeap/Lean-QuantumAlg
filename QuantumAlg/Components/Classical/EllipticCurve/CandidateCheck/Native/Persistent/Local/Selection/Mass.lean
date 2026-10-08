/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Local.Selection
import all QuantumAlg.Core.Execution.Circuit.Support

/-!
# Acceptance mass across local work beside persistent recovery cells

The existing accepted bit is retained by an actual local circuit. Its
subnormalized probability is identical before and after that circuit, while
all other classical cells, paths and references remain arbitrary.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind}

private theorem selected_mass {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (read : C → Bool) (flag : Bool) :
    (state.selectClassical read flag).mass =
      state.effectWeight (fun value => if read value = flag then
        Effect.one R else Effect.zero R) := by
  rw [ExecutionState.selectClassical_mass]
  unfold ExecutionState.effectWeight
  apply Finset.sum_congr rfl
  intro value _
  by_cases selected : read value = flag <;>
    simp only [selected, if_true, if_false, Effect.weight_one, Effect.weight_zero]

/-- A local circuit leaves the actual accepted or rejected mass unchanged. -/
theorem underPersistent_acceptance_mass
    (code : Circuit model ctx ctx) (supported : code.IsLocal) (width scalarWidth : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H))
    (flag : Bool) :
    ((underPersistent code supported width scalarWidth).execute Reference state).effectWeight
      (fun entry => if (entry.1.read
        (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = flag then
          Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
        else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference)) =
    state.effectWeight (fun entry => if (entry.1.read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = flag then
        Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
      else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference)) := by
  let read := fun entry : Store (persistentCtx ctx width scalarWidth) ×
      (model.HiddenState × H) =>
    (entry.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool
  have selected := underPersistent_acceptance_effectWeight code supported width
    scalarWidth state flag
    (fun _ => Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference))
  change _ = ((underPersistent code supported width scalarWidth).execute Reference
    (state.selectClassical read flag)).effectWeight (fun _ => Effect.one _) at selected
  calc
    _ = ((underPersistent code supported width scalarWidth).execute Reference
        (state.selectClassical read flag)).effectWeight (fun _ => Effect.one _) := selected
    _ = (state.selectClassical read flag).mass := by
      rw [ExecutionState.effectWeight_constant, Effect.weight_one,
        ExecutionState.quantumMarginal_mass, Circuit.execute_mass]
    _ = state.effectWeight (fun entry => if read entry = flag then
          Effect.one _ else Effect.zero _) := selected_mass state read flag

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
