/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Inputs
import all QuantumAlg.Components.Classical.FirstAccepted.StoreSemantics
import all QuantumAlg.Components.Classical.FirstAccepted.Preservation
import all QuantumAlg.Components.Classical.FirstAccepted.Resources

/-!
# Actual early-factor selection after the quantum batch

The stored sampler flag controls the existing two-copy selector. Both flag
and factor are read from the same retained parameter that selected the real
quantum members. This operation preserves an already accepted factor and
requires no fresh allocation or reinitialization. Its internal separation
facts will be supplied by the actual recovery workspace layout.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery

open Execution

open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The early-factor candidate is the actual pair of parameter projections. -/
def earlyInputs (inputs : Inputs ctx N) : FirstAccepted.Inputs ctx (modulusBits N) where
  eligible := earlyFlag inputs
  candidate := earlyWord inputs

/-- Copy the stored early factor only when its flag is true and the latch is still clear. -/
def earlyCircuit (inputs : Inputs ctx N) (refs : FirstAccepted.Refs ctx (modulusBits N)) :
    Circuit ctx ctx :=
  FirstAccepted.circuit (earlyInputs inputs) refs

/-- The real selector update and its exact branch path. -/
noncomputable def earlyStep (inputs : Inputs ctx N) (refs : FirstAccepted.Refs ctx (modulusBits N))
    (store : Store ctx) : Store ctx × (earlyCircuit inputs refs).Path :=
  FirstAccepted.step (earlyInputs inputs) refs store

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The whole mixed state follows the actual selector store map on every reference. -/
theorem nativeRecovery_early_execute (inputs : Inputs ctx N)
    (refs : FirstAccepted.Refs ctx (modulusBits N)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (earlyCircuit inputs refs).execute Reference state =
      state.mapClassical (fun entry =>
        ((earlyStep inputs refs entry.1).1, (entry.2, (earlyStep inputs refs entry.1).2))) :=
  FirstAccepted.firstAccepted_execute (earlyInputs inputs) refs Reference state

/-- The actual parameter flag and payload determine the persistent first-factor latches. -/
theorem nativeRecovery_early_latches (inputs : Inputs ctx N)
    (refs : FirstAccepted.Refs ctx (modulusBits N))
    (separated : FirstAccepted.Separated (earlyInputs inputs) refs) (store : Store ctx) :
    let final := (earlyStep inputs refs store).1
    (final.read (FirstAccepted.cellRead refs.accepted)).toBool =
        ((store.read (FirstAccepted.cellRead refs.accepted)).toBool ||
          (store.read inputs.parameter).second.first.toBool) ∧
      final.read (FirstAccepted.cellRead refs.selected) =
        if (!(store.read (FirstAccepted.cellRead refs.accepted)).toBool) &&
            (store.read inputs.parameter).second.first.toBool then
          (store.read inputs.parameter).second.second
        else store.read (FirstAccepted.cellRead refs.selected) :=
  FirstAccepted.firstAccepted_latches (earlyInputs inputs) refs separated store

/-- Intrinsic writable references preserve the complete borrowed joint state without assumptions. -/
theorem nativeRecovery_early_borrowedRestored (inputs : Inputs ctx N)
    (refs : FirstAccepted.Refs ctx (modulusBits N)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (earlyCircuit inputs refs).BorrowedRestored Reference state
      ((earlyCircuit inputs refs).execute Reference state) :=
  FirstAccepted.firstAccepted_borrowedRestored (earlyInputs inputs) refs Reference state

/-- All native coordinates are charged to the independent existing four-operation allowance. -/
theorem nativeRecovery_early_pool_le (inputs : Inputs ctx N)
    (refs : FirstAccepted.Refs ctx (modulusBits N)) (path : (earlyCircuit inputs refs).Path) :
    (earlyCircuit inputs refs).resourcePool path ≤
      FirstAccepted.nativeEnvelope kind (modulusBits N) :=
  FirstAccepted.firstAccepted_pool_le (earlyInputs inputs) refs path

/-- The actual branch has two or four unit-duration classical operations. -/
theorem nativeRecovery_early_depth (inputs : Inputs ctx N)
    (refs : FirstAccepted.Refs ctx (modulusBits N)) (path : (earlyCircuit inputs refs).Path) :
    (earlyCircuit inputs refs).depth (fun _ => 1) path =
      if path.2.1.toBool then 4 else 2 :=
  FirstAccepted.firstAccepted_unit_depth (earlyInputs inputs) refs path

/-- Early selection uses only the genuinely existing bank and classical cells. -/
theorem nativeRecovery_early_resident_le (inputs : Inputs ctx N)
    (refs : FirstAccepted.Refs ctx (modulusBits N)) (path : (earlyCircuit inputs refs).Path) :
    (earlyCircuit inputs refs).peakResidentSpace path ≤ ctx.residentSpace :=
  FirstAccepted.firstAccepted_resident_le (earlyInputs inputs) refs path

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery
