/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Specification
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Source

/-!
# Exact source failure law for every original declared EH input

The independent one-batch source distribution fixes its own failure mass. The
same actual finite execution performs every requested batch, complete recovery,
first-success selection and terminal physical bank cleanup. A populated output
is accepted only when it is a checked nontrivial divisor of the original
modulus. No good-key condition is needed for the exact finite law; the stronger
good-key numerical floor remains a separate theorem.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace AllKeys

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {N : Nat}

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

/-- Shared all-input acceptance, full state and storage specification.
The zero and first completed branches use this budget directly; repeated
completed contracts replace its event and duration allowances with the
actual per-batch pack and reset budgets. -/
def problem (input : Input N) (count : Nat)
    (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Problem (model input) base (context base noQuantum N count)
      (LatticeBatchRecoveryOutput.OutputShape N) where
  valid := fun _ => True
  initialization := fun _ => True
  accepts := fun _ output => output ∈ accepts N
  successLB := ⟨1 - sourceFailure input ^ count, tsub_le_self⟩
  states := [Cleanup.stateRequirement base noQuantum N count]
  resources :=
    { events := Cleanup.eventBudget input count
      resident := additionalSpace N count + base.residentSpace
      auxiliary := additionalSpace N count + base.auxiliarySpace }
  depth :=
    { duration := duration
      limit := Cleanup.durationBudget input duration count
      classicalQuery_unit := fun coordinate => nomatch coordinate
      quantumQuery_unit := unitQueries }

end

end AllKeys
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
