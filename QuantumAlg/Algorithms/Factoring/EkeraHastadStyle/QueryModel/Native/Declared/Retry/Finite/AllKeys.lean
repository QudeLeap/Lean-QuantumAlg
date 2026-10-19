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
def problem (input : Input N) (count : Nat) :
    Problem (model N) base (context base noQuantum N count)
      (LatticeBatchRecoveryOutput.OutputShape N) where
  Witness := Unit
  valid := fun environment _ _ => environment = sourceEnvironment input
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ output => output ∈ accepts N
  successLB := fun _ _ => ⟨1 - sourceFailure input ^ count, tsub_le_self⟩
  states := fun _ _ => [Cleanup.stateRequirement base noQuantum N count]
  resources :=
    { events := Cleanup.eventBudget N count
      resident := additionalSpace N count + base.residentSpace
      auxiliary := additionalSpace N count + base.auxiliarySpace }
  quantumTimeLimit := Cleanup.durationBudget N Resource.Event.quantumDuration count

/-- Every original source input admits every normalized caller and external-reference extension. -/
lemma declaredFiniteAllKeys_admits (input : Input N) (count : Nat) {Reference : Register}
    (original : OracleInput (model N).classicalOracles base Reference) :
    (problem base noQuantum input count).Admits (sourceEnvironment input) () original :=
  ⟨rfl, trivial⟩

end

end AllKeys
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
