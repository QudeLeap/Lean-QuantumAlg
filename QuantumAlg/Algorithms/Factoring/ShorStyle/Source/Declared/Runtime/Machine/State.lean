/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Readout
import all QuantumAlg.Core.Execution.SelectionAll.Reference
import all QuantumAlg.Core.Execution.State.Requirement

/-!
# Independent full bank and original reference promise of the initialized machine

The target is the predetermined zero bank tensor the original caller's
complete reference state. It is chosen independently of every observed
factor and real execution history. Every actual optional output fiber,
including zero-mass fibers, satisfies this same full joint promise.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine

open Execution

noncomputable section

/-- The full independently chosen physical zero bank and original external reference. -/
def stateTarget (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (N count : Nat) {Reference : Register} (input : Execution.Input base Reference) :
    DensityOperator ((context base noQuantum N count).register.prod Reference) :=
  BasisReference.target (R := (context base noQuantum N count).register)
    (context base noQuantum N count).quantumLayout.zeroLabel
    input.state.referenceMarginal

/-- The original reference and actual full bank seed form a normalized target. -/
lemma stateTarget_normalized (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N count : Nat) {Reference : Register}
    (input : Execution.Input base Reference) :
    (stateTarget base noQuantum N count input).IsNormalized :=
  BasisReference.target_normalized (R := (context base noQuantum N count).register)
    (context base noQuantum N count).quantumLayout.zeroLabel
    input.state.referenceMarginal
    ((ExecutionState.referenceMarginal_mass input.state).trans input.normalized)

/-- The independently chosen requirement observes every bank wire jointly with the reference. -/
def stateRequirement (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (N count : Nat) : StateRequirement base (context base noQuantum N count) :=
  .jointReference Finset.univ (.read (.storage (result base noQuantum N count).toCStorageRef))
    (fun Reference input _ => .mixed
      (DensityOperator.observeSelectionWithReference (context base noQuantum N count).quantumLayout
        Finset.univ Reference (stateTarget base noQuantum N count input))
      ((DensityOperator.observeSelectionWithReference_mass
        (context base noQuantum N count).quantumLayout Finset.univ Reference
        (stateTarget base noQuantum N count input)).trans
          (stateTarget_normalized base noQuantum N count input)))

/-- The same actual complete machine meets the full predetermined joint output requirement. -/
lemma stateRequirement_holds (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N : Nat) (input : Input N) (count : Nat)
    {Reference : Register}
    (original : OracleInput (executionModel N).classicalOracles base Reference) :
    (stateRequirement base noQuantum N count).Holds original.caller
      ((run base noQuantum N input count).finalState (environment input) Reference
        original.state) :=
  fun value => StatePromise.mixed_fullSelection (context base noQuantum N count).quantumLayout
    Reference (stateTarget base noQuantum N count original.caller)
    (stateTarget_normalized base noQuantum N count original.caller) _
    (output_state base noQuantum N input count original value)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine
