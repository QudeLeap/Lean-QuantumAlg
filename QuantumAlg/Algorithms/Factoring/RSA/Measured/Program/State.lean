/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Probability.Output
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Seed
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.State
import all QuantumAlg.Core.Execution.State.Readout
import all QuantumAlg.Core.Execution.State.Requirement
import all QuantumAlg.Core.Execution.SelectionAll.Reference

/-!
# Complete output-conditioned physical seed and external Reference state

The actual complete measured program ends in its physical reload seed.
Its proved full-reference output law fixes each real optional-output block,
including zero-mass blocks, jointly with the entire original Reference.
The independent target does not depend on an execution or its probability
[EH17, source.tex:878-966; G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.Factoring.RSA.Measured.Program

noncomputable section

variable [configuration : Configuration]
variable {environment : MeasuredRSAModel.Environment}

open Execution EkeraHastadStyle.Canonical

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- Every positive optional output has the independent full physical seed/Reference target. -/
private def positiveStateRequirement (laterCount : Nat) :
    StateRequirement base (readyContext base noQuantum N (laterCount + 1)) :=
  .jointReference Finset.univ
    (.read (.storage (bankWrite base noQuantum N (laterCount + 1)
      (Recycling.ClassicalFrame.selectedRef base N (laterCount + 1))).toCStorageRef))
    (fun Reference input _ => .mixed
      (DensityOperator.observeSelectionWithReference
        (readyContext base noQuantum N (laterCount + 1)).quantumLayout Finset.univ Reference
        (BasisReference.target (memberSeed base noQuantum N (laterCount + 1))
          input.state.referenceMarginal))
      ((DensityOperator.observeSelectionWithReference_mass
        (readyContext base noQuantum N (laterCount + 1)).quantumLayout Finset.univ Reference
        (BasisReference.target (memberSeed base noQuantum N (laterCount + 1))
          input.state.referenceMarginal)).trans
        (BasisReference.target_normalized (memberSeed base noQuantum N (laterCount + 1))
          input.state.referenceMarginal
          ((ExecutionState.referenceMarginal_mass input.state).trans input.normalized))))

/-- Zero batches preserve the original joint state; positive batches restore the whole bank. -/
def stateRequirement : (count : Nat) → StateRequirement base (outputContext base noQuantum N count)
  | 0 => NativeFiniteRetry.zeroStateRequirement base N
  | laterCount + 1 => positiveStateRequirement base noQuantum N laterCount

/-- Actual stored output blocks retain the whole original Reference beside the physical seed. -/
lemma rsaMeasuredParent_positive_output_statePromise (specification : Input N) (laterCount : Nat)
    {Reference : Register} (input : OracleInput .empty base Reference)
    (value : (LatticeBatchRecoveryOutput.OutputShape N).Value) :
    (StatePromise.mixed
      (BasisReference.target (memberSeed base noQuantum N (laterCount + 1))
        input.caller.state.referenceMarginal)
      (BasisReference.target_normalized (memberSeed base noQuantum N (laterCount + 1))
        input.caller.state.referenceMarginal
        ((ExecutionState.referenceMarginal_mass input.caller.state).trans
          input.caller.normalized))).Holds
      ((((positiveRun base noQuantum N specification laterCount).finalState environment
        Reference input.state).mapClassical
          (positiveRun base noQuantum N specification laterCount).output.eval).block value) := by
  let program := positiveRun base noQuantum N specification laterCount
  let seed := memberSeed base noQuantum N (laterCount + 1)
  let distribution := Probability.outputDistribution specification (laterCount + 1)
  apply AlgorithmRun.basisReference_readout_of_entries program environment input seed value
    (distribution value).toReal
  intro left right leftRef rightRef
  exact BasisSeeded.readout_entry_of_reference input.state
    (program.execute environment Reference input.state) seed
    (rsaMeasuredParent_positiveCode_seeded (environment := environment) base noQuantum N
      specification laterCount
      (input.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))))
    program.output.eval distribution
    (fun weight first second =>
      Probability.rsaMeasuredProbability_positiveRun_output_reference base noQuantum N
        specification laterCount environment input.state weight first second)
    value left right leftRef rightRef

/-- The complete actual run satisfies the independent joint state requirement at every count. -/
lemma rsaMeasuredParent_stateRequirement_holds (specification : Input N) (count : Nat)
    {Reference : Register} (input : OracleInput .empty base Reference) :
    (stateRequirement base noQuantum N count).Holds input.caller
      ((run base noQuantum N specification count).finalState environment Reference
        input.state) := by
  cases count with
  | zero => exact NativeFiniteRetry.zero_stateRequirement_holds base N input
  | succ laterCount =>
      intro value
      exact StatePromise.mixed_fullSelection
        (readyContext base noQuantum N (laterCount + 1)).quantumLayout Reference
        (BasisReference.target (memberSeed base noQuantum N (laterCount + 1))
          input.caller.state.referenceMarginal)
        (BasisReference.target_normalized (memberSeed base noQuantum N (laterCount + 1))
          input.caller.state.referenceMarginal
          ((ExecutionState.referenceMarginal_mass input.caller.state).trans
            input.caller.normalized))
        ((((positiveRun base noQuantum N specification laterCount).finalState environment
          Reference input.state).mapClassical
            (positiveRun base noQuantum N specification laterCount).output.eval).block value)
        (rsaMeasuredParent_positive_output_statePromise (environment := environment)
          base noQuantum N specification laterCount input value)

end

end QuantumAlg.Factoring.RSA.Measured.Program
