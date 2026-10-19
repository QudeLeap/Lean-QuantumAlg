/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Input
public import QuantumAlg.Core.Base.Classical.Oracle
public import QuantumAlg.Core.Execution.Random.Kernel
import all QuantumAlg.Core.Execution.Input
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Base.State.Density

/-!
# Complete initial states of a caller and a classical oracle

The hidden service state belongs to the complete mathematical input, alongside
the actual caller store and quantum/reference blocks. The service state is
neither an addressable caller cell nor an additional caller memory charge.
Its admissible initial correlations are specified by the problem. Execution
receives this state once and passes its current value through subsequent calls.

The caller projection retains every actual cell and wire. The local joint
projection forgets only the external reference; a local initialization contract
therefore admits every reference extension of that same joint input.
-/

namespace QuantumAlg.Execution

/-- A normalized complete input containing the selected service's persistent state. -/
public structure OracleInput (oracles : ClassicalOracleModel) {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (Reference : Register) where
  /-- Joint caller, hidden-state and quantum/reference correlations before execution. -/
  state : ExecutionState (Store ctx × oracles.HiddenState) (Register.prod ctx.register Reference)
  /-- The complete initial distribution has total mass one. -/
  normalized : state.IsNormalized

namespace OracleInput

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {oracles : ClassicalOracleModel} {kind : ProblemKind}
  {ctx : RuntimeCtx kind} {Reference : Register}

/-- Forget service state while retaining the complete actual caller and external reference. -/
public def caller (input : OracleInput oracles ctx Reference) : Input ctx Reference where
  state := input.state.mapClassical Prod.fst
  normalized := (input.state.mapClassical_mass Prod.fst).trans input.normalized

/-- The initialization contract observes the local caller and hidden state jointly. -/
public def localState (input : OracleInput oracles ctx Reference) :
    ExecutionState (Store ctx × oracles.HiddenState) ctx.register where
  block value := DensityOperator.marginalLeft (input.state.block value)
  total_le_one := by
    simp_rw [DensityOperator.marginalLeft_mass]
    exact input.state.total_le_one

private lemma oracleInput_localState_block_proof
    (input : OracleInput oracles ctx Reference) (value : Store ctx × oracles.HiddenState) :
    input.localState.block value = DensityOperator.marginalLeft (input.state.block value) := rfl

/-- Each local initialization block preserves its actual hidden-state label. -/
@[simp] public lemma oracleInput_localState_block
    (input : OracleInput oracles ctx Reference) (value : Store ctx × oracles.HiddenState) :
    input.localState.block value = DensityOperator.marginalLeft (input.state.block value) :=
  oracleInput_localState_block_proof input value

/-- Forgetting the external reference preserves complete initialization mass. -/
public lemma oracleInput_localState_mass (input : OracleInput oracles ctx Reference) :
    input.localState.mass = input.state.mass := by
  simp only [ExecutionState.mass, oracleInput_localState_block,
    DensityOperator.marginalLeft_mass]

/-- The local joint state supplied to the initialization contract is normalized. -/
public lemma oracleInput_localState_normalized (input : OracleInput oracles ctx Reference) :
    input.localState.IsNormalized :=
  (oracleInput_localState_mass input).trans input.normalized

/-- Observing caller input does not alter any joint quantum/reference marginal entry. -/
public lemma oracleInput_caller_quantumMarginal (input : OracleInput oracles ctx Reference) :
    input.caller.state.quantumMarginal = input.state.quantumMarginal :=
  ExecutionState.mapClassical_quantumMarginal _ _

/-- Construct a normalized initialization from a declared finite conditional distribution.

This samples the hidden state once. It does not certify a problem's separate
initialization predicate and is not an executable reset instruction.
-/
public def ofKernel (input : Input ctx Reference) (initial : Store ctx → PMF oracles.HiddenState) :
    OracleInput oracles ctx Reference where
  state := kernelChoice input.state initial
  normalized := (kernelChoice_mass input.state initial).trans input.normalized

/-- Kernel initialization retains the full input block with its actual declared weight. -/
public lemma oracleInput_ofKernel_block_matrix (input : Input ctx Reference)
    (initial : Store ctx → PMF oracles.HiddenState) (store : Store ctx)
    (hidden : oracles.HiddenState) :
    (((ofKernel input initial).state).block (store, hidden)).matrix =
      (initial store hidden).toReal • (input.state.block store).matrix :=
  kernelChoice_block_matrix input.state initial store hidden

end

end OracleInput

end QuantumAlg.Execution
