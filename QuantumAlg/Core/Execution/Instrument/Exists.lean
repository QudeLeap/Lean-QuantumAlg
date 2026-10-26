/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Instrument.Basic
import all QuantumAlg.Core.Execution.Instrument.Basic

/-! # Composing concrete full-record instruments without expanding their outcome carriers -/

@[expose] public section

namespace QuantumAlg.Execution

noncomputable section

open Instrument

variable {gates : GateModel} {oracles : OracleModel}
  {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel} {allowAllocation : Bool}

/-- A fixed actual program has a finite full-record local instrument on every input state. -/
def HasInstrument
    (code : Circuit (.quantum gates oracles operations services)
      ctx ctx allowAllocation)
    (environment : (ExecutionModel.quantum gates oracles operations
      services).Environment) : Prop :=
  ∃ Outcome : Type, ∃ finite : Fintype Outcome,
    let : Fintype Outcome := finite
    Nonempty (Instrument code Outcome environment)

/-- A concrete certified instrument provides its exact actual program's existential form. -/
lemma Instrument.to_exists {Outcome : Type} [Fintype Outcome]
    {code : Circuit (.quantum gates oracles operations services)
      ctx ctx allowAllocation}
    {environment : (ExecutionModel.quantum gates oracles operations
      services).Environment}
    (actual : Instrument code Outcome environment) : HasInstrument code environment :=
  ⟨Outcome, inferInstance, ⟨actual⟩⟩

/-- Keep the actual intermediate Store and two actual paths while composing finite instruments. -/
lemma HasInstrument.seq
    {first second : Circuit (.quantum gates oracles operations services)
  ctx ctx allowAllocation}
    {environment : (ExecutionModel.quantum gates oracles operations
      services).Environment}
    (head : HasInstrument first environment) (tail : HasInstrument second environment) :
    HasInstrument (first.seq second) environment := by
  rcases head with ⟨First, firstFinite, ⟨head⟩⟩
  rcases tail with ⟨Second, secondFinite, ⟨tail⟩⟩
  let : Fintype First := firstFinite
  let : Fintype Second := secondFinite
  exact (head.seq tail).to_exists

/-- Existence of the proved actual instrument entails arbitrary-reference unitary naturality. -/
lemma HasInstrument.reference_unitary
    {code : Circuit (.quantum gates oracles operations services)
  ctx ctx allowAllocation}
    {environment : (ExecutionModel.quantum gates oracles operations
      services).Environment} (actual : HasInstrument code environment)
    (Reference : Register) (operator : UnitaryOperator Reference)
    {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    code.execute environment Reference
        (state.applyUnitary (fun _ =>
          UnitaryOperator.prodTensor (1 : UnitaryOperator ctx.register) operator)) =
      (code.execute environment Reference state).applyUnitary (fun _ =>
        UnitaryOperator.prodTensor (1 : UnitaryOperator ctx.register) operator) := by
  rcases actual with ⟨Outcome, finite, ⟨actual⟩⟩
  let : Fintype Outcome := finite
  exact actual.reference_unitary Reference operator state

end

end QuantumAlg.Execution
