/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.QubitReadouts
import all QuantumAlg.Core.Execution.Measurement.Effect

/-!
# Actual terminal readout events depend only on the quantum marginal

Each named qubit is measured by the existing sequential interpreter and writes
its own finite result cell. The event reads precisely those cells in the given
index order. Distinct result keys ensure that these writes replace every value
the event reads, so no initial store or history is consulted by the observation.

The resulting observable is the diagonal projector on the same physical basis
event, with the complete external reference retained. Its trace pairing equals
the actual final event weight for arbitrary mixed input states. The statement
includes zero requested wires and imposes no condition on older classical data.
-/

open scoped ComplexOrder

namespace QuantumAlg.Execution.QubitReadouts

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum} {width : Nat}

/-- The same ordered measured-wire event acts on the full register beside its reference. -/
def eventEffect (wires : Fin width → Fin ctx.systemCount)
    (event : (Fin width → Bool) → Bool) (Reference : Register) :
    Effect (Register.prod ctx.register Reference) where
  matrix := @ZMeasurement.projector (Register.prod ctx.register Reference) Bool
    (Classical.decEq Bool)
    (fun basis => event (fun index => decide ((basis.1 (wires index)).val = 1))) true
  positive := Matrix.PosSemidef.diagonal (by
    intro basis
    dsimp only [Pi.zero_apply]
    split_ifs <;> simp)
  contractive vector := ZMeasurement.projector_applyVec_norm_le
    (R := Register.prod ctx.register Reference)
    (fun basis => event (fun index => decide ((basis.1 (wires index)).val = 1))) true vector

/-- The event projector pairs with every retained reference coordinate of the input density. -/
theorem eventEffect_weight (wires : Fin width → Fin ctx.systemCount)
    (event : (Fin width → Bool) → Bool) (Reference : Register)
    (state : DensityOperator (Register.prod ctx.register Reference)) :
    (eventEffect wires event Reference).weight state =
      (∑ basis, if event (fun index => decide ((basis.1 (wires index)).val = 1)) = true then
        state.matrix basis basis else 0).re := by
  have sameDecision : instDecidableEqBool = Classical.decEq Bool :=
    Subsingleton.elim _ _
  rw [sameDecision]
  simp only [Effect.weight, eventEffect, ZMeasurement.projector, Matrix.diagonal_mul,
    Matrix.trace, Matrix.diag, ite_mul, one_mul, zero_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro basis _
  split_ifs <;> rfl

/-- Actual sequential measurement reads only its newly written result cells in the final event. -/
theorem measurement_eventEffectWeight (wires : Fin width → Fin ctx.systemCount)
    (qubits : ∀ index, (ctx.quantumLayout.wire (wires index)).dimension = 2)
    (cells : Fin width → CWriteRef ctx (.finite 2))
    (distinct : Function.Injective fun index => (cells index).key)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (event : (Fin width → Bool) → Bool) :
    ExecutionState.effectWeight
      ((Circuit.measurementSequence (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := services)
        (readouts wires qubits cells)).execute
          Reference state)
        (fun record => if event (mask (record.1.read (input cells))) = true then
          Effect.one (Register.prod ctx.register Reference)
        else Effect.zero (Register.prod ctx.register Reference)) =
      (eventEffect wires event Reference).weight state.quantumMarginal := by
  have sameDecision : instDecidableEqBool = Classical.decEq Bool :=
    Subsingleton.elim _ _
  rw [sameDecision]
  rw [ExecutionState.effectWeight_observed_mass,
    Circuit.measurementSequence_observed_mass, eventEffect_weight]
  have written (store : Store ctx) (basis : ctx.register.Index) :
      mask ((Circuit.writeMeasurementPath (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := services)
        (readouts wires qubits cells) store
        (Circuit.measurementBasisPath (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := services)
        (readouts wires qubits cells) basis)).read (input cells)) =
      fun index => decide ((basis (wires index)).val = 1) := by
    funext index
    exact written_mask (gates := gates) (oracles := oracles)
      (operations := operations) (services := services)
      wires qubits cells distinct store basis index
  simp only [written, ExecutionState.diagonalSum]
  congr 1
  apply Finset.sum_congr rfl
  intro basis _
  change (∑ original, (if event (fun index => decide ((basis.1 (wires index)).val = 1)) =
      true then (1 : ℂ) else 0) * (state.block original).matrix basis basis) =
    if event (fun index => decide ((basis.1 (wires index)).val = 1)) = true then
      (∑ original, (state.block original).matrix) basis basis else 0
  split_ifs <;> simp only [one_mul, zero_mul, Finset.sum_const_zero, Matrix.sum_apply]

/-- Equal full quantum marginals give equal readout events despite different old histories. -/
theorem measurement_eventEffectWeight_eq_of_quantumMarginal_eq
    {leftGates rightGates : GateModel} {leftOracles rightOracles : OracleModel}
    {leftOperations rightOperations : ClassicalOpModel}
    {leftServices rightServices : ClassicalOracleModel}
    (wires : Fin width → Fin ctx.systemCount)
    (qubits : ∀ index, (ctx.quantumLayout.wire (wires index)).dimension = 2)
    (cells : Fin width → CWriteRef ctx (.finite 2))
    (distinct : Function.Injective fun index => (cells index).key)
    {Reference : Register} {LeftHistory RightHistory : Type}
    [Fintype LeftHistory] [Fintype RightHistory]
    (left : State ctx Reference (leftServices.HiddenState × LeftHistory))
    (right : State ctx Reference (rightServices.HiddenState × RightHistory))
    (same : left.quantumMarginal = right.quantumMarginal)
    (event : (Fin width → Bool) → Bool) :
    ExecutionState.effectWeight
      ((Circuit.measurementSequence (gates := leftGates) (oracles := leftOracles)
        (operations := leftOperations) (classicalOracles := leftServices)
        (readouts wires qubits cells)).execute Reference left)
        (fun record => if event (mask (record.1.read (input cells))) = true then
          Effect.one (Register.prod ctx.register Reference)
        else Effect.zero (Register.prod ctx.register Reference)) =
      ExecutionState.effectWeight
        ((Circuit.measurementSequence (gates := rightGates) (oracles := rightOracles)
          (operations := rightOperations) (classicalOracles := rightServices)
          (readouts wires qubits cells)).execute Reference right)
        (fun record => if event (mask (record.1.read (input cells))) = true then
          Effect.one (Register.prod ctx.register Reference)
        else Effect.zero (Register.prod ctx.register Reference)) := by
  rw [measurement_eventEffectWeight (gates := leftGates) (oracles := leftOracles)
      (operations := leftOperations) wires qubits cells distinct left event,
    measurement_eventEffectWeight (gates := rightGates) (oracles := rightOracles)
      (operations := rightOperations) wires qubits cells distinct right event, same]

end

end QuantumAlg.Execution.QubitReadouts
