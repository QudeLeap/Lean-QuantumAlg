/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Target
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.State
import all QuantumAlg.Core.Execution.State.Requirement
import all QuantumAlg.Core.Execution.MarginalLaws

/-!
# Complete independent state requirements for in-place arithmetic

The promise observes every live physical quantum system and the entire
external reference. The actual unit classical observation aggregates
all stored measurement results. Its prescribed mixed target is the
independent prime-word permutation beside the original fixed auxiliary
state [LYL+26, sec_point_add/sec_point_add.tex:24-36,45-105,119-122].

The target expression uses only the independent mathematical density.
The actual-run state equalities discharge the generic observation law
below without conditional arithmetic callbacks. Borrowed restoration remains an independent
requirement, even though all output resources are explicitly retained.
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceRequirement

noncomputable section

open Execution MAU.Inversion.SharedEEA InversePreparation

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Select the whole live layout, preserving its complete external reference. -/
def selectedDensity (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (Reference : Register)
    (input : Input (before modulus.size) Reference) :
    DensityOperator (Register.prod
      ((NumeratorMeasurement.context modulus.size).quantumLayout.selectedRegister Finset.univ)
      Reference) :=
  DensityOperator.observeSelectionWithReference
    (NumeratorMeasurement.context modulus.size).quantumLayout Finset.univ Reference
    (InPlaceTarget.density operation modulus prime Reference input.state.quantumMarginal)

/-- The independent full-system observation is normalized on every certified joint input. -/
theorem selectedDensity_normalized (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (Reference : Register)
    (input : Input (before modulus.size) Reference) :
    (selectedDensity operation modulus prime Reference input).IsNormalized := by
  change (selectedDensity operation modulus prime Reference input).mass = 1
  rw [selectedDensity, DensityOperator.observeSelectionWithReference_mass]
  exact InPlaceTarget.density_normalized operation modulus prime Reference input

/-- The complete independent target is promised after summing every actual classical outcome. -/
def requirement (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) :
    StateRequirement (before modulus.size) (NumeratorMeasurement.context modulus.size) :=
  .jointReference Finset.univ .unit fun Reference input _ =>
    .mixed (selectedDensity operation modulus prime Reference input)
      (selectedDensity_normalized operation modulus prime Reference input)

/-- Exact full-state agreement supplies the complete promise through its actual unit observation. -/
theorem holds_of_quantumMarginal (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) {Reference : Register}
    (input : Input (before modulus.size) Reference)
    (final : ExecutionState (Store (NumeratorMeasurement.context modulus.size))
      (Register.prod (NumeratorMeasurement.context modulus.size).register Reference))
    (same : final.quantumMarginal =
      InPlaceTarget.density operation modulus prime Reference input.state.quantumMarginal) :
    (requirement operation modulus prime).Holds input final := by
  intro value
  cases value with
  | unit =>
    change (StatePromise.mixed (selectedDensity operation modulus prime Reference input)
        (selectedDensity_normalized operation modulus prime Reference input)).Holds
      (DensityOperator.observeSelectionWithReference
        (NumeratorMeasurement.context modulus.size).quantumLayout Finset.univ Reference
        ((final.mapClassical (fun _ => CShape.Value.unit)).block CShape.Value.unit))
    rw [ExecutionState.executionState_mapClassical_const_block, same]
    change (selectedDensity operation modulus prime Reference input).matrix =
      ((selectedDensity operation modulus prime Reference input).mass : ℝ) •
        (selectedDensity operation modulus prime Reference input).matrix
    rw [selectedDensity_normalized]
    simp only [one_smul]

/-- The complete mixed-state requirement holds for the actual division run and any full output. -/
theorem division_holds (modulus : Nat) (prime : Nat.Prime modulus)
    {shape : CShape} (output : Output (NumeratorMeasurement.context modulus.size) shape)
    {Reference : Register} (input : Input (before modulus.size) Reference)
    (valid : InPlaceDomain.valid modulus input.localState) :
    (requirement .division modulus prime).Holds input
      (({ code := InPlaceDivision.code modulus prime, output := output } :
        AlgorithmRun (before modulus.size)
          (NumeratorMeasurement.context modulus.size) shape).finalState Reference input.state) :=
  holds_of_quantumMarginal .division modulus prime input _
    (InPlaceState.division_finalState modulus prime output input valid)

/-- Actual multiplication meets the full reference-aware requirement after summing real outcomes. -/
theorem multiplication_holds (modulus : Nat) (prime : Nat.Prime modulus)
    {shape : CShape} (output : Output (NumeratorMeasurement.context modulus.size) shape)
    {Reference : Register} (input : Input (before modulus.size) Reference)
    (valid : InPlaceDomain.valid modulus input.localState) :
    (requirement .multiplication modulus prime).Holds input
      (({ code := InPlaceMultiplication.code modulus prime, output := output } :
        AlgorithmRun (before modulus.size)
          (NumeratorMeasurement.context modulus.size) shape).finalState Reference input.state) :=
  holds_of_quantumMarginal .multiplication modulus prime input _
    (InPlaceState.multiplication_finalState modulus prime output input valid)


end

end QuantumAlg.MeasuredUncompute.InPlaceRequirement
