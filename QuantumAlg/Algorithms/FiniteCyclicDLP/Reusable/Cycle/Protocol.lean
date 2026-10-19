/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Restart
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Readout
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Counts
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Space
public import QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Amplification.Model
import all QuantumAlg.Core.Execution.State.Requirement

/-!
# Independent complete-sample protocols for sequential finite-cyclic DLP

Each intended quantum computation returns one measured Fourier sample, with
the original full selected-family probability floor, and resets all its owned
physical qubits. The input's pure zero condition is supplied by the actual
initial preparation or the preceding physical reset. It does not restrict the
original empty-input algorithm or its arbitrary external reference and hidden
classical service state [Sho95, source.tex:1756-1984].
-/

namespace QuantumAlg.FiniteCyclicDLP.Reusable.Cycle

noncomputable section

open Execution

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- The original selected-family floor is an admissible probability threshold. -/
public def successLowerBound (P : KnownOrderProblem G) : ProbabilityLowerBound where
  value := ENNReal.ofReal (Binary.attemptFloor P)
  le_one := by
    apply ENNReal.ofReal_le_one.mpr
    have positive : (0 : Real) < Canonical.successDenominator P := by
      exact_mod_cast (Canonical.sourceFailureBudget_strictlyWellFormed P).denominator_pos
    change Canonical.attemptFloor P ≤ 1
    unfold Canonical.attemptFloor
    apply (div_le_iff₀ positive).mpr
    simpa only [one_mul] using
      (show (Canonical.successNumerator P : Real) ≤ Canonical.successDenominator P by
        exact_mod_cast (Canonical.successNumerator_lt_successDenominator P).le)

/-- An independently stated local zero input admits all of its reference extensions. -/
public def initialized (P : KnownOrderProblem G) (count : Nat)
    (state : ExecutionState (Store (context P count) × (model P).HiddenState)
      (context P count).register) : Prop :=
  (StatePromise.pure (NormalizedVector.ket (R := (context P count).register)
    (context P count).quantumLayout.zeroLabel)).Holds state.quantumMarginal

/-- Observe only this intended sample while retaining every actual live entry. -/
public def resultRead (P : KnownOrderProblem G) {count : Nat} (slot : Fin count) :
    OutputRead (context P count) (.fixedVector (sampleWidth P) (.finite 2)) :=
  .read (sampleInput P slot)

/-- Every output fiber retains the same zero state on the entire owned binary bank. -/
public def stateRequirement (P : KnownOrderProblem G) {count : Nat} (slot : Fin count) :
    StateRequirement (context P count) (context P count) :=
  .marginal (context P count).borrowedSelectionᶜ (resultRead P slot)
    (fun _ _ => .pure (NormalizedVector.ket (zeroSeed P count)))

/-- One source-defined Fourier sample, including real terminal measurement and reset.

**Input.** The same existing binary bank in local pure zero, with arbitrary
retained classical values, hidden service state and external reference.
**Output.** One designated retained Fourier sample and the fixed zero bank in
every complete output fiber.
**Resource budget.** The independent round allowance includes native
preparation, the declared query, inverse transforms, exponent readout and
physical reset; resident and auxiliary space are the original live context.
**Success.** Membership in the original selected Fourier family has probability
at least `N phi(N)/(4q^2)`.
**Source.** [Sho95, source.tex:1756-1984]; [dW19, qcnotes.tex:5409-5420].
-/
@[expose] public def problem (P : KnownOrderProblem G) {count : Nat} (slot : Fin count)
    (expansion : OrderExpansion P.order) :
    Problem (model P) (context P count) (context P count)
      (.fixedVector (sampleWidth P) (.finite 2)) where
  Witness := Input P
  valid := fun environment _ _ => environment = sourceEnvironment P
  initialization := fun _ _ => initialized P count
  accepts := fun _ secret _ value => Probability.SelectedOutcome P secret (observedOutcome P value)
  successLB := fun _ _ => successLowerBound P
  states := fun _ _ => [stateRequirement P slot]
  resources := {
    events := roundEventBudget P expansion
    resident := (context P count).residentSpace
    auxiliary := (context P count).auxiliarySpace }
  quantumTimeLimit := roundUnitDepth P expansion

/-- The sole candidate executes the same actual native, measured and reset round. -/
public def algorithm (P : KnownOrderProblem G) {count : Nat} (slot : Fin count)
    (expansion : OrderExpansion P.order) :
    Algorithm (model P) (context P count) (context P count)
      (.fixedVector (sampleWidth P) (.finite 2)) where
  run := ⟨round P slot expansion, Output.all (context P count) (resultRead P slot)⟩

end

end QuantumAlg.FiniteCyclicDLP.Reusable.Cycle
