/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Allocation.Execution
import all QuantumAlg.Core.Execution.State.Requirement
import all QuantumAlg.Core.Execution.MarginalLaws

/-!
# Complete independent state promise for measured affine point addition

The observation selects every actual live quantum system jointly with the
entire external reference. Its unit classical observation aggregates the actual
measurement outcomes. The target is the independent point-action density,
including restored prepared work. Output completeness and borrowed restoration
are discharged by their separate laws for the same run.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Allocation

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The independent full-reference target is normalized for every certified input state. -/
theorem resultDensity_normalized {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (Reference : Register) (input : Input (before p.size) Reference) :
    (resultDensity E Q Reference input.state.quantumMarginal).IsNormalized := by
  change (resultDensity E Q Reference input.state.quantumMarginal).mass = 1
  exact (DensityOperator.applyUnitary_mass (placedTarget E Q Reference)
    (initializedDensity p Reference input.state.quantumMarginal)).trans
    ((initializedDensity_mass p Reference input.state.quantumMarginal).trans
      ((ExecutionState.quantumMarginal_mass input.state).trans input.normalized))

/-- The independent state promise observes all actual final systems and the complete reference. -/
def selectedDensity {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (Reference : Register) (input : Input (before p.size) Reference) :
    DensityOperator (Register.prod
      ((after p.size).quantumLayout.selectedRegister Finset.univ) Reference) :=
  DensityOperator.observeSelectionWithReference (after p.size).quantumLayout Finset.univ Reference
    (resultDensity E Q Reference input.state.quantumMarginal)

/-- Selecting the complete physical output preserves the target's normalization. -/
theorem selectedDensity_normalized {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (Reference : Register) (input : Input (before p.size) Reference) :
    (selectedDensity E Q Reference input).IsNormalized := by
  change (selectedDensity E Q Reference input).mass = 1
  rw [selectedDensity, DensityOperator.observeSelectionWithReference_mass]
  exact resultDensity_normalized E Q Reference input

/-- Promise the independent complete quantum-reference target while aggregating actual outcomes. -/
def requirement {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] (Q : AffinePoint E) :
    StateRequirement (before p.size) (after p.size) :=
  .jointReference Finset.univ .unit fun Reference input _ =>
    .mixed (selectedDensity E Q Reference input) (selectedDensity_normalized E Q Reference input)

private theorem requirement_of_marginal {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) {Reference : Register}
    (input : Input (before p.size) Reference)
    (final : ExecutionState (Store (after p.size))
      (Register.prod (after p.size).register Reference))
    (same : final.quantumMarginal = resultDensity E Q Reference input.state.quantumMarginal) :
    (requirement E Q).Holds input final := by
  intro value
  cases value with
  | unit =>
    change (StatePromise.mixed (selectedDensity E Q Reference input)
      (selectedDensity_normalized E Q Reference input)).Holds
      (DensityOperator.observeSelectionWithReference (after p.size).quantumLayout Finset.univ
        Reference ((final.mapClassical (fun _ => CShape.Value.unit)).block CShape.Value.unit))
    rw [ExecutionState.executionState_mapClassical_const_block, same]
    change (selectedDensity E Q Reference input).matrix =
      ((selectedDensity E Q Reference input).mass : ℝ) •
        (selectedDensity E Q Reference input).matrix
    rw [selectedDensity_normalized]
    simp only [one_smul]

/-- The same complete actual run satisfies the independent state promise on the original domain. -/
theorem requirement_holds {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {Reference : Register} (input : Input (before p.size) Reference)
    (allowed : valid E Q input.localState) :
    (requirement E Q).Holds input ((run E Q).finalState Reference input.state) :=
  requirement_of_marginal E Q input _ (run_finalState E Q input allowed)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Allocation
