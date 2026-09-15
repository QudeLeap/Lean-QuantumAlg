/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Allocation.Correctness
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Execution.Input

/-!
# One complete allocating measured point-addition run

The original local support predicate admits every external-reference extension.
One AlgorithmRun connects the actual allocating circuit and its complete Output.
Its full-reference state guarantee and borrowed restoration are separate facts,
each derived from that same execution rather than the output listing.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Allocation

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The original affine/control domain is a support predicate on the supplied local mixed state. -/
def valid {p : Nat} (E : PrimeFieldShortWeierstrass p) (Q : AffinePoint E)
    (state : ExecutionState (Store (before p.size)) (before p.size).register) : Prop :=
  ∀ basis, ¬inputAdmissible E Q basis → state.quantumMarginal.matrix basis basis = 0

/-- Local input support allows every complete external-reference extension. -/
theorem valid_joint_support {p : Nat} (E : PrimeFieldShortWeierstrass p) (Q : AffinePoint E)
    {Reference : Register} (input : Input (before p.size) Reference)
    (allowed : valid E Q input.localState)
    (basis : (Register.prod (before p.size).register Reference).Index)
    (outside : ¬inputAdmissible E Q basis.1) :
    input.state.quantumMarginal.matrix basis basis = 0 := by
  have localZero := allowed basis.1 outside
  rw [Input.localState_quantumMarginal] at localZero
  exact DensityOperator.joint_diagonal_zero_of_marginal_diagonal_zero
    input.state.quantumMarginal basis.1 localZero basis.2

/-- The single run combines the actual allocating circuit and complete actual result-cell output. -/
def run {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] (Q : AffinePoint E) :
    AlgorithmRun (before p.size) (after p.size) (.fixedVector p.size (.finite 2)) :=
  { code := circuit E Q, output := output p.size }

/-- The same actual output enumerates every still-live quantum system and classical cell. -/
theorem run_output_listing {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) : (run E Q).output.listing = (after p.size).keys :=
  output_listing p.size

/-- The complete run state has the independent quantum-reference target on the original domain. -/
theorem run_finalState {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {Reference : Register} (input : Input (before p.size) Reference)
    (allowed : valid E Q input.localState) :
    ((run E Q).finalState Reference input.state).quantumMarginal =
      resultDensity E Q Reference input.state.quantumMarginal := by
  let copied : State (before p.size) Reference (Store (before p.size)) :=
    input.state.mapClassical (fun stored => (stored, stored))
  have copiedMarginal : copied.quantumMarginal = input.state.quantumMarginal :=
    ExecutionState.mapClassical_quantumMarginal input.state (fun stored => (stored, stored))
  have copiedSupport :
      ∀ basis : (Register.prod (before p.size).register Reference).Index,
        ¬inputAdmissible E Q basis.1 → copied.quantumMarginal.matrix basis basis = 0 := by
    intro basis outside
    exact (congrArg (fun density :
      DensityOperator (Register.prod (before p.size).register Reference) =>
        density.matrix basis basis) copiedMarginal).trans
      (valid_joint_support E Q input allowed basis outside)
  have history : ((run E Q).finalState Reference input.state).quantumMarginal =
      ((circuit E Q).execute Reference copied).quantumMarginal :=
    ExecutionState.mapClassical_quantumMarginal _ Prod.fst
  exact history.trans ((circuit_density E Q copied copiedSupport).trans
    (congrArg (resultDensity E Q Reference) copiedMarginal))

private theorem before_noBorrowedQuantum (width : Nat) :
    (before width).borrowedQuantumWires = [] := rfl

/-- Actual execution restores the complete borrowed-reference observation for every input. -/
theorem run_restoresBorrowed {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {Reference : Register} (input : Input (before p.size) Reference) :
    (run E Q).RestoresBorrowed input :=
  Circuit.borrowedRestored_of_noBorrowedQuantum (circuit E Q) (before_noBorrowedQuantum p.size)
    Reference (input.state.mapClassical (fun stored => (stored, stored)))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Allocation
