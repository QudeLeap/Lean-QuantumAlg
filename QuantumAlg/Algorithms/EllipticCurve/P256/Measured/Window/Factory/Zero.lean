/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Run
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Finalized.Zero
import all QuantumAlg.Core.Execution.Restart.Sequence
import all QuantumAlg.Core.Algorithm.AlgorithmRun.FixedOutput

/-!
# Physical terminal zeroing after the actual paid factory prefix

The same whole-bank cleanup reaches every complete final record, including
the retained classical result and arbitrary incoming Reference correlations.
The bank remains allocated. No input state or success premise is required.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Factory

noncomputable section

open Execution ClassicalRoutines.EllipticCurve
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

variable {services : ClassicalOracleModel}
    (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (I : DomainParameters.PublicKeyInstance)
    (basePoint targetPoint : CInputRef base (PointShape 256))

/-- The physical zero basis on the complete owned bank after the actual final pack. -/
def paidRunZeroSeed :
    (CandidateCheck.Native.batchResultCtx
      (tableContext base noQuantum) 256 260).quantumLayout.SelectedBasis
        (CandidateCheck.Native.batchResultCtx
          (tableContext base noQuantum) 256 260).borrowedSelectionᶜ :=
  CandidateCheck.Native.finalPackSeed (tableContext base noQuantum) 256 260
    (QuantumLayout.restrictSelectedBasis
      (CandidateCheck.Native.persistentCtx (tableContext base noQuantum) 256 260).quantumLayout
      (CandidateCheck.Native.persistentCtx (tableContext base noQuantum) 256 260).borrowedSelectionᶜ
      (fun _ => 0))

/-- The real paid prefix and finalized run leave the same fixed physical zero state. -/
lemma paidRun_reinitializedAt
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    Circuit.ReinitializedAt
      (paidRun (services := services) base noQuantum I basePoint targetPoint).code environment
      (paidRunZeroSeed base noQuantum) := by
  have noBorrowed : base.borrowedQuantumWires = [] := by
    have sub := base.borrowedQuantumWires_sublist
    rw [noQuantum] at sub
    exact List.sublist_nil.mp sub
  have retainedOwned : (tableContext base noQuantum).borrowedQuantumWires = [] :=
    (Circuit.borrowedQuantumWires_preserved
      (paidPrefix (services := services) base noQuantum I basePoint targetPoint)).trans noBorrowed
  exact Circuit.RestartCleanup.afterAt
    (paidPrefix (services := services) base noQuantum I basePoint targetPoint)
    ((retainedInputs base noQuantum I basePoint targetPoint).runFinalized
      (services := services)).code environment (paidRunZeroSeed base noQuantum)
    ((retainedInputs base noQuantum I basePoint targetPoint).runFinalized_reinitializedAt
      environment retainedOwned)

/-- Every actual optional result retains terminal bank zeroing in the final state contract. -/
lemma paidRun_zero_requirement
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register}
    (supplied : OracleInput services base Reference) :
    (StateRequirement.marginal
      (CandidateCheck.Native.batchResultCtx
        (tableContext base noQuantum) 256 260).borrowedSelectionᶜ
      (.read (CandidateCheck.Native.batchResultRead (tableContext base noQuantum) 256 260))
      (fun _ _ => .pure (NormalizedVector.ket (paidRunZeroSeed base noQuantum)))).Holds
        supplied.caller
        ((paidRun (services := services) base noQuantum I basePoint targetPoint).finalState
          environment Reference supplied.state) :=
  AlgorithmRun.stateRequirement_of_reinitializedAt
    (paidRun (services := services) base noQuantum I basePoint targetPoint) environment
    (paidRunZeroSeed base noQuantum)
    (paidRun_reinitializedAt base noQuantum I basePoint targetPoint environment) _ supplied

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Factory
