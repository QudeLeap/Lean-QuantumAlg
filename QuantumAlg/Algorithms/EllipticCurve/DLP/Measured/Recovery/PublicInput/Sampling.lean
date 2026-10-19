/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.PublicInput.Allocation.Fixed
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Initialization.Reset
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Conversion.Protocol
import all QuantumAlg.Core.Execution.Time
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Actual public allocation, reset and converted streaming sampling

The allocating parent now contains the literal reset followed by all four
conversions and the complete measured stream. Both borrowed public points
remain resident. Its exact peak concerns this complete sampling execution,
including allocation and reset, on every syntactic path.

The full sequential execution equality retains allocation and child Paths,
every Store, service value and external Reference correlation. Gate time
includes both reset and sampling. This module does not claim a finite
recovery Algorithm, success probability or its eventual peak resources.

-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.PublicInput
namespace Sampling

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass

private abbrev Model : ExecutionModel := .quantum AlgorithmGate.model .empty

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail m : Nat) (seed : AffinePoint E)
  (r : Nat) (points : Fin (2 * m) → AffinePoint E) (coefficient : (ZMod p)ˣ)

/-- The actual reset precedes the original-order converted stream in one fixed child. -/
def body : Circuit Model (Recovery.Layout.terminal p.size m) (Recovery.Layout.terminal p.size m)
  false :=
  (Recovery.Initialization.newReset E fieldTail m seed).seq
    (Recovery.Conversion.convertedStages E r points (Recovery.Layout.order m) coefficient)

/-- Real zero allocation and retains precede this specific reset and sampler. -/
def circuit : Circuit Model (Recovery.PublicInput.frame E m) (Recovery.PublicInput.context E m) :=
  AllocatedFixed.code E m (body E fieldTail m seed r points coefficient)

variable {Reference : Register} {History : Type} [Fintype History]

/-- The literal reset and converted execution keep every complete nested record. -/
lemma body_execute
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    (body E fieldTail m seed r points coefficient).execute environment Reference state =
      ((Recovery.Conversion.convertedStages E r points (Recovery.Layout.order m)
        coefficient).execute environment Reference ((Recovery.Initialization.newReset E fieldTail
          m seed).execute environment Reference
          state)).mapHistory
          (fun record =>
            (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))) :=
  Circuit.execute_seq (environment := environment) (Recovery.Initialization.newReset E fieldTail m
    seed)
    (Recovery.Conversion.convertedStages E r points (Recovery.Layout.order m) coefficient) state

/-- Allocation is executed before embedding; its actual Path remains in the output History. -/
lemma circuit_execute
    (state : State (Recovery.PublicInput.frame E m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    (circuit E fieldTail m seed r points coefficient).execute environment Reference state =
      ((Circuit.embed (allowAllocation := true) (AllocatedFixed.placement E m)
        (body E fieldTail m seed r points coefficient)).execute environment Reference
          ((Allocation.circuit E m).execute environment Reference state)).mapHistory
            (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))) :=
  Circuit.execute_seq (environment := environment) (Allocation.circuit E m)
    (Circuit.embed (allowAllocation := true) (AllocatedFixed.placement E m)
      (body E fieldTail m seed r points coefficient)) state

/-- Both borrowed public inputs and their full Reference observation survive this actual run. -/
lemma circuit_borrowedRestored
    (state : State (Recovery.PublicInput.frame E m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    (circuit E fieldTail m seed r points coefficient).BorrowedRestored Reference state
      ((circuit E fieldTail m seed r points coefficient).execute environment Reference state) :=
  Circuit.borrowedRestored_of_noBorrowedQuantum (environment := environment)
    (circuit E fieldTail m seed r points coefficient) rfl Reference state

/-- The complete allocation, reset and sampler preserve arbitrary subnormalized total mass. -/
lemma circuit_execute_mass
    (state : State (Recovery.PublicInput.frame E m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    ((circuit E fieldTail m seed r points coefficient).execute environment Reference state).mass =
      state.mass :=
  Circuit.execute_mass (environment := environment) (circuit E fieldTail m seed r points
    coefficient) Reference state

/-- All visited resident storage of this actual sampler peaks at its complete public context. -/
lemma circuit_resident (path : (circuit E fieldTail m seed r points coefficient).Path) :
    (circuit E fieldTail m seed r points coefficient).peakResidentSpace path =
      (Recovery.PublicInput.context E m).residentSpace :=
  AllocatedFixed.code_resident E m (body E fieldTail m seed r points coefficient) path

/-- All actual owned auxiliary roles remain charged, including during reset. -/
lemma circuit_auxiliary (path : (circuit E fieldTail m seed r points coefficient).Path) :
    (circuit E fieldTail m seed r points coefficient).peakAuxiliarySpace path =
      (Recovery.PublicInput.context E m).auxiliarySpace :=
  AllocatedFixed.code_auxiliary E m (body E fieldTail m seed r points coefficient) path

/-- The specific full allocation/reset/sampling execution peaks at 818 qubits at width 256. -/
lemma circuit_width256_qubits (width : p.size = 256)
    (path : (circuit E fieldTail m seed r points coefficient).Path) :
    SpacePool.count (.quantumSystems 2)
      ((circuit E fieldTail m seed r points coefficient).peakResidentSpace path) = 818 :=
  AllocatedFixed.code_width256_qubits E m width
    (body E fieldTail m seed r points coefficient) path

/-- The same actual parent Path charges reset and every converted sampling instruction. -/
lemma circuit_quantumTime (path : (circuit E fieldTail m seed r points coefficient).Path) :
    (circuit E fieldTail m seed r points coefficient).quantumTime path =
      (Recovery.Initialization.newReset E fieldTail m seed).quantumTime path.2.1 +
        (Recovery.Conversion.convertedStages E r points (Recovery.Layout.order m)
          coefficient).quantumTime
          path.2.2 := by
  let allocation : Circuit Model (Recovery.PublicInput.frame E m) (Recovery.PublicInput.context
    E m) :=
    Allocation.circuit E m
  let placed : Circuit Model (Recovery.PublicInput.context E m) (Recovery.PublicInput.context E
    m) :=
    Circuit.embed (model := Model) (allowAllocation := true) (AllocatedFixed.placement E m)
      (body E fieldTail m seed r points coefficient)
  have outer : (circuit E fieldTail m seed r points coefficient).quantumTime path =
      allocation.quantumTime path.1 + placed.quantumTime path.2 :=
    Circuit.quantumTime_seq allocation placed path.1 path.2
  have allocationTime : allocation.quantumTime path.1 = 0 :=
    Allocation.circuit_quantumTime E m path.1
  have placedTime : placed.quantumTime path.2 =
      (body E fieldTail m seed r points coefficient).quantumTime path.2 :=
    Circuit.quantumTime_embed (model := Model) (AllocatedFixed.placement E m)
      (body E fieldTail m seed r points coefficient) path.2
  have localTime : (body E fieldTail m seed r points coefficient).quantumTime path.2 =
      (Recovery.Initialization.newReset E fieldTail m seed).quantumTime path.2.1 +
        (Recovery.Conversion.convertedStages E r points (Recovery.Layout.order m)
          coefficient).quantumTime
          path.2.2 :=
    Circuit.quantumTime_seq (model := Model) (Recovery.Initialization.newReset E fieldTail m seed)
      (Recovery.Conversion.convertedStages E r points (Recovery.Layout.order m) coefficient)
      path.2.1 path.2.2
  exact outer.trans ((congrArg₂ Nat.add allocationTime placedTime).trans
    ((Nat.zero_add _).trans localTime))

end

end Sampling
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.PublicInput
