/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Layout.Curve
import all QuantumAlg.Core.Execution.Local.MeasurementSequence
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling

/-!
# Original opaque ECDLP sampling with actual complete candidate recovery

The original prime subgroup order supplies the same modular recovery domain.
Each round uses the literal source preparation, opaque group query and inverse
QFTs on the one existing bank. Its actual finite readouts immediately feed
complete raw recovery, scalar multiplication, point comparison and the
first-success latches. Both public points are read from their incoming storage.
The seven persistent destinations are allocated once; only the final optional
result is packed. Every surviving entry belongs to the complete output.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
namespace GateLevelAttempt.Native

open Execution
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}
  (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (I : ECDLPInstance E)

private theorem range_isLocal {ctx : RuntimeCtx .quantum} (count : Nat)
    (body : Fin count → Circuit ctx ctx) (supported : ∀ index, (body index).IsLocal) :
    (Circuit.forRange count body).IsLocal := by
  induction count with
  | zero => trivial
  | succ count ih => exact ⟨supported 0, ih _ (fun index => supported index.succ)⟩

/-- The original subgroup primality supplies the unchanged nontrivial recovery modulus. -/
def recoveryModulus :
    ClassicalAlgorithms.Modular.ModulusSpec (FiniteCyclicDLP.orderWidth (problem I)) where
  modulus := I.subgroupOrder
  two_le := I.subgroupOrder_prime.two_le
  le_capacity := by
    simpa [problem, ClassicalAlgorithms.modulus, FiniteCyclicDLP.fourierModulus] using
      FiniteCyclicDLP.order_le_fourierModulus (problem I)

/-- The original unitary and actual readout sequence preserve their existing context. -/
theorem nativeECDLP_sample_isLocal (B : OrderExpansion (problem I).order) (A : Access I) :
    (sample base noQuantum I B A).IsLocal :=
  ⟨trivial, Circuit.measurementSequence_isLocal _⟩

/-- Every reset, stored correction and basis shift acts on existing resources. -/
theorem nativeECDLP_reset_isLocal : (reset base noQuantum I).IsLocal :=
  range_isLocal _ _ (fun _ => ⟨⟨trivial, fun _ => trivial⟩, trivial⟩)

/-- A complete repeated sample can be framed beneath the persistent recovery destinations. -/
theorem nativeECDLP_reusedSample_isLocal
    (B : OrderExpansion (problem I).order) (A : Access I) :
    (reusedSample base noQuantum I B A).IsLocal :=
  ⟨nativeECDLP_reset_isLocal base noQuantum I, nativeECDLP_sample_isLocal base noQuantum I B A⟩

/-- One original bank, its finite cells, seven persistent destinations and the final result. -/
def recoveryContext : RuntimeCtx .quantum :=
  batchResultCtx (context base noQuantum I) (Layout.fieldWidth E)
    (FiniteCyclicDLP.orderWidth (problem I))

/-- Actual original sampling and complete checked recovery share one bank for every round. -/
def recoveryRun (B : OrderExpansion (problem I).order) (A : Access I) (count : Nat)
    (basePoint targetPoint : CInputRef base
      (ClassicalRoutines.EllipticCurve.PointShape (Layout.fieldWidth E))) :
    AlgorithmRun base (recoveryContext base noQuantum I)
      (.option (.unsignedWord (FiniteCyclicDLP.orderWidth (problem I)))) :=
  let tail := sampledRecoveryRun (reusedSample base noQuantum I B A)
    (nativeECDLP_reusedSample_isLocal base noQuantum I B A) count
    (Layout.curveSpec E) (recoveryModulus I) (sampleInput base noQuantum I)
    (liftInput base noQuantum I basePoint) (liftInput base noQuantum I targetPoint)
  { code := (allocate base noQuantum I).seq tail.code
    output := tail.output }

/-- No original input, measurement cell, quantum bank or persistent result is omitted. -/
theorem nativeECDLP_recovery_output_listing
    (B : OrderExpansion (problem I).order) (A : Access I) (count : Nat)
    (basePoint targetPoint : CInputRef base
      (ClassicalRoutines.EllipticCurve.PointShape (Layout.fieldWidth E))) :
    (recoveryRun base noQuantum I B A count basePoint targetPoint).output.listing =
      (recoveryContext base noQuantum I).keys := rfl

end

end GateLevelAttempt.Native
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
