/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.RetainedTables
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Signed.Program
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Inputs
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Finalized

/-!
# Executable paid prefix and finalized run

This module constructs the actual retained bank, measurement records and table
cells, executes the signed-row preparation, then calls the existing
three-attempt finalized sampler. Success and resource theorems are separate.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Factory

noncomputable section

open QuantumAlg.Execution
open QuantumAlg.ClassicalRoutines.EllipticCurve
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (I : DomainParameters.PublicKeyInstance)
    (basePoint targetPoint : CInputRef base (PointShape 256))

/-- The actual retained references supply every port of the internal sampler. -/
def retainedInputs : Sampling.Storage.Inputs (tableContext base noQuantum) :=
  inputs I (tableContext_wires base noQuantum)
    (resultsAfterTables base noQuantum) (tableFrame base noQuantum)
    (originalInputAfterTables base noQuantum basePoint)
    (originalInputAfterTables base noQuantum targetPoint)

/-- The literal paid prefix precedes the unchanged finalized sampler context. -/
def paidPrefix {services : ClassicalOracleModel} :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      base (tableContext base noQuantum) :=
  (prepareWithTables (services := services) base noQuantum).seq
    (WindowTables.Outer.Preparation.Signed.prepare
      (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (tableFrame base noQuantum)
      (actualCurveSpec I).field (actualCurveSpec I).curve.a.val
      (originalInputAfterTables base noQuantum basePoint)
      (originalInputAfterTables base noQuantum targetPoint))

/-- The resulting single run includes physical bank and retained-cell setup. -/
def paidRun {services : ClassicalOracleModel} :
    AlgorithmRun (.quantum AlgorithmGate.model .empty BitWord.model services)
      base
      (CandidateCheck.Native.batchResultCtx (tableContext base noQuantum) 256 260)
      (.option (.unsignedWord 260)) :=
  let continuation := (retainedInputs base noQuantum I basePoint targetPoint).runFinalized
    (services := services)
  { code := (paidPrefix (services := services) base noQuantum I basePoint targetPoint).seq
      continuation.code
    output := continuation.output }

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Factory
