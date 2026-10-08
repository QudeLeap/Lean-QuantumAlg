/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.P256.DomainParameters
public import QuantumAlg.Algorithms.EllipticCurve.Resources
import all QuantumAlg.Algorithms.EllipticCurve.P256.Cascade.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Seed
import all QuantumAlg.Algorithms.EllipticCurve.Resources
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Spec

/-!
# The original actual P-256 run as one generic measured execution

The original affine addends and one fixed original subgroup offset instantiate
4714 actual reset, sampling and checked-recovery rounds. All rounds share the
same quantum systems, terminal measurement cells and seven first-success
cells. One final optional scalar is packed from the actual latches. The
independent correctness and resource contract is proved by the P-256 resource
owner using the same generic complete-run theorem.
-/

namespace QuantumAlg.EllipticCurve.P256.ActualRun

noncomputable section

open Execution PrimeFieldShortWeierstrass

/-- The fixed instance keeps the complete original quantum input and two public borrowed points. -/
public def Pre (I : DomainParameters.PublicKeyInstance) : RuntimeCtx .quantum :=
  LogicalResources.inputContext (DomainParameters.curve I.curveCert) (Cascade.ecdlpInstance I)

/-- Every final live quantum system, classical result and recovery latch remains represented. -/
public def Post (I : DomainParameters.PublicKeyInstance) : RuntimeCtx .quantum :=
  LogicalResources.outputContext (DomainParameters.curve I.curveCert) (Cascade.ecdlpInstance I)

/-- The actual final retained result is the original optional oversampled-width scalar word. -/
public def OutputShape (I : DomainParameters.PublicKeyInstance) : CShape :=
  .option (.unsignedWord (FiniteCyclicDLP.orderWidth (ECDLP.Canonical.problem
    (Cascade.ecdlpInstance I))))

/-- Exactly one application of the generic complete actual measured run. -/
def run (I : DomainParameters.PublicKeyInstance) :
    AlgorithmRun (.quantum AlgorithmGate.model .empty BitWord.model)
      (Pre I) (Post I) (OutputShape I) := by
  letI : Fact DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  exact (LogicalResources.algorithm (DomainParameters.curve I.curveCert) 255
    Measured.fieldTail_sameWidth Measured.fieldTail_fits (Measured.fieldModulus_odd I.curveCert)
    (Cascade.ecdlpInstance I) (Cascade.addend I) (Measured.fixedSeed I) 4714).run

/-- A successful actual optional output represents a bounded solution of the original equation. -/
public def SuccessfulOutput (I : DomainParameters.PublicKeyInstance)
    (output : CShape.Value (OutputShape I)) : Prop :=
  LogicalResources.AcceptedOutput (DomainParameters.curve I.curveCert)
    (Cascade.ecdlpInstance I) output

end

end QuantumAlg.EllipticCurve.P256.ActualRun
