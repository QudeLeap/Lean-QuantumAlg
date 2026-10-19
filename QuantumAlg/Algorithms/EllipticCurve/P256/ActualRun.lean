/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.Resources.Execution
public import QuantumAlg.Algorithms.EllipticCurve.P256.DomainParameters
public import QuantumAlg.Algorithms.EllipticCurve.P256.Cascade.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Seed

/-!
# The fixed P-256 instance of the generic streaming algorithm

The original certified instance fixes the affine schedule, subgroup seed and
4714 attempts. The algorithm is constructed by the generic factory, which
allocates the bank, retains the recovery cells and packs the checked result.
The same algorithm supplies the complete contract and all resource theorems.
-/

namespace QuantumAlg.EllipticCurve.P256.ActualRun

noncomputable section

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open FiniteCyclicDLP

/-- The borrowed public-point context before the algorithm allocates its bank. -/
public def Pre (I : P256.DomainParameters.PublicKeyInstance) : RuntimeCtx .quantum := by
  letI : Fact P256.DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  exact LogicalResources.Execution.inputContext (P256.DomainParameters.curve I.curveCert)
    (P256.Cascade.ecdlpInstance I)

/-- The complete final bank, public frame, recovery cells and optional result. -/
public def Post (I : P256.DomainParameters.PublicKeyInstance) : RuntimeCtx .quantum := by
  letI : Fact P256.DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  exact LogicalResources.Execution.outputContext (P256.DomainParameters.curve I.curveCert)
    (P256.Cascade.ecdlpInstance I)

/-- The original optional scalar word at the final observation. -/
public def OutputShape (I : P256.DomainParameters.PublicKeyInstance) : CShape :=
  .option (.unsignedWord (orderWidth (ECDLP.Canonical.problem (P256.Cascade.ecdlpInstance I))))

/-- The generic actual algorithm specialized to the original fixed P-256 instance. -/
public def algorithm (I : P256.DomainParameters.PublicKeyInstance) :
    Algorithm (.quantum AlgorithmGate.model .empty BitWord.model)
      (Pre I) (Post I) (OutputShape I) := by
  letI : Fact P256.DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  exact LogicalResources.algorithm (P256.DomainParameters.curve I.curveCert) 255
    P256.Measured.fieldTail_sameWidth P256.Measured.fieldTail_fits
    (P256.Measured.fieldModulus_odd I.curveCert) (P256.Cascade.ecdlpInstance I)
    (P256.Cascade.addend I) (P256.Measured.fixedSeed I) 4714

end

end QuantumAlg.EllipticCurve.P256.ActualRun
