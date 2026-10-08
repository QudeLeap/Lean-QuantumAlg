/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.Resources.SevenCoordinates
import all QuantumAlg.Algorithms.EllipticCurve.Resources.SevenCoordinates

/-!
# Complete generic logical resources of original elliptic-curve discrete logarithms

The registered theorem binds the original named algorithm, success and joint
borrowed restoration to a physically complete cycle certificate and seven
scalar bounds on every actual path. Parameters and retry counts are symbolic.
Zero and one have their actual complete single computations; larger counts
use the admitted initialized/reused/terminal plan with real cleanup. Whole-run
chronological depth is retained separately from maximum complete-cycle depth.
The literal binary-gap preparation is unchanged and consumes its generic
width ceiling [SV24, Uniform.tex:622-664,996-1024]. The original group-addition
and sampling organization remains [PZ03, ecc.tex:448-556].
-/

namespace QuantumAlg.EllipticCurve.LogicalResources

noncomputable section

open Execution PrimeFieldShortWeierstrass FiniteCyclicDLP

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- Complete same-run generic correctness, physical cycles and seven scalar resource ceilings. -/
public theorem main (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E) (addends : AddendEncoding E I points)
    (count : Nat) (failure : ℝ)
    (calibrated : RepetitionCondition E I points seed count failure) :
    ∃ cycles : Algorithm.CycleSolves
        (algorithm E fieldTail sameWidth fits odd I points seed count)
        (completeCycleProblem E fieldTail sameWidth fits I points seed addends count failure),
      (algorithm E fieldTail sameWidth fits odd I points seed count).Solves
          (problem E I count failure) ∧
        (∀ path : (algorithm E fieldTail sameWidth fits odd I points seed count).run.code.Path,
          SevenCoordinateBounds E fieldTail sameWidth fits odd I points seed addends count failure
            cycles path) ∧
        (∀ path : (algorithm E fieldTail sameWidth fits odd I points seed count).run.code.Path,
          (algorithm E fieldTail sameWidth fits odd I points seed count).run.code.depth
              (fun _ => 1) path ≤
            Scalar.wholeRunEvents p.size (Nat.clog 2 p)
              (orderWidth (ECDLP.Canonical.problem I)) count) :=
  ⟨completeCycleCertificate E fieldTail sameWidth fits odd I points seed addends count
      failure calibrated,
    algorithm_solves E fieldTail sameWidth fits odd I points seed addends count failure calibrated,
    algorithm_sevenCoordinates E fieldTail sameWidth fits odd I points seed addends count
      failure calibrated,
    algorithm_wholeRunDepth_scalar E fieldTail sameWidth fits odd I points seed count⟩

end

end QuantumAlg.EllipticCurve.LogicalResources
