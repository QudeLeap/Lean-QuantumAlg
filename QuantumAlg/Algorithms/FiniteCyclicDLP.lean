/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Endpoint.Specification
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Endpoint.Specification
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Endpoint.Final

/-!
# Finite-cyclic discrete logarithms

The canonical problem and named algorithm concern the same complete native
execution. The original literal uniform preparation, encoded group query and
Fourier readout feed the actual call-counted recovery. One retained quantum
bank is reused, every later reset is charged, and all measured samples remain
live through recovery. Complete input-reference correlations are admitted.
-/

namespace QuantumAlg.FiniteCyclicDLP

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- The original known-order finite-cyclic discrete-logarithm problem.

**Input.** A generator of known finite order N, a target in its cyclic
subgroup, the original binary expansion with at least two set bits, and
encoded quantum and classical group access with the same injective encoding.
Only the encoded target is borrowed. Every normalized state with that target
value and every external reference extension is admitted. The secret witness
appears in the acceptance relation, never in the executable parameters.
**Output.** The accepted optional word is exactly the original secret residue.
The complete output retains the target, one 3t-qubit bank, every actual finite
sample and the final result. All borrowed correlations must be restored;
there is no additional final zero-bank promise.
**Resources.** The original t = ceil(log2(12N)), q = 2^t and
k = max(1,ceil(log(3)/log(4q^2/(4q^2-totient(N))))) are retained.
The independent native event, unit-depth, resident and auxiliary limits
include one bank preparation, k literal sampling members, k-1 paid resets,
all finite measurements, the result allocation, and complete call-counted
classical recovery. The independent pool includes reset alternatives; actual
path bounds count the selected reset operations. All live samples, recovery
scratch, the result and the borrowed input remain in the storage allowance.
**Success.** The required probability of the exact secret is at least 2/3.
**Source.** [Sho95, source.tex:1704-1740,1907-1987];
[SV24, Uniform.tex:622-664,775-805,996-1024].
-/
public def problem (P : KnownOrderProblem G)
    (input : Canonical.Probability.SecretInput P)
    (B : UniformSuperposition.BinaryExpansion P.order)
    (A : Canonical.Endpoint.Access P) :
    Problem .quantum (Canonical.Endpoint.pre P) (Canonical.Endpoint.outputContext P)
      (.option (.unsignedWord (orderWidth P))) :=
  Canonical.Endpoint.Specification.specification P input B A

/-- One actual bank, finite sample batch and complete call-counted recovery of the public target. -/
public def algorithm (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order)
    (A : Canonical.Endpoint.Access P) :
    Algorithm .quantum (Canonical.Endpoint.pre P) (Canonical.Endpoint.outputContext P)
      (.option (.unsignedWord (orderWidth P))) :=
  Canonical.Endpoint.Final.algorithm P B A

/-- The named actual execution meets the original domain, two-thirds success and native budgets. -/
public theorem main (P : KnownOrderProblem G)
    (input : Canonical.Probability.SecretInput P)
    (B : UniformSuperposition.BinaryExpansion P.order)
    (A : Canonical.Endpoint.Access P) :
    Algorithm.Solves (algorithm P B A) (problem P input B A) :=
  Canonical.Endpoint.Final.algorithm_solves P B A input

end

end QuantumAlg.FiniteCyclicDLP
