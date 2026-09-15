/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Endpoint.Input
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Endpoint.Input
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Amplification.Model
import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Native.Batch
import all QuantumAlg.Algorithms.FiniteCyclicDLP.CallCountedRecovery.Native.Selection

/-!
# The actual finite-cyclic sampler followed by complete classical recovery

The original retry count determines all retained raw samples on one original
bank. Sampling finishes before the optional result is allocated and every
classical attempt executes. One final optional pack selects the first accepted
candidate. The complete output lists the original borrowed target, all sample
cells, the actual quantum bank and the real result.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.Endpoint

open Execution

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- The original count of real samples coexists with the one original bank and borrowed target. -/
def sampledContext (P : KnownOrderProblem G) : RuntimeCtx .quantum :=
  GateLevelAttempt.Native.Batch.context (pre P) (input_quantumWires P) P (retryCount P)

/-- The real result is allocated only after all original quantum samples have completed. -/
def outputKey (P : KnownOrderProblem G) : StorageKey := (sampledContext P).canonicalFreshKey

/-- The selected result has a fresh key in the complete post-sampling context. -/
theorem outputKey_fresh (P : KnownOrderProblem G) :
    outputKey P ∉ (sampledContext P).keys := (sampledContext P).canonicalFreshKey_fresh

/-- Every measured sample and the same quantum bank remain alongside the actual optional result. -/
public def outputContext (P : KnownOrderProblem G) : RuntimeCtx .quantum :=
  (sampledContext P).addRetained (outputKey P) (.option (.unsignedWord (orderWidth P)))
    (outputKey_fresh P)

/-- Structural observation of the one actually allocated result cell. -/
def outputRef (P : KnownOrderProblem G) :
    CWriteRef (outputContext P) (.option (.unsignedWord (orderWidth P))) :=
  CWriteRef.retainedHead (sampledContext P) (outputKey P)
    (.option (.unsignedWord (orderWidth P))) (outputKey_fresh P)

/-- Original samples are transported through result allocation without copying or packing. -/
def retainedSample (P : KnownOrderProblem G) (index : Fin (retryCount P)) :
    CInputRef (outputContext P)
      (.fixedVector (orderWidth P + orderWidth P) (.finite 2)) :=
  (GateLevelAttempt.Native.Batch.samples (pre P) (input_quantumWires P) P (retryCount P) index
    ).underRetained (outputKey P) (.option (.unsignedWord (orderWidth P))) (outputKey_fresh P)

/-- The same original encoded borrowed target is read after both actual allocations. -/
def retainedTarget (P : KnownOrderProblem G) :
    CInputRef (outputContext P) (.unsignedWord (orderWidth P)) :=
  (GateLevelAttempt.Native.Batch.liftInput (pre P) (input_quantumWires P) P (retryCount P)
    (targetRef P)).underRetained (outputKey P) (.option (.unsignedWord (orderWidth P)))
      (outputKey_fresh P)

/-- Every original raw sample reaches the actual complete group recovery and stored selector. -/
def recoveryCircuit (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P) :
    Circuit (outputContext P) (outputContext P) :=
  CallCountedRecovery.Native.recoveryInto (recoveryParameters P B A) (retryCount P)
    (retainedSample P) (retainedTarget P) (outputRef P)

/-- One real result allocation encloses the complete classical recovery tail. -/
def retainedRecovery (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P) :
    Circuit (sampledContext P) (outputContext P) :=
  (Circuit.retain (sampledContext P) (outputKey P)
    (.option (.unsignedWord (orderWidth P))) (outputKey_fresh P)).seq (recoveryCircuit P B A)

/-- The complete actual batch runs before the result allocation and every classical attempt. -/
def code (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P) :
    Circuit (pre P) (outputContext P) :=
  (GateLevelAttempt.Native.Batch.code (pre P) (input_quantumWires P) P (retryCount P) B A.ux).seq
    (retainedRecovery P B A)

/-- One actual run retains all live entries and reads the real final optional candidate. -/
def run (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P) :
    AlgorithmRun (pre P) (outputContext P) (.option (.unsignedWord (orderWidth P))) where
  code := code P B A
  output := Output.all (outputContext P) (.read (.storage (outputRef P).toCStorageRef))

/-- The output contains the original target, every raw sample, the bank and the result. -/
theorem finiteCyclic_run_output_listing (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P) :
    (run P B A).output.listing = (outputContext P).keys := rfl

end

end QuantumAlg.FiniteCyclicDLP.Canonical.Endpoint
