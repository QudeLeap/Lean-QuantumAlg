/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Gates
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Parameters

/-!
# Three native gate ceilings for the actual RSA-2048 execution

The decimals evaluate independent arithmetic and Fourier width formulas for
all 112 measured members. Single-qubit gates also include every physical
reset/reload and the one-time initial seed loading. Classical recovery has
zero native quantum gates. Each ceiling applies to a path of the same actual
seven-batch finite execution, without asserting that the ceiling is attained.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRSA2048

open Execution ShortDLP.CompiledMAU

noncomputable section

/-- Independent separate native coordinate ceilings of one complete measured round. -/
def roundGateCountBound : AlgorithmGate.Coordinate → Nat
  | .toffoli => 4_332_746_167_099_392
  | .cnot => 4_332_746_169_729_029
  | .singleQubit => 4_332_746_171_055_631

/-- Independent separate native coordinate ceilings of all seven batches. -/
def gateCountBound : AlgorithmGate.Coordinate → Nat
  | .toffoli => 485_267_570_715_131_904
  | .cnot => 485_267_571_009_651_248
  | .singleQubit => 485_267_571_158_230_673

/-- The round decimals are kernel-checked evaluations of the three independent width formulas. -/
theorem roundGateWidthBound_eq (coordinate : AlgorithmGate.Coordinate) :
    RuntimeRound.gateWidthBound 1_025 513 2_048 coordinate = roundGateCountBound coordinate := by
  cases coordinate <;>
    norm_num [RuntimeRound.gateWidthBound, RuntimeRound.memberGateBound,
      RuntimeRound.arithmeticGateBound, MAU.Exponentiation.Gidney.eventBound,
      MAU.Exponentiation.Gidney.stageEventBound, MAU.Multiplication.Gidney.eventBound,
      MAU.Multiplication.Accumulate.Gidney.stageEventBound,
      MAU.Addition.Gidney.modularOffsetEventBound, MAU.Addition.Gidney.pivotEventBound,
      MAU.Addition.Gidney.biFlipEventBound, MAU.Addition.Gidney.comparisonEventBound,
      MAU.Addition.Gidney.constantOffsetEventBound, Nat.choose_two_right,
      totalQubits_eq, roundGateCountBound]

-- Scalar substitution precedes evaluation; no dependent execution tree is unfolded.
attribute [local irreducible] RuntimeRound.gateWidthBound

/-- Every original exact-width key has the same independently evaluated gate-coordinate ceilings. -/
theorem model_gateCountBound_eq {N : Nat} (model : FixedWidthModel N)
    (coordinate : AlgorithmGate.Coordinate) :
    NativeFiniteRetry.gateCountBound N rounds coordinate = gateCountBound coordinate := by
  unfold NativeFiniteRetry.gateCountBound
  rw [model_shortLogBits_eq model, model_tradeoffBits_eq model, model_arithmeticBits_eq model]
  change (if 7 = 0 then 0 else
    16 * 7 * RuntimeRound.gateWidthBound 1_025 513 2_048 coordinate +
      if coordinate = .singleQubit then 1 else 0) = _
  rw [roundGateWidthBound_eq]
  cases coordinate <;> norm_num [roundGateCountBound, gateCountBound] <;> decide

attribute [local irreducible] NativeFiniteRetry.run NativeFiniteRetry.code NativeFiniteRetry.context

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- Every actual complete path obeys all three coordinate bounds, including reset corrections. -/
theorem run_gateCount_le (model : FixedWidthModel N) (input : Canonical.Input N)
    (path : (NativeFiniteRetry.run base noQuantum input rounds).code.Path)
    (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := RuntimeRound.model) (.gate coordinate)
        ((NativeFiniteRetry.run base noQuantum input rounds).code.resourcePool path) ≤
      gateCountBound coordinate :=
  (NativeFiniteRetry.run_gateCount_le base noQuantum input rounds path coordinate).trans_eq
    (model_gateCountBound_eq model coordinate)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRSA2048
