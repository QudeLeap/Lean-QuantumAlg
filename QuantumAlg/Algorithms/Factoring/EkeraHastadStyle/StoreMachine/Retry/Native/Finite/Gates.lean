/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Events
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Gates
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Round.Gates

/-!
# Separate native gates of the actual finite factoring execution

The initial seed loading contributes at most one single-qubit gate. Each
sixteen-round batch retains its arithmetic, Fourier, reset and reload
coordinates. Sampling, complete classical recovery and final selection add
no quantum gates. These independent width formulas apply to the very same
paths as the state, success, memory and whole-run depth contracts.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry

open Execution ShortDLP.CompiledMAU

noncomputable section

/-- Independent gate-coordinate bounds include the one-time initial seed X. -/
def gateCountBound (N totalRounds : Nat) (coordinate : AlgorithmGate.Coordinate) : Nat :=
  if totalRounds = 0 then 0 else
    16 * totalRounds * RuntimeRound.gateWidthBound
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) coordinate +
        if coordinate = .singleQubit then 1 else 0

/-- The complete independent pool has no quantum contributions from classical processing. -/
theorem eventEnvelope_gate_succ (N count : Nat) (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := RuntimeRound.model) (.gate coordinate)
        (eventEnvelope N (count + 1)) =
      16 * (count + 1) * ResourcePool.count (model := RuntimeRound.model) (.gate coordinate)
        (RuntimeRound.eventEnvelope (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N) +
      if coordinate = .singleQubit then
        reloadXCount (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N else 0 := by
  rw [eventEnvelope_succ]
  simp only [NativeBatchReuseRecovery.eventEnvelope, NativeBatchReuse.nativeEnvelope,
    ResourcePool.count_add, ResourcePool.count_nsmul,
    RecoveryNativeGates.sampler_gate_count_zero, RecoveryNativeGates.recovery_gate_count_zero,
    RecoveryNativeGates.selection_gate_count_zero, ResourcePool.count_singleton]
  cases coordinate <;> simp <;> ring

/-- Every independent gate coordinate satisfies its own closed width formula. -/
theorem eventEnvelope_gate_le (N totalRounds : Nat) (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := RuntimeRound.model) (.gate coordinate)
      (eventEnvelope N totalRounds) ≤ gateCountBound N totalRounds coordinate := by
  cases totalRounds with
  | zero => simp [eventEnvelope, gateCountBound, ResourcePool.count]
  | succ count =>
    have round := RuntimeRound.eventEnvelope_gate_le
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N coordinate
    have repeated := Nat.mul_le_mul_left (16 * (count + 1)) round
    have reload := seedReload_count_le_one
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
    rw [eventEnvelope_gate_succ]
    cases coordinate <;> simp only [gateCountBound, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, and_false, if_false, if_true, reduceCtorEq] at * <;> omega

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- Each same-run path obeys all three independent native gate-coordinate ceilings. -/
theorem run_gateCount_le (input : Input N) (totalRounds : Nat)
    (path : (run base noQuantum input totalRounds).code.Path)
    (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := RuntimeRound.model) (.gate coordinate)
        ((run base noQuantum input totalRounds).code.resourcePool path) ≤
      gateCountBound N totalRounds coordinate :=
  ((ResourcePool.le_iff_count.mp (run_pool_le base noQuantum input totalRounds path))
    (.gate coordinate)).trans (eventEnvelope_gate_le N totalRounds coordinate)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry
