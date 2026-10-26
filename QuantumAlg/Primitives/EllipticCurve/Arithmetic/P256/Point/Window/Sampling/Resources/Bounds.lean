/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Resources.Sequence

/-!
# Independent native allowances of the actual34-window sampling schedule

The literal schedule has32 complete16-bit windows and two4-bit tails.
The allowances include both active reset and H preparation, every complete
point/table middle and all prior and internal Fourier feedback. Restarting
the whole854-bank and classical nearest recovery remain separate operations.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open Execution

/-- Each original full or tail point middle retains its previously proved native allowance. -/
def pointNativeLimit (coordinate : AlgorithmGate.Coordinate) (index : WindowIndex) : Nat :=
  match coordinate with
  | .toffoli => if index.full then 973308840 else 972514108
  | .cnot => if index.full then 807326434 else 605259730
  | .singleQubit => if index.full then 252013842 else 251220930

def pointTimeLimit (index : WindowIndex) : Nat :=
  if index.full then 1678797896 else 1670106516

/-- Earlier-bit phases, within-window pairs, and both real H/reset words. -/
def windowFourierLimit (index : WindowIndex) : Nat :=
  (index.lowerWidth + 1) * index.start + (index.lowerWidth + 1).choose 2 +
    4 * (index.lowerWidth + 1)

def windowNativeLimit (coordinate : AlgorithmGate.Coordinate) (index : WindowIndex) : Nat :=
  pointNativeLimit coordinate index +
    if coordinate = .singleQubit then windowFourierLimit index else 0

def windowTimeLimit (index : WindowIndex) : Nat :=
  pointTimeLimit index + windowFourierLimit index

/-- Closed allowances are independent of stores, measurement values and actual paths. -/
def samplerNativeLimit : AlgorithmGate.Coordinate → Nat
  | .toffoli => 33090911096
  | .cnot => 27044965348
  | .singleQubit => 8566954224

def samplerQuantumTimeLimit : Nat := 57061815124

lemma schedule_native_limit_sum (coordinate : AlgorithmGate.Coordinate) :
    (schedule.map (windowNativeLimit coordinate)).sum = samplerNativeLimit coordinate := by
  cases coordinate <;> decide +kernel

lemma schedule_quantumTime_limit_sum :
    (schedule.map windowTimeLimit).sum = samplerQuantumTimeLimit := by
  decide +kernel

lemma schedule_fourier_limit_sum :
    (schedule.map windowFourierLimit).sum = 69420 := by
  decide +kernel

/-- Measurement occurrence is exact and is independent of every reset and phase value. -/
lemma schedule_measurement_sum :
    (schedule.map fun index => 2048 + 2 * (index.lowerWidth + 1)).sum = 70672 := by
  decide +kernel

namespace Parameters

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Parameters ctx)

private lemma actualPointLimits (index : WindowIndex) :
    (parameters.pointParameters index).toffoliLimit = pointNativeLimit .toffoli index ∧
      (parameters.pointParameters index).cnotLimit = pointNativeLimit .cnot index ∧
      (parameters.pointParameters index).singleQubitLimit = pointNativeLimit .singleQubit index ∧
      (parameters.pointParameters index).quantumTimeLimit = pointTimeLimit index := by
  by_cases full : index.full <;>
    norm_num [Driver.Parameters.toffoliLimit, Driver.Parameters.cnotLimit,
      Driver.Parameters.singleQubitLimit, Driver.Parameters.quantumTimeLimit, pointParameters,
      pointNativeLimit, pointTimeLimit, WindowIndex.highRemaining, WindowIndex.lowWidth, full,
      Chain.Program.Parameters.controlToffoli, Chain.Program.Parameters.controlCnot,
      Chain.Program.Parameters.controlSingle, Chain.Program.Parameters.controlQuantumTime,
      EncodedBit.Word.OneDirtyLayout.gateCount,
      Chain.Program.Parameters.bareQueryToffoliLimit,
      Chain.Program.Parameters.bareQueryCnotLimit,
      Chain.Program.Parameters.bareQuerySingleLimit,
      Chain.Program.Parameters.bareQueryQuantumTimeLimit,
      EncodedBit.WindowLookup.staticCycleCnotLimit]

private lemma actualFourierLimit (index : WindowIndex) :
    parameters.fourierSingleLimit index + 2 * (index.lowerWidth + 1) =
      windowFourierLimit index := by
  unfold fourierSingleLimit windowFourierLimit
  rw [QuantumFourierTransform.Semiclassical.Window.priorPhaseCount_complete]
  change (index.lowerWidth + 1) * index.start + (index.lowerWidth + 1).choose 2 +
    2 * (index.lowerWidth + 1) + 2 * (index.lowerWidth + 1) = _
  omega

lemma block_native_limit_le (coordinate : AlgorithmGate.Coordinate) (index : WindowIndex)
    (path : (parameters.block (services := services) index).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate coordinate) ((parameters.block index).resourcePool path) ≤
        windowNativeLimit coordinate index := by
  have limits := parameters.actualPointLimits index
  cases coordinate with
  | toffoli =>
      have actual := parameters.block_toffoli_le index path
      rw [limits.1] at actual
      simpa only [windowNativeLimit, reduceCtorEq, ↓reduceIte, Nat.add_zero] using actual
  | cnot =>
      have actual := parameters.block_cnot_le index path
      rw [limits.2.1] at actual
      simpa only [windowNativeLimit, reduceCtorEq, ↓reduceIte, Nat.add_zero] using actual
  | singleQubit =>
      have actual := parameters.block_singleQubit_le index path
      have phases := parameters.actualFourierLimit index
      rw [limits.2.2.1] at actual
      simp only [windowNativeLimit, ↓reduceIte]
      omega

lemma block_time_limit_le (index : WindowIndex)
    (path : (parameters.block (services := services) index).Path) :
    (parameters.block index).depth Resource.Event.quantumDuration path ≤ windowTimeLimit index := by
  have actual := parameters.block_quantumTime_le index path
  have point := (parameters.actualPointLimits index).2.2.2
  have phases := parameters.actualFourierLimit index
  rw [point] at actual
  unfold windowTimeLimit
  omega

/-- The same actual34 allocating drivers satisfy each separate native quantum allowance. -/
lemma circuit_native_count_le (coordinate : AlgorithmGate.Coordinate)
    (path : (circuit (services := services) parameters).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate coordinate) ((circuit parameters).resourcePool path) ≤
        samplerNativeLimit coordinate := by
  have actual := parameters.sequence_count_le (.gate coordinate) (windowNativeLimit coordinate)
    (fun index current => parameters.block_native_limit_le coordinate index current) schedule path
  rw [schedule_native_limit_sum] at actual
  exact actual

/-- This is the actual chronological dependency-time bound, including all window Fourier words. -/
lemma circuit_quantumTime_le (path : (circuit (services := services) parameters).Path) :
    (circuit parameters).depth Resource.Event.quantumDuration path ≤ samplerQuantumTimeLimit := by
  have actual := parameters.sequence_depth_le Resource.Event.quantumDuration windowTimeLimit
    (fun index current => parameters.block_time_limit_le index current) schedule path
  rw [schedule_quantumTime_limit_sum] at actual
  exact actual

lemma circuit_measurement_count (path : (circuit (services := services) parameters).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+)) ((circuit parameters).resourcePool path) = 70672 := by
  have actual := parameters.sequence_count_eq (.measurement (2 : ℕ+))
    (fun index => 2048 + 2 * (index.lowerWidth + 1))
    (fun index current => parameters.block_measurement_count index current) schedule path
  rw [schedule_measurement_sum] at actual
  exact actual

end Parameters

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
