/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Reset
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver.Resources
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Resources
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Preparation.Resources
import all QuantumAlg.Core.Execution.Composition.Resources

/-!
# Same-path resources of one actual recycled sampling window

The exact decomposition keeps active reset, real H preparation, complete
five-table driver and actual stored-feedback Fourier readout in order.
The table builder remains in the driver and retains its separate classical
charge. No enclosing restart or nearest checker is included in this block.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Parameters

noncomputable section

open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Driver

open Execution

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Parameters ctx)

attribute [local irreducible] Circuit.depth UnitaryCircuit.evaluatedEventDepth

/-- The actual allocating point/table middle has its original complete path. -/
def pointPath (index : WindowIndex)
    (path : (parameters.block (services := services) index).Path) :
    (Driver.circuit (services := services) (parameters.pointParameters index)
      parameters.frame parameters.modulus index.row).Path := path.2.2.1

/-- The actual measured readout retains the branch path following that same point middle. -/
def fourierPath (index : WindowIndex)
    (path : (parameters.block (services := services) index).Path) :
    (QuantumFourierTransform.Semiclassical.Window.inverseCode
      (operations := BitWord.model) (services := services) (parameters.ports index)).Path :=
  path.2.2.2

private lemma pool_succ_nsmul {model : ExecutionModel} (pool : ResourcePool model) (count : Nat) :
    pool + count • pool = (count + 1) • pool := by
  rw [succ_nsmul]
  exact add_comm _ _

private lemma preparation_pool (count : Nat)
    (ports : QuantumFourierTransform.Semiclassical.Window.Ports ctx 260 count) :
    (QuantumFourierTransform.Semiclassical.Window.preparation count ports).eventCost
      BitWord.model services =
        count • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model .empty BitWord.model services)
          (.gate .singleQubit) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [QuantumFourierTransform.Semiclassical.Window.preparation]
      change ResourcePool.singleton
        (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .singleQubit) +
        (QuantumFourierTransform.Semiclassical.Window.preparation count ports.tail).eventCost
          BitWord.model services = _
      rw [ih ports.tail]
      exact pool_succ_nsmul _ count

/-- All four literal component pools occur once, with no paid driver body omitted. -/
lemma block_resourcePool (index : WindowIndex)
    (path : (parameters.block (services := services) index).Path) :
    (parameters.block index).resourcePool path =
      (parameters.reset index).resourcePool path.1 +
        ((index.lowerWidth + 1) • ResourcePool.singleton
            (model := .quantum AlgorithmGate.model .empty BitWord.model services)
            (.gate .singleQubit) +
          ((Driver.circuit (parameters.pointParameters index) parameters.frame parameters.modulus
              index.row).resourcePool (parameters.pointPath index path) +
            (QuantumFourierTransform.Semiclassical.Window.inverseCode
              (parameters.ports index)).resourcePool (parameters.fourierPath index path))) := by
  change (parameters.reset index).resourcePool path.1 + (ResourcePool.ofList
    ((QuantumFourierTransform.Semiclassical.Window.preparation
      (index.lowerWidth + 1) (parameters.ports index)).eventTrace BitWord.model services) +
      ((Driver.circuit (parameters.pointParameters index) parameters.frame parameters.modulus
        index.row).resourcePool (parameters.pointPath index path) +
        (QuantumFourierTransform.Semiclassical.Window.inverseCode (operations := BitWord.model)
          (services := services) (parameters.ports index)).resourcePool
          (parameters.fourierPath index path))) = _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost _ BitWord.model services, preparation_pool]

def fourierSingleLimit (index : WindowIndex) : Nat :=
  (index.lowerWidth + 1) * QuantumFourierTransform.Semiclassical.Window.priorPhaseCount
      (parameters.ports index)
      (QuantumFourierTransform.Semiclassical.Window.previousPositions 260) +
    (index.lowerWidth + 1).choose 2 + 2 * (index.lowerWidth + 1)

private lemma fourier_native_counts (index : WindowIndex)
    (path : (parameters.block (services := services) index).Path) :
    let pool := (QuantumFourierTransform.Semiclassical.Window.inverseCode
      (operations := BitWord.model) (services := services) (parameters.ports index)).resourcePool
        (parameters.fourierPath index path)
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.gate .toffoli) pool = 0 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.gate .cnot) pool = 0 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.gate .singleQubit) pool ≤ parameters.fourierSingleLimit index := by
  have bounded := QuantumFourierTransform.Semiclassical.Window.inverseCode_pool_le
    (operations := BitWord.model) (services := services) (parameters.ports index)
      (parameters.fourierPath index path)
  have counts := ResourcePool.le_iff_count.mp bounded
  have first := counts (.gate .toffoli)
  have second := counts (.gate .cnot)
  have third := counts (.gate .singleQubit)
  simp only [ResourcePool.count_add, ResourcePool.count_nsmul,
    ResourcePool.count_singleton, reduceCtorEq, ↓reduceIte, Nat.mul_zero, Nat.mul_one,
    Nat.add_zero] at first second third
  exact ⟨Nat.eq_zero_of_le_zero first, Nat.eq_zero_of_le_zero second, third⟩

lemma block_toffoli_le (index : WindowIndex)
    (path : (parameters.block (services := services) index).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate .toffoli) ((parameters.block index).resourcePool path) ≤
        (parameters.pointParameters index).toffoliLimit := by
  have reset := (parameters.reset_native_counts index path.1).1
  have fourier := (parameters.fourier_native_counts index path).1
  have point := (parameters.pointParameters index).circuit_toffoli_le parameters.frame
    parameters.modulus index.row (parameters.pointPath index path)
  have different : (Resource.Event.gate .singleQubit :
      Resource.Event (.quantum AlgorithmGate.model .empty BitWord.model services)) ≠
        .gate .toffoli := by intro equality; cases equality
  rw [block_resourcePool]
  simp only [ResourcePool.count_add, ResourcePool.count_nsmul,
    ResourcePool.count_singleton, if_neg different, Nat.mul_zero,
    reset, fourier, Nat.zero_add, Nat.add_zero]
  exact point

lemma block_cnot_le (index : WindowIndex)
    (path : (parameters.block (services := services) index).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate .cnot) ((parameters.block index).resourcePool path) ≤
        (parameters.pointParameters index).cnotLimit := by
  have reset := (parameters.reset_native_counts index path.1).2.1
  have fourier := (parameters.fourier_native_counts index path).2.1
  have point := (parameters.pointParameters index).circuit_cnot_le parameters.frame
    parameters.modulus index.row (parameters.pointPath index path)
  have different : (Resource.Event.gate .singleQubit :
      Resource.Event (.quantum AlgorithmGate.model .empty BitWord.model services)) ≠
        .gate .cnot := by intro equality; cases equality
  rw [block_resourcePool]
  simp only [ResourcePool.count_add, ResourcePool.count_nsmul,
    ResourcePool.count_singleton, if_neg different, Nat.mul_zero,
    reset, fourier, Nat.zero_add, Nat.add_zero]
  exact point

lemma block_singleQubit_le (index : WindowIndex)
    (path : (parameters.block (services := services) index).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate .singleQubit) ((parameters.block index).resourcePool path) ≤
        (parameters.pointParameters index).singleQubitLimit +
          parameters.fourierSingleLimit index + 2 * (index.lowerWidth + 1) := by
  have reset := (parameters.reset_native_counts index path.1).2.2
  have fourier := (parameters.fourier_native_counts index path).2.2
  have point := (parameters.pointParameters index).circuit_singleQubit_le parameters.frame
    parameters.modulus index.row (parameters.pointPath index path)
  rw [block_resourcePool]
  simp only [ResourcePool.count_add, ResourcePool.count_nsmul,
    ResourcePool.count_singleton, ↓reduceIte, Nat.mul_one]
  omega

end

end Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
