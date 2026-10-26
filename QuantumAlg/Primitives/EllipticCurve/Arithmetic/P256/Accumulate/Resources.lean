/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Schedule.Resources
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Resources

/-! # Exact native events of arbitrary-accumulator MAC and complete source restoration -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate

noncomputable section

open QuantumAlg.EncodedBit GateSpec Horner

variable {Saved : Type} (saved : BinaryLabelEncoding Saved)
  (multiplier : RetainedMultiplier saved) (outer : EncodedBit saved)
  (outerMultiplier : ∀ index,
    (operandSavedBit saved outer).wire ≠
      (operandMultiplierBit saved (.retained (multiplier.bits index))).wire)

private lemma round_count (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (doubleCount addCount : Nat)
    (doubleLaw : ResourcePool.count focus Doubling.doublingProgram.eventCost = doubleCount)
    (addLaw : ∀ port separation, ResourcePool.count focus
      (stageProgram saved port outer separation).eventCost = addCount) (index : Fin width) :
    ResourcePool.count focus
        (forwardRoundProgram saved multiplier outer outerMultiplier index).eventCost =
      if index.val = 0 then addCount else doubleCount + addCount :=
  Horner.conditional_count focus (index.val = 0) (sourceDoublingProgram saved)
    (stageProgram saved (.retained (multiplier.bits index)) outer (outerMultiplier index))
    doubleCount addCount
    ((congrArg (ResourcePool.count focus) (sourceDoubling_eventCost saved)).trans doubleLaw)
    (addLaw _ _)

private lemma forward_count (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (doubleCount addCount : Nat)
    (doubleLaw : ResourcePool.count focus Doubling.doublingProgram.eventCost = doubleCount)
    (addLaw : ∀ port separation, ResourcePool.count focus
      (stageProgram saved port outer separation).eventCost = addCount) :
    ResourcePool.count focus (forwardProgram saved multiplier outer outerMultiplier).eventCost =
      addCount + 255 * (doubleCount + addCount) :=
  Horner.count_ofFn focus (stages := 255)
    (forwardRoundProgram saved multiplier outer outerMultiplier) _ _
    (round_count saved multiplier outer outerMultiplier focus doubleCount addCount doubleLaw addLaw)

private lemma repeated_count {count : Nat} {layout : QuantumLayout count}
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) (repetitions : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty layout) (amount : Nat)
    (law : ResourcePool.count focus body.eventCost = amount) :
    ResourcePool.count focus (UnitaryCircuit.iterate repetitions body).eventCost =
      repetitions * amount :=
  (ResourcePool.count_nsmul focus repetitions body.eventCost).trans
    (congrArg (fun value => repetitions * value) law)

private lemma restoration_count (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (doubleCount : Nat)
    (inverseLaw : ResourcePool.count focus Doubling.inverseDoublingProgram.eventCost =
      doubleCount) :
    ResourcePool.count focus (restorationProgram saved).eventCost = 255 * doubleCount :=
  repeated_count focus (width - 1) (inverseSourceDoublingProgram saved) doubleCount
    ((congrArg (ResourcePool.count focus) (inverseSourceDoubling_eventCost saved)).trans inverseLaw)

private lemma complete_count (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (doubleCount addCount : Nat)
    (doubleLaw : ResourcePool.count focus Doubling.doublingProgram.eventCost = doubleCount)
    (inverseLaw : ResourcePool.count focus Doubling.inverseDoublingProgram.eventCost = doubleCount)
    (addLaw : ∀ port separation, ResourcePool.count focus
      (stageProgram saved port outer separation).eventCost = addCount) :
    ResourcePool.count focus (program saved multiplier outer outerMultiplier).eventCost =
      (addCount + 255 * (doubleCount + addCount)) + 255 * doubleCount :=
  (ResourcePool.count_add focus _ _).trans
    (congrArg₂ Nat.add
      (forward_count saved multiplier outer outerMultiplier focus doubleCount addCount
        doubleLaw addLaw) (restoration_count saved focus doubleCount inverseLaw))

/-- Every bit latch, forward source doubling and complete inverse doubling is actually paid. -/
lemma program_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program saved multiplier outer outerMultiplier).eventCost = 22717258 :=
  complete_count saved multiplier outer outerMultiplier (.gate .toffoli) 18267 52348
    Doubling.doubling_toffoli_count Doubling.inverseDoubling_toffoli_count
    (fun port separation => stage_toffoli_count saved port outer separation)

/-- The complete source-restoring native MAC retains all actual CNOT instructions. -/
lemma program_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program saved multiplier outer outerMultiplier).eventCost = 1241338 :=
  complete_count saved multiplier outer outerMultiplier (.gate .cnot) 2179 508
    Doubling.doubling_cnot_count Doubling.inverseDoubling_cnot_count
    (fun port separation => stage_cnot_count saved port outer separation)

/-- Actual single-qubit operations are counted in both complete source traversals. -/
lemma program_x_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program saved multiplier outer outerMultiplier).eventCost = 259080 :=
  complete_count saved multiplier outer outerMultiplier (.gate .singleQubit) 508 0
    Doubling.doubling_x_count Doubling.inverseDoubling_x_count
    (fun port separation => Horner.stage_x_count saved outer port separation)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate
