/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Resources
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Selection
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Resources
import all QuantumAlg.Components.Encoded.BitGates.QuantumTime
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! # Exact native ledger of the complete quantum-operand Horner schedule -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner

noncomputable section

open QuantumAlg.EncodedBit GateSpec ModularAddition

variable {Saved : Type} (saved : BinaryLabelEncoding Saved)
  (multiplier : QuantumMultiplier saved) (outer : EncodedBit saved)
  (outerMultiplier : ∀ index,
    (operandSavedBit saved outer).wire ≠
      (operandMultiplierBit saved (multiplier.ports index)).wire)

private lemma first_sum {count : Nat} (values : Fin (count + 1) → Nat)
    (first rest : Nat)
    (laws : ∀ index, values index = if index.val = 0 then first else rest) :
    (List.ofFn values).sum = first + count * rest := by
  have same : values =
      (fun index : Fin (count + 1) => if index.val = 0 then first else rest) := funext laws
  rw [same, List.ofFn_succ]
  simp only [Fin.val_zero, ↓reduceIte, Fin.val_succ, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, List.sum_cons, List.ofFn_const, List.sum_replicate, nsmul_eq_mul]
  rfl

private lemma count_fold {count : Nat} {layout : QuantumLayout count}
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (programs : List (UnitaryCircuit AlgorithmGate.model .empty layout)) :
    ResourcePool.count focus
        (programs.foldr UnitaryCircuit.seq
          (UnitaryCircuit.identity AlgorithmGate.model .empty layout)).eventCost =
      (programs.map (fun program => ResourcePool.count focus program.eventCost)).sum := by
  induction programs with
  | nil => exact ResourcePool.count_zero focus
  | cons first rest ih =>
      exact (ResourcePool.count_add focus first.eventCost _).trans
        (congrArg (fun amount => ResourcePool.count focus first.eventCost + amount) ih)

private lemma count_ofFn {count : Nat} {layout : QuantumLayout count}
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) {stages : Nat}
    (programs : Fin (stages + 1) → UnitaryCircuit AlgorithmGate.model .empty layout)
    (first rest : Nat)
    (laws : ∀ index, ResourcePool.count focus (programs index).eventCost =
      if index.val = 0 then first else rest) :
    ResourcePool.count focus
        ((List.ofFn programs).foldr UnitaryCircuit.seq
          (UnitaryCircuit.identity AlgorithmGate.model .empty layout)).eventCost =
      first + stages * rest := by
  refine (count_fold focus (List.ofFn programs)).trans ?_
  rw [← List.ofFn_comp']
  exact first_sum _ first rest laws

private lemma conditional_count {count : Nat} {layout : QuantumLayout count}
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (first : Prop) [Decidable first]
    (doubling addition : UnitaryCircuit AlgorithmGate.model .empty layout)
    (doubleCount addCount : Nat)
    (doubleLaw : ResourcePool.count focus doubling.eventCost = doubleCount)
    (addLaw : ResourcePool.count focus addition.eventCost = addCount) :
    ResourcePool.count focus
        (if first then addition else UnitaryCircuit.seq doubling addition).eventCost =
      if first then addCount else doubleCount + addCount := by
  by_cases selected : first
  · simpa only [selected, ↓reduceIte] using addLaw
  · simp only [selected, ↓reduceIte, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
      doubleLaw, addLaw]

private lemma round_count (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (doubleCount addCount : Nat)
    (doubleLaw : ResourcePool.count focus Doubling.doublingProgram.eventCost = doubleCount)
    (addLaw : ∀ port separation, ResourcePool.count focus
      (stageProgram saved port outer separation).eventCost = addCount) (index : Fin width) :
    ResourcePool.count focus
        (cleanRoundProgram saved multiplier outer outerMultiplier index).eventCost =
      if index.val = 0 then addCount else doubleCount + addCount :=
  conditional_count focus (index.val = 0)
    (operandDoublingProgram saved)
    (stageProgram saved (multiplier.ports (highIndex index)) outer
      (outerMultiplier (highIndex index))) doubleCount addCount
    ((congrArg (ResourcePool.count focus) (operandDoubling_eventCost saved)).trans doubleLaw)
    (addLaw _ _)

private lemma clean_count (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (doubleCount addCount : Nat)
    (doubleLaw : ResourcePool.count focus Doubling.doublingProgram.eventCost = doubleCount)
    (addLaw : ∀ port separation, ResourcePool.count focus
      (stageProgram saved port outer separation).eventCost = addCount) :
    ResourcePool.count focus (cleanProgram saved multiplier outer outerMultiplier).eventCost =
      addCount + 255 * (doubleCount + addCount) :=
  count_ofFn focus (stages := 255) (cleanRoundProgram saved multiplier outer outerMultiplier) _ _
    (round_count saved multiplier outer outerMultiplier focus doubleCount addCount doubleLaw addLaw)

/-- Every selected multiplication pays all 256 latch pairs and all 255 target doublings. -/
lemma cleanProgram_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (cleanProgram saved multiplier outer outerMultiplier).eventCost = 18059173 :=
  clean_count saved multiplier outer outerMultiplier (.gate .toffoli) 18267 52348
    Doubling.doubling_toffoli_count (fun port separation =>
      stage_toffoli_count saved port outer separation)

/-- CNOT accounting includes the complete actual target rotations and cleanup. -/
lemma cleanProgram_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (cleanProgram saved multiplier outer outerMultiplier).eventCost = 685693 :=
  clean_count saved multiplier outer outerMultiplier (.gate .cnot) 2179 508
    Doubling.doubling_cnot_count (fun port separation =>
      stage_cnot_count saved port outer separation)

private lemma stage_x_count (port : MultiplierPort saved) (separation) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (stageProgram saved port outer separation).eventCost = 0 := by
  have body : ((operandAdditionGates saved).map xMultiplicity).sum = 0 := by
    rw [← programList_x_count_eq_sum
      (layout := QubitLayout.canonical (operandEncoding saved).width) (oracles := .empty)]
    change ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (operandAdditionProgram saved).eventCost = 0
    rw [operandAddition_eventCost, Controlled.controlledAddition_x_count]
  rw [stageProgram, Selection.program, programList_x_count_eq_sum]
  simp only [Selection.gates, List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, Selection.latchGate, xMultiplicity_toffoli, body,
    Nat.add_zero]

/-- All actual single-qubit instructions of the complete schedule remain in the ledger. -/
lemma cleanProgram_x_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (cleanProgram saved multiplier outer outerMultiplier).eventCost = 129540 :=
  clean_count saved multiplier outer outerMultiplier (.gate .singleQubit) 508 0
    Doubling.doubling_x_count (fun port separation => stage_x_count saved outer port separation)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner
