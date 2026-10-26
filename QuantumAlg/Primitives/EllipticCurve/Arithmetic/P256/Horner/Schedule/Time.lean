/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Schedule.Resources
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Resources
import all QuantumAlg.Components.Encoded.BitGates.QuantumTime

/-! # Complete actual quantum duration of the high-to-low Horner schedule -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner

noncomputable section

open QuantumAlg.EncodedBit GateSpec

variable {Saved : Type} (saved : BinaryLabelEncoding Saved)
  (multiplier : QuantumMultiplier saved) (outer : EncodedBit saved)
  (outerMultiplier : ∀ index,
    (operandSavedBit saved outer).wire ≠
      (operandMultiplierBit saved (multiplier.ports index)).wire)

lemma operandDoubling_quantumTime :
    (operandDoublingProgram saved).evaluatedEventDepth Resource.Event.quantumDuration = 20954 := by
  have length : (operandDoublingGates saved).length = Doubling.doublingGates.length := by
    rw [operandDoublingGates, List.length_map, List.length_map]
  exact (programList_quantumTime (QubitLayout.canonical _) .empty
    (operandDoublingGates saved)).trans (length.trans Doubling.doubling_length)

lemma operandInverseDoubling_quantumTime :
    (operandInverseDoublingProgram saved).evaluatedEventDepth
        Resource.Event.quantumDuration = 20954 := by
  have length : (operandInverseDoublingGates saved).length = Doubling.doublingGates.length := by
    rw [operandInverseDoublingGates, List.length_map, List.length_map,
      Doubling.inverseDoublingGates, List.length_reverse]
  exact (programList_quantumTime (QubitLayout.canonical _) .empty
    (operandInverseDoublingGates saved)).trans (length.trans Doubling.doubling_length)

lemma stage_quantumTime (port : MultiplierPort saved) (separation) :
    (stageProgram saved port outer separation).evaluatedEventDepth
      Resource.Event.quantumDuration = 52856 := by
  have counted : primitiveEventCount (stageProgram saved port outer separation) =
      (stageGates saved port outer separation).length :=
    primitiveEventCount_programList (layout := QubitLayout.canonical _) (oracles := .empty) _
  have coordinates : primitiveEventCount (stageProgram saved port outer separation) = 52856 := by
    rw [primitiveEventCount, stage_x_count, stage_cnot_count, stage_toffoli_count]
  exact (programList_quantumTime (QubitLayout.canonical _) .empty
    (stageGates saved port outer separation)).trans (counted.symm.trans coordinates)

private lemma depth_fold {count : Nat} {layout : QuantumLayout count}
    (programs : List (UnitaryCircuit AlgorithmGate.model .empty layout)) :
    (programs.foldr UnitaryCircuit.seq
        (UnitaryCircuit.identity AlgorithmGate.model .empty layout)).evaluatedEventDepth
          Resource.Event.quantumDuration =
      (programs.map (fun program =>
        program.evaluatedEventDepth Resource.Event.quantumDuration)).sum := by
  induction programs with
  | nil => rfl
  | cons first rest ih =>
      exact (UnitaryCircuit.evaluatedEventDepth_seq _ first _).trans
        (congrArg (fun amount =>
          first.evaluatedEventDepth Resource.Event.quantumDuration + amount) ih)

private lemma depth_ofFn {count : Nat} {layout : QuantumLayout count} {stages : Nat}
    (programs : Fin (stages + 1) → UnitaryCircuit AlgorithmGate.model .empty layout)
    (first rest : Nat)
    (laws : ∀ index, (programs index).evaluatedEventDepth Resource.Event.quantumDuration =
      if index.val = 0 then first else rest) :
    ((List.ofFn programs).foldr UnitaryCircuit.seq
        (UnitaryCircuit.identity AlgorithmGate.model .empty layout)).evaluatedEventDepth
          Resource.Event.quantumDuration = first + stages * rest := by
  refine (depth_fold (List.ofFn programs)).trans ?_
  rw [← List.ofFn_comp']
  exact first_sum _ first rest laws

private lemma conditional_depth {count : Nat} {layout : QuantumLayout count}
    (first : Prop) [Decidable first]
    (doubling addition : UnitaryCircuit AlgorithmGate.model .empty layout)
    (doubleCount addCount : Nat)
    (doubleLaw : doubling.evaluatedEventDepth Resource.Event.quantumDuration = doubleCount)
    (addLaw : addition.evaluatedEventDepth Resource.Event.quantumDuration = addCount) :
    (if first then addition else UnitaryCircuit.seq doubling addition).evaluatedEventDepth
        Resource.Event.quantumDuration = if first then addCount else doubleCount + addCount := by
  by_cases selected : first
  · simpa only [selected, ↓reduceIte] using addLaw
  · simp only [selected, ↓reduceIte, UnitaryCircuit.evaluatedEventDepth_seq, doubleLaw, addLaw]

private lemma round_quantumTime (index : Fin width) :
    (cleanRoundProgram saved multiplier outer outerMultiplier index).evaluatedEventDepth
      Resource.Event.quantumDuration = if index.val = 0 then 52856 else 20954 + 52856 :=
  conditional_depth (index.val = 0) (operandDoublingProgram saved)
    (stageProgram saved (multiplier.ports (highIndex index)) outer
      (outerMultiplier (highIndex index))) 20954 52856
    (operandDoubling_quantumTime saved) (stage_quantumTime saved outer _ _)

/-- Duration follows the same actual native program tree, including all latch and cleanup gates. -/
lemma cleanProgram_quantumTime :
    (cleanProgram saved multiplier outer outerMultiplier).evaluatedEventDepth
      Resource.Event.quantumDuration = 18874406 :=
  depth_ofFn (stages := 255) (cleanRoundProgram saved multiplier outer outerMultiplier) _ _
    (round_quantumTime saved multiplier outer outerMultiplier)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner
