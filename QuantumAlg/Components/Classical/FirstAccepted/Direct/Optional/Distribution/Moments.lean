/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Distribution
import all QuantumAlg.Util.PMF.VectorMass
import all QuantumAlg.Util.PMF.FiniteWeights

/-!
# Finite complex moments of chronological optional selection

An arbitrary optional-word PMF and complex weight determine the exact finite
moment of the chronological retain fold. The empty fold, first-sample
recurrence, and initially empty selector law use the original PMF without
additional assumptions or any execution-state premise.
-/

namespace QuantumAlg.ClassicalRoutines.FirstAccepted.Direct.Optional.Distribution

noncomputable section

def moment {width : Nat}
    (distribution : PMF (CShape.option (.unsignedWord width)).Value) (count : Nat)
    (previous : (CShape.option (.unsignedWord width)).Value)
    (weight : (CShape.option (.unsignedWord width)).Value → ℂ) : ℂ :=
  ∑ samples : List.Vector (CShape.option (.unsignedWord width)).Value count,
    ((PMF.independentReplicateVector distribution count samples).toReal : ℂ) *
      weight (samples.toList.foldl Optional.retainValue previous)

private lemma moment_zero {width : Nat}
    (distribution : PMF (CShape.option (.unsignedWord width)).Value)
    (previous : (CShape.option (.unsignedWord width)).Value)
    (weight : (CShape.option (.unsignedWord width)).Value → ℂ) :
    moment distribution 0 previous weight = weight previous := by
  simp [moment, PMF.independentReplicateVector, apply_ite]

lemma moment_succ {width : Nat}
    (distribution : PMF (CShape.option (.unsignedWord width)).Value)
    (count : Nat) (previous : (CShape.option (.unsignedWord width)).Value)
    (weight : (CShape.option (.unsignedWord width)).Value → ℂ) :
    moment distribution (count + 1) previous weight =
      ∑ candidate : (CShape.option (.unsignedWord width)).Value,
        ((distribution candidate).toReal : ℂ) *
          moment distribution count (Optional.retainValue previous candidate) weight :=
  PMF.independentReplicateVector_weighted_cons distribution count
    (fun values => weight (values.toList.foldl Optional.retainValue previous))

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The finite fold from the empty selector is the pure first-success law. -/
lemma moment_selected {width : Nat}
    (distribution : PMF (CShape.option (.unsignedWord width)).Value) (count : Nat)
    (weight : (CShape.option (.unsignedWord width)).Value → ℂ) :
    moment distribution count .optionNone weight =
      ∑ selected : (CShape.option (.unsignedWord width)).Value,
        ((Optional.Distribution.selectedDistribution distribution count selected).toReal : ℂ) *
          weight selected :=
  (PMF.sum_map_toReal_mul (PMF.independentReplicateVector distribution count)
    (fun values => Optional.Distribution.firstValue values.toList) weight).symm

end

end QuantumAlg.ClassicalRoutines.FirstAccepted.Direct.Optional.Distribution
