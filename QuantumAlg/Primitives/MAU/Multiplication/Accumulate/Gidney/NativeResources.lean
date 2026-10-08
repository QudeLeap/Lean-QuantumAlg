/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Resources
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Native.Resources

/-!
# Independent finite native resource pool for modular accumulation

The source selector is expanded into actual default gates. Every instruction
therefore belongs to the same three-coordinate native alphabet. The numerical
budget includes both nested control expansions and is independent of the
compiled coefficient and execution.
-/

namespace QuantumAlg.MAU.Multiplication.Accumulate.Gidney

noncomputable section

/-- The three actual default-model coordinates emitted by the accumulation circuit. -/
def nativeAlphabet : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  EncodedBit.GateSpec.primitiveAlphabet

/-- Independent budget with the same explicit cap at each of the three native coordinates. -/
def nativeBudget (width : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  (width * stageEventBound width) • nativeAlphabet

theorem gidneyCanonicalStage_native_support (extra : Nat)
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1))
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (present : focus ∈ (canonicalProgram extra modulus constant).eventCost) :
    focus ∈ nativeAlphabet :=
  EncodedBit.GateSpec.programList_native_support _
    (canonicalGates extra modulus constant) focus present

theorem gidneyPlacedStage_native_support (extra : Nat) (selected : Fin (extra + 3))
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1))
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (present : focus ∈ (placedStageProgram extra selected modulus constant).eventCost) :
    focus ∈ nativeAlphabet := by
  rw [(gidneyPlacedStage_resources extra selected modulus constant (fun _ => 1)).1] at present
  exact gidneyCanonicalStage_native_support extra modulus constant focus present

theorem gidneySmallStage_native_support (width : Nat) (small : width ≤ 2)
    (selected : Fin width) (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1))
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (present : focus ∈ (smallStageProgram width small selected modulus constant).eventCost) :
    focus ∈ nativeAlphabet :=
  EncodedBit.GateSpec.programList_native_support _
    (smallStageGates width small selected modulus constant) focus present

theorem gidneyStage_native_support (width : Nat) (selected : Fin width)
    (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1))
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (present : focus ∈ (stageProgram width selected modulus constant).eventCost) :
    focus ∈ nativeAlphabet := by
  rcases width with _ | width
  · exact Fin.elim0 selected
  rcases width with _ | width
  · simp only [stageProgram] at present
    exact gidneySmallStage_native_support 1 (by decide) selected modulus constant focus present
  rcases width with _ | extra
  · simp only [stageProgram] at present
    exact gidneySmallStage_native_support 2 (by decide) selected modulus constant focus present
  simp only [stageProgram] at present
  exact gidneyPlacedStage_native_support extra selected modulus constant focus present

theorem gidneyAccumulatePrefix_native_support (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (coefficient count : Nat) (within : count ≤ width)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (present : focus ∈ (prefixProgram width modulus coefficient count within).eventCost) :
    focus ∈ nativeAlphabet := by
  induction count with
  | zero =>
      change focus ∈ (0 : ResourcePool (.quantum AlgorithmGate.model .empty)) at present
      simp at present
  | succ index ih =>
      change focus ∈ ((prefixProgram width modulus coefficient index (by omega)).seq
        (stageProgram width ⟨index, by omega⟩ modulus
          (Nat.FixedWidth.accumulateConstant modulus coefficient index))).eventCost at present
      rw [UnitaryCircuit.seq_eventCost] at present
      rcases Multiset.mem_add.mp present with before | current
      · exact ih (by omega) before
      · exact gidneyStage_native_support width ⟨index, by omega⟩ modulus
          (Nat.FixedWidth.accumulateConstant modulus coefficient index) focus current

/-- Every actual event belongs to the explicit three-coordinate alphabet. -/
theorem gidneyAccumulate_native_support (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (present : focus ∈ (program width modulus coefficient).eventCost) :
    focus ∈ nativeAlphabet :=
  gidneyAccumulatePrefix_native_support width modulus coefficient width
    (Nat.le_refl width) focus present

/-- The complete actual circuit meets the independent finite native-resource budget. -/
theorem gidneyAccumulate_native_bound (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) :
    (program width modulus coefficient).eventCost ≤ nativeBudget width :=
  ResourcePool.le_scaled_of_support_card_le _ _ _
    (gidneyAccumulate_native_support width modulus coefficient)
    (gidneyAccumulate_event_count_bound width modulus coefficient)

end

end QuantumAlg.MAU.Multiplication.Accumulate.Gidney
