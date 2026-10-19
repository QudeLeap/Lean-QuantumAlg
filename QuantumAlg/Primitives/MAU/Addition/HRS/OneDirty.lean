/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.Recursive.Step

/-!
# Actual HRS constant addition with one arbitrary dirty bit

The recursion uses the proven six-block carry bridge and borrows storage
only from existing input halves. The same external dirty bit is reused
and restored by both recursive calls [HRS16, paper.tex:175-177,232-260].
The constant is a compile-time finite word. All widths and all joint input
basis labels are covered; no initialization or phase allowance is assumed.
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

/-- Actual recursive constant adder on the original word and one dirty bit. -/
def oneDirtyProgram (width : Nat) (constant : Fin (2 ^ width)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (oneDirtyEncoding width).width).toQuantum :=
  if _hbase : width ≤ 1 then
    oneDirtyBaseProgram width constant
  else
    recursiveStepProgram width constant
      (oneDirtyProgram (lowWidth width) ((splitWord width) constant).1)
      (oneDirtyProgram (highWidth width) ((splitWord width) constant).2)
termination_by width
decreasing_by
  all_goals
    have htwo : 2 ≤ width := by omega
    first
    | exact (hrsSplit_decreases width htwo).1
    | exact (hrsSplit_decreases width htwo).2

/-- Every actual recursive gate sequence implements the independent finite addition contract. -/
lemma hrsOneDirty_realizes (width : Nat) (constant : Fin (2 ^ width)) :
    UnitaryCircuit.Realizes (oneDirtyEncoding width) (oneDirtyProgram width constant) environment
      (oneDirtyOutput constant) := by
  induction width using Nat.strong_induction_on with
  | h width ih =>
      by_cases hbase : width ≤ 1
      · rw [oneDirtyProgram, dif_pos hbase]
        exact hrsOneDirtyBase_realizes width hbase constant
      · rw [oneDirtyProgram, dif_neg hbase]
        have hdecrease := hrsSplit_decreases width (by omega)
        exact hrsRecursiveStep_realizes width constant _ _
          (ih (lowWidth width) hdecrease.1 ((splitWord width) constant).1)
          (ih (highWidth width) hdecrease.2 ((splitWord width) constant).2)

/-- The external carrier has exactly `width + 1` canonically addressed qubits. -/
lemma hrsOneDirty_interface (width : Nat) (_constant : Fin (2 ^ width)) :
    (oneDirtyEncoding width).width = width + 1 ∧
      (QubitLayout.canonical (oneDirtyEncoding width).width).systemIdx =
        List.range (width + 1) := by
  constructor
  · rfl
  · exact QubitLayout.canonical_systemIdx (width + 1)

/-- Literal computational-basis action, with the dirty value restored and no relative phase. -/
lemma hrsOneDirty_apply (width : Nat) (constant input : Fin (2 ^ width)) (dirty : Bool) :
    (oneDirtyProgram width constant).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical (oneDirtyEncoding width).width).basisEquiv.symm
            ((oneDirtyEncoding width).encode (input, dirty)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (oneDirtyEncoding width).width).basisEquiv.symm
          ((oneDirtyEncoding width).encode (addWord constant input, dirty))) :=
  (hrsOneDirty_realizes width constant).apply_encoded_ket (input, dirty)

/-- The same exact endpoint extends across an arbitrary encoded reference system. -/
lemma hrsOneDirty_realizes_with_reference {Reference : Type}
    (reference : BinaryLabelEncoding Reference) (width : Nat) (constant : Fin (2 ^ width)) :
    UnitaryCircuit.Realizes
      (layout := QubitLayout.canonical ((oneDirtyEncoding width).width + reference.width))
      (BinaryLabelEncoding.prod (oneDirtyEncoding width) reference)
      (UnitaryCircuit.onBinaryPrefix reference.width (oneDirtyProgram width constant)) environment
      (fun state => (oneDirtyOutput constant state.1, state.2)) :=
  UnitaryCircuit.Realizes.onBinaryPrefix (right := reference)
    (hrsOneDirty_realizes width constant)

end

end QuantumAlg.MAU.Addition.HRS
