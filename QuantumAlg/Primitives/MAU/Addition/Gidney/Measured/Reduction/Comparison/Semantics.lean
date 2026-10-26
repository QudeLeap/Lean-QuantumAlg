/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Comparison.Projection
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Comparison.Carry
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Comparison.Arithmetic

/-!
# Exact complete-label semantics of the actual controlled native comparison

The literal source word toggles only the original flag by strict less-than
under both active controls. Both helpers are restored physically. The
original flag, dirty outputs, inactive controls and untouched encoded data
are arbitrary [G25, main.tex:253-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The literal native comparator changes exactly its flag on every admitted complete label. -/
lemma comparisonGates_step (layout : Layout encoding width) (wide : 2 ≤ width)
    (threshold : BitVec width) (state : Data)
    (clean : ∀ index, (layout.clean index).get state = false) :
    stepList (layout.comparisonGates wide threshold) state =
      if (layout.control.get state && layout.selector.get state) &&
          decide ((layout.sourceWord state).toNat < threshold.toNat) then
        layout.flag.flip state else state := by
  by_cases zero : threshold = 0
  · subst threshold
    simp [comparisonGates, stepList]
  · have positive : 0 < threshold.toNat := by
      have nonzero : threshold.toNat ≠ 0 := by
        intro same
        apply zero
        apply BitVec.eq_of_toNat_eq
        exact same
      omega
    let computed := stepList layout.activePairGates state
    let active := layout.control.get state && layout.selector.get state
    have helper : (layout.clean 1).get computed = active := by
      rw [activePairGates_helper, clean 1, Bool.false_xor]
    have low : (layout.clean 0).get computed = false := by
      exact (activePairGates_get layout (layout.clean 0) (layout.wire_ne (by simp)) state).trans
        (clean 0)
    have originalWord : layout.sourceWord computed = layout.sourceWord state :=
      activePairGates_sourceWord layout state
    have carry : (layout.comparisonLayout wide).carryValues (-threshold) computed width =
        Nat.BinaryArithmetic.natAddCarry (layout.sourceWord state).toNat
          (if active then (-threshold).toNat else 0) width := by
      rw [comparisonCarryValues_eq_nat layout wide (-threshold) computed width le_rfl,
        originalWord, helper]
    have mask : ((layout.comparisonLayout wide).carryValues (-threshold) computed width ^^
        (layout.clean 1).get computed) =
          (active && decide ((layout.sourceWord state).toNat < threshold.toNat)) := by
      rw [carry, helper]
      exact comparisonCarry_below threshold (layout.sourceWord state) positive active
    rw [comparisonGates, if_neg zero]
    simp only [stepList_append]
    rw [comparisonCarry_step layout wide (-threshold) computed low]
    change stepList layout.activePairGates
      (cnotStep (layout.clean 1) layout.flag
        (if (layout.comparisonLayout wide).carryValues (-threshold) computed width then
          layout.flag.flip computed else computed)) = _
    rw [comparisonFlagCnot_mask, mask]
    by_cases below : active && decide ((layout.sourceWord state).toNat < threshold.toNat)
    · rw [if_pos below, if_pos below, activePairGates_flag_flip, activePairGates_twice]
    · rw [if_neg below, if_neg below, activePairGates_twice]

/-- The compiler realizes the same literal native word before its clean-subspace specialization. -/
lemma comparisonProgram_realizes_fold (layout : Layout encoding width) (wide : 2 ≤ width)
    (threshold : BitVec width) (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes encoding
      (layout.comparisonProgram wide threshold physical oracles) environment
      (stepList (layout.comparisonGates wide threshold)) :=
  realizesList physical oracles _ environment

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout
