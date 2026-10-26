/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Reverse.Preservation
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Arithmetic
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Invariant
import all QuantumAlg.Util.Classical.Modular.BatchInverse

/-!
# Exact actual decreasing batch-inverse pass

The chronological invariant records original prefixes, unconsumed original
denominators, already overwritten canonical inverse rows, and the inverse
of the remaining prefix product. Each actual step consumes its original
denominator before overwriting it. No per-row inverse operation is added.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular

noncomputable section

section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}

/-- Complete field meaning of the actual in-place decreasing batch record. -/
structure ReverseInvariant (frame : BatchFrame ctx width length) (spec : ModulusSpec width)
    [Fact spec.modulus.Prime] (values : Nat → ZMod spec.modulus)
    (count processed : Nat) (current : Store ctx) : Prop where
  processedLe : processed ≤ count
  modulus : current.read frame.modulus = .unsignedWord spec.extendedWord
  prefixes : ∀ index : Fin length, 1 ≤ index.val → index.val ≤ count →
    ((current.read (rowRead frame.prefixes index)).toNat : ZMod spec.modulus) =
      BatchInverse.prefixProduct values (index.val - 1)
  denominators : ∀ index : Fin length, 1 ≤ index.val → index.val ≤ count →
    ((current.read (rowRead frame.denominators index)).toNat : ZMod spec.modulus) =
      if index.val ≤ count - processed then values (index.val - 1)
      else (values (index.val - 1))⁻¹
  inverse : ((current.read (wordRead frame.work.inverse)).toNat : ZMod spec.modulus) =
    (BatchInverse.prefixProduct values (count - processed))⁻¹
  canonical : ∀ index : Fin length, 1 ≤ index.val → index.val ≤ count →
    count - processed < index.val →
      (current.read (rowRead frame.denominators index)).toNat < spec.modulus

end

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}

/-- The actual two multiplies and C overwrite advance the complete decreasing invariant. -/
lemma ReverseInvariant.advance (frame : BatchFrame ctx width length) (spec : ModulusSpec width)
    [Fact spec.modulus.Prime] (values : Nat → ZMod spec.modulus) {count processed : Nat}
    (index : Fin length) (indexAt : index.val = count - processed) (next : processed < count)
    (denominatorModulusFree : frame.denominators.key ∉ frame.modulus.storageKeys)
    (inverseModulusFree : frame.work.inverse.key ∉ frame.modulus.storageKeys)
    (temporaryModulusFree : frame.work.temporary.key ∉ frame.modulus.storageKeys)
    (nonzero : ∀ position < count, values position ≠ 0)
    (current : Store ctx) (before : ReverseInvariant frame spec values count processed current) :
    ReverseInvariant frame spec values count (processed + 1)
      (frame.reverseRecord (model := model) index current).1 := by
  let remaining := count - processed
  have positive : 0 < remaining := by dsimp only [remaining]; omega
  have indexPositive : 1 ≤ index.val := by omega
  have indexBound : index.val ≤ count := by omega
  have expanded : BatchInverse.prefixProduct values remaining =
      BatchInverse.prefixProduct values (remaining - 1) * values (remaining - 1) := by
    calc
      BatchInverse.prefixProduct values remaining =
          BatchInverse.prefixProduct values ((remaining - 1) + 1) := by
        congr 1
        omega
      _ = _ := rfl
  have reduction := BatchInverse.reverse_step
    (BatchInverse.prefixProduct values (remaining - 1)) (values (remaining - 1))
    (BatchInverse.prefixProduct_ne_zero values (remaining - 1)
      (fun position earlier => nonzero position (by dsimp only [remaining] at *; omega)))
    (nonzero (remaining - 1) (by dsimp only [remaining] at *; omega))
  rw [← expanded] at reduction
  have currentDenominator := before.denominators index indexPositive indexBound
  rw [if_pos (by omega)] at currentDenominator
  have selected :
      (((frame.reverseRecord (model := model) index current).1).read
        (rowRead frame.denominators index)).toNat =
      (multiplyValue (current.read (wordRead frame.work.inverse))
        (current.read (rowRead frame.prefixes index))
        (.unsignedWord spec.extendedWord)).toNat := by
    rw [frame.reverseRecord_read_denominator, before.modulus]
  have selectedField :
      ((((frame.reverseRecord (model := model) index current).1).read
        (rowRead frame.denominators index)).toNat : ZMod spec.modulus) =
        (values (remaining - 1))⁻¹ := by
    rw [selected, multiplyValue_cast, before.inverse,
      before.prefixes index indexPositive indexBound, indexAt]
    exact reduction.1
  have running :
      ((((frame.reverseRecord (model := model) index current).1).read
        (wordRead frame.work.inverse)).toNat : ZMod spec.modulus) =
        (BatchInverse.prefixProduct values (remaining - 1))⁻¹ := by
    rw [frame.reverseRecord_read_inverse index temporaryModulusFree current, before.modulus,
      multiplyValue_cast, before.inverse, currentDenominator, indexAt]
    exact reduction.2
  constructor
  · omega
  · exact (reverseRecord_read_other frame index frame.modulus denominatorModulusFree
      inverseModulusFree temporaryModulusFree current).trans before.modulus
  · intro observed observedPositive observedBound
    rw [frame.reverseRecord_read_prefix]
    exact before.prefixes observed observedPositive observedBound
  · intro observed observedPositive observedBound
    by_cases same : observed = index
    · subst observed
      rw [selectedField, if_neg (by omega), indexAt]
    · rw [frame.reverseRecord_read_other_denominator index observed same current,
        before.denominators observed observedPositive observedBound]
      have different : observed.val ≠ index.val := fun equal => same (Fin.ext equal)
      by_cases original : observed.val ≤ count - processed
      · rw [if_pos original, if_pos (by omega)]
      · rw [if_neg original, if_neg (by omega)]
  · have shifted : count - (processed + 1) = remaining - 1 := by
      dsimp only [remaining]
      omega
    rw [shifted]
    exact running
  · intro observed observedPositive observedBound consumed
    by_cases same : observed = index
    · subst observed
      rw [selected]
      exact multiplyValue_canonical spec _ _
    · rw [frame.reverseRecord_read_other_denominator index observed same current]
      apply before.canonical observed observedPositive observedBound
      have different : observed.val ≠ index.val := fun equal => same (Fin.ext equal)
      omega

/-- The full real decreasing pass replaces every positive denominator by its canonical inverse. -/
lemma reversePassRecord_values (frame : BatchFrame ctx width length) (spec : ModulusSpec width)
    [Fact spec.modulus.Prime] (count : Nat) (fits : count < length)
    (denominatorModulusFree : frame.denominators.key ∉ frame.modulus.storageKeys)
    (inverseModulusFree : frame.work.inverse.key ∉ frame.modulus.storageKeys)
    (temporaryModulusFree : frame.work.temporary.key ∉ frame.modulus.storageKeys)
    (values : Nat → ZMod spec.modulus) (nonzero : ∀ position < count, values position ≠ 0)
    (store : Store ctx) (initial : ReverseInvariant frame spec values count 0 store) :
    ReverseInvariant frame spec values count count
      (frame.reversePassRecord (model := model) count fits store).1 := by
  exact Circuit.forRangeStoreRecord_invariant count
    (fun index => frame.reverseStep (model := model) ⟨count - index.val, by omega⟩)
    (fun index => frame.reverseRecord (model := model) ⟨count - index.val, by omega⟩)
    (fun processed current => ReverseInvariant frame spec values count processed current)
    (fun index current established => ReverseInvariant.advance frame spec values
      ⟨count - index.val, by omega⟩ rfl index.isLt denominatorModulusFree inverseModulusFree
      temporaryModulusFree nonzero current established) store initial

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame
