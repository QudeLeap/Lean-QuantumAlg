/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Forward.Correctness
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Reverse.Correctness
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Coefficient.Correctness

/-!
# The actual single XGCD coefficient initializes the decreasing batch invariant

Nonzero original denominators make the proved actual prefix product a unit.
Its canonical actual scalar word identifies the same raw XGCD coefficient
with that product's inverse. All original C and D entries survive the real
coefficient scope. No independent inverse is supplied to the runtime code.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}

/-- The actual paid coefficient, on its original returned Store, prepares every reverse premise. -/
lemma ForwardInvariant.after_coefficient (frame : BatchFrame ctx width length)
    (spec : ModulusSpec width) [Fact spec.modulus.Prime]
    (environment : model.Environment) (original current : Store ctx)
    (values : Nat → ZMod spec.modulus) (count : Nat)
    (before : ForwardInvariant frame spec original values count current)
    (nonzero : ∀ position < count, values position ≠ 0)
    (represented : ∀ index : Fin length, 1 ≤ index.val → index.val ≤ count →
      ((original.read (rowRead frame.denominators index)).toNat : ZMod spec.modulus) =
        values (index.val - 1))
    (inverseModulusFree : frame.work.inverse.key ∉ frame.modulus.storageKeys)
    (hidden : model.HiddenState) :
    ReverseInvariant frame spec values count 0
      (Field.Native.coefficientIntoWordStep (environment := environment) spec
        (wordRead frame.work.product) frame.work.inverse (current, hidden)).1.1 := by
  let _ : NeZero spec.modulus := ⟨Nat.ne_of_gt (modulusSpec_modulus_pos spec)⟩
  have representedProduct : (current.read (wordRead frame.work.product)).toNat =
      (BatchInverse.prefixProduct values count).val := by
    have actual := congrArg ZMod.val before.product
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt before.productCanonical] at actual
    exact actual
  have productUnit : IsUnit (BatchInverse.prefixProduct values count) :=
    isUnit_iff_ne_zero.mpr (BatchInverse.prefixProduct_ne_zero values count nonzero)
  constructor
  · exact Nat.zero_le _
  · exact (Field.Native.coefficientIntoWord_read_other (environment := environment)
      spec (wordRead frame.work.product) frame.work.inverse frame.modulus inverseModulusFree
      current hidden).trans before.modulus
  · intro index positive within
    have kept := Field.Native.coefficientIntoWord_read_other (environment := environment)
      spec (wordRead frame.work.product) frame.work.inverse (rowRead frame.prefixes index)
      (by
        change frame.work.inverse.key ∉ [frame.prefixes.key]
        simpa only [List.mem_singleton] using word_array_key_ne frame.work.inverse frame.prefixes)
      current hidden
    rw [kept]
    exact before.prefixes index positive within
  · intro index positive within
    have kept := Field.Native.coefficientIntoWord_read_other (environment := environment)
      spec (wordRead frame.work.product) frame.work.inverse (rowRead frame.denominators index)
      (by
        change frame.work.inverse.key ∉ [frame.denominators.key]
        simpa only [List.mem_singleton] using
          word_array_key_ne frame.work.inverse frame.denominators) current hidden
    rw [kept, before.denominators index, if_pos (by omega)]
    exact represented index positive within
  · simpa only [Nat.sub_zero, Field.Native.coefficientRead, wordRead] using
      Field.Native.fieldCoefficient_output_inverse (environment := environment)
        spec (wordRead frame.work.product) frame.work.inverse current hidden
        (BatchInverse.prefixProduct values count) representedProduct productUnit
  · intro index positive within consumed
    omega

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame
