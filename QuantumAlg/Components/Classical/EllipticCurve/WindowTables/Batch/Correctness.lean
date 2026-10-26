/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Record
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Initialization
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Prepared

/-!
# Complete actual batch-inverse values

The real initializer, forward record, single actual XGCD coefficient and
decreasing overwrite record share their actual intermediate Stores. The
resulting canonical inverse entries are attached to that same complete
interpreter record; no row value or inverse enters the code constructor.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}

/-- Complete field invariant of the actual original nonempty branch's returned Store. -/
lemma nonemptyValueRecord_values (frame : BatchFrame ctx width length) (spec : ModulusSpec width)
    [Fact spec.modulus.Prime] (environment : model.Environment)
    (count : Nat) (fits : count < length)
    (prefixModulusFree : frame.prefixes.key ∉ frame.modulus.storageKeys)
    (productModulusFree : frame.work.product.key ∉ frame.modulus.storageKeys)
    (denominatorModulusFree : frame.denominators.key ∉ frame.modulus.storageKeys)
    (inverseModulusFree : frame.work.inverse.key ∉ frame.modulus.storageKeys)
    (temporaryModulusFree : frame.work.temporary.key ∉ frame.modulus.storageKeys)
    (values : Nat → ZMod spec.modulus) (before : Store ctx × model.HiddenState)
    (loaded : before.1.read frame.modulus = .unsignedWord spec.extendedWord)
    (one : (before.1.read frame.one).toNat = 1)
    (nonzero : ∀ position < count, values position ≠ 0)
    (represented : ∀ index : Fin length, 1 ≤ index.val → index.val ≤ count →
      ((before.1.read (rowRead frame.denominators index)).toNat : ZMod spec.modulus) =
        values (index.val - 1)) :
    ReverseInvariant frame spec values count count
      (frame.nonemptyValueRecord (environment := environment) spec count fits before).1.1 := by
  let initialized := frame.initializeStore before.1
  let forward := frame.forwardPassRecord (model := model) count fits initialized
  let inverted := Field.Native.coefficientIntoWordStep (environment := environment) spec
    (wordRead frame.work.product) frame.work.inverse (forward.1, before.2)
  have loadedAfter : initialized.read frame.modulus = .unsignedWord spec.extendedWord :=
    (frame.initializeStore_read_other frame.modulus productModulusFree before.1).trans loaded
  have productOne : (initialized.read (wordRead frame.work.product)).toNat = 1 :=
    (frame.initializeStore_read_product before.1).trans one
  have originalRows (index : Fin length) :
      initialized.read (rowRead frame.denominators index) =
        before.1.read (rowRead frame.denominators index) :=
    frame.initializeStore_read_other (rowRead frame.denominators index)
      (by
        change frame.work.product.key ∉ [frame.denominators.key]
        simpa only [List.mem_singleton] using
          word_array_key_ne frame.work.product frame.denominators) before.1
  have representedAfter : ∀ index : Fin length, 1 ≤ index.val → index.val ≤ count →
      ((initialized.read (rowRead frame.denominators index)).toNat : ZMod spec.modulus) =
        values (index.val - 1) := by
    intro index positive within
    rw [originalRows]
    exact represented index positive within
  have forwarded : ForwardInvariant frame spec initialized values count forward.1 :=
    frame.forwardPassRecord_values spec count fits prefixModulusFree productModulusFree
      values initialized loadedAfter productOne (fun index => by
        have bounded := index.isLt
        have actual := representedAfter ⟨index.val + 1, by omega⟩
          (by change 1 ≤ index.val + 1; omega)
          (by change index.val + 1 ≤ count; omega)
        simpa only [Nat.add_sub_cancel] using actual)
  have prepared : ReverseInvariant frame spec values count 0 inverted.1.1 :=
    forwarded.after_coefficient frame spec environment initialized forward.1 values count
      nonzero representedAfter inverseModulusFree before.2
  have completed := frame.reversePassRecord_values spec count fits denominatorModulusFree
    inverseModulusFree temporaryModulusFree values nonzero inverted.1.1 prepared
  exact completed

/-- Every positive actual C row is the canonical inverse of its original represented value. -/
lemma nonemptyValueRecord_denominator_inverse (frame : BatchFrame ctx width length)
    (spec : ModulusSpec width) [Fact spec.modulus.Prime] (environment : model.Environment)
    (count : Nat) (fits : count < length)
    (prefixModulusFree : frame.prefixes.key ∉ frame.modulus.storageKeys)
    (productModulusFree : frame.work.product.key ∉ frame.modulus.storageKeys)
    (denominatorModulusFree : frame.denominators.key ∉ frame.modulus.storageKeys)
    (inverseModulusFree : frame.work.inverse.key ∉ frame.modulus.storageKeys)
    (temporaryModulusFree : frame.work.temporary.key ∉ frame.modulus.storageKeys)
    (values : Nat → ZMod spec.modulus) (before : Store ctx × model.HiddenState)
    (loaded : before.1.read frame.modulus = .unsignedWord spec.extendedWord)
    (one : (before.1.read frame.one).toNat = 1)
    (nonzero : ∀ position < count, values position ≠ 0)
    (represented : ∀ index : Fin length, 1 ≤ index.val → index.val ≤ count →
      ((before.1.read (rowRead frame.denominators index)).toNat : ZMod spec.modulus) =
        values (index.val - 1))
    (index : Fin length) (positive : 1 ≤ index.val) (within : index.val ≤ count) :
    ((frame.nonemptyValueRecord (environment := environment) spec count fits before).1.1.read
      (rowRead frame.denominators index)).toNat = ((values (index.val - 1))⁻¹).val := by
  let _ : NeZero spec.modulus := ⟨Nat.ne_of_gt (modulusSpec_modulus_pos spec)⟩
  have actual := nonemptyValueRecord_values frame spec environment count fits prefixModulusFree
    productModulusFree denominatorModulusFree inverseModulusFree temporaryModulusFree
    values before loaded one nonzero represented
  have fieldValue := actual.denominators index positive within
  rw [Nat.sub_self, if_neg (by omega)] at fieldValue
  have canonical := actual.canonical index positive within (by omega)
  have value := congrArg ZMod.val fieldValue
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt canonical] at value
  exact value

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame
