/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Total

/-!
# Actual inverse-row values of the original total batch record

Every visited positive C row receives the inverse of its original field
value. A requested visited row itself proves the batch is nonempty. The
true empty branch remains identity and imposes no accumulator or old
working-word postcondition.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}

/-- Every positive row visited by the original conditional batch has its canonical inverse. -/
lemma valueRecord_denominator_inverse (frame : BatchFrame ctx width length)
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
    ((frame.valueRecord spec count fits environment before).1.1.read
      (rowRead frame.denominators index)).toNat = ((values (index.val - 1))⁻¹).val := by
  have nonempty : count ≠ 0 := by omega
  rw [frame.valueRecord_nonempty_state spec count fits environment before nonempty]
  exact frame.nonemptyValueRecord_denominator_inverse spec environment count fits
    prefixModulusFree productModulusFree denominatorModulusFree inverseModulusFree
    temporaryModulusFree values before loaded one nonzero represented index positive within

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame
