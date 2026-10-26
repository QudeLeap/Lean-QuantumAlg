/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Values
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Frame.Columns
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Lookup

/-!
# Original constructed table values at the actual full runtime address

The runtime loader reads the same physical column and the complete address,
including its original top bit. A certified actual returned Store therefore
gives the original canonical group-table word at that address. These are
read identities; no executable table generation or arithmetic is replaced.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve
open EncodedBit.WindowLookup

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width addressWidth : Nat}
    {curve : ClassicalAlgorithms.EllipticCurve.CurveSpec width}
    {frame : TableFrame ctx width (2 ^ (addressWidth + 1))}
    {point : Point curve} {store : Store ctx}

/-- The genuine runtime full-address read is the certified original group-table word. -/
lemma TableValue.runtimeTable_value (values : TableValue curve frame point store)
    (column : Fin 5) (top : Bool) (address : Fin (2 ^ addressWidth)) :
    RuntimeTable.tableValue
        (store.read (.storage (frame.arrays.column column).toCStorageRef)) top address =
      RuntimeTable.wordEncoding
        (pointFiveWords curve ((RuntimeTable.index top address).val • point) column) := by
  change RuntimeTable.wordEncoding
      (store.read (rowRead (frame.finishColumns column) (RuntimeTable.index top address))) = _
  rw [values (RuntimeTable.index top address) column]

/-- Every selected original group-table word is canonical in its original field. -/
lemma TableValue.runtimeTable_canonical (values : TableValue curve frame point store)
    (column : Fin 5) (top : Bool) (address : Fin (2 ^ addressWidth)) :
    (RuntimeTable.tableValue
      (store.read (.storage (frame.arrays.column column).toCStorageRef)) top address).val <
        curve.field.modulus := by
  let _ : NeZero curve.field.modulus :=
    ⟨Nat.ne_of_gt (ClassicalAlgorithms.Modular.modulusSpec_modulus_pos curve.field)⟩
  rw [values.runtimeTable_value]
  change (pointFiveWords curve ((RuntimeTable.index top address).val • point) column).toNat < _
  rw [pointFiveWords_toNat]
  exact ZMod.val_lt _

/-- The actual full-address word represents exactly the independent original field column. -/
lemma TableValue.runtimeTable_field (values : TableValue curve frame point store)
    (column : Fin 5) (top : Bool) (address : Fin (2 ^ addressWidth)) :
    ((RuntimeTable.tableValue
      (store.read (.storage (frame.arrays.column column).toCStorageRef)) top address).val :
        ZMod curve.field.modulus) =
      pointFiveColumns curve ((RuntimeTable.index top address).val • point) column := by
  rw [values.runtimeTable_value]
  change ((pointFiveWords curve ((RuntimeTable.index top address).val • point) column).toNat :
    ZMod curve.field.modulus) = _
  rw [pointFiveWords_toNat, ZMod.natCast_zmod_val]

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
