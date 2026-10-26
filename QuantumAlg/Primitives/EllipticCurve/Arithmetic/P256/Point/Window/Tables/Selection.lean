/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Values.Lookup
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Selection

/-!
# Actual full-address selection from the original constructed group tables

The original current digit selects one complete row, including the top
address bit. Certified values belong to the actual returned Store of the
paid builder. No mathematical table substitutes for an executable read.
The address width remains symbolic, including width zero.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace Tables

noncomputable section

open Execution EncodedBit.WindowLookup ClassicalAlgorithms.EllipticCurve
open ClassicalRoutines.EllipticCurve.WindowTables

/-- Complete original runtime row selected by the genuine top and address bits. -/
def selectedRow (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Raw) : Fin (2 ^ (width + 1)) :=
  RuntimeTable.index (((selector stream width bounded).stack ⟨0, by omega⟩).get state)
    ((selector stream width bounded).addressLabelAt width 0 (by omega) 0 (by omega) state)

variable {ctx : RuntimeCtx .quantum} {stream : Fin 2} {width : Nat} {bounded : width ≤ 15}
    {curve : CurveSpec 256}
    {frame : TableFrame ctx 256 (2 ^ (width + 1))}
    {point : ClassicalAlgorithms.EllipticCurve.Point curve} {store : Store ctx}

/-- The original selected numerical word is the actual builder's canonical group-table word. -/
lemma selectedWord_value (values : TableFrame.TableValue curve frame point store)
    (column : Fin 5) (state : Raw) :
    QueryInsertion.selectedWord stream width bounded
        (RuntimeTable.tableValue
          (store.read (.storage (frame.arrays.column column).toCStorageRef))) state =
      RuntimeTable.wordEncoding
        (pointFiveWords curve ((selectedRow stream width bounded state).val • point) column) :=
  values.runtimeTable_value column _ _

/-- The true selected operand is canonical under the original modulus identity. -/
lemma selectedWord_canonical (sameModulus : curve.field.modulus = modulus)
    (values : TableFrame.TableValue curve frame point store) (column : Fin 5) (state : Raw) :
    Canonical (QueryInsertion.selectedWord stream width bounded
      (RuntimeTable.tableValue
        (store.read (.storage (frame.arrays.column column).toCStorageRef))) state) := by
  change (QueryInsertion.selectedWord stream width bounded _ state).val < modulus
  rw [← sameModulus]
  exact values.runtimeTable_canonical column _ _

/-- The same actual selected word represents its original field column at the complete row. -/
lemma selectedWord_field (values : TableFrame.TableValue curve frame point store)
    (column : Fin 5) (state : Raw) :
    ((QueryInsertion.selectedWord stream width bounded
      (RuntimeTable.tableValue
        (store.read (.storage (frame.arrays.column column).toCStorageRef))) state).val :
        ZMod curve.field.modulus) =
      pointFiveColumns curve ((selectedRow stream width bounded state).val • point) column :=
  values.runtimeTable_field column _ _

end

end Tables

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
