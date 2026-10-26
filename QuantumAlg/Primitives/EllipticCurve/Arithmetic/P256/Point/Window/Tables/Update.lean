/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Tables.Selection
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Effect
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.State.Update
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Normal
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Address.Congruence

/-!
# The original complete table row survives the chronological point updates

Every numerical word setter, actual enable toggle and genuine normal
toggle retains the original current digit. Consequently all six real
queries select the same complete group-table row. These are readout laws
for the existing physical label, with no new executable instructions.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

noncomputable section

namespace Tables

open EncodedBit.WindowLookup

/-- Equal original digit readouts give the same full top-plus-address table row. -/
lemma selectedRow_eq_of_digit (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (first second : Raw)
    (reads : ∀ index, (Enable.digitBit stream width bounded index).get first =
      (Enable.digitBit stream width bounded index).get second) :
    selectedRow stream width bounded first = selectedRow stream width bounded second := by
  have root : (streamBit stream).get first = (streamBit stream).get second := reads 0
  have address := (selector stream width bounded).addressLabelAt_congr first second
    (fun index => reads index.succ) width 0 (by omega) 0 (by omega)
  unfold selectedRow
  change RuntimeTable.index ((streamBit stream).get first) _ =
    RuntimeTable.index ((streamBit stream).get second) _
  rw [root, address]

/-- Every original numerical word replacement keeps the whole actual table row. -/
lemma selectedRow_setWord (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (port : WordPort) (value : Word) (state : Raw) :
    selectedRow stream width bounded (resultSetConstant (resultWord port) value state) =
      selectedRow stream width bounded state :=
  selectedRow_eq_of_digit stream width bounded _ _
    (fun index => resultSetConstant_digit port value state stream width bounded index)

/-- The actual live-enable preparation and clearing retain the original selected row. -/
lemma selectedRow_enable (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) (state : Raw) :
    selectedRow stream width bounded (Enable.step stream width bounded state) =
      selectedRow stream width bounded state :=
  selectedRow_eq_of_digit stream width bounded _ _
    (fun index => Enable.step_digit stream width bounded index state)

/-- Preparing or clearing genuine N retains both stream roles and the original full address. -/
lemma selectedRow_normal (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) (state : Raw) :
    selectedRow stream width bounded (Chain.Normal.step state) =
      selectedRow stream width bounded state := by
  apply selectedRow_eq_of_digit
  intro index
  apply Chain.Normal.step_other
  intro same
  have positions := congrArg Fin.val same
  rw [normalBit_wire, Enable.digitBit_wire] at positions
  split_ifs at positions <;> omega

end Tables

namespace QueryInsertion

open EncodedBit.WindowLookup

/-- The actual ordinary or exceptional enable survives any separate numerical word result. -/
lemma querySelected_setWord (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (exceptional : Bool) (port : WordPort) (value : Word) (state : Raw) :
    querySelected stream width bounded exceptional
        (resultSetConstant (resultWord port) value state) =
      querySelected stream width bounded exceptional state := by
  simp only [querySelected, resultSetConstant_digit, resultSetConstant_normal]

end QueryInsertion

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
