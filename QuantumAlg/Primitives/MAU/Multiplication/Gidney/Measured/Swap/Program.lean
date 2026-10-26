/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Layout
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Fredkin

/-!
# Actual one-Toffoli-per-bit controlled exchange of the multiplication words

Every physical row is the same three-gate Fredkin decomposition on the
original global control and paired original source/target wires. All rows
remain sequential because the global control is shared
[G25, main.tex:354-360; VBE95, 9511018.tex:333-367].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open EncodedBit

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The actual native one-Toffoli exchange of one original source/target pair. -/
def swapRowGates (layout : Layout encoding width) (index : Fin width) :
    List (GateSpec encoding) :=
  fredkinGates layout.control (layout.source index) (layout.target index)
    (layout.wire_ne (by intro impossible; cases impossible))
    (layout.wire_ne (by intro impossible; cases impossible))
    (layout.wire_ne (by intro impossible; cases impossible))

/-- The actual native source-order exchange prefix, retaining all original physical systems. -/
def swapPrefixGates (layout : Layout encoding width) :
    (count : Nat) → count ≤ width → List (GateSpec encoding)
  | 0, _ => []
  | count + 1, bounded =>
      layout.swapPrefixGates count (by omega) ++ layout.swapRowGates ⟨count, by omega⟩

/-- The complete actual controlled word exchange. -/
def swapWordGates (layout : Layout encoding width) : List (GateSpec encoding) :=
  layout.swapPrefixGates width le_rfl

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
