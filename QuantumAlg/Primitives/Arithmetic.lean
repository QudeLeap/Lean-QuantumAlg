/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.Arithmetic.BitSlice
import all QuantumAlg.Primitives.Arithmetic.Comparator
import all QuantumAlg.Primitives.Arithmetic.PlainAdder
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.Physical
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.Schedule
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.Schedule.ZeroTestValue
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.StructuredCircuit
import all QuantumAlg.Primitives.Arithmetic.CleanCircuit

/-!
# Reversible arithmetic primitives

This module re-exports reusable non-modular reversible-arithmetic primitives:
bit-slice base-gate blocks, comparator schedule shells and their cleanup-aware
fixed-layout circuit, plain-adder interfaces, folded plain-adder schedule
shells, and plain-adder structured same-Circuit witness interfaces.  Modular
arithmetic units are re-exported by
`QuantumAlg.Primitives.MAU`.
-/

section

end
