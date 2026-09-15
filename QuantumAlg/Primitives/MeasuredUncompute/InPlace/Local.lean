/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Division
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Multiplication
import all QuantumAlg.Core.Execution.Local.MeasurementSequence

/-!
# Reusable measured arithmetic bodies retain one actual runtime context

The original division and multiplication bodies use only their present quantum
words, EEA history and finite measurement-result cells. They can therefore be
placed inside an actual disjoint runtime frame without repeating the standalone
preparation or allocation [LYL+26, sec_point_add/sec_point_add.tex:45-122].

These certificates inspect the same original circuit syntax. They do not
change either arithmetic schedule, add a caller domain condition, or assert
restoration merely from the absence of allocation.
-/

namespace QuantumAlg.MeasuredUncompute

private theorem numeratorReset_isLocal (width : Nat) :
    (NumeratorReset.code width).IsLocal :=
  ⟨trivial, ⟨Circuit.measurementSequence_isLocal (NumeratorMeasurement.readouts width),
    fun _ => trivial⟩⟩

/-- The complete division body reuses its already present words and measurement cells. -/
theorem inPlaceDivision_body_isLocal (modulus : Nat) (prime : Nat.Prime modulus) :
    (InPlaceDivision.body modulus prime).IsLocal :=
  ⟨trivial, ⟨trivial, ⟨numeratorReset_isLocal modulus.size,
    ⟨trivial, ⟨fun _ => trivial, trivial⟩⟩⟩⟩⟩

/-- The complete multiplication body reuses exactly the same actual live context. -/
theorem inPlaceMultiplication_body_isLocal (modulus : Nat) (prime : Nat.Prime modulus) :
    (InPlaceMultiplication.body modulus prime).IsLocal :=
  ⟨trivial, ⟨numeratorReset_isLocal modulus.size,
    ⟨trivial, ⟨fun _ => trivial, ⟨trivial, trivial⟩⟩⟩⟩⟩

end QuantumAlg.MeasuredUncompute
