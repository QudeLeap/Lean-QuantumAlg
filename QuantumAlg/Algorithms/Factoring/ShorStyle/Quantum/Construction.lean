/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Quantum.Parameters
import all QuantumAlg.Algorithms.OrderFinding.Construction
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Program

/-!
# Native Shor members on one shared multiplication bank

The original phase Hadamards precede the actual selected-power MAU program,
followed by the original inverse QFT on those same phase positions. The power
word starts at one and the shared multiplier auxiliary at zero. This avoids
an additional XOR-copy word in the surrounding order-finding computation;
the independent XOR-oracle primitive retains its own full contract.

The phase/target organization and the order-finding transforms are unchanged
[Sho95, source.tex:1183-1245]. The clean seeded-power action composes the
project's clean-auxiliary specialization of unit-inverse multiplication
[G17, paper.tex:186-211] with its increasing-bit power schedule.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeQuantum

noncomputable section

/-- The actual member contains source Hadamards, compiled modular power and source inverse QFT. -/
def program {N : Nat} (parameter : CShape.Value (ParameterShape (modulusBits N))) :
    UnitaryCircuit (Qubits (totalQubits N)) :=
  (OrderFinding.orderFindingPreparationCircuit (phaseBits N)
    (modulusBits N + modulusBits N)).seq
    ((MAU.Exponentiation.Gidney.program (phaseBits N) (modulusBits N)
      (modulus N) (selectedUnit parameter)).seq
      (OrderFinding.orderFindingReadoutCircuit (phaseBits N)
        (modulusBits N + modulusBits N)))

/-- Every selected native member uses the same actual phase, power and auxiliary positions. -/
theorem program_physicalIdx {N : Nat}
    (parameter : CShape.Value (ParameterShape (modulusBits N))) :
    (program parameter).physical_idx = List.range (totalQubits N) := by
  simp [program, UnitaryCircuit.seq, MAU.Exponentiation.Gidney.gidneyExponent_physical,
    totalQubits, two_mul]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeQuantum
