/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Quantum.Construction
import all QuantumAlg.Algorithms.OrderFinding.AccessCircuit
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Execution.Preparation

/-!
# Native Shor bank identities and initial seed

The original phase and power positions precede the one shared arithmetic
auxiliary. One actual basis preparation sets phase zero, power one and
auxiliary zero. Every physical system has dimension two; no hidden quantum
storage is introduced by the binary coordinate map.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeQuantum

noncomputable section

/-- The ordered physical phase, power and auxiliary wires, all dimension two. -/
def runtimeLayout (N : Nat) : QuantumLayout (totalQubits N) :=
  (OrderFinding.layout (phaseBits N) (modulusBits N + modulusBits N)).toQuantumLayout

/-- The whole-bank source seed contains exactly the unchanged zero phase and unit power. -/
def seedLabel (N : Nat) : Fin (2 ^ totalQubits N) :=
  (MAU.Exponentiation.Gidney.encoding (phaseBits N) (modulusBits N)).encode (0, 1, 0)

/-- The single actual native preparation uses the explicit binary labels of those same wires. -/
def seedPreparation (N : Nat) : BasisPreparation (runtimeLayout N) :=
  ⟨(OrderFinding.layout (phaseBits N) (modulusBits N + modulusBits N)).binaryIndexEquiv.symm
    (seedLabel N)⟩

/-- Every physical system in the bank is a qubit, including in total low-width definitions. -/
theorem runtimeLayout_dimension (N : Nat) (wire : Fin (totalQubits N)) :
    ((runtimeLayout N).wire wire).dimension = 2 := rfl

/-- The source bank uses each consecutive physical identity once. -/
theorem runtimeLayout_identities (N : Nat) :
    (runtimeLayout N).identities = List.range (totalQubits N) :=
  (QubitLayout.toQuantumLayout_identities
    (OrderFinding.layout (phaseBits N) (modulusBits N + modulusBits N))).trans
    (OrderFinding.layout_systemIdx (phaseBits N) (modulusBits N + modulusBits N))

/-- Exact dimension-indexed capacity of the bank declared for the single preparation. -/
theorem runtimeLayout_dimensionCount (N : Nat) (dimension : ℕ+) :
    (runtimeLayout N).dimensionCount dimension =
      if (2 : ℕ+) = dimension then 4 * modulusBits N else 0 := by
  change QuantumLayout.dimensionCount
    (OrderFinding.layout (phaseBits N) (modulusBits N + modulusBits N)).toQuantumLayout
    dimension = _
  rw [QubitLayout.toQuantumLayout_dimensionCount]
  exact congrArg (fun count => if (2 : ℕ+) = dimension then count else 0)
    (totalQubits_eq_four_mul N)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeQuantum
