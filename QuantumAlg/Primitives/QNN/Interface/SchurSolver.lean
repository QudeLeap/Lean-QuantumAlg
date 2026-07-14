/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.Algebras.PauliSchurFamily

/-!
# Compatibility wrapper for the Pauli-family Schur solver

The Pauli-specific Schur-discharge implementation now lives with the algebra-specific QNN modules in
`QuantumAlg.Primitives.QNN.Algebras.PauliSchurFamily`. This module preserves the older public import
path.
-/

@[expose] public section

namespace QuantumAlg

/-- Compatibility spelling for the old `SchurSolver` helper. Use `omega4_self_zero` in new code. -/
theorem omega4_self (a : Fin 4) : omega4 a a = 0 :=
  omega4_self_zero a

/-- Compatibility spelling for the old `SchurSolver` helper. Use `xor4_zero_right` in new code. -/
theorem xor4_zero (a : Fin 4) : xor4 a 0 = a :=
  xor4_zero_right a

/-- Compatibility spelling for the old `SchurSolver` helper. Use `pauliXor_zero_right` in new code.
-/
theorem pauliXor_zero {n : ℕ} (s : Fin n → Fin 4) : pauliXor s 0 = s :=
  pauliXor_zero_right s

end QuantumAlg
