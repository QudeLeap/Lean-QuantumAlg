/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.ShorStyle.Parameters
public import Mathlib.Data.Nat.Choose.Basic
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Parameters

/-!
# Independent width-only scalar ceilings of the declared Shor machine

Every formula depends only on the original modulus and symbolic number of
complete attempts. Conservative native branch capacities are added instead
of evaluating bit tables, operands, modular exponentiation or quantum states.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Scalar

/-- One physical exponent/work bank of binary systems. -/
public def qubits (N : Nat) : Nat := 3 * modulusBits N

/-- Hadamards, native inverse Fourier gates and every reset correction. -/
public def roundSingleQubit (N : Nat) : Nat :=
  2 * phaseBits N + 3 * (phaseBits N).choose 2 + qubits N

/-- Native inverse-Fourier controlled phases and final swaps. -/
public def roundCnot (N : Nat) : Nat :=
  2 * (phaseBits N).choose 2 + 3 * (phaseBits N / 2)

/-- Actual phase readout and one full physical bank reset. -/
public def roundMeasurements (N : Nat) : Nat := phaseBits N + qubits N

/-- Scalar capacity for all fixed continued-fraction visits and both selected branches. -/
public def orderRecoveryEvents (N : Nat) : Nat :=
  4 * (phaseBits N + 1) + 4 +
    2 * (phaseBits N + 1) * (2 * modulusBits N + 19 + 6 * (phaseBits N + 1))

/-- The two native modular half-power and GCD-selection stages, including every constant load. -/
public def reductionEvents (N : Nat) : Nat :=
  2 * modulusBits N + 6 + 6 * (phaseBits N + 1) + 28 * (modulusBits N + 1) + 40

/-- Preserve the original known even-modulus exception and all non-exceptional recovery work. -/
public def recoveryEvents (N : Nat) : Nat :=
  if 2 < N ∧ Even N then 2 * modulusBits N + 3
  else orderRecoveryEvents N + reductionEvents N + 9

/-- Full sampled preparation, readout packing, recovery and first-success feedback. -/
public def roundClassicalOperations (N : Nat) : Nat :=
  44 * modulusBits N + 169 + recoveryEvents N

/-- The same conservative complete classical allowance has a simple modulus-width polynomial. -/
lemma roundClassicalOperations_polynomial (N : Nat) :
    roundClassicalOperations N =
      if 2 < N ∧ Even N then 46 * modulusBits N + 172
      else 56 * (modulusBits N) ^ 2 + 222 * modulusBits N + 316 := by
  unfold roundClassicalOperations recoveryEvents orderRecoveryEvents reductionEvents phaseBits
  split <;> ring

/-- Both scalar classical capacities include persistent heads, retained results and scratch. -/
public def classicalBits (N count : Nat) : Nat :=
  count * (22 * modulusBits N + 1) + 70 * modulusBits N + 42

/-- Both genuine boundary instructions coexist with every complete original attempt. -/
public def classicalOperations (N count : Nat) : Nat :=
  count * roundClassicalOperations N + 2

/-- Complete quantum and classical native event allowance for one original attempt. -/
public def roundEvents (N : Nat) : Nat :=
  roundSingleQubit N + roundCnot N + 1 + roundMeasurements N + roundClassicalOperations N

/-- Chronological depth additionally counts all requested complete attempts and the final pack. -/
public def wholeRunDepth (N count : Nat) : Nat := qubits N + count * roundEvents N + 2

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Scalar
