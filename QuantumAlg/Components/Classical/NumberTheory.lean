/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.NumberTheory.GCD
public import QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.Public.Correctness
public import QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.Retained.Resources
public import QuantumAlg.Components.Classical.NumberTheory.Checked
public import QuantumAlg.Components.Classical.NumberTheory.IntegerSqrt
public import QuantumAlg.Components.Classical.NumberTheory.Nat.ModCheck
public import QuantumAlg.Components.Classical.NumberTheory.Nat.Sqrt
public import QuantumAlg.Components.Classical.NumberTheory.Nat.Sub
public import QuantumAlg.Components.Classical.NumberTheory.SignedWord
public import QuantumAlg.Components.Classical.NumberTheory.SignedWord.Classification
public import QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv

/-!
# Native fixed-width number theory

Total GCD, bounded signed extended GCD, checked inversion and integer
arithmetic share the current circuit interpreter and independent pure models.
-/
