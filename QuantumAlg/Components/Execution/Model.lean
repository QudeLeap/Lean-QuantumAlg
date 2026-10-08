/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Model
public import QuantumAlg.Components.Classical.Model.BitWord
public import QuantumAlg.Components.GateModel

/-!
# Built-in combinations of classical and quantum operation declarations

Problems may choose arbitrary Core models. These convenience selections pair
the built-in width-indexed bit/word operations with a specified quantum gate
alphabet when needed. Classical and quantum oracle access remain independently
chosen, and both default to empty access.

Preparation in zero and computational Z measurement retain their fixed circuit
semantics. Word operations retain their actual widths; choosing this model does
not equate an arbitrary-width operation with a Boolean gate.
-/

namespace QuantumAlg.ExecutionModel

noncomputable section

/-- The built-in classical bit/word language, with only the supplied oracle access. -/
@[expose, implicit_reducible]
public def bitWordClassical (classicalOracles : ClassicalOracleModel := .empty) : ExecutionModel :=
  .classical BitWord.model classicalOracles

/-- Toffoli, CNOT and arbitrary single-qubit gates, with built-in classical processing. -/
@[expose, implicit_reducible]
public def algorithmDefault (oracles : OracleModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) : ExecutionModel :=
  .quantum AlgorithmGate.model oracles BitWord.model classicalOracles

/-- Exactly H, S, T and CNOT, with built-in classical processing and explicit oracle access. -/
@[expose, implicit_reducible]
public def cliffordTDefault (oracles : OracleModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) : ExecutionModel :=
  .quantum CliffordTGate.model oracles BitWord.model classicalOracles

end

end QuantumAlg.ExecutionModel
