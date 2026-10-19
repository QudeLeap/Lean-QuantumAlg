/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Classical.Value
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Model-relative classical native operations

A native declaration fixes each token's operand shapes, probability semantics
and accounting coordinate. Deterministic instructions use point distributions.
Randomized instructions have normalized finite-valued outcomes; their result
distribution is part of the declaration, not an argument supplied at a call.

These declarations do not place storage, grant oracle access or attach a bit
complexity to a word operation. Actual placement and interpretation are separate
boundaries using the same declared token.
-/

namespace QuantumAlg

/-- A classical native language with fixed typed semantics and resource coordinates. -/
public structure ClassicalOpModel where
  /-- Actual native-operation instances, including their semantic parameters. -/
  Token : Type
  /-- Decidable coordinates may group several parameterized operations. -/
  Coordinate : Type
  /-- Counts require equality of coordinates, not of semantic parameters. -/
  coordinateDecidableEq : DecidableEq Coordinate
  /-- Operand shape fixed by the native token. -/
  inputShape : Token → CShape
  /-- Result shape fixed by the same token. -/
  outputShape : Token → CShape
  /-- The declaration's normalized result distribution for the actual operands. -/
  evaluate : (token : Token) → (inputShape token).Value → PMF (outputShape token).Value
  /-- The native coordinate emitted by one actual token occurrence. -/
  coordinate : Token → Coordinate

attribute [instance] ClassicalOpModel.coordinateDecidableEq

namespace ClassicalOpModel

/-- The empty native grant contains no executable tokens or native coordinates. -/
@[expose, implicit_reducible]
public def empty : ClassicalOpModel where
  Token := Empty
  Coordinate := Empty
  coordinateDecidableEq := inferInstance
  inputShape token := nomatch token
  outputShape token := nomatch token
  evaluate token := nomatch token
  coordinate token := nomatch token

/-- Declare deterministic native instructions through the same normalized semantics. -/
@[expose, implicit_reducible]
public noncomputable def deterministic (Token Coordinate : Type)
    (equality : DecidableEq Coordinate) (inputShape outputShape : Token → CShape)
    (evaluate : (token : Token) → (inputShape token).Value → (outputShape token).Value)
    (coordinate : Token → Coordinate) : ClassicalOpModel where
  Token := Token
  Coordinate := Coordinate
  coordinateDecidableEq := equality
  inputShape := inputShape
  outputShape := outputShape
  evaluate token input := PMF.pure (evaluate token input)
  coordinate := coordinate

/-- The empty declaration cannot supply a classical native instruction. -/
public lemma no_empty_classical_native_token (token : empty.Token) : False :=
  nomatch token

end ClassicalOpModel

end QuantumAlg
