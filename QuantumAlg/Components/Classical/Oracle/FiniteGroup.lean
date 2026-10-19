/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Classical.Oracle
public import QuantumAlg.Core.Algorithm.ClassicalOp
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Fintype.Card

/-!
# Representation-independent finite-group accumulator oracle

The mathematical group element is persistent hidden service state. Callers
can reset it to the identity, square it, multiply it by a declaration-owned
right operand, or compare it with a declaration-owned value. Every query has
only a one-bit acknowledgement/result port, so this interface neither chooses
a binary encoding for group elements nor charges caller-visible bit storage
for them.

Reset is an explicit query. Initialization remains a separate problem-level
contract, and no ordinary query implicitly restarts the accumulator.
-/

namespace QuantumAlg.ClassicalFiniteGroupOracle

noncomputable section

universe u

variable (G : Type u) [Group G] [Fintype G]

/-- Actual cardinality of the supplied finite group, used only to seal
declaration-owned operands into a finite query language. -/
public def cardinality : ℕ+ := by
  letI : Nonempty G := ⟨1⟩
  exact ⟨Fintype.card G, Fintype.card_pos⟩

/-- Abstract finite labels for declaration-owned group constants. This is
query metadata and never a caller storage shape. -/
public def carrierEquiv : Fin (cardinality G) ≃ G :=
  (Equiv.swap 0 (Fintype.equivFin G 1)).trans (Fintype.equivFin G).symm

/-- Seal a mathematical group value into hidden oracle state. -/
@[expose] public def encode (value : G) : Fin (cardinality G) := (carrierEquiv G).symm value

/-- Interpret hidden oracle state as its mathematical group value. -/
@[expose] public def decode (state : Fin (cardinality G)) : G := carrierEquiv G state

@[simp] public lemma decode_encode (value : G) : decode G (encode G value) = value :=
  (carrierEquiv G).apply_symm_apply value

@[simp] public lemma encode_decode (state : Fin (cardinality G)) :
    encode G (decode G state) = state := (carrierEquiv G).symm_apply_apply state

@[simp] public lemma encode_inj {left right : G} :
    encode G left = encode G right ↔ left = right :=
  (carrierEquiv G).symm.injective.eq_iff

/-- Granted operations on one persistent hidden accumulator. -/
public inductive Query (cardinality : ℕ+) : Type where
  | reset
  | square
  | multiplyRight (right : Fin cardinality)
  | equals (right : Fin cardinality)

/-- Reset, group operations and equality remain separate query coordinates. -/
public inductive Coordinate where
  | reset
  | groupOperation
  | equalityTest
  deriving DecidableEq

/-- Query that multiplies the hidden accumulator on the right by one group value. -/
@[expose, implicit_reducible] public def multiplyRightQuery (right : G) : Query (cardinality G) :=
  .multiplyRight ((carrierEquiv G).symm right)

/-- Query that compares the hidden accumulator with one group value. -/
@[expose, implicit_reducible] public def equalsQuery (right : G) : Query (cardinality G) :=
  .equals ((carrierEquiv G).symm right)

/-- Every call uses one real Boolean caller port. Group values stay hidden. -/
@[expose, implicit_reducible]
public def queryInputShape (_query : Query (cardinality G)) : CShape := .bit

/-- Reset and multiplication return a false acknowledgement; equality returns
its actual Boolean result. -/
@[expose, implicit_reducible]
public def queryOutputShape (_query : Query (cardinality G)) : CShape := .bit

/-- Accounting coordinate selected by each finite-group query. -/
@[expose] public def queryCoordinate : Query (cardinality G) → Coordinate
  | .reset => .reset
  | .square | .multiplyRight _ => .groupOperation
  | .equals _ => .equalityTest

/-- Decidable equality of two hidden finite labels. -/
public def equalResult (left right : Fin (cardinality G)) : Bool :=
  @decide (left = right) (Classical.propDecidable _)

/-- Exact stateful transition of the hidden accumulator. -/
@[expose] public def transition : (query : Query (cardinality G)) →
    Fin (cardinality G) →
    CShape.Value (queryInputShape G query) →
      PMF (Fin (cardinality G) × CShape.Value (queryOutputShape G query))
  | .reset, _state, _input => PMF.pure (encode G 1, .bit false)
  | .square, state, _input =>
      PMF.pure (encode G (decode G state * decode G state), .bit false)
  | .multiplyRight right, state, _input =>
      PMF.pure (encode G (decode G state * decode G right), .bit false)
  | .equals right, state, _input =>
      PMF.pure (state, .bit (equalResult G state right))

/-- Stateful deterministic access to a representation-independent finite-group
accumulator. -/
@[expose, implicit_reducible]
public def model : ClassicalOracleModel :=
  .service
    { Query := Query (cardinality G)
      Coordinate := Coordinate
      coordinateDecidableEq := inferInstance
      HiddenState := Fin (cardinality G)
      stateFintype := inferInstance
      inputShape := queryInputShape G
      outputShape := queryOutputShape G
      coordinate := queryCoordinate G }

/-- The source group supplies one fixed transition law, independent of its persistent state. -/
@[expose] public def interpretation : (model G).Interpretation where
  transition := transition G

public lemma transition_reset (state : (model G).HiddenState)
    (input : CShape.Value ((model G).inputShape .reset)) :
    (model G).transition (interpretation G) .reset state input =
      PMF.pure (encode G 1, .bit false) := rfl

public lemma transition_square (state : (model G).HiddenState)
    (input : CShape.Value ((model G).inputShape .square)) :
    (model G).transition (interpretation G) .square state input =
      PMF.pure (encode G (decode G state * decode G state), .bit false) := rfl

public lemma transition_multiplyRight (right : Fin (cardinality G))
    (state : (model G).HiddenState)
    (input : CShape.Value ((model G).inputShape (.multiplyRight right))) :
    (model G).transition (interpretation G) (.multiplyRight right) state input =
      PMF.pure (encode G (decode G state * decode G right), .bit false) := rfl

/-- Multiplication by a declaration-owned group element, without exposing its
finite hidden-state label to callers. -/
public lemma transition_multiplyRightQuery (right : G)
    (state : (model G).HiddenState)
    (input : CShape.Value ((model G).inputShape (multiplyRightQuery G right))) :
    (model G).transition (interpretation G) (multiplyRightQuery G right) state input =
      PMF.pure (encode G (decode G state * right), .bit false) := by
  change transition G (multiplyRightQuery G right) state input = _
  simp only [transition, decode, multiplyRightQuery, Equiv.apply_symm_apply]

public lemma transition_equals (right : Fin (cardinality G))
    (state : (model G).HiddenState)
    (input : CShape.Value ((model G).inputShape (.equals right))) :
    (model G).transition (interpretation G) (.equals right) state input =
      PMF.pure (state, .bit (equalResult G state right)) := rfl

/-- Equality with a declaration-owned group element, stated at the public
group-value boundary rather than at the hidden finite-label boundary. -/
public lemma transition_equalsQuery (right : G)
    (state : (model G).HiddenState)
    (input : CShape.Value ((model G).inputShape (equalsQuery G right))) :
    (model G).transition (interpretation G) (equalsQuery G right) state input =
      PMF.pure (state, .bit (equalResult G state (encode G right))) := by
  exact transition_equals G (encode G right) state input

end

end QuantumAlg.ClassicalFiniteGroupOracle
