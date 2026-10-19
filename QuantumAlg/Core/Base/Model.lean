/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Kind
public import QuantumAlg.Core.Base.Classical.Model
public import QuantumAlg.Core.Base.Classical.Oracle
public import QuantumAlg.Core.Base.Gate.Model
public import QuantumAlg.Core.Base.Oracle.Model

/-!
# Models of executable computation

Every execution selects its classical native operations and declared classical
oracle access. Quantum execution additionally selects native gates and quantum
oracle access. Pure quantum circuit accounting may use empty classical grants;
full algorithms choose their classical language explicitly in Components.
Mathematical quantum states and physical layouts still depend only on kind.
-/

namespace QuantumAlg

/-- The operation language shared by an implementation and its specification. -/
public inductive ExecutionModel where
  /-- Classical native operations and classical oracle access are independent selections. -/
  | classical (operations : ClassicalOpModel) (oracles : ClassicalOracleModel)
  /-- All four grants remain independent; empty classical grants suffice for pure unitary words. -/
  | quantum (gates : GateModel) (oracles : OracleModel)
      (operations : ClassicalOpModel := ClassicalOpModel.empty)
      (classicalOracles : ClassicalOracleModel := ClassicalOracleModel.empty)

namespace ExecutionModel

/-- Forget operation selection when constructing mathematical state and storage types. -/
@[expose, implicit_reducible]
public def kind : ExecutionModel → ProblemKind
  | .classical _ _ => .classical
  | .quantum _ _ _ _ => .quantum

/-- The chosen classical native language is present in pure and hybrid execution. -/
@[expose, implicit_reducible]
public def classicalOperations : ExecutionModel → ClassicalOpModel
  | .classical operations _ => operations
  | .quantum _ _ operations _ => operations

/-- The classical oracle service declaration is independent of every other language. -/
@[expose, implicit_reducible]
public def classicalOracles : ExecutionModel → ClassicalOracleModel
  | .classical _ oracles => oracles
  | .quantum _ _ _ oracles => oracles

/-- Quantum query syntax is absent from classical execution. -/
@[expose, implicit_reducible]
public def quantumOracles : ExecutionModel → OracleModel
  | .classical _ _ => .empty
  | .quantum _ oracles _ _ => oracles

/-- Fixed query interpretations supplied to the interpreter, never stored in program syntax. -/
public structure Environment (model : ExecutionModel) where
  /-- Interpretation of the granted quantum query interface. -/
  quantum : model.quantumOracles.Interpretation
  /-- Separate transition laws of the declared persistent classical services. -/
  classical : model.classicalOracles.Interpretation

/-- Model-owned native coordinates for actual classical instructions. -/
@[expose, implicit_reducible]
public def ClassicalCoordinate (model : ExecutionModel) : Type :=
  model.classicalOperations.Coordinate

/-- Independently owned coordinates for actual classical oracle queries. -/
@[expose, implicit_reducible]
public def ClassicalOracleCoordinate (model : ExecutionModel) : Type :=
  model.classicalOracles.Coordinate

/-- Persistent service state is fixed by the selected classical oracle declaration. -/
@[expose, implicit_reducible]
public def HiddenState (model : ExecutionModel) : Type := model.classicalOracles.HiddenState

public instance classicalCoordinateDecidableEq (model : ExecutionModel) :
    DecidableEq model.ClassicalCoordinate := model.classicalOperations.coordinateDecidableEq

public instance classicalOracleCoordinateDecidableEq (model : ExecutionModel) :
    DecidableEq model.ClassicalOracleCoordinate := model.classicalOracles.coordinateDecidableEq

public instance hiddenStateFintype (model : ExecutionModel) : Fintype model.HiddenState :=
  model.classicalOracles.stateFintype

/-- Classical state and storage types do not depend on operation selection. -/
@[simp] public lemma classical_kind (operations : ClassicalOpModel)
    (oracles : ClassicalOracleModel) : (classical operations oracles).kind = .classical := rfl

/-- Quantum state and storage types do not depend on operation selection. -/
@[simp] public lemma quantum_kind (gates : GateModel) (oracles : OracleModel)
    (operations : ClassicalOpModel) (classicalOracles : ClassicalOracleModel) :
    (quantum gates oracles operations classicalOracles).kind = .quantum := rfl

/-- Native gate coordinates are absent from classical execution. -/
@[expose, implicit_reducible]
public def GateCoordinate : ExecutionModel → Type
  | .classical _ _ => Empty
  | .quantum gates _ _ _ => gates.Coordinate

/-- Query coordinates are absent from classical execution and independent of native gates. -/
@[expose, implicit_reducible]
public def OracleCoordinate : ExecutionModel → Type
  | .classical _ _ => Empty
  | .quantum _ oracles _ _ => oracles.Coordinate

/-- Fixed preparation and measurement dimensions exist only in quantum execution. -/
@[expose, implicit_reducible]
public def SystemDimension : ExecutionModel → Type
  | .classical _ _ => Empty
  | .quantum _ _ _ _ => ℕ+

public instance gateCoordinateDecidableEq (model : ExecutionModel) :
    DecidableEq model.GateCoordinate := by
  cases model with
  | classical _ _ => exact inferInstanceAs (DecidableEq Empty)
  | quantum gates _ _ _ => exact gates.coordinateDecidableEq

public instance oracleCoordinateDecidableEq (model : ExecutionModel) :
    DecidableEq model.OracleCoordinate := by
  cases model with
  | classical _ _ => exact inferInstanceAs (DecidableEq Empty)
  | quantum _ oracles _ _ => exact oracles.coordinateDecidableEq

public instance systemDimensionDecidableEq (model : ExecutionModel) :
    DecidableEq model.SystemDimension := by
  cases model with
  | classical _ _ => exact inferInstanceAs (DecidableEq Empty)
  | quantum _ _ _ _ => exact inferInstanceAs (DecidableEq ℕ+)

end ExecutionModel

end QuantumAlg
