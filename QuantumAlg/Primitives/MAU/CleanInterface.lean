/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Components.Encoded.BasisMap
import Mathlib.Tactic
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Components.Encoded.BitGates.Word.Swap
import all QuantumAlg.Primitives.Arithmetic.BitSlice
import all QuantumAlg.Primitives.Arithmetic.PlainAdder
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.Schedule
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.StructuredCircuit

/-!
# Clean-ancilla interface for modular arithmetic units

This module turns a work-preserving reversible map into the shared typed-circuit
interface used by modular-arithmetic units. A realization owns one concrete
`UnitaryCircuit`; basis-map correctness and strict event accounting both refer to that
circuit. Downstream arithmetic components cannot attach an unrelated resource
tuple to the semantic map.
-/

section

namespace QuantumAlg

namespace ModularArithmetic

/-- Data and target labels are bundled before attaching the reusable work
register.  Concrete arithmetic units decide what belongs in each component. -/
abbrev DataTarget (Data Target : Type) :=
  Data × Target

/-- Clean-ancilla reversible map with separate data, target, and work labels. -/
abbrev CleanAncillaMap (Data Target Work : Type) :=
  WorkRegister.CleanReversibleMap (DataTarget Data Target) Work

end ModularArithmetic

namespace WorkRegister

namespace CleanReversibleMap

variable {Data Work : Type}

/-- Register whose basis labels are data/work pairs for a clean reversible map. -/
@[implicit_reducible]
def register (Data Work : Type)
    [Fintype Data] [DecidableEq Data] [Fintype Work] [DecidableEq Work] :
    Register where
  Index := Data × Work
  fintype := inferInstance
  decEq := inferInstance

/-- Metadata-free permutation operator induced by a clean reversible map. -/
noncomputable def op [Fintype Data] [DecidableEq Data] [Fintype Work] [DecidableEq Work]
    (clean : CleanReversibleMap Data Work) : UnitaryOperator (register Data Work) :=
  UnitaryOperator.ofPerm clean.perm.symm

/-- Basis-state action of the clean reversible map operator. -/
theorem op_apply_ket [Fintype Data] [DecidableEq Data] [Fintype Work] [DecidableEq Work]
    (clean : CleanReversibleMap Data Work) (x : Data × Work) :
    clean.op.apply (NormalizedVector.ket (R := register Data Work) x) =
      NormalizedVector.ket (R := register Data Work) (clean.perm x) := by
  rw [op, UnitaryOperator.ofPerm_apply_ket]
  rfl

/-- A concrete typed-circuit realization of a clean reversible map. Correctness,
cost, and depth are all tied to the single stored circuit. -/
structure CircuitRealization
    [Fintype Data] [DecidableEq Data] [Fintype Work] [DecidableEq Work]
    (clean : CleanReversibleMap Data Work) where
  /-- The executable circuit whose sequence owns all resource metadata. -/
  circuit : UnitaryCircuit (register Data Work)
  /-- Exact action of that same circuit on every encoded basis label. -/
  applyNormalized :
    ∀ x : Data × Work,
      circuit.applyNormalized (NormalizedVector.ket (R := register Data Work) x) =
        NormalizedVector.ket (R := register Data Work) (clean.perm x)

namespace CircuitRealization

variable [Fintype Data] [DecidableEq Data] [Fintype Work] [DecidableEq Work]
variable {clean : CleanReversibleMap Data Work}

/-- Ordered strict events derived from the realized clean circuit. -/
def eventTrace (realization : CircuitRealization clean) :
    List (Resource.Event .quantum) :=
  realization.circuit.eventTrace

/-- Strict event pool derived from the realized clean circuit. -/
def eventCost (realization : CircuitRealization clean) : ResourcePool .quantum :=
  realization.circuit.eventCost

/-- Strict symbolic event critical path of the realized clean circuit. -/
def eventDepth (realization : CircuitRealization clean) :
    DepthExpr (Resource.Event .quantum) :=
  realization.circuit.eventDepth

/-- Literal depth of one strict event coordinate in the clean circuit. -/
def eventQueryDepth (realization : CircuitRealization clean)
    (focus : Resource.Event .quantum) : Nat :=
  realization.circuit.eventQueryDepth focus

/-- Exact multiplicity of one gate coordinate in the clean circuit. -/
def eventGateCount (realization : CircuitRealization clean)
    (label : Resource.GateLabel) : Nat :=
  ResourcePool.count (.gate label) realization.circuit.eventCost

/-- Linearizing the clean circuit's event depth recovers its event pool. -/
theorem resourcesFromEventDepth_eq_eventCost
    (realization : CircuitRealization clean) :
    realization.circuit.resourcesFromEventDepth = realization.circuit.eventCost :=
  UnitaryCircuit.resourcesFromEventDepth_eq_eventCost realization.circuit





/-- Compose two clean-map realizations by composing their owned circuits in the
same execution order. The resulting semantics and resource metadata therefore
come from one `UnitaryCircuit.seq`, rather than an unrelated composition witness. -/
noncomputable def sequential
    {firstClean secondClean : CleanReversibleMap Data Work}
    (first : CircuitRealization firstClean)
    (second : CircuitRealization secondClean) :
    CircuitRealization
      (WorkRegister.CleanReversibleMap.sequential firstClean secondClean) where
  circuit := UnitaryCircuit.seq first.circuit second.circuit
  applyNormalized := by
    intro x
    rw [UnitaryCircuit.applyNormalized_seq, first.applyNormalized, second.applyNormalized]
    rfl

/-- Clean realizations preserve the work-register label on every basis input. -/
theorem preservesWork (_realization : CircuitRealization clean) (x : Data × Work) :
    (clean.perm x).2 = x.2 := by
  exact clean.preservesWork x

end CircuitRealization

end CleanReversibleMap

end WorkRegister

end QuantumAlg

end
