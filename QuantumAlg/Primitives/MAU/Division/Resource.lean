/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.MAU.Division.StructuredCircuit

/-!
# Circuit-derived modular-division resources

The ideal unit-denominator operator is kept as a mathematical specification.
Every physical resource view in this module is projected from an exact
inverse / product / target-add / uncompute actual `UnitaryCircuit` witness defined in
`StructuredCircuit`; callers cannot attach a separate resource profile.
-/

section

namespace QuantumAlg
namespace MAU.Division

noncomputable section

/-! ### Ideal unit-denominator action -/

/-- Register whose basis labels are unit-denominator division data states. -/
@[implicit_reducible]
def register (N : ℕ) [NeZero N] : Register where
  Index := Data N
  fintype := inferInstance
  decEq := inferInstance

/-- The ideal modular-division operator.  This is a semantic specification,
not the physical resource-accounted circuit. -/
noncomputable def divOp (N : ℕ) [NeZero N] : UnitaryOperator (register N) :=
  UnitaryOperator.ofPerm (Data.divEquiv N).symm

/-- Ideal clean basis action of modular division. -/
theorem divOp_apply_ket (N : ℕ) [NeZero N] (x : Data N) :
    (divOp N).apply (NormalizedVector.ket (R := register N) x) =
      NormalizedVector.ket (R := register N) x.addQuotientIntoTarget := by
  rw [divOp, UnitaryOperator.ofPerm_apply_ket]
  rfl

/-! ### Exact decomposed-circuit resource view -/

namespace DecomposedCircuit

variable {N : Nat}

/-- The exact circuit folded from the witness inverse / product / target-add /
inverse-product / inverse-inverse program. -/
def circuit (w : DecomposedPipelineWitness N) : UnitaryCircuit (Qubits w.encoding.width) :=
  w.program

/-- Ordered strict events of the exact decomposed circuit. -/
def eventTrace (w : DecomposedPipelineWitness N) :
    List (Resource.Event .quantum) :=
  w.program.eventTrace

/-- Strict event pool of the exact decomposed circuit. -/
def eventCost (w : DecomposedPipelineWitness N) : ResourcePool .quantum :=
  w.program.eventCost

/-- Strict symbolic event critical path of the decomposed circuit. -/
def eventDepth (w : DecomposedPipelineWitness N) :
    DepthExpr (Resource.Event .quantum) :=
  w.program.eventDepth

/-- Evaluated decomposed-circuit depth under literal event durations. -/
def evaluatedEventDepth (w : DecomposedPipelineWitness N)
    (assign : Resource.Event .quantum → Nat) : Nat :=
  w.program.evaluatedEventDepth assign

/-- Literal depth of one strict event coordinate in the decomposed circuit. -/
def eventQueryDepth (w : DecomposedPipelineWitness N)
    (focus : Resource.Event .quantum) : Nat :=
  w.program.eventQueryDepth focus

/-- Exact multiplicity of one gate coordinate in the decomposed event pool. -/
def eventGateCount (w : DecomposedPipelineWitness N)
    (label : Resource.GateLabel) : Nat :=
  ResourcePool.count (.gate label) w.program.eventCost











/-- Physical qubit count of the witness encoding. -/
def qubitCount (w : DecomposedPipelineWitness N) : Nat :=
  w.encoding.width

/-- The exact decomposed circuit preserves normalization on its clean endpoint. -/
theorem applyNormalized_clean_ket (w : DecomposedPipelineWitness N)
    (u : (ZMod N)ˣ) (v z : ZMod N) :
    w.program.applyNormalized
        (NormalizedVector.ket (R := Qubits w.encoding.width)
          (w.encoding.encode (PipelineState.initial u v z))) =
      NormalizedVector.ket (R := Qubits w.encoding.width)
        (w.encoding.encode
          ({ denominator := u
             numerator := v
             target := z + quotientResidue u v
             inverseScratch := 0
             quotientScratch := 0
             flag := false } : PipelineState N)) :=
  DecomposedPipelineWitness.applyNormalized_clean_ket w u v z



/-- Linearizing decomposed event depth recovers its exact strict event pool. -/
theorem resourcesFromEventDepth_eq_eventCost (w : DecomposedPipelineWitness N) :
    w.program.resourcesFromEventDepth = w.program.eventCost :=
  UnitaryCircuit.resourcesFromEventDepth_eq_eventCost w.program

/-- Event-native source bound whose predicates refer to literal event
coordinates of the same exact circuit. -/
structure SupportsEventSourceBound (w : DecomposedPipelineWitness N)
    (eventCostBound : ResourcePool .quantum)
    (eventDepthBound : Resource.Event .quantum → Nat) : Prop where
  eventCost_le : eventCost w ≤ eventCostBound
  eventQueryDepth_le :
    ∀ event, eventQueryDepth w event ≤ eventDepthBound event



end DecomposedCircuit

/-! ### Exact encoded-circuit resource view -/

namespace EncodedCircuit

variable {N : Nat}

/-- Exact circuit carried by an encoded division witness. -/
def circuit (w : StructuredCircuitWitness N) : UnitaryCircuit (Qubits w.encoding.width) :=
  w.circuit

/-- Ordered strict events of the exact encoded circuit. -/
def eventTrace (w : StructuredCircuitWitness N) :
    List (Resource.Event .quantum) :=
  w.circuit.eventTrace

/-- Strict event pool of the exact encoded circuit. -/
def eventCost (w : StructuredCircuitWitness N) : ResourcePool .quantum :=
  w.circuit.eventCost

/-- Strict symbolic event critical path of the encoded circuit. -/
def eventDepth (w : StructuredCircuitWitness N) :
    DepthExpr (Resource.Event .quantum) :=
  w.circuit.eventDepth

/-- Evaluated encoded-circuit depth under literal event durations. -/
def evaluatedEventDepth (w : StructuredCircuitWitness N)
    (assign : Resource.Event .quantum → Nat) : Nat :=
  w.circuit.evaluatedEventDepth assign

/-- Literal depth of one strict event coordinate in the encoded circuit. -/
def eventQueryDepth (w : StructuredCircuitWitness N)
    (focus : Resource.Event .quantum) : Nat :=
  w.circuit.eventQueryDepth focus

/-- Exact multiplicity of one gate coordinate in the encoded event pool. -/
def eventGateCount (w : StructuredCircuitWitness N)
    (label : Resource.GateLabel) : Nat :=
  ResourcePool.count (.gate label) w.circuit.eventCost











/-- Physical qubit count of the encoded witness. -/
def qubitCount (w : StructuredCircuitWitness N) : Nat :=
  w.encoding.width

/-- Normalized clean endpoint of the exact encoded circuit. -/
theorem applyNormalized_clean_ket (w : StructuredCircuitWitness N)
    (u : (ZMod N)ˣ) (v z : ZMod N) :
    w.circuit.applyNormalized
        (NormalizedVector.ket (R := Qubits w.encoding.width)
          (w.encoding.encode
            ({ denominator := u, numerator := v, target := z, flag := false } :
              Data N))) =
      NormalizedVector.ket (R := Qubits w.encoding.width)
        (w.encoding.encode
          ({ denominator := u
             numerator := v
             target := z + quotientResidue u v
             flag := false } : Data N)) :=
  StructuredCircuitWitness.applyNormalized_clean_ket w u v z



/-- Linearizing encoded event depth recovers its exact strict event pool. -/
theorem resourcesFromEventDepth_eq_eventCost (w : StructuredCircuitWitness N) :
    w.circuit.resourcesFromEventDepth = w.circuit.eventCost :=
  UnitaryCircuit.resourcesFromEventDepth_eq_eventCost w.circuit

end EncodedCircuit

end

end MAU.Division
end QuantumAlg

end
