/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QSP.SingleQubit.Chebyshev.Basic
import all QuantumAlg.Primitives.QSP.SingleQubit.Chebyshev.Basic
import all QuantumAlg.Components.Gates
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Actual reflection-convention QSP words

The source word has one processing rotation per phase and one signal
occurrence per list entry [Lin22, hermfunc.tex:1103-1138]. Its placement,
matrix, event pool and depth all come from that same literal word.
-/

namespace QuantumAlg.ReflectionBasedQuantumSignalProcessing

noncomputable section

/-- The declared source signal coordinate. -/
public def signalEvent : Resource.Event .quantum :=
  .gate (.declared "qsp" "qsp-signal-o")

/-- The declared exact processing-rotation coordinate. -/
public def rotationEvent : Resource.Event .quantum :=
  .gate (.declared "QuantumAlg.Components.Gate" "rotation-z")

/-- Independent native ledger for a degree-d source word. -/
public def eventBudget (d : Nat) : ResourcePool .quantum :=
  ResourcePool.singleton signalEvent d + ResourcePool.singleton rotationEvent (d + 1)

/-- The actual source-order processing word, without preparation or new wires. -/
public def circuit (φ₀ : Real) (φs : List Real) (x : Real)
    (hx : x ∈ Set.Icc (-1 : Real) 1) : UnitaryCircuit (Qubits 1) :=
  qspOIndexedCircuit φ₀ φs x hx

/-- The independent algebraic source product, certified on its signal domain. -/
public def operator (φ₀ : Real) (φs : List Real) (x : Real)
    (hx : x ∈ Set.Icc (-1 : Real) 1) : UnitaryOperator (Qubits 1) :=
  .ofMatrix (qspO φ₀ φs x) (qspO_mem_unitaryGroup φ₀ φs hx)

theorem circuit_matrix (φ₀ : Real) (φs : List Real) (x : Real)
    (hx : x ∈ Set.Icc (-1 : Real) 1) :
    (circuit φ₀ φs x hx).matrix = operator φ₀ φs x hx := by
  apply Subtype.ext
  exact qspOIndexedCircuit_matrix φ₀ φs x hx

private theorem fold_placement (phases : List Real) (x : Real)
    (hx : x ∈ Set.Icc (-1 : Real) 1) (start : UnitaryCircuit (Qubits 1))
    (placed : start.physical_idx = [0]) :
    (phases.foldl (fun acc φ => .seq (qspOStepCircuit x φ hx) acc) start).physical_idx =
      [0] := by
  induction phases generalizing start with
  | nil => exact placed
  | cons φ tail ih =>
      apply ih
      change UnitaryCircuit.unionPhysicalIdx [0] start.physical_idx = [0]
      rw [placed]
      rfl

theorem circuit_physicalIdx (φ₀ : Real) (φs : List Real) (x : Real)
    (hx : x ∈ Set.Icc (-1 : Real) 1) :
    (circuit φ₀ φs x hx).physical_idx = List.range 1 :=
  fold_placement φs x hx _ rfl

private theorem fold_events (phases : List Real) (x : Real)
    (hx : x ∈ Set.Icc (-1 : Real) 1) (start : UnitaryCircuit (Qubits 1)) :
    (phases.foldl (fun acc φ => .seq (qspOStepCircuit x φ hx) acc) start).eventCost =
      ResourcePool.singleton signalEvent phases.length +
        ResourcePool.singleton rotationEvent phases.length + start.eventCost := by
  induction phases generalizing start with
  | nil => simp
  | cons φ tail ih =>
      simp only [List.foldl_cons, List.length_cons, ih, UnitaryCircuit.seq_eventCost]
      change _ + _ + (ResourcePool.singleton rotationEvent +
        ResourcePool.singleton signalEvent + start.eventCost) = _
      simp only [ResourcePool.singleton, Multiset.replicate_add]
      ac_rfl

theorem circuit_events (φ₀ : Real) (φs : List Real) (x : Real)
    (hx : x ∈ Set.Icc (-1 : Real) 1) :
    (circuit φ₀ φs x hx).eventCost = eventBudget φs.length := by
  rw [circuit, qspOIndexedCircuit, fold_events]
  change _ + _ + ResourcePool.singleton rotationEvent = _
  simp only [eventBudget, ResourcePool.singleton, Multiset.replicate_add, add_assoc]

private theorem fold_depth (phases : List Real) (x : Real)
    (hx : x ∈ Set.Icc (-1 : Real) 1) (start : UnitaryCircuit (Qubits 1)) :
    UnitaryCircuit.evaluatedEventDepth (fun _ => 1)
      (phases.foldl (fun acc φ => UnitaryCircuit.seq (qspOStepCircuit x φ hx) acc) start) =
        2 * phases.length + start.evaluatedEventDepth (fun _ => 1) := by
  induction phases generalizing start with
  | nil => simp
  | cons φ tail ih =>
      simp only [List.foldl_cons, List.length_cons, ih,
        UnitaryCircuit.evaluatedEventDepth_seq]
      change 2 * tail.length + (2 + _) = _
      omega

theorem circuit_depth (φ₀ : Real) (φs : List Real) (x : Real)
    (hx : x ∈ Set.Icc (-1 : Real) 1) :
    (circuit φ₀ φs x hx).evaluatedEventDepth (fun _ => 1) = 2 * φs.length + 1 :=
  fold_depth φs x hx _

end

end QuantumAlg.ReflectionBasedQuantumSignalProcessing
