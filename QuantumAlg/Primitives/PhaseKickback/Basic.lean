/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Components.Control
import all QuantumAlg.Components.Control
public import QuantumAlg.Components.Kets
import all QuantumAlg.Components.Kets
import all QuantumAlg.Components.Oracle
public import QuantumAlg.Components.Oracle.Common
import all QuantumAlg.Components.Oracle.Common
public import QuantumAlg.Core.Base
import all QuantumAlg.Core.Base
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
public import Mathlib.Analysis.Complex.Exponential

/-!
# Phase kickback

Querying the XOR oracle of `f` with the target qubit in `|−⟩` leaves the
target untouched and kicks the value of `f` back into the phase of the
input register [dW19, qcnotes.tex:1167]:

`U_f (|x⟩ ⊗ |−⟩) = (−1)^{f(x)} · (|x⟩ ⊗ |−⟩)`,

the "phase kick-back trick" [dW19, qcnotes.tex:1173]. Dually, a `|+⟩`
target is left invariant, which lets circuits choose per-branch whether a
phase query happens [dW19, qcnotes.tex:1173].

The eigenvalue form replaces the oracle by a controlled unitary: if the
target register holds an eigenstate `|u⟩` of `U`, the eigenvalue `e^{iθ}`
is "kicked back" in front of the `|1⟩` component of the control
[CEMM98, cemm6.tex:163].

## Main results

- `QuantumAlg.PhaseKickback.xor_action` — `U_f (|x⟩ ⊗ |−⟩) = (−1)^{f(x)} (|x⟩ ⊗ |−⟩)`,
  with the sign written as `if f x then -1 else 1`.
- `QuantumAlg.xorOracleOp_apply_tensor_ketPlus` —
  `U_f (|x⟩ ⊗ |+⟩) = |x⟩ ⊗ |+⟩`.
- `QuantumAlg.GeneralizedPhaseKickback.eigenvalue_action` —
  `c-U ((a|0⟩ + b|1⟩) ⊗ |u⟩) = (a|0⟩ + e^{iθ} b|1⟩) ⊗ |u⟩` when
  `U |u⟩ = e^{iθ} |u⟩`.
-/

section

namespace QuantumAlg

open NormalizedVector Gate

noncomputable section

variable {n : ℕ}

/-- Strict event coordinate of one XOR-oracle query. -/
def phaseKickbackEvent (n : Nat) : Resource.Event .quantum :=
  .quantumSubroutine (xorOracleSubroutineLabel n).quantum

/-- The phase-kickback circuit emits its declared XOR-oracle event once. -/
@[simp]
theorem phaseKickback_eventTrace (f : Fin (2 ^ n) → Bool) :
    (Gate.xorOracle f).eventTrace = [phaseKickbackEvent n] :=
  rfl

/-- The strict event pool records one literal XOR-oracle query. -/
theorem phaseKickback_eventCost (f : Fin (2 ^ n) → Bool) :
    (Gate.xorOracle f).eventCost =
      ResourcePool.singleton (phaseKickbackEvent n) :=
  rfl

/-- The strict event critical path consists of the same XOR-oracle query. -/
theorem phaseKickback_eventDepth (f : Fin (2 ^ n) → Bool) :
    (Gate.xorOracle f).eventDepth = .atom (phaseKickbackEvent n) :=
  rfl

/-- The phase-kickback circuit contains exactly one event at its declared
XOR-oracle coordinate. -/
theorem phaseKickback_event_count (f : Fin (2 ^ n) → Bool) :
    ResourcePool.count (phaseKickbackEvent n) (Gate.xorOracle f).eventCost = 1 := by
  rw [phaseKickback_eventCost]
  simp

/-- The literal XOR-oracle event occurs on exactly one sequential layer. -/
@[simp]
theorem phaseKickback_eventQueryDepth (f : Fin (2 ^ n) → Bool) :
    (Gate.xorOracle f).eventQueryDepth (phaseKickbackEvent n) = 1 := by
  simp [UnitaryCircuit.eventQueryDepth, phaseKickbackEvent]

/-- Linearizing the strict event critical path recovers the same event pool. -/
theorem phaseKickback_resourcesFromEventDepth (f : Fin (2 ^ n) → Bool) :
    (Gate.xorOracle f).resourcesFromEventDepth =
      ResourcePool.singleton (phaseKickbackEvent n) := by
  rw [UnitaryCircuit.resourcesFromEventDepth_eq_eventCost, phaseKickback_eventCost]





/-- **Phase kickback**: on a `|−⟩` target the XOR oracle acts as the phase
oracle `|x⟩ ↦ (−1)^{f(x)} |x⟩`; the sign `(−1)^{f(x)}` is written
`if f x then -1 else 1`. -/
public theorem PhaseKickback.xor_action (f : Fin (2 ^ n) → Bool) (x : Fin (2 ^ n)) :
    (xorOracleOp f).applyVec
        (((ket x : NormalizedVector (Qubits n)).tensor ketMinus :
          NormalizedVector (Qubits (n + 1))) : HilbertVector (Qubits (n + 1)))
      = (if f x then (-1 : ℂ) else 1)
          • (((ket x : NormalizedVector (Qubits n)).tensor ketMinus :
              NormalizedVector (Qubits (n + 1))) : HilbertVector (Qubits (n + 1))) := by
  apply WithLp.ofLp_injective
  funext i
  rcases (prodEquiv (m := n) (n := 1)).surjective i with ⟨⟨y, b⟩, rfl⟩
  rw [xorOracleOp_apply]
  simp only [NormalizedVector.tensor_apply_prod, Equiv.symm_apply_apply,
    xorPerm_apply]
  by_cases hy : y = x
  · subst y
    by_cases h : f x
    · fin_cases b <;>
        simp [h, ketMinus_apply]
    · simp [h, ketMinus_apply]
  · by_cases hx : f x <;> by_cases h : f y <;> fin_cases b <;>
      simp [hx, h, hy, NormalizedVector.ket_apply]



/-- Controlling a structured circuit maps its ordered strict event trace
pointwise to the corresponding controlled coordinates. -/
@[simp]
theorem generalizedPhaseKickback_eventTrace (controlSystemIdx : List Nat)
    (U : UnitaryCircuit (Qubits n))
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx U.physical_idx)
    (activationValue : Fin 2) :
    (UnitaryCircuit.controlQubitsAt controlSystemIdx U layout
        activationValue).eventTrace =
      U.eventTrace.map (fun event => event.controlForDimension 2) :=
  UnitaryCircuit.controlQubitsAt_eventTrace controlSystemIdx U layout activationValue

/-- Controlling a structured circuit preserves multiplicities while moving
every strict event to its controlled coordinate. -/
@[simp]
theorem generalizedPhaseKickback_eventCost (controlSystemIdx : List Nat)
    (U : UnitaryCircuit (Qubits n))
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx U.physical_idx)
    (activationValue : Fin 2) :
    (UnitaryCircuit.controlQubitsAt controlSystemIdx U layout
        activationValue).eventCost =
      ResourcePool.controlForDimension 2 U.eventCost :=
  UnitaryCircuit.controlQubitsAt_eventCost controlSystemIdx U layout activationValue

/-- Controlling a structured circuit transforms every event atom and
serializes the branches that now share the added control systems. -/
@[simp]
theorem generalizedPhaseKickback_eventDepth (controlSystemIdx : List Nat)
    (U : UnitaryCircuit (Qubits n))
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx U.physical_idx)
    (activationValue : Fin 2) :
    (UnitaryCircuit.controlQubitsAt controlSystemIdx U layout
        activationValue).eventDepth =
      .controlled "circuit-control"
        (DepthExpr.controlEventsForDimension 2 U.eventDepth) :=
  UnitaryCircuit.controlQubitsAt_eventDepth controlSystemIdx U layout activationValue

/-- A controlled event is counted exactly as often as its source event. -/
theorem generalizedPhaseKickback_event_count
    (focus : Resource.Event .quantum) (controlSystemIdx : List Nat)
    (U : UnitaryCircuit (Qubits n))
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx U.physical_idx)
    (activationValue : Fin 2) :
    ResourcePool.count (focus.controlForDimension 2)
        (UnitaryCircuit.controlQubitsAt controlSystemIdx U layout
          activationValue).eventCost =
      ResourcePool.count focus U.eventCost :=
  UnitaryCircuit.count_controlQubitsAt_eventCost focus controlSystemIdx U layout
    activationValue

/-- Strict controlled-query depth counts every source occurrence at the
transformed coordinate because all controlled events share the control. -/
theorem generalizedPhaseKickback_eventQueryDepth
    (focus : Resource.Event .quantum) (controlSystemIdx : List Nat)
    (U : UnitaryCircuit (Qubits n))
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx U.physical_idx)
    (activationValue : Fin 2) :
    (UnitaryCircuit.controlQubitsAt controlSystemIdx U layout
        activationValue).eventQueryDepth (focus.controlForDimension 2) =
      DepthExpr.costEval (DepthExpr.indicator focus) U.eventDepth :=
  UnitaryCircuit.eventQueryDepth_controlQubitsAt focus controlSystemIdx U layout
    activationValue

/-- Linearizing controlled strict event depth applies the same pointwise
control transform to the source event pool. -/
theorem generalizedPhaseKickback_resourcesFromEventDepth
    (controlSystemIdx : List Nat) (U : UnitaryCircuit (Qubits n))
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx U.physical_idx)
    (activationValue : Fin 2) :
    (UnitaryCircuit.controlQubitsAt controlSystemIdx U layout
        activationValue).resourcesFromEventDepth =
      ResourcePool.controlForDimension 2 U.resourcesFromEventDepth :=
  UnitaryCircuit.resourcesFromEventDepth_controlQubitsAt controlSystemIdx U layout
    activationValue




/-- **Eigenvalue phase kickback** [CEMM98, cemm6.tex:163]: if the target
register holds an eigenstate `|u⟩` of `U` with eigenvalue `e^{iθ}`, the
controlled `U` leaves the target unchanged and kicks the eigenvalue back
onto the `|1⟩` component of the control [CEMM98, cemm6.tex:142]:

`c-U ((a|0⟩ + b|1⟩) ⊗ |u⟩) = (a|0⟩ + e^{iθ} b|1⟩) ⊗ |u⟩`. -/
public theorem GeneralizedPhaseKickback.eigenvalue_action (U : UnitaryOperator (Qubits n))
    (u : NormalizedVector (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      Complex.exp (θ * Complex.I) • (u : HilbertVector (Qubits n))) (a b : ℂ) :
    (UnitaryOperator.controlledQubits U).applyVec
        (HilbertVector.tensor
          ((a • ket0 + b • ket1 : HilbertVector (Qubits 1))) (u : HilbertVector (Qubits n)))
      =
      HilbertVector.tensor
        ((a • ket0 + (Complex.exp (θ * Complex.I) * b) • ket1 : HilbertVector (Qubits 1)))
        (u : HilbertVector (Qubits n)) := by
  rw [HilbertVector.add_tensor, HilbertVector.smul_tensor, HilbertVector.smul_tensor,
    UnitaryOperator.applyVec_add, UnitaryOperator.applyVec_smul,
    UnitaryOperator.applyVec_smul,
    UnitaryOperator.controlledQubits_applyVec_ket0_tensor,
    UnitaryOperator.controlledQubits_applyVec_ket1_tensor]
  rw [HilbertVector.add_tensor, HilbertVector.smul_tensor, HilbertVector.smul_tensor]
  rw [hu, HilbertVector.tensor_smul, smul_smul]
  module


end

end QuantumAlg

end
