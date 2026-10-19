/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Semiclassical.Refined.Construction
public import QuantumAlg.Core.Execution.Time
import all QuantumAlg.Primitives.QFT.Semiclassical.Refined.Construction
import all QuantumAlg.Components.Gates.SemiclassicalFourier
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Circuit.Weighted
import all QuantumAlg.Core.Base.Depth.WeightedCost
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Independent gate and quantum-time bounds for the measured Fourier schedule

Each actual selected branch executes at most its remaining phase word.
The induction charges one Hadamard and one measurement at each real physical
wire, summing the phase lengths to n choose 2. The resulting native allowance
also bounds the original path's quantum time; measurements have duration zero
[GN96, 9511007.tex:214-244].
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Refined

open Execution

noncomputable section

variable {ctx : RuntimeCtx .quantum}

/-- A real native phase prefix contains exactly count occurrences of the phase coordinate. -/
public lemma qftSemiclassical_refinedPhasePrefix_events (inverse : Bool) {n : Nat}
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (count : Nat) (bounded : count ≤ n) :
    (phasePrefix inverse wires qubits count bounded).eventCost =
      count • ResourcePool.singleton
        (model := .quantum SemiclassicalFourierGate.model .empty) (.gate .phase) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [phasePrefix, UnitaryCircuit.seq_eventCost, ih,
        SemiclassicalFourierGate.semiclassicalFourier_phaseAt_eventCost, succ_nsmul]

/-- Reading the real cell selects at most the n native phases that remain in the stage. -/
public lemma qftSemiclassical_refinedFeedback_events (inverse : Bool) {n : Nat}
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    {dimension : ℕ+} (result : CWriteRef ctx (.finite dimension))
    (path : (feedbackCode inverse wires qubits result).Path) :
    (feedbackCode inverse wires qubits result).resourcePool path ≤
      n • ResourcePool.singleton
        (model := .quantum SemiclassicalFourierGate.model .empty) (.gate .phase) := by
  change ResourcePool.ofList (selectedPhase inverse wires qubits path.1).eventTrace ≤ _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost]
  rcases path.1 with ⟨bit⟩
  simp only [selectedPhase]
  split_ifs
  · exact (qftSemiclassical_refinedPhasePrefix_events inverse wires qubits n le_rfl).le
  · simp only [UnitaryCircuit.identity_eventCost]
    exact zero_le

/-- Every actual adaptive path fits separate independent H, phase and measurement allowances. -/
public lemma qftSemiclassical_refinedCode_events (inverse : Bool) :
    ∀ (n : Nat) (wires : Fin n ↪ Fin ctx.systemCount)
      (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
      (outputs : ∀ i, CWriteRef ctx (.finite (ctx.quantumLayout.wire (wires i)).dimension))
      (path : (code inverse n wires qubits outputs).Path),
      (code inverse n wires qubits outputs).resourcePool path ≤
        n • ResourcePool.singleton
            (model := .quantum SemiclassicalFourierGate.model .empty) (.gate .hadamard) +
          (n.choose 2) • ResourcePool.singleton
            (model := .quantum SemiclassicalFourierGate.model .empty) (.gate .phase) +
          n • ResourcePool.singleton
            (model := .quantum SemiclassicalFourierGate.model .empty)
            (.measurement (2 : ℕ+)) := by
  intro n
  induction n with
  | zero => intro wires qubits outputs path; exact le_rfl
  | succ n ih =>
      intro wires qubits outputs path
      let tailWires : Fin n ↪ Fin ctx.systemCount :=
        ⟨fun i => wires i.succ, fun _ _ same => Fin.succ_injective n (wires.injective same)⟩
      let tailQubits := fun i : Fin n => qubits i.succ
      have feedback := qftSemiclassical_refinedFeedback_events inverse tailWires tailQubits
        (outputs 0) path.2.2.1
      have tail := ih tailWires tailQubits (fun i => outputs i.succ) path.2.2.2
      have hadamardEvents :
          ResourcePool.ofList
              (SemiclassicalFourierGate.hadamardAt ctx.quantumLayout .empty
                (wires 0) (qubits 0)).eventTrace =
            ResourcePool.singleton
              (model := .quantum SemiclassicalFourierGate.model .empty) (.gate .hadamard) :=
        (UnitaryCircuit.ofList_eventTrace_eq_eventCost _).trans
          (SemiclassicalFourierGate.semiclassicalFourier_hadamardAt_eventCost _ _ _ _)
      have measured :
          ResourcePool.singleton
              (model := .quantum SemiclassicalFourierGate.model .empty)
              (.measurement (ctx.quantumLayout.wire (wires 0)).dimension) =
            ResourcePool.singleton
              (model := .quantum SemiclassicalFourierGate.model .empty)
              (.measurement (2 : ℕ+)) := by
        rw [qubits 0]
      change ResourcePool.ofList
          (SemiclassicalFourierGate.hadamardAt ctx.quantumLayout .empty
            (wires 0) (qubits 0)).eventTrace +
        (ResourcePool.singleton (model := .quantum SemiclassicalFourierGate.model .empty)
          (.measurement (ctx.quantumLayout.wire (wires 0)).dimension) +
          ((feedbackCode inverse tailWires tailQubits (outputs 0)).resourcePool path.2.2.1 +
            (code inverse n tailWires tailQubits
              (fun i => outputs i.succ)).resourcePool path.2.2.2)) ≤ _
      rw [hadamardEvents, measured]
      refine (add_le_add_right (add_le_add_right (add_le_add feedback tail) _) _).trans_eq ?_
      rw [show (n + 1).choose 2 = n + n.choose 2 by
        simpa using (Nat.choose_succ_succ n 1), add_nsmul, succ_nsmul, succ_nsmul]
      simp only [add_nsmul]
      ac_rfl

/-- The same adaptive path's quantum time is at most n+n choose 2, with measurement time zero. -/
public lemma qftSemiclassical_refinedCode_quantumTime (inverse : Bool) (n : Nat)
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (outputs : ∀ i, CWriteRef ctx (.finite (ctx.quantumLayout.wire (wires i)).dimension))
    (path : (code inverse n wires qubits outputs).Path) :
    (code inverse n wires qubits outputs).quantumTime path ≤ n + n.choose 2 := by
  refine (Circuit.depth_le_weightedCount_of_pool_le _ Resource.Event.quantumDuration _ path
    (qftSemiclassical_refinedCode_events inverse n wires qubits outputs path)).trans_eq ?_
  simp [ResourcePool.weightedCount_add, ResourcePool.weightedCount_nsmul,
    ResourcePool.weightedCount_singleton, Resource.Event.quantumDuration]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Refined
