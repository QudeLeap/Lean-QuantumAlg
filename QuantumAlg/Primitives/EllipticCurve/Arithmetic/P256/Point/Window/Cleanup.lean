/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Frame
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Recorded
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence.State
import all QuantumAlg.Components.QuditShift.Qubit
import all QuantumAlg.Components.Classical.Model.BitWord
import all QuantumAlg.Core.Execution.QubitReadouts

/-!
# Actual complete point-bank cleanup on every reachable input

Every original physical system is measured and corrected from its actual
stored outcome. The one supplied outcome cell is consumed before reuse;
all previous outcomes remain in the complete execution history. The same
854 systems remain present and end at zero for arbitrary original labels,
stores, service histories and external-reference correlations.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace Cleanup

noncomputable section

open Execution

private instance cleanupDimensionNeZero (dimension : ℕ+) : NeZero (dimension : Nat) :=
  ⟨Nat.ne_of_gt dimension.property⟩

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

/-- The original ordered bank and one existing sequentially reused result cell. -/
structure Parameters (ctx : RuntimeCtx .quantum) where
  sameWires : (QubitLayout.canonical encoding.width).toQuantum.wires = ctx.quantumLayout.wires
  output : CWriteRef ctx (.finite 2)

namespace Parameters

variable (parameters : Parameters ctx)

include parameters in
lemma qubit (wire : Fin ctx.systemCount) :
    (ctx.quantumLayout.wire wire).dimension = 2 := by
  obtain ⟨original, rfl⟩ :=
    (positionsOfEqualWires (QubitLayout.canonical encoding.width).toQuantum
      ctx.quantumLayout parameters.sameWires).surjective wire
  exact congrArg QuantumWire.dimension
    (wireAtCorrespondingPosition (QubitLayout.canonical encoding.width).toQuantum
      ctx.quantumLayout parameters.sameWires original)

def outputAt (wire : Fin ctx.systemCount) :
    CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension) :=
  QubitReadouts.outputAt _ (parameters.qubit wire) parameters.output

def shifts (wire : Fin ctx.systemCount) :
    QuditShift.Realizations AlgorithmGate.model .empty ctx.quantumLayout wire :=
  QuditShift.qubitRealizations ctx.quantumLayout wire (parameters.qubit wire) .empty

/-- The existing literal MZ, same-cell read and native identity/X; no allocation occurs. -/
@[implicit_reducible]
def one (wire : Fin ctx.systemCount) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  QuditShift.resetCircuit wire (parameters.outputAt wire) (parameters.shifts wire)
    BitWord.model services false

/-- Symbolic finite recursion retains the whole actual bank and every chronological path. -/
def run (count : Nat) (wires : Fin count → Fin ctx.systemCount) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  Circuit.forRange count (fun index => parameters.one (wires index))

/-- Every original physical system is reset once in its existing finite-index order. -/
def circuit :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  parameters.run ctx.systemCount id

private lemma one_supported
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (wire : Fin ctx.systemCount)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    QuditShift.WireSupported wire 0
      ((parameters.one wire).execute environment Reference state) := by
  intro result left right refLeft refRight different
  dsimp only [one]
  rw [QuditShift.Recorded.block_entry]
  simp only [different, false_and, if_false, ite_self, Finset.sum_const_zero]

private lemma one_preserves
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (wire focus : Fin ctx.systemCount)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (supported : QuditShift.WireSupported focus 0 state) :
    QuditShift.WireSupported focus 0
      ((parameters.one wire).execute environment Reference state) := by
  by_cases same : focus = wire
  · subst focus
    exact parameters.one_supported environment wire state
  · intro result left right refLeft refRight outside
    dsimp only [one]
    rw [QuditShift.Recorded.block_entry]
    apply Finset.sum_eq_zero
    intro record _
    apply Finset.sum_eq_zero
    intro outcome _
    have zero := supported record (Function.update left wire outcome)
      (Function.update right wire outcome) refLeft refRight (by
        simpa only [Function.update_of_ne same] using outside)
    simp only [zero, ite_self]

private lemma supported_sequence (wire : Fin ctx.systemCount)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (first second : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      ctx ctx false) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (supported : QuditShift.WireSupported wire 0
      (second.execute environment Reference (first.execute environment Reference state))) :
    QuditShift.WireSupported wire 0 ((first.seq second).execute environment Reference state) := by
  exact Eq.mpr (congrArg (QuditShift.WireSupported wire 0)
    (Circuit.execute_seq (environment := environment) first second state))
    (QuditShift.supported_mapHistory wire 0 _ _ supported)

private lemma run_preserves
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (count : Nat) (wires : Fin count → Fin ctx.systemCount)
    (focus : Fin ctx.systemCount) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (supported : QuditShift.WireSupported focus 0 state) :
    QuditShift.WireSupported focus 0
      ((parameters.run count wires).execute environment Reference state) := by
  induction count generalizing History with
  | zero =>
      intro record left right refLeft refRight different
      rcases record with ⟨store, hidden, history, path⟩
      cases path
      change (((Circuit.id (allowAllocation := false)
        (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx).execute
          environment Reference state).block (store, (hidden, (history, ())))).matrix
            (left, refLeft) (right, refRight) = 0
      rw [Circuit.execute_id_block]
      exact supported (store, (hidden, history)) left right refLeft refRight different
  | succ count ih =>
      apply supported_sequence focus environment (parameters.one (wires 0))
        (parameters.run count (fun index => wires index.succ)) state
      exact ih _ _ (parameters.one_preserves environment (wires 0) focus state supported)

/-- Each actual selected wire is zero in every complete record, without an input-state promise. -/
lemma run_supported
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (count : Nat) (wires : Fin count → Fin ctx.systemCount)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) (index : Fin count) :
    QuditShift.WireSupported (wires index) 0
      ((parameters.run count wires).execute environment Reference state) := by
  induction count generalizing History with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      refine Fin.cases ?_ (fun next => ?_) index
      · apply supported_sequence (wires 0) environment (parameters.one (wires 0))
          (parameters.run count (fun index => wires index.succ)) state
        exact parameters.run_preserves environment count (fun index => wires index.succ)
          (wires 0) _ (parameters.one_supported environment (wires 0) state)
      · apply supported_sequence (wires next.succ) environment (parameters.one (wires 0))
          (parameters.run count (fun index => wires index.succ)) state
        exact ih _ _ next

/-- The actual whole-bank cleanup preserves the complete quantum and classical resident peak. -/
lemma circuit_peakResidentSpace
    (path : (parameters.circuit (services := services)).Path) :
    parameters.circuit.peakResidentSpace path = ctx.residentSpace :=
  parameters.circuit.fixed_peakResidentSpace path

end Parameters

end

end Cleanup

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
