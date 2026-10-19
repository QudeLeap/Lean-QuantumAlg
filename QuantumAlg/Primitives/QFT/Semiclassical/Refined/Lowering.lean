/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Refined.Construction
import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.Instrument
import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.Stage.Blocks
import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.Recursion
import all QuantumAlg.Core.Execution.Measured.Stage
import all QuantumAlg.Core.Execution.Store.History
import all QuantumAlg.Core.Execution.Store.Blocks

/-!
# Actual stored-instrument lowering of the separately counted Fourier schedule

The fine language and the default language execute the same physical H,
measurement, stored feedback and recursive tail. Their literal native gate
matrices agree by the concrete gate definitions. Each complete final store
therefore has the same full density matrix, including arbitrary original
storage correlations, every spectator system and the external reference.

This specialized structural proof derives the common instrument from both
actual programs. No program-equivalence or matrix certificate is an input,
and no generic compiler or alternative interpreter is introduced.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Refined

noncomputable section

open Execution
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum}

/-- The same literal head stage, with separately counted native H and phase tokens. -/
def stageCode (inverse : Bool) {n : Nat} (head : Fin ctx.systemCount)
    (headQubit : (ctx.quantumLayout.wire head).dimension = 2)
    (tail : Fin n ↪ Fin ctx.systemCount)
    (tailQubits : ∀ i, (ctx.quantumLayout.wire (tail i)).dimension = 2)
    (result : CWriteRef ctx (.finite (ctx.quantumLayout.wire head).dimension)) :
    Circuit (.quantum SemiclassicalFourierGate.model .empty) ctx ctx false :=
  (Circuit.unitary (operations := .empty) (classicalOracles := .empty)
    (SemiclassicalFourierGate.hadamardAt ctx.quantumLayout .empty head headQubit)).seq
    ((Circuit.measureZ head result).seq (feedbackCode inverse tail tailQubits result))

/-- Real fine-model and default-model stages have equal complete final-store densities. -/
lemma stageCode_lowering_store_matrix {environment : (ExecutionModel.quantum
    SemiclassicalFourierGate.model .empty).Environment} (inverse : Bool) {n : Nat}
    (head : Fin ctx.systemCount) (headQubit : (ctx.quantumLayout.wire head).dimension = 2)
    (tail : Fin n ↪ Fin ctx.systemCount)
    (tailQubits : ∀ i, (ctx.quantumLayout.wire (tail i)).dimension = 2)
    (result : CWriteRef ctx (.finite (ctx.quantumLayout.wire head).dimension))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store ctx) :
    (((stageCode inverse head headQubit tail tailQubits result).execute environment) Reference state
      |>.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      (((Semiclassical.stageCode inverse head headQubit tail tailQubits result).execute
        ⟨environment.quantum, environment.classical⟩)
        Reference state |>.filterClassical
          (fun entry => entry.1 = stored)).quantumMarginal.matrix := by
  have fine := Circuit.unitary_measureZ_selected_store_matrix
    (operations := .empty) (services := .empty)
    (SemiclassicalFourierGate.hadamardAt ctx.quantumLayout .empty head headQubit)
    head result (selectedPhase inverse tail tailQubits) environment state stored
  have native := nativeStage_store_matrix
    (environment := ⟨environment.quantum, environment.classical⟩) inverse head headQubit tail
    tailQubits result state stored
  refine fine.trans (Eq.trans ?_ native.symm)
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases written : original.1.write result (.finite outcome) = stored
  · simp only [if_pos written, qftSemiclassical_refinedSelectedPhase_matrix,
      SemiclassicalFourierGate.semiclassicalFourier_hadamardAt_matrix, nativeStageKraus]
  · simp only [if_neg written]

/-- Lowering also preserves the original stored-block sum, without fixing any input cell. -/
lemma stageCode_store_binary_blocks_matrix {environment : (ExecutionModel.quantum
    SemiclassicalFourierGate.model .empty).Environment} (inverse : Bool) {n : Nat}
    (head : Fin ctx.systemCount) (headQubit : (ctx.quantumLayout.wire head).dimension = 2)
    (tail : Fin n ↪ Fin ctx.systemCount)
    (tailQubits : ∀ i, (ctx.quantumLayout.wire (tail i)).dimension = 2)
    (result : CWriteRef ctx (.finite (ctx.quantumLayout.wire head).dimension))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store ctx) :
    (((stageCode inverse head headQubit tail tailQubits result).execute environment) Reference state
      |>.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ∑ original : Store ctx, ∑ bit : Fin 2,
        let outcome := Fin.cast
          (congrArg (fun size : ℕ+ => (size : Nat)) headQubit).symm bit
        if original.write result (.finite outcome) = stored then
          nativeStageKraus
            (environment := environment.quantum) inverse head headQubit tail tailQubits Reference
            outcome *
            (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix *
              (nativeStageKraus
                (environment := environment.quantum) inverse head headQubit tail tailQubits
                Reference outcome).conjTranspose
        else 0 := by
  rw [stageCode_lowering_store_matrix]
  exact nativeStage_store_binary_blocks_matrix inverse head headQubit tail tailQubits
    result state stored

/-- The empty fine schedule preserves every actual stored quantum-reference block. -/
lemma code_zero_store {environment : (ExecutionModel.quantum SemiclassicalFourierGate.model
    .empty).Environment} (inverse : Bool)
    (wires : Fin 0 ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (outputs : ∀ i, CWriteRef ctx (.finite (ctx.quantumLayout.wire (wires i)).dimension))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store ctx) :
    (((code inverse 0 wires qubits outputs).execute environment) Reference state
      |>.filterClassical (fun entry => entry.1 = stored)).quantumMarginal =
      (state.filterClassical (fun entry => entry.1 = stored)).quantumMarginal := by
  rw [code, Circuit.execute_id]
  calc
    _ = (ExecutionState.filterClassical
        (state.mapHistory (fun record => (record.1, (record.2, ()))))
        (fun entry => entry.1 = stored)).quantumMarginal := by
      apply congrArg (fun result : State ctx Reference
        (ClassicalOracleModel.empty.HiddenState × (History × Unit)) =>
          (result.filterClassical (fun entry => entry.1 = stored)).quantumMarginal)
      exact ExecutionState.executionState_mapClassical_congr state rfl
    _ = _ := State.mapHistory_store_marginal _ _ _

/-- Reassociation changes only mathematical path histories, retaining the real stage output. -/
lemma stageCode_continuation_store {environment : (ExecutionModel.quantum
    SemiclassicalFourierGate.model .empty).Environment} (inverse : Bool) {n : Nat}
    (head : Fin ctx.systemCount) (headQubit : (ctx.quantumLayout.wire head).dimension = 2)
    (tail : Fin n ↪ Fin ctx.systemCount)
    (tailQubits : ∀ i, (ctx.quantumLayout.wire (tail i)).dimension = 2)
    (result : CWriteRef ctx (.finite (ctx.quantumLayout.wire head).dimension))
    (continuation : Circuit (.quantum SemiclassicalFourierGate.model .empty) ctx ctx false)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store ctx) :
    ((((Circuit.unitary (allowAllocation := false)
        (operations := .empty) (classicalOracles := .empty)
        (SemiclassicalFourierGate.hadamardAt ctx.quantumLayout .empty head headQubit)).seq
      ((Circuit.measureZ head result).seq
        ((feedbackCode inverse tail tailQubits result).seq continuation))).execute environment)
      Reference state |>.filterClassical (fun entry => entry.1 = stored)).quantumMarginal =
      ((continuation.execute environment) Reference
        (((stageCode inverse head headQubit tail tailQubits result).execute environment)
          Reference state)
        |>.filterClassical (fun entry => entry.1 = stored)).quantumMarginal := by
  let leading : Circuit (.quantum SemiclassicalFourierGate.model .empty) ctx ctx false :=
    .unitary (SemiclassicalFourierGate.hadamardAt ctx.quantumLayout .empty head headQubit)
  let measured : Circuit (.quantum SemiclassicalFourierGate.model .empty) ctx ctx false :=
    .measureZ head result
  let feedback := feedbackCode inverse tail tailQubits result
  calc
    _ = (ExecutionState.filterClassical
        (((measured.seq (feedback.seq continuation)).execute environment) Reference
          ((leading.execute environment) Reference state))
        (fun entry => entry.1 = stored)).quantumMarginal :=
      Circuit.seq_store_marginal leading (measured.seq (feedback.seq continuation)) environment
        state stored
    _ = (ExecutionState.filterClassical
        ((((measured.seq feedback).seq continuation).execute environment) Reference
          ((leading.execute environment) Reference state))
        (fun entry => entry.1 = stored)).quantumMarginal :=
      Circuit.seq_assoc_store_marginal measured feedback continuation environment
        ((leading.execute environment) Reference state) stored
    _ = (ExecutionState.filterClassical
        (((leading.seq ((measured.seq feedback).seq continuation)).execute environment)
          Reference state)
        (fun entry => entry.1 = stored)).quantumMarginal :=
      (Circuit.seq_store_marginal leading ((measured.seq feedback).seq continuation) environment
        state stored).symm
    _ = (ExecutionState.filterClassical
        ((((leading.seq (measured.seq feedback)).seq continuation).execute environment)
          Reference state)
        (fun entry => entry.1 = stored)).quantumMarginal :=
      Circuit.seq_assoc_store_marginal leading (measured.seq feedback) continuation environment
        state stored
    _ = _ := Circuit.seq_store_marginal
      (leading.seq (measured.seq feedback)) continuation environment state stored

/-- One fine recursive call consumes exactly its actual measured-and-fed-back head stage. -/
lemma code_succ_store {environment : (ExecutionModel.quantum SemiclassicalFourierGate.model
    .empty).Environment} (inverse : Bool) (n : Nat)
    (wires : Fin (n + 1) ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (outputs : ∀ i, CWriteRef ctx (.finite (ctx.quantumLayout.wire (wires i)).dimension))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store ctx) :
    (((code inverse (n + 1) wires qubits outputs).execute environment) Reference state
      |>.filterClassical (fun entry => entry.1 = stored)).quantumMarginal =
      (((code inverse n (tailPhysicalWires wires) (fun i => qubits i.succ)
        (fun i => outputs i.succ)).execute environment) Reference
        (((stageCode inverse (wires 0) (qubits 0) (tailPhysicalWires wires)
          (fun i => qubits i.succ) (outputs 0)).execute environment) Reference state)
        |>.filterClassical (fun entry => entry.1 = stored)).quantumMarginal := by
  dsimp only [code]
  exact stageCode_continuation_store inverse _ _ _ _ _ _ state stored

/-- The fine schedule derives the same actual default-native branch products and writes. -/
lemma code_instrument_store_matrix {environment : (ExecutionModel.quantum
    SemiclassicalFourierGate.model .empty).Environment} (inverse : Bool) (n : Nat)
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (outputs : ∀ i, CWriteRef ctx (.finite (ctx.quantumLayout.wire (wires i)).dimension))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store ctx) :
    (((code inverse n wires qubits outputs).execute environment) Reference state
      |>.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ∑ original : Store ctx, ∑ outcome : Bits n,
        if outcomeStore wires qubits outputs original outcome = stored then
          nativeOutcomeKraus
            (environment := environment.quantum) inverse Reference n wires qubits outcome *
            (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix *
              (nativeOutcomeKraus
                (environment := environment.quantum) inverse Reference n wires qubits
                outcome).conjTranspose
        else 0 := by
  induction n generalizing History with
  | zero =>
      rw [code_zero_store]
      change _ = ∑ original : Store ctx, ∑ _ : Unit,
        if original = stored then
          (1 : HilbertOperator (ctx.register.prod Reference)) *
            (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix *
              (1 : HilbertOperator (ctx.register.prod Reference)).conjTranspose
        else 0
      simp only [Fintype.sum_unique, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
  | succ n ih =>
      rw [code_succ_store]
      refine (ih (tailPhysicalWires wires) (fun i => qubits i.succ)
        (fun i => outputs i.succ)
        (((stageCode inverse (wires 0) (qubits 0) (tailPhysicalWires wires)
          (fun i => qubits i.succ) (outputs 0)).execute environment) Reference state)).trans ?_
      have stageBlocks := fun original => stageCode_store_binary_blocks_matrix
        (environment := environment)
        inverse (wires 0) (qubits 0) (tailPhysicalWires wires)
        (fun i => qubits i.succ) (outputs 0) state original
      have regrouped := congrArg
        (fun density : Store ctx → HilbertOperator (ctx.register.prod Reference) =>
          ∑ intermediate : Store ctx, ∑ outcome : Bits n,
            if outcomeStore (tailPhysicalWires wires) (fun i => qubits i.succ)
                (fun i => outputs i.succ) intermediate outcome = stored then
              nativeOutcomeKraus
                (environment := environment.quantum) inverse Reference n (tailPhysicalWires wires)
                  (fun i => qubits i.succ) outcome * density intermediate *
                (nativeOutcomeKraus
                  (environment := environment.quantum) inverse Reference n (tailPhysicalWires wires)
                  (fun i => qubits i.succ) outcome).conjTranspose
            else 0) (funext stageBlocks)
      refine regrouped.trans ?_
      refine (storedConjugation_compose
        (fun bit original => original.write (outputs 0)
          (.finite (Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) (qubits 0)).symm bit)))
        (fun outcome original => outcomeStore (tailPhysicalWires wires)
          (fun i => qubits i.succ) (fun i => outputs i.succ) original outcome)
        (fun bit => nativeStageKraus
          (environment := environment.quantum) inverse (wires 0) (qubits 0) (tailPhysicalWires
          wires)
          (fun i => qubits i.succ) Reference
          (Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) (qubits 0)).symm bit))
        (fun outcome => nativeOutcomeKraus
          (environment := environment.quantum) inverse Reference n (tailPhysicalWires wires)
          (fun i => qubits i.succ) outcome)
        (fun original =>
          (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix)
        stored).trans ?_
      change _ = ∑ original : Store ctx, ∑ outcome : Fin 2 × Bits n,
        if outcomeStore wires qubits outputs original outcome = stored then
          nativeOutcomeKraus
            (environment := environment.quantum) inverse Reference (n + 1) wires qubits outcome *
            (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix *
              (nativeOutcomeKraus
                (environment := environment.quantum) inverse Reference (n + 1) wires qubits
                outcome).conjTranspose
        else 0
      simp only [Fintype.sum_prod_type, nativeOutcomeKraus,
        outcomeStore_head_tail, tailPhysicalWires]
      rfl

/-- Full physical lowering preserves every final store for arbitrary mixed inputs and reference. -/
lemma code_lowering_store_matrix {environment : (ExecutionModel.quantum
    SemiclassicalFourierGate.model .empty).Environment} (inverse : Bool) (n : Nat)
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (outputs : ∀ i, CWriteRef ctx (.finite (ctx.quantumLayout.wire (wires i)).dimension))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store ctx) :
    (((code inverse n wires qubits outputs).execute environment) Reference state
      |>.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      (((Semiclassical.code inverse n wires qubits outputs).execute ⟨environment.quantum,
        environment.classical⟩) Reference state
        |>.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix := by
  rw [code_instrument_store_matrix, Semiclassical.code_instrument_store_matrix]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Refined
