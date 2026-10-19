/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.Stage.Blocks
import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.Recursion
import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.Outputs
import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.Tail
import all QuantumAlg.Primitives.QFT.Semiclassical.Mathematics
import all QuantumAlg.Core.Execution.Store.WritePrefix

/-!
# Complete stored instrument of the actual native Fourier recursion

Each branch matrix below is the product of the actual H, observed projector,
selected native phase and recursively executed tail matrices. The theorem
derives its complete stored density from Construction.code. It retains all
physical systems, arbitrary original storage, mixed input and reference. No
instrument or matrix-equality certificate is a premise. Source row identification
is a separate derived matrix equality in genuine physical bank coordinates.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical

noncomputable section

open Execution
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum}

/-- Branch matrices formed only from actual native stages and their actual recursive tail. -/
def nativeOutcomeKraus {environment : OracleModel.empty.Interpretation} (inverse : Bool)
    (Reference : Register) :
    (n : Nat) → (wires : Fin n ↪ Fin ctx.systemCount) →
      (∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2) →
      Bits n → HilbertOperator (ctx.register.prod Reference)
  | 0, _, _, _ => 1
  | n + 1, wires, qubits, (head, tail) =>
      nativeOutcomeKraus (environment := environment) inverse Reference n (tailPhysicalWires wires)
        (fun i => qubits i.succ) tail *
          nativeStageKraus
            (environment := environment) inverse (wires 0) (qubits 0) (tailPhysicalWires wires)
            (fun i => qubits i.succ) Reference
            (Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) (qubits 0)).symm head)

private lemma storedConjugation_compose {S First Second : Type}
    [Fintype S] [Fintype First] [Fintype Second] {R : Register}
    (before : First → S → S) (after : Second → S → S)
    (leading : First → HilbertOperator R) (trailing : Second → HilbertOperator R)
    (density : S → HilbertOperator R) (stored : S) :
    (∑ intermediate : S, ∑ second : Second,
      if after second intermediate = stored then
        trailing second *
          (∑ original : S, ∑ first : First,
            if before first original = intermediate then
              leading first * density original * (leading first).conjTranspose
            else 0) * (trailing second).conjTranspose
      else 0) =
      ∑ original : S, ∑ first : First, ∑ second : Second,
        if after second (before first original) = stored then
          (trailing second * leading first) * density original *
            (trailing second * leading first).conjTranspose
        else 0 := by
  let contribution (intermediate : S) (second : Second) (original : S) (first : First) :=
    if after second intermediate = stored then
      if before first original = intermediate then
        trailing second * (leading first * density original * (leading first).conjTranspose) *
          (trailing second).conjTranspose
      else 0
    else 0
  calc
    _ = ∑ intermediate : S, ∑ second : Second, ∑ original : S, ∑ first : First,
        contribution intermediate second original first := by
      apply Finset.sum_congr rfl
      intro intermediate _
      apply Finset.sum_congr rfl
      intro second _
      by_cases reaches : after second intermediate = stored
      · simp only [contribution, if_pos reaches, Matrix.mul_sum, Matrix.sum_mul,
          mul_ite, ite_mul, Matrix.mul_zero, Matrix.zero_mul]
      · simp only [contribution, if_neg reaches, Finset.sum_const_zero]
    _ = ∑ original : S, ∑ first : First, ∑ intermediate : S, ∑ second : Second,
        contribution intermediate second original first := by
      have swapped :
          (∑ left : S × Second, ∑ right : S × First,
            contribution left.1 left.2 right.1 right.2) =
          ∑ right : S × First, ∑ left : S × Second,
            contribution left.1 left.2 right.1 right.2 := Finset.sum_comm
      simpa only [Fintype.sum_prod_type] using swapped
    _ = ∑ original : S, ∑ first : First, ∑ second : Second, ∑ intermediate : S,
        contribution intermediate second original first := by
      apply Finset.sum_congr rfl
      intro original _
      apply Finset.sum_congr rfl
      intro first _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro original _
      apply Finset.sum_congr rfl
      intro first _
      apply Finset.sum_congr rfl
      intro second _
      rw [Finset.sum_eq_single (before first original)]
      · simp only [contribution, if_true, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      · intro other _ different
        simp only [contribution, if_neg (Ne.symm different), ite_self]
      · intro absent
        exact False.elim (absent (Finset.mem_univ _))

/-- The actual recursion writes every output and keeps each complete final stored density. -/
lemma code_instrument_store_matrix {environment : (ExecutionModel.quantum AlgorithmGate.model
    .empty).Environment} (inverse : Bool) (n : Nat)
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
      change (((code inverse n (tailPhysicalWires wires) (fun i => qubits i.succ)
        (fun i => outputs i.succ)).execute environment) Reference
          (((stageCode inverse (wires 0) (qubits 0) (tailPhysicalWires wires)
            (fun i => qubits i.succ) (outputs 0)).execute environment) Reference state)
        |>.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix = _
      refine (ih (tailPhysicalWires wires) (fun i => qubits i.succ)
        (fun i => outputs i.succ)
        (((stageCode inverse (wires 0) (qubits 0) (tailPhysicalWires wires)
          (fun i => qubits i.succ) (outputs 0)).execute environment) Reference state)).trans ?_
      have stageBlocks := fun original => nativeStage_store_binary_blocks_matrix
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

end

end QuantumAlg.QuantumFourierTransform.Semiclassical
