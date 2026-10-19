/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.Dirty.Conjunction

/-!
# Cancellation of arbitrary conjunction-work values

Comparing the literal conjunction chain before and after its first Toffoli
removes every incoming work value. The remaining xor is exactly the source
conjunction. This is the Boolean correctness step needed to realize the
multi-control construction from elementary gates [dW19, qcnotes.tex:1335-1337].
-/

namespace QuantumAlg.EncodedBit.Word.ZeroTestLayout

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {tail : Nat}
variable (layout : ZeroTestLayout (encoding := encoding) tail)

/-- The conjunction of a source prefix, independent of all work and output bits. -/
def sourceConjunction (state : Data) (count : Nat) : Bool :=
  ((List.ofFn fun index : Fin (tail + 2) => (layout.source.bit index).get state).take count).all id

private lemma sourceConjunction_zero (state : Data) :
    sourceConjunction layout state 0 = true := by
  simp [sourceConjunction]

private lemma sourceConjunction_succ (state : Data) (index : Fin (tail + 2)) :
    sourceConjunction layout state (index.val + 1) =
      (sourceConjunction layout state index.val && (layout.source.bit index).get state) := by
  let bits := List.ofFn fun position : Fin (tail + 2) => (layout.source.bit position).get state
  have bound : index.val < bits.length := by
    simpa only [bits, List.length_ofFn] using index.isLt
  have splitPrefix : bits.take (index.val + 1) =
      bits.take index.val ++ [bits[index.val]'bound] :=
    (List.take_concat_get' bits index.val bound).symm
  change (bits.take (index.val + 1)).all id = _
  rw [splitPrefix, List.all_append]
  simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true, bits, List.getElem_ofFn]
  rfl

/-- The complete source conjunction tests every actual source coordinate. -/
lemma sourceConjunction_eq_true_iff (state : Data) :
    sourceConjunction layout state (tail + 2) = true ↔
      ∀ index, (layout.source.bit index).get state = true := by
  unfold sourceConjunction
  rw [List.take_of_length_le (by rw [List.length_ofFn])]
  simp only [List.all_eq_true, List.mem_ofFn, id_eq, forall_exists_index, forall_apply_eq_imp_iff]

private lemma xor_common_incoming (incoming left right control : Bool) :
    ((incoming ^^ (left && control)) ^^ (incoming ^^ (right && control))) =
      ((left ^^ right) && control) := by
  cases incoming <;> cases left <;> cases right <;> cases control <;> rfl

/-- The first physical Toffoli changes the full-chain result by precisely the source prefix. -/
lemma dirtyChain_firstGate_difference (positive : 0 < tail) (index : Fin tail)
    (state : Data) :
    ((layout.work.bit index).get
        (andStageIndexStep layout ((andGateAt layout ⟨0, positive⟩).step state)) ^^
      (layout.work.bit index).get (andStageIndexStep layout state)) =
        sourceConjunction layout state (index.val + 2) := by
  have result : ∀ value, ∀ index : Fin tail, index.val = value →
      ((layout.work.bit index).get
          (andStageIndexStep layout ((andGateAt layout ⟨0, positive⟩).step state)) ^^
        (layout.work.bit index).get (andStageIndexStep layout state)) =
          sourceConjunction layout state (index.val + 2) := by
    intro value
    refine Nat.strong_induction_on value ?_
    intro value inductionHypothesis index indexValue
    rw [dirtyAndChain_work, dirtyAndChain_work]
    by_cases initial : index.val = 0
    · have indexZero : index = ⟨0, positive⟩ := Fin.ext initial
      subst index
      simp only [chainControlA, chainControlB, andStageIndexStep_get_source,
        andGateAt_get_source, andGateAt_get_work, ↓reduceDIte]
      have sourceOne : chainSourceIndex (⟨0, positive⟩ : Fin tail) = 1 := by
        apply Fin.ext
        rfl
      rw [sourceOne]
      have prefixTwo := sourceConjunction_succ layout state (1 : Fin (tail + 2))
      have prefixOne := sourceConjunction_succ layout state (0 : Fin (tail + 2))
      simp only [Fin.val_one, Fin.val_zero, Nat.zero_add, Nat.reduceAdd] at prefixTwo prefixOne
      rw [prefixTwo, prefixOne, sourceConjunction_zero]
      cases (layout.work.bit ⟨0, positive⟩).get state <;>
        cases (layout.source.bit 0).get state <;> cases (layout.source.bit 1).get state <;> rfl
    · have distinct : (⟨0, positive⟩ : Fin tail) ≠ index := by
        intro equal
        exact initial (congrArg Fin.val equal.symm)
      rw [andGateAt_get_work_of_ne layout _ _ distinct]
      simp only [chainControlA, initial, ↓reduceDIte, chainControlB,
        andStageIndexStep_get_source, andGateAt_get_source]
      rw [xor_common_incoming]
      have previousLess : (previousWorkIndex index initial).val < value := by
        dsimp [previousWorkIndex]
        omega
      rw [inductionHypothesis _ previousLess _ rfl]
      have previousCount : (previousWorkIndex index initial).val + 2 = index.val + 1 := by
        dsimp [previousWorkIndex]
        omega
      rw [previousCount]
      exact (sourceConjunction_succ layout state (chainSourceIndex index)).symm
  exact result index.val index rfl

/-- The two actual final Toffoli controls differ by exactly the complete source conjunction. -/
lemma dirtyFinal_firstGate_difference (positive : 0 < tail) (state : Data) :
    (finalControl layout
        (andStageIndexStep layout ((andGateAt layout ⟨0, positive⟩).step state)) ^^
      finalControl layout (andStageIndexStep layout state)) =
        sourceConjunction layout state (tail + 2) := by
  have nonzero : tail ≠ 0 := Nat.ne_of_gt positive
  simp only [finalControl, nonzero, ↓reduceDIte, andStageIndexStep_get_source,
    andGateAt_get_source]
  have distribute (left right control : Bool) :
      ((left && control) ^^ (right && control)) = ((left ^^ right) && control) := by
    cases left <;> cases right <;> cases control <;> rfl
  rw [distribute, dirtyChain_firstGate_difference]
  have prefixCount : (lastWorkIndex tail nonzero).val + 2 = tail + 1 := by
    dsimp [lastWorkIndex]
    omega
  rw [prefixCount]
  exact (sourceConjunction_succ layout state (lastSourceIndex tail)).symm

end

end QuantumAlg.EncodedBit.Word.ZeroTestLayout
