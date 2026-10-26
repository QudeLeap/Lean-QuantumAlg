/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Resources.General
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Round.Resources

/-!
# Full-domain native event bounds of the same actual measured recycling round

The independent parity-independent multiplier pool is propagated through
the unchanged H/arithmetic/feedback/H/MZ-reset chronology, both exponent
streams, paid packing and complete reset/reload. The program syntax is
unchanged and no modulus parity is required [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Resources.General

noncomputable section

open Execution

/-- The all-parity multiplier pool charges the same three control gates and one readout. -/
def baseBudget (width : Nat) : ResourcePool model :=
  MAU.Multiplication.Gidney.Measured.Layout.generalMultiplicationBudget
    .empty BitWord.model .empty width + 2 • oneQubit + oneQubit + oneMeasurement

/-- Every actual earlier exponent bit retains its separate native phase opportunity. -/
def stageBudget (width position : Nat) : ResourcePool model :=
  baseBudget width + position • oneQubit

/-- The source-order suffix retains all chronological arithmetic and feedback opportunities. -/
def suffixBudget (width remaining position : Nat) : ResourcePool model :=
  remaining • baseBudget width + feedbackWork remaining position • oneQubit

/-- Both original exponent streams are independently charged in the complete member allowance. -/
def memberBudget (m ell width : Nat) : ResourcePool model :=
  resultBits m ell • baseBudget width + ((ell + m).choose 2 + ell.choose 2) • oneQubit

/-- All original packing, full physical reset and literal reload remain in the full-domain cap. -/
def roundBudget (m ell width N : Nat) : ResourcePool model :=
  memberBudget m ell width + Round.packingBudget m ell +
    (BankReset.eventBudget width + EncodedBit.Word.BasisLoad.xCount (seedLabel width N) •
      ResourcePool.singleton (model := model) (.gate .singleQubit))

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev GeneralCtx := context base noQuantum m ell width

/-- Every actual stage path satisfies the independent pool on every admitted arithmetic width. -/
lemma measuredGeneralStage_events (wide : 2 ≤ width) (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (GeneralCtx base noQuantum m ell width) (.finite 2))
    (modulus : BitVec width) (unit : (ZMod modulus.toNat)ˣ) (position : Fin bits)
    (path : (stage base noQuantum m ell width wide inverse outputs modulus unit position).Path) :
    (stage base noQuantum m ell width wide inverse outputs modulus unit position).resourcePool
      path ≤ stageBudget width position.val := by
  have firstH : ResourcePool.ofList ((single base noQuantum m ell width Gate.HOp).eventTrace
      BitWord.model .empty) ≤ oneQubit := le_rfl
  have arithmetic :=
    MAU.Multiplication.Gidney.Measured.Layout.multiplicationCircuit_pool_bound_general
      _ wide modulus _ _ _ (context_wires base noQuantum m ell width)
      (ventCell base noQuantum m ell width) path.2.1
  have phases := measuredFeedbackPrefix_events base noQuantum m ell width inverse outputs position
    position.val le_rfl path.2.2.1
  have reset := measuredControlReset_events base noQuantum m ell width (outputs position)
    path.2.2.2.2
  refine (seq_pool _ _ path _ _ firstH
    (seq_pool _ _ path.2 _ _ arithmetic (seq_pool _ _ path.2.2 _ _ phases
      (seq_pool _ _ path.2.2.2 _ _ firstH reset)))).trans_eq ?_
  simp only [stageBudget, baseBudget, two_nsmul]
  ac_rfl

/-- Literal suffix recursion accumulates the same general pool without parity or key witnesses. -/
lemma measuredGeneralSuffix_events (wide : 2 ≤ width) (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (GeneralCtx base noQuantum m ell width) (.finite 2))
    (modulus : BitVec width) (unit : (ZMod modulus.toNat)ˣ)
    (remaining position : Nat) (bounded : position + remaining ≤ bits)
    (path : (exponentSuffix base noQuantum m ell width wide inverse outputs modulus unit
      remaining position bounded).Path) :
    (exponentSuffix base noQuantum m ell width wide inverse outputs modulus unit
      remaining position bounded).resourcePool path ≤ suffixBudget width remaining position := by
  induction remaining generalizing position with
  | zero =>
      simp [exponentSuffix, Circuit.resourcePool, Circuit.eventTrace, suffixBudget, feedbackWork]
  | succ remaining ih =>
      have head := measuredGeneralStage_events base noQuantum m ell width wide inverse outputs
        modulus unit ⟨position, by omega⟩ path.1
      have tail := ih (position + 1) (by omega) path.2
      have full :
          (exponentSuffix base noQuantum m ell width wide inverse outputs modulus unit
            (remaining + 1) position bounded).resourcePool path ≤
              stageBudget width position + suffixBudget width remaining (position + 1) := by
        simpa only [exponentSuffix, Circuit.resourcePool, Circuit.eventTrace,
          ResourcePool.ofList_append] using add_le_add head tail
      refine full.trans_eq ?_
      simp only [suffixBudget, stageBudget, measuredFeedbackWork_succ, succ_nsmul, add_nsmul]
      ac_rfl

/-- Every measured stage of one complete actual exponent retains its full-domain allowance. -/
lemma measuredGeneralExponent_events (wide : 2 ≤ width) (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (GeneralCtx base noQuantum m ell width) (.finite 2))
    (modulus : BitVec width) (unit : (ZMod modulus.toNat)ˣ)
    (path : (exponentCode base noQuantum m ell width wide inverse outputs modulus unit).Path) :
    (exponentCode base noQuantum m ell width wide inverse outputs modulus unit).resourcePool path ≤
      bits • baseBudget width + bits.choose 2 • oneQubit := by
  simpa only [exponentCode, suffixBudget, feedbackWork, Nat.mul_zero, Nat.zero_add] using
    measuredGeneralSuffix_events base noQuantum m ell width wide inverse outputs
      modulus unit bits 0 (by omega) path

/-- The two original actual exponent streams satisfy the general native member allowance. -/
lemma measuredGeneralMember_events (wide : 2 ≤ width) (modulus : BitVec width)
    (generator target : (ZMod modulus.toNat)ˣ)
    (path : (member base noQuantum m ell width wide modulus generator target).Path) :
    (member base noQuantum m ell width wide modulus generator target).resourcePool path ≤
      memberBudget m ell width := by
  have first := measuredGeneralExponent_events base noQuantum m ell width wide true
    (firstCell base noQuantum m ell width) modulus generator path.1
  have second := measuredGeneralExponent_events base noQuantum m ell width wide true
    (secondCell base noQuantum m ell width) modulus target⁻¹ path.2
  have full : (member base noQuantum m ell width wide modulus generator target).resourcePool path ≤
      ((ell + m) • baseBudget width + (ell + m).choose 2 • oneQubit) +
        (ell • baseBudget width + ell.choose 2 • oneQubit) := by
    simpa only [member, Circuit.resourcePool, Circuit.eventTrace, ResourcePool.ofList_append] using
      add_le_add first second
  refine full.trans_eq ?_
  simp only [memberBudget, resultBits, add_nsmul]
  ac_rfl

/-- The same actual complete round obeys the general cap for every original parameter value. -/
lemma measuredGeneralRound_events {shape : CShape}
    (parameter : CInputRef (GeneralCtx base noQuantum m ell width) shape)
    (wide : 2 ≤ width) (modulus : BitVec width)
    (generator target : shape.Value → (ZMod modulus.toNat)ˣ)
    (result : CWriteRef (GeneralCtx base noQuantum m ell width) (.bits (resultBits m ell)))
    (path : (Round.code base noQuantum m ell width parameter wide modulus
      generator target result).Path) :
    (Round.code base noQuantum m ell width parameter wide modulus
      generator target result).resourcePool path ≤ roundBudget m ell width modulus.toNat := by
  have selected :
      (Round.selected base noQuantum m ell width parameter wide modulus
        generator target).resourcePool path.1.1 ≤ memberBudget m ell width := by
    change (Circuit.embed (allowAllocation := true)
      (ContextEmbedding.identity (GeneralCtx base noQuantum m ell width))
      (member base noQuantum m ell width wide modulus (generator path.1.1.1)
        (target path.1.1.1))).resourcePool path.1.1.2 ≤ _
    rw [Circuit.resourcePool_embed]
    exact measuredGeneralMember_events base noQuantum m ell width wide modulus
      (generator path.1.1.1) (target path.1.1.1) path.1.1.2
  have packing := Round.measuredRound_packing_events base noQuantum m ell width result path.1.2
  have restart := Round.measuredRound_restart_events base noQuantum m ell width modulus path.2
  have sampled :
      (Round.sampled base noQuantum m ell width parameter wide modulus
        generator target result).resourcePool path.1 ≤
          memberBudget m ell width + Round.packingBudget m ell := by
    simpa only [Round.sampled, Circuit.resourcePool, Circuit.eventTrace,
      ResourcePool.ofList_append] using add_le_add selected packing.le
  simpa only [Round.code, roundBudget, Circuit.resourcePool, Circuit.eventTrace,
    ResourcePool.ofList_append] using add_le_add sampled restart

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Resources.General
