/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.OneHot.Address

/-!
# The actual unitary binary-to-unary program

One actual initial X creates the unary token. The successive controlled
move words and physical parallel CNOT layers select its original binary
address. All output positions must initially be zero; address values remain
arbitrary and are preserved by every actual stage.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.UnaryFrame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Compile every remaining actual doubling stage on the original output range. -/
def stagesProgramAt (frame : UnaryFrame encoding width) (physical : QubitLayout encoding.width)
    (oracles : OracleModel) : (remaining depth : Nat) → depth + remaining = width →
      UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum
  | 0, _, _ => UnitaryCircuit.identity _ _ _
  | remaining + 1, depth, fits =>
      ((frame.stage depth (by omega)).program physical oracles).seq
        (frame.stagesProgramAt physical oracles remaining (depth + 1) (by omega))

/-- Complete arbitrary-input operational action of those same physical stages. -/
def stagesStepAt (frame : UnaryFrame encoding width) :
    (remaining depth : Nat) → depth + remaining = width → Data → Data
  | 0, _, _, state => state
  | remaining + 1, depth, fits, state =>
      frame.stagesStepAt remaining (depth + 1) (by omega)
        ((frame.stage depth (by omega)).step state)

/-- The stage word has its exact full-data encoded action, independently of clean inputs. -/
lemma stagesProgramAt_realizes (frame : UnaryFrame encoding width)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (remaining depth : Nat) (fits : depth + remaining = width)
    (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes encoding
      (frame.stagesProgramAt physical oracles remaining depth fits) environment
      (frame.stagesStepAt remaining depth fits) := by
  induction remaining generalizing depth with
  | zero => exact UnitaryCircuit.Realizes.identityAt _ _ _ _ _
  | succ remaining ih =>
      exact ((frame.stage depth (by omega)).program_realizes physical oracles environment).seq
        (ih (depth + 1) (by omega))

/-- Every original binary address field survives the full sequence of actual unary stages. -/
lemma stagesStepAt_address (frame : UnaryFrame encoding width) (remaining depth : Nat)
    (fits : depth + remaining = width) (bit : Fin width) (state : Data) :
    (frame.address bit).get (frame.stagesStepAt remaining depth fits state) =
      (frame.address bit).get state := by
  induction remaining generalizing depth state with
  | zero => rfl
  | succ remaining ih =>
      dsimp only [stagesStepAt]
      rw [ih, frame.stage_address]

/-- The unique token advances through every original binary address bit. -/
lemma stagesStepAt_oneHot (frame : UnaryFrame encoding width) (remaining depth : Nat)
    (fits : depth + remaining = width) (state : Data)
    (oneHot : frame.OneHot (frame.prefixLabel depth (by omega) state) state) :
    frame.OneHot (frame.prefixLabel width (Nat.le_refl _) state)
      (frame.stagesStepAt remaining depth fits state) := by
  induction remaining generalizing depth state with
  | zero =>
      have same : depth = width := by omega
      subst depth
      exact oneHot
  | succ remaining ih =>
      have advanced := frame.stage_oneHot depth (by omega)
        (frame.prefixLabel depth (by omega) state) (frame.prefixLabel_lt depth (by omega) state)
        state oneHot
      rw [frame.nextLabel_prefixLabel] at advanced
      rw [← frame.prefixLabel_stage depth (by omega) (depth + 1) (by omega) state] at advanced
      have final := ih (depth + 1) (by omega) _ advanced
      rw [frame.prefixLabel_stage] at final
      exact final

/-- The initial token is an actual native X on the original position zero. -/
def program (frame : UnaryFrame encoding width) (physical : QubitLayout encoding.width)
    (oracles : OracleModel) : UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  ((GateSpec.x (frame.target ⟨0, Nat.two_pow_pos width⟩)).program physical oracles).seq
    (frame.stagesProgramAt physical oracles width 0 (by omega))

/-- Full-data action of the original initial X and every original unary stage. -/
def step (frame : UnaryFrame encoding width) (state : Data) : Data :=
  frame.stagesStepAt width 0 (by omega) ((frame.target ⟨0, Nat.two_pow_pos width⟩).flip state)

/-- The complete actual unitary has the exact same arbitrary-input operational action. -/
lemma program_realizes (frame : UnaryFrame encoding width) (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes encoding (frame.program physical oracles) environment frame.step := by
  have initial : UnitaryCircuit.Realizes encoding
      ((GateSpec.x (frame.target ⟨0, Nat.two_pow_pos width⟩)).program physical oracles) environment
      (frame.target ⟨0, Nat.two_pow_pos width⟩).flip :=
    GateSpec.realizes physical oracles _ environment
  exact initial.seq (frame.stagesProgramAt_realizes physical oracles width 0 (by omega) environment)

private lemma seed_oneHot (frame : UnaryFrame encoding width) (state : Data)
    (clean : ∀ index, (frame.target index).get state = false) :
    frame.OneHot ⟨0, Nat.two_pow_pos width⟩
      ((frame.target ⟨0, Nat.two_pow_pos width⟩).flip state) := by
  intro index
  by_cases same : index = ⟨0, Nat.two_pow_pos width⟩
  · subst index
    rw [EncodedBit.get_flip_self, clean]
    rfl
  · rw [EncodedBit.get_flip_of_wire_ne _ _
      (fun equal => same (frame.targetDistinct equal).symm), clean]
    exact (decide_eq_false same).symm

/-- The actual program produces exactly one set output at the original complete address. -/
lemma step_oneHot (frame : UnaryFrame encoding width) (state : Data)
    (clean : ∀ index, (frame.target index).get state = false) :
    frame.OneHot (frame.prefixLabel width (Nat.le_refl _) state) (frame.step state) := by
  have seeded : frame.OneHot
      (frame.prefixLabel 0 (by omega) ((frame.target ⟨0, Nat.two_pow_pos width⟩).flip state))
      ((frame.target ⟨0, Nat.two_pow_pos width⟩).flip state) := frame.seed_oneHot state clean
  have final := frame.stagesStepAt_oneHot width 0 (by omega) _ seeded
  have addressSame := frame.prefixLabel_congr width (Nat.le_refl _)
    ((frame.target ⟨0, Nat.two_pow_pos width⟩).flip state) state
    (fun index => EncodedBit.get_flip_of_wire_ne _ _ (Ne.symm (frame.outside index _)) state)
  rw [addressSame] at final
  exact final

/-- One-hot preparation retains all original binary address readouts. -/
lemma step_address (frame : UnaryFrame encoding width) (bit : Fin width) (state : Data) :
    (frame.address bit).get (frame.step state) = (frame.address bit).get state := by
  unfold step
  rw [frame.stagesStepAt_address]
  exact EncodedBit.get_flip_of_wire_ne _ _ (Ne.symm (frame.outside bit _)) state

end

end QuantumAlg.EncodedBit.WindowLookup.UnaryFrame
