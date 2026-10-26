/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.FTQC.CliffordT.Checker.Basic
public import QuantumAlg.Analysis.FTQC.CliffordT.CertificateData

/-!
# Kernel verification of synthesized rotation candidates

Generated accumulator checkpoints split long word reductions into eight-letter steps.
Each step and the final rational error bound are proved by kernel computation.
The final theorem rewrites the original checker, retaining its semantic soundness.
-/

section

namespace QuantumAlg.CliffordT
private def word14Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word14State1 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word14Step0 :
    word14Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word14State1 := by decide +kernel

private def word14Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word14State2 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word14Step1 :
    word14Chunk1.foldl (fun acc a => a.applyPacked acc)
      word14State1 = word14State2 := by decide +kernel

private def word14Chunk2 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word14State3 : PackedMat2 :=
    ⟨⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word14Step2 :
    word14Chunk2.foldl (fun acc a => a.applyPacked acc)
      word14State2 = word14State3 := by decide +kernel

private def word14Chunk3 : List Letter := [.h, .s, .h, .s, .h, .s, .s, .s]
private def word14State4 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩⟩⟩
private lemma word14Step3 :
    word14Chunk3.foldl (fun acc a => a.applyPacked acc)
      word14State3 = word14State4 := by decide +kernel

private def word14Chunk4 : List Letter := [.s, .h, .t, .h, .s, .t, .h, .s]
private def word14State5 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word14Step4 :
    word14Chunk4.foldl (fun acc a => a.applyPacked acc)
      word14State4 = word14State5 := by decide +kernel

private def word14Chunk5 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word14State6 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word14Step5 :
    word14Chunk5.foldl (fun acc a => a.applyPacked acc)
      word14State5 = word14State6 := by decide +kernel

private def word14Chunk6 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word14State7 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩,
       ⟨((7 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((5 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word14Step6 :
    word14Chunk6.foldl (fun acc a => a.applyPacked acc)
      word14State6 = word14State7 := by decide +kernel

private def word14Chunk7 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word14State8 : PackedMat2 :=
    ⟨⟨⟨((-5 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((11 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((-11 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        (0 : Dyadic)⟩⟩⟩
private lemma word14Step7 :
    word14Chunk7.foldl (fun acc a => a.applyPacked acc)
      word14State7 = word14State8 := by decide +kernel

private def word14Chunk8 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word14State9 : PackedMat2 :=
    ⟨⟨⟨((11 : Dyadic) * half ^ 5),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((-11 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-13 : Dyadic) * half ^ 5),
        ((-11 : Dyadic) * half ^ 5)⟩,
       ⟨((-9 : Dyadic) * half ^ 5),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((11 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((-11 : Dyadic) * half ^ 5),
        ((-11 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-13 : Dyadic) * half ^ 5),
        ((11 : Dyadic) * half ^ 5)⟩,
       ⟨((11 : Dyadic) * half ^ 5),
        (0 : Dyadic)⟩⟩⟩
private lemma word14Step8 :
    word14Chunk8.foldl (fun acc a => a.applyPacked acc)
      word14State8 = word14State9 := by decide +kernel

private def word14Chunk9 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word14State10 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 4),
        ((5 : Dyadic) * half ^ 5)⟩,
       ⟨((13 : Dyadic) * half ^ 5),
        ((-3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((13 : Dyadic) * half ^ 5),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 4),
        ((5 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word14Step9 :
    word14Chunk9.foldl (fun acc a => a.applyPacked acc)
      word14State9 = word14State10 := by decide +kernel

private def word14Chunk10 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word14State11 : PackedMat2 :=
    ⟨⟨⟨((-17 : Dyadic) * half ^ 6),
        ((1 : Dyadic) * half ^ 7)⟩,
       ⟨((-3 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-23 : Dyadic) * half ^ 5),
        ((19 : Dyadic) * half ^ 7)⟩,
       ⟨((-21 : Dyadic) * half ^ 6),
        ((-43 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-23 : Dyadic) * half ^ 5),
        ((19 : Dyadic) * half ^ 7)⟩,
       ⟨((21 : Dyadic) * half ^ 6),
        ((43 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((17 : Dyadic) * half ^ 6),
        ((-1 : Dyadic) * half ^ 7)⟩,
       ⟨((-3 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word14Step10 :
    word14Chunk10.foldl (fun acc a => a.applyPacked acc)
      word14State10 = word14State11 := by decide +kernel

private def word14Chunk11 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word14State12 : PackedMat2 :=
    ⟨⟨⟨((-27 : Dyadic) * half ^ 6),
        ((23 : Dyadic) * half ^ 8)⟩,
       ⟨((17 : Dyadic) * half ^ 7),
        ((-49 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-35 : Dyadic) * half ^ 7),
        ((83 : Dyadic) * half ^ 8)⟩,
       ⟨((-15 : Dyadic) * half ^ 5),
        ((-83 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((95 : Dyadic) * half ^ 8)⟩,
       ⟨((-83 : Dyadic) * half ^ 7),
        ((-25 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-13 : Dyadic) * half ^ 7),
        ((-37 : Dyadic) * half ^ 8)⟩,
       ⟨((9 : Dyadic) * half ^ 5),
        ((-71 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word14Step11 :
    word14Chunk11.foldl (fun acc a => a.applyPacked acc)
      word14State11 = word14State12 := by decide +kernel

private def word14Chunk12 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word14State13 : PackedMat2 :=
    ⟨⟨⟨((33 : Dyadic) * half ^ 7),
        ((3 : Dyadic) * half ^ 6)⟩,
       ⟨((-17 : Dyadic) * half ^ 6),
        ((-13 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 3),
        ((-9 : Dyadic) * half ^ 7)⟩,
       ⟨((-43 : Dyadic) * half ^ 6),
        ((-7 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 3),
        ((-9 : Dyadic) * half ^ 7)⟩,
       ⟨((43 : Dyadic) * half ^ 6),
        ((7 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-33 : Dyadic) * half ^ 7),
        ((-3 : Dyadic) * half ^ 6)⟩,
       ⟨((-17 : Dyadic) * half ^ 6),
        ((-13 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word14Step12 :
    word14Chunk12.foldl (fun acc a => a.applyPacked acc)
      word14State12 = word14State13 := by decide +kernel

private def word14Chunk13 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word14State14 : PackedMat2 :=
    ⟨⟨⟨((67 : Dyadic) * half ^ 9),
        ((73 : Dyadic) * half ^ 9)⟩,
       ⟨((29 : Dyadic) * half ^ 9),
        ((55 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((137 : Dyadic) * half ^ 9),
        ((21 : Dyadic) * half ^ 6)⟩,
       ⟨((121 : Dyadic) * half ^ 9),
        ((-257 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((121 : Dyadic) * half ^ 9),
        ((-257 : Dyadic) * half ^ 9)⟩,
       ⟨((137 : Dyadic) * half ^ 9),
        ((21 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-29 : Dyadic) * half ^ 9),
        ((-55 : Dyadic) * half ^ 8)⟩,
       ⟨((-67 : Dyadic) * half ^ 9),
        ((-73 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word14Step13 :
    word14Chunk13.foldl (fun acc a => a.applyPacked acc)
      word14State13 = word14State14 := by decide +kernel

private def word14Chunk14 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word14State15 : PackedMat2 :=
    ⟨⟨⟨((-227 : Dyadic) * half ^ 10),
        ((7 : Dyadic) * half ^ 6)⟩,
       ⟨((413 : Dyadic) * half ^ 10),
        ((381 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((653 : Dyadic) * half ^ 10),
        ((-203 : Dyadic) * half ^ 10)⟩,
       ⟨((-21 : Dyadic) * half ^ 10),
        ((-15 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((21 : Dyadic) * half ^ 10),
        ((15 : Dyadic) * half ^ 9)⟩,
       ⟨((-653 : Dyadic) * half ^ 10),
        ((203 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((413 : Dyadic) * half ^ 10),
        ((381 : Dyadic) * half ^ 10)⟩,
       ⟨((-227 : Dyadic) * half ^ 10),
        ((7 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word14Step14 :
    word14Chunk14.foldl (fun acc a => a.applyPacked acc)
      word14State14 = word14State15 := by decide +kernel

private def word14Chunk15 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word14State16 : PackedMat2 :=
    ⟨⟨⟨((-105 : Dyadic) * half ^ 10),
        ((-319 : Dyadic) * half ^ 10)⟩,
       ⟨((297 : Dyadic) * half ^ 9),
        ((161 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-399 : Dyadic) * half ^ 10),
        ((151 : Dyadic) * half ^ 10)⟩,
       ⟨((205 : Dyadic) * half ^ 9),
        ((-21 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-17 : Dyadic) * half ^ 10),
        ((11 : Dyadic) * half ^ 11)⟩,
       ⟨((319 : Dyadic) * half ^ 10),
        ((-809 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((79 : Dyadic) * half ^ 9),
        ((-489 : Dyadic) * half ^ 11)⟩,
       ⟨((15 : Dyadic) * half ^ 5),
        ((699 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word14Step15 :
    word14Chunk15.foldl (fun acc a => a.applyPacked acc)
      word14State15 = word14State16 := by decide +kernel

private def word14Chunk16 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word14State17 : PackedMat2 :=
    ⟨⟨⟨((-15 : Dyadic) * half ^ 9),
        ((-1215 : Dyadic) * half ^ 11)⟩,
       ⟨((693 : Dyadic) * half ^ 11),
        ((-23 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-333 : Dyadic) * half ^ 10),
        ((-41 : Dyadic) * half ^ 10)⟩,
       ⟨((483 : Dyadic) * half ^ 11),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-483 : Dyadic) * half ^ 11),
        (0 : Dyadic)⟩,
       ⟨((333 : Dyadic) * half ^ 10),
        ((41 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((693 : Dyadic) * half ^ 11),
        ((-23 : Dyadic) * half ^ 8)⟩,
       ⟨((-15 : Dyadic) * half ^ 9),
        ((-1215 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word14Step16 :
    word14Chunk16.foldl (fun acc a => a.applyPacked acc)
      word14State16 = word14State17 := by decide +kernel

private def word14Chunk17 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word14State18 : PackedMat2 :=
    ⟨⟨⟨((-2147 : Dyadic) * half ^ 12),
        ((2045 : Dyadic) * half ^ 13)⟩,
       ⟨((-743 : Dyadic) * half ^ 11),
        ((-1265 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((397 : Dyadic) * half ^ 11),
        ((-1353 : Dyadic) * half ^ 13)⟩,
       ⟨((-1291 : Dyadic) * half ^ 12),
        ((-2777 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-2065 : Dyadic) * half ^ 12),
        ((-497 : Dyadic) * half ^ 13)⟩,
       ⟨((89 : Dyadic) * half ^ 9),
        ((2085 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-195 : Dyadic) * half ^ 11),
        ((3633 : Dyadic) * half ^ 13)⟩,
       ⟨((-1655 : Dyadic) * half ^ 12),
        ((661 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word14Step17 :
    word14Chunk17.foldl (fun acc a => a.applyPacked acc)
      word14State17 = word14State18 := by decide +kernel

private def word14Chunk18 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word14State19 : PackedMat2 :=
    ⟨⟨⟨((4325 : Dyadic) * half ^ 13),
        ((-2191 : Dyadic) * half ^ 13)⟩,
       ⟨((-2121 : Dyadic) * half ^ 13),
        ((925 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((2085 : Dyadic) * half ^ 13),
        ((145 : Dyadic) * half ^ 10)⟩,
       ⟨((-3469 : Dyadic) * half ^ 13),
        ((-325 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-2085 : Dyadic) * half ^ 13),
        ((-145 : Dyadic) * half ^ 10)⟩,
       ⟨((-3469 : Dyadic) * half ^ 13),
        ((-325 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((4325 : Dyadic) * half ^ 13),
        ((-2191 : Dyadic) * half ^ 13)⟩,
       ⟨((2121 : Dyadic) * half ^ 13),
        ((-925 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word14Step18 :
    word14Chunk18.foldl (fun acc a => a.applyPacked acc)
      word14State18 = word14State19 := by decide +kernel

private def word14Chunk19 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word14State20 : PackedMat2 :=
    ⟨⟨⟨((1499 : Dyadic) * half ^ 14),
        ((6177 : Dyadic) * half ^ 14)⟩,
       ⟨((7615 : Dyadic) * half ^ 14),
        ((-905 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((8905 : Dyadic) * half ^ 14),
        ((731 : Dyadic) * half ^ 13)⟩,
       ⟨((-4381 : Dyadic) * half ^ 14),
        ((-1207 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((2669 : Dyadic) * half ^ 14),
        ((6643 : Dyadic) * half ^ 14)⟩,
       ⟨((-255 : Dyadic) * half ^ 14),
        ((-1131 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-9797 : Dyadic) * half ^ 14),
        ((1529 : Dyadic) * half ^ 13)⟩,
       ⟨((2557 : Dyadic) * half ^ 14),
        ((4557 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word14Step19 :
    word14Chunk19.foldl (fun acc a => a.applyPacked acc)
      word14State19 = word14State20 := by decide +kernel

private def word14Chunk20 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word14State21 : PackedMat2 :=
    ⟨⟨⟨((-1557 : Dyadic) * half ^ 13),
        ((7711 : Dyadic) * half ^ 15)⟩,
       ⟨((-107 : Dyadic) * half ^ 13),
        ((7877 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((11669 : Dyadic) * half ^ 14),
        ((1873 : Dyadic) * half ^ 15)⟩,
       ⟨((-351 : Dyadic) * half ^ 14),
        ((-10945 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-351 : Dyadic) * half ^ 14),
        ((-10945 : Dyadic) * half ^ 15)⟩,
       ⟨((11669 : Dyadic) * half ^ 14),
        ((1873 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((107 : Dyadic) * half ^ 13),
        ((-7877 : Dyadic) * half ^ 15)⟩,
       ⟨((1557 : Dyadic) * half ^ 13),
        ((-7711 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word14Step20 :
    word14Chunk20.foldl (fun acc a => a.applyPacked acc)
      word14State20 = word14State21 := by decide +kernel

private def word14Chunk21 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word14State22 : PackedMat2 :=
    ⟨⟨⟨((379 : Dyadic) * half ^ 13),
        ((-26125 : Dyadic) * half ^ 16)⟩,
       ⟨((227 : Dyadic) * half ^ 15),
        ((18601 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((2141 : Dyadic) * half ^ 15),
        ((31383 : Dyadic) * half ^ 16)⟩,
       ⟨((-3535 : Dyadic) * half ^ 14),
        ((4499 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-17941 : Dyadic) * half ^ 15),
        ((4929 : Dyadic) * half ^ 16)⟩,
       ⟨((-6721 : Dyadic) * half ^ 14),
        ((-9211 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-1881 : Dyadic) * half ^ 14),
        ((1743 : Dyadic) * half ^ 16)⟩,
       ⟨((-22363 : Dyadic) * half ^ 15),
        ((1289 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word14Step21 :
    word14Chunk21.foldl (fun acc a => a.applyPacked acc)
      word14State21 = word14State22 := by decide +kernel

private def word14Chunk22 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word14State23 : PackedMat2 :=
    ⟨⟨⟨((10969 : Dyadic) * half ^ 16),
        ((-8443 : Dyadic) * half ^ 15)⟩,
       ⟨((6165 : Dyadic) * half ^ 16),
        ((-971 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((49515 : Dyadic) * half ^ 16),
        ((10333 : Dyadic) * half ^ 16)⟩,
       ⟨((-22133 : Dyadic) * half ^ 16),
        ((14207 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-1937 : Dyadic) * half ^ 15),
        ((2239 : Dyadic) * half ^ 12)⟩,
       ⟨((-6135 : Dyadic) * half ^ 14),
        ((-13691 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((467 : Dyadic) * half ^ 11),
        ((-1201 : Dyadic) * half ^ 15)⟩,
       ⟨((-4707 : Dyadic) * half ^ 14),
        ((8567 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word14Step22 :
    word14Chunk22.foldl (fun acc a => a.applyPacked acc)
      word14State22 = word14State23 := by decide +kernel

private def word14Chunk23 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word14State24 : PackedMat2 :=
    ⟨⟨⟨((14797 : Dyadic) * half ^ 17),
        ((-513 : Dyadic) * half ^ 14)⟩,
       ⟨((23337 : Dyadic) * half ^ 17),
        ((-16283 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((60623 : Dyadic) * half ^ 17),
        ((31959 : Dyadic) * half ^ 17)⟩,
       ⟨((-17397 : Dyadic) * half ^ 17),
        ((64191 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-60623 : Dyadic) * half ^ 17),
        ((-31959 : Dyadic) * half ^ 17)⟩,
       ⟨((-17397 : Dyadic) * half ^ 17),
        ((64191 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((14797 : Dyadic) * half ^ 17),
        ((-513 : Dyadic) * half ^ 14)⟩,
       ⟨((-23337 : Dyadic) * half ^ 17),
        ((16283 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word14Step23 :
    word14Chunk23.foldl (fun acc a => a.applyPacked acc)
      word14State23 = word14State24 := by decide +kernel

private def word14Chunk24 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word14State25 : PackedMat2 :=
    ⟨⟨⟨((-63777 : Dyadic) * half ^ 18),
        ((86373 : Dyadic) * half ^ 18)⟩,
       ⟨((-146485 : Dyadic) * half ^ 18),
        ((-595 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((52853 : Dyadic) * half ^ 18),
        ((351 : Dyadic) * half ^ 17)⟩,
       ⟨((152335 : Dyadic) * half ^ 18),
        ((33629 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-32927 : Dyadic) * half ^ 18),
        ((-49741 : Dyadic) * half ^ 18)⟩,
       ⟨((-34331 : Dyadic) * half ^ 18),
        ((-51297 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-88753 : Dyadic) * half ^ 18),
        ((-20677 : Dyadic) * half ^ 17)⟩,
       ⟨((83993 : Dyadic) * half ^ 18),
        ((-105131 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word14Step24 :
    word14Chunk24.foldl (fun acc a => a.applyPacked acc)
      word14State24 = word14State25 := by decide +kernel

private def word14Chunk25 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word14State26 : PackedMat2 :=
    ⟨⟨⟨((93021 : Dyadic) * half ^ 17),
        ((-60695 : Dyadic) * half ^ 19)⟩,
       ⟨((-27609 : Dyadic) * half ^ 16),
        ((-93741 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-43577 : Dyadic) * half ^ 18),
        ((-67149 : Dyadic) * half ^ 19)⟩,
       ⟨((-13187 : Dyadic) * half ^ 18),
        ((150657 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-13187 : Dyadic) * half ^ 18),
        ((150657 : Dyadic) * half ^ 19)⟩,
       ⟨((-43577 : Dyadic) * half ^ 18),
        ((-67149 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((27609 : Dyadic) * half ^ 16),
        ((93741 : Dyadic) * half ^ 19)⟩,
       ⟨((-93021 : Dyadic) * half ^ 17),
        ((60695 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word14Step25 :
    word14Chunk25.foldl (fun acc a => a.applyPacked acc)
      word14State25 = word14State26 := by decide +kernel

private def word14Chunk26 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word14State27 : PackedMat2 :=
    ⟨⟨⟨((39661 : Dyadic) * half ^ 17),
        ((496215 : Dyadic) * half ^ 20)⟩,
       ⟨((134055 : Dyadic) * half ^ 19),
        ((-338331 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-37439 : Dyadic) * half ^ 19),
        ((58667 : Dyadic) * half ^ 20)⟩,
       ⟨((92149 : Dyadic) * half ^ 18),
        ((-169129 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((37439 : Dyadic) * half ^ 19),
        ((-58667 : Dyadic) * half ^ 20)⟩,
       ⟨((92149 : Dyadic) * half ^ 18),
        ((-169129 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((39661 : Dyadic) * half ^ 17),
        ((496215 : Dyadic) * half ^ 20)⟩,
       ⟨((-134055 : Dyadic) * half ^ 19),
        ((338331 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word14Step26 :
    word14Chunk26.foldl (fun acc a => a.applyPacked acc)
      word14State26 = word14State27 := by decide +kernel

private def word14Chunk27 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word14State28 : PackedMat2 :=
    ⟨⟨⟨((2669 : Dyadic) * half ^ 18),
        ((44221 : Dyadic) * half ^ 20)⟩,
       ⟨((12075 : Dyadic) * half ^ 18),
        ((159263 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((48039 : Dyadic) * half ^ 17),
        ((-43343 : Dyadic) * half ^ 20)⟩,
       ⟨((-177955 : Dyadic) * half ^ 19),
        ((20489 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((48039 : Dyadic) * half ^ 17),
        ((-43343 : Dyadic) * half ^ 20)⟩,
       ⟨((177955 : Dyadic) * half ^ 19),
        ((-20489 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-2669 : Dyadic) * half ^ 18),
        ((-44221 : Dyadic) * half ^ 20)⟩,
       ⟨((12075 : Dyadic) * half ^ 18),
        ((159263 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word14Step27 :
    word14Chunk27.foldl (fun acc a => a.applyPacked acc)
      word14State27 = word14State28 := by decide +kernel

private def word14Chunk28 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word14State29 : PackedMat2 :=
    ⟨⟨⟨((42507 : Dyadic) * half ^ 21),
        ((-640577 : Dyadic) * half ^ 21)⟩,
       ⟨((1369101 : Dyadic) * half ^ 21),
        ((-138795 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((950497 : Dyadic) * half ^ 21),
        ((186411 : Dyadic) * half ^ 20)⟩,
       ⟨((-126563 : Dyadic) * half ^ 21),
        ((-418065 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-790887 : Dyadic) * half ^ 21),
        ((-269265 : Dyadic) * half ^ 20)⟩,
       ⟨((-45243 : Dyadic) * half ^ 21),
        ((411967 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-362987 : Dyadic) * half ^ 21),
        ((-663297 : Dyadic) * half ^ 21)⟩,
       ⟨((918167 : Dyadic) * half ^ 21),
        ((-176451 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word14Step28 :
    word14Chunk28.foldl (fun acc a => a.applyPacked acc)
      word14State28 = word14State29 := by decide +kernel

private def word14Chunk29 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word14State30 : PackedMat2 :=
    ⟨⟨⟨((-225047 : Dyadic) * half ^ 18),
        ((-52725 : Dyadic) * half ^ 22)⟩,
       ⟨((-159809 : Dyadic) * half ^ 20),
        ((310459 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((457357 : Dyadic) * half ^ 21),
        ((727985 : Dyadic) * half ^ 22)⟩,
       ⟨((-627367 : Dyadic) * half ^ 21),
        ((523849 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((627367 : Dyadic) * half ^ 21),
        ((-523849 : Dyadic) * half ^ 22)⟩,
       ⟨((-457357 : Dyadic) * half ^ 21),
        ((-727985 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-159809 : Dyadic) * half ^ 20),
        ((310459 : Dyadic) * half ^ 22)⟩,
       ⟨((-225047 : Dyadic) * half ^ 18),
        ((-52725 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word14Step29 :
    word14Chunk29.foldl (fun acc a => a.applyPacked acc)
      word14State29 = word14State30 := by decide +kernel

private def word14Chunk30 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word14State31 : PackedMat2 :=
    ⟨⟨⟨((-1116381 : Dyadic) * half ^ 22),
        ((-151419 : Dyadic) * half ^ 22)⟩,
       ⟨((70487 : Dyadic) * half ^ 19),
        ((-1205513 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((650747 : Dyadic) * half ^ 22),
        ((1099991 : Dyadic) * half ^ 22)⟩,
       ⟨((-159703 : Dyadic) * half ^ 20),
        ((-743115 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-159703 : Dyadic) * half ^ 20),
        ((-743115 : Dyadic) * half ^ 22)⟩,
       ⟨((650747 : Dyadic) * half ^ 22),
        ((1099991 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-70487 : Dyadic) * half ^ 19),
        ((1205513 : Dyadic) * half ^ 21)⟩,
       ⟨((1116381 : Dyadic) * half ^ 22),
        ((151419 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word14Step30 :
    word14Chunk30.foldl (fun acc a => a.applyPacked acc)
      word14State30 = word14State31 := by decide +kernel

private def word14Chunk31 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word14State32 : PackedMat2 :=
    ⟨⟨⟨((-254929 : Dyadic) * half ^ 22),
        ((2601225 : Dyadic) * half ^ 24)⟩,
       ⟨((-4095327 : Dyadic) * half ^ 23),
        ((2114513 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((5401239 : Dyadic) * half ^ 23),
        ((3340209 : Dyadic) * half ^ 24)⟩,
       ⟨((-1547545 : Dyadic) * half ^ 22),
        ((2602635 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-1485711 : Dyadic) * half ^ 22),
        ((-2306149 : Dyadic) * half ^ 24)⟩,
       ⟨((-368787 : Dyadic) * half ^ 23),
        ((-8496329 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((2357869 : Dyadic) * half ^ 23),
        ((-4605185 : Dyadic) * half ^ 24)⟩,
       ⟨((60839 : Dyadic) * half ^ 21),
        ((3585469 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word14Step31 :
    word14Chunk31.foldl (fun acc a => a.applyPacked acc)
      word14State31 = word14State32 := by decide +kernel

private def word14Chunk32 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word14State33 : PackedMat2 :=
    ⟨⟨⟨((1114345 : Dyadic) * half ^ 21),
        ((-453081 : Dyadic) * half ^ 23)⟩,
       ⟨((-2239877 : Dyadic) * half ^ 23),
        ((4813299 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((4554941 : Dyadic) * half ^ 23),
        ((1912227 : Dyadic) * half ^ 23)⟩,
       ⟨((847003 : Dyadic) * half ^ 23),
        ((-3069477 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((4554941 : Dyadic) * half ^ 23),
        ((1912227 : Dyadic) * half ^ 23)⟩,
       ⟨((-847003 : Dyadic) * half ^ 23),
        ((3069477 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-1114345 : Dyadic) * half ^ 21),
        ((453081 : Dyadic) * half ^ 23)⟩,
       ⟨((-2239877 : Dyadic) * half ^ 23),
        ((4813299 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word14Step32 :
    word14Chunk32.foldl (fun acc a => a.applyPacked acc)
      word14State32 = word14State33 := by decide +kernel

private def word14Chunk33 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word14State34 : PackedMat2 :=
    ⟨⟨⟨((1912453 : Dyadic) * half ^ 25),
        ((-1300483 : Dyadic) * half ^ 25)⟩,
       ⟨((11647427 : Dyadic) * half ^ 25),
        ((-4546927 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((9862039 : Dyadic) * half ^ 25),
        ((7198431 : Dyadic) * half ^ 24)⟩,
       ⟨((-2748533 : Dyadic) * half ^ 25),
        ((12215717 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-2748533 : Dyadic) * half ^ 25),
        ((12215717 : Dyadic) * half ^ 25)⟩,
       ⟨((9862039 : Dyadic) * half ^ 25),
        ((7198431 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-11647427 : Dyadic) * half ^ 25),
        ((4546927 : Dyadic) * half ^ 24)⟩,
       ⟨((-1912453 : Dyadic) * half ^ 25),
        ((1300483 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word14Step33 :
    word14Chunk33.foldl (fun acc a => a.applyPacked acc)
      word14State33 = word14State34 := by decide +kernel

private def word14Chunk34 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word14State35 : PackedMat2 :=
    ⟨⟨⟨((29465119 : Dyadic) * half ^ 26),
        ((-5394145 : Dyadic) * half ^ 26)⟩,
       ⟨((50881731 : Dyadic) * half ^ 26),
        ((3318943 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((1448321 : Dyadic) * half ^ 26),
        ((2296631 : Dyadic) * half ^ 24)⟩,
       ⟨((24653883 : Dyadic) * half ^ 26),
        ((-7792405 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((16978929 : Dyadic) * half ^ 26),
        ((-11602781 : Dyadic) * half ^ 26)⟩,
       ⟨((-1394119 : Dyadic) * half ^ 26),
        ((-6525551 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((12032031 : Dyadic) * half ^ 26),
        ((5354153 : Dyadic) * half ^ 25)⟩,
       ⟨((1243741 : Dyadic) * half ^ 26),
        ((40173425 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word14Step34 :
    word14Chunk34.foldl (fun acc a => a.applyPacked acc)
      word14State34 = word14State35 := by decide +kernel

private def word14Chunk35 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word14State36 : PackedMat2 :=
    ⟨⟨⟨((-15055425 : Dyadic) * half ^ 25),
        ((32013757 : Dyadic) * half ^ 27)⟩,
       ⟨((565219 : Dyadic) * half ^ 22),
        ((53279991 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-17872977 : Dyadic) * half ^ 26),
        ((14634871 : Dyadic) * half ^ 27)⟩,
       ⟨((18372621 : Dyadic) * half ^ 26),
        ((40478293 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((13778291 : Dyadic) * half ^ 25),
        ((124911 : Dyadic) * half ^ 25)⟩,
       ⟨((-12921711 : Dyadic) * half ^ 26),
        ((-18122799 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-21323437 : Dyadic) * half ^ 25),
        ((10533673 : Dyadic) * half ^ 26)⟩,
       ⟨((10633117 : Dyadic) * half ^ 26),
        ((19577177 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word14Step35 :
    word14Chunk35.foldl (fun acc a => a.applyPacked acc)
      word14State35 = word14State36 := by decide +kernel

private def word14Chunk36 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word14State37 : PackedMat2 :=
    ⟨⟨⟨((-4586329 : Dyadic) * half ^ 27),
        ((-114001335 : Dyadic) * half ^ 28)⟩,
       ⟨((9022713 : Dyadic) * half ^ 25),
        ((86346363 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((9727281 : Dyadic) * half ^ 25),
        ((-97291593 : Dyadic) * half ^ 28)⟩,
       ⟨((11972199 : Dyadic) * half ^ 27),
        ((12225759 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-9727281 : Dyadic) * half ^ 25),
        ((97291593 : Dyadic) * half ^ 28)⟩,
       ⟨((11972199 : Dyadic) * half ^ 27),
        ((12225759 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-4586329 : Dyadic) * half ^ 27),
        ((-114001335 : Dyadic) * half ^ 28)⟩,
       ⟨((-9022713 : Dyadic) * half ^ 25),
        ((-86346363 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word14Step36 :
    word14Chunk36.foldl (fun acc a => a.applyPacked acc)
      word14State36 = word14State37 := by decide +kernel

private def word14Chunk37 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word14State38 : PackedMat2 :=
    ⟨⟨⟨((-92417435 : Dyadic) * half ^ 28),
        ((-74745967 : Dyadic) * half ^ 29)⟩,
       ⟨((-9468011 : Dyadic) * half ^ 27),
        ((96531325 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-14096269 : Dyadic) * half ^ 25),
        ((-132328369 : Dyadic) * half ^ 29)⟩,
       ⟨((-163572619 : Dyadic) * half ^ 28),
        ((122285757 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-14096269 : Dyadic) * half ^ 25),
        ((-132328369 : Dyadic) * half ^ 29)⟩,
       ⟨((163572619 : Dyadic) * half ^ 28),
        ((-122285757 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((92417435 : Dyadic) * half ^ 28),
        ((74745967 : Dyadic) * half ^ 29)⟩,
       ⟨((-9468011 : Dyadic) * half ^ 27),
        ((96531325 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word14Step37 :
    word14Chunk37.foldl (fun acc a => a.applyPacked acc)
      word14State37 = word14State38 := by decide +kernel

private def word14Chunk38 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word14State39 : PackedMat2 :=
    ⟨⟨⟨((-146870525 : Dyadic) * half ^ 28),
        ((-271093593 : Dyadic) * half ^ 30)⟩,
       ⟨((122177391 : Dyadic) * half ^ 29),
        ((-369141761 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-99485763 : Dyadic) * half ^ 29),
        ((241340623 : Dyadic) * half ^ 30)⟩,
       ⟨((-18193875 : Dyadic) * half ^ 28),
        ((289124317 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-132616235 : Dyadic) * half ^ 28),
        ((135873513 : Dyadic) * half ^ 30)⟩,
       ⟨((23891847 : Dyadic) * half ^ 29),
        ((63098013 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-320117677 : Dyadic) * half ^ 29),
        ((-171563659 : Dyadic) * half ^ 30)⟩,
       ⟨((12256021 : Dyadic) * half ^ 27),
        ((-415918441 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word14Step38 :
    word14Chunk38.foldl (fun acc a => a.applyPacked acc)
      word14State38 = word14State39 := by decide +kernel

private def word14Chunk39 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word14State40 : PackedMat2 :=
    ⟨⟨⟨((-293785221 : Dyadic) * half ^ 30),
        ((-229840481 : Dyadic) * half ^ 30)⟩,
       ⟨((-699270561 : Dyadic) * half ^ 30),
        ((131192753 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-16012677 : Dyadic) * half ^ 30),
        ((-189797359 : Dyadic) * half ^ 29)⟩,
       ⟨((67461163 : Dyadic) * half ^ 30),
        ((134426721 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-16012677 : Dyadic) * half ^ 30),
        ((-189797359 : Dyadic) * half ^ 29)⟩,
       ⟨((-67461163 : Dyadic) * half ^ 30),
        ((-134426721 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((293785221 : Dyadic) * half ^ 30),
        ((229840481 : Dyadic) * half ^ 30)⟩,
       ⟨((-699270561 : Dyadic) * half ^ 30),
        ((131192753 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word14Step39 :
    word14Chunk39.foldl (fun acc a => a.applyPacked acc)
      word14State39 = word14State40 := by decide +kernel

private def word14Chunk40 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word14State41 : PackedMat2 :=
    ⟨⟨⟨((616009871 : Dyadic) * half ^ 31),
        ((-2443885 : Dyadic) * half ^ 26)⟩,
       ⟨((239376449 : Dyadic) * half ^ 31),
        ((-1126414567 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-406111425 : Dyadic) * half ^ 31),
        ((298844837 : Dyadic) * half ^ 31)⟩,
       ⟨((-893485677 : Dyadic) * half ^ 31),
        ((-122882791 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-790376001 : Dyadic) * half ^ 31),
        ((-121843563 : Dyadic) * half ^ 30)⟩,
       ⟨((-192686327 : Dyadic) * half ^ 31),
        ((-649798551 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((1048210247 : Dyadic) * half ^ 31),
        ((188316711 : Dyadic) * half ^ 31)⟩,
       ⟨((1204618887 : Dyadic) * half ^ 31),
        ((-53461645 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word14Step40 :
    word14Chunk40.foldl (fun acc a => a.applyPacked acc)
      word14State40 = word14State41 := by decide +kernel

private def word14Chunk41 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word14State42 : PackedMat2 :=
    ⟨⟨⟨((161349 : Dyadic) * half ^ 26),
        ((1443579601 : Dyadic) * half ^ 32)⟩,
       ⟨((-632576235 : Dyadic) * half ^ 30),
        ((-330359035 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((1053592611 : Dyadic) * half ^ 31),
        ((7215419 : Dyadic) * half ^ 32)⟩,
       ⟨((-814275101 : Dyadic) * half ^ 31),
        ((531773727 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-269494573 : Dyadic) * half ^ 31),
        ((-119658755 : Dyadic) * half ^ 31)⟩,
       ⟨((131139577 : Dyadic) * half ^ 30),
        ((-29185433 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((556610283 : Dyadic) * half ^ 31),
        ((-629994651 : Dyadic) * half ^ 31)⟩,
       ⟨((443484659 : Dyadic) * half ^ 30),
        ((635157819 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word14Step41 :
    word14Chunk41.foldl (fun acc a => a.applyPacked acc)
      word14State41 = word14State42 := by decide +kernel

private def word14Chunk42 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word14State43 : PackedMat2 :=
    ⟨⟨⟨((1219618749 : Dyadic) * half ^ 31),
        ((101367861 : Dyadic) * half ^ 33)⟩,
       ⟨((-62916713 : Dyadic) * half ^ 32),
        ((-2954593051 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((1378100803 : Dyadic) * half ^ 32),
        ((315422193 : Dyadic) * half ^ 33)⟩,
       ⟨((309041957 : Dyadic) * half ^ 29),
        ((-351019145 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((1378100803 : Dyadic) * half ^ 32),
        ((315422193 : Dyadic) * half ^ 33)⟩,
       ⟨((-309041957 : Dyadic) * half ^ 29),
        ((351019145 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-1219618749 : Dyadic) * half ^ 31),
        ((-101367861 : Dyadic) * half ^ 33)⟩,
       ⟨((-62916713 : Dyadic) * half ^ 32),
        ((-2954593051 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word14Step42 :
    word14Chunk42.foldl (fun acc a => a.applyPacked acc)
      word14State42 = word14State43 := by decide +kernel

private def word14Chunk43 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word14State44 : PackedMat2 :=
    ⟨⟨⟨((2222492065 : Dyadic) * half ^ 32),
        ((4497821355 : Dyadic) * half ^ 34)⟩,
       ⟨((-591579523 : Dyadic) * half ^ 33),
        ((-546068869 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((1232712369 : Dyadic) * half ^ 33),
        ((-3288756537 : Dyadic) * half ^ 34)⟩,
       ⟨((1423185361 : Dyadic) * half ^ 31),
        ((-2856566911 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((768165431 : Dyadic) * half ^ 31),
        ((-6925453813 : Dyadic) * half ^ 34)⟩,
       ⟨((216094813 : Dyadic) * half ^ 33),
        ((4460029075 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((1975876243 : Dyadic) * half ^ 33),
        ((3853404607 : Dyadic) * half ^ 34)⟩,
       ⟨((315243139 : Dyadic) * half ^ 30),
        ((5036563653 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word14Step43 :
    word14Chunk43.foldl (fun acc a => a.applyPacked acc)
      word14State43 = word14State44 := by decide +kernel

private def word14Chunk44 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word14State45 : PackedMat2 :=
    ⟨⟨⟨((3856688509 : Dyadic) * half ^ 34),
        ((6362396833 : Dyadic) * half ^ 34)⟩,
       ⟨((9591656705 : Dyadic) * half ^ 34),
        ((229047699 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-4536513851 : Dyadic) * half ^ 34),
        ((2454953251 : Dyadic) * half ^ 33)⟩,
       ⟨((-1032275019 : Dyadic) * half ^ 34),
        ((2160698805 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-4536513851 : Dyadic) * half ^ 34),
        ((2454953251 : Dyadic) * half ^ 33)⟩,
       ⟨((1032275019 : Dyadic) * half ^ 34),
        ((-2160698805 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-3856688509 : Dyadic) * half ^ 34),
        ((-6362396833 : Dyadic) * half ^ 34)⟩,
       ⟨((9591656705 : Dyadic) * half ^ 34),
        ((229047699 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word14Step44 :
    word14Chunk44.foldl (fun acc a => a.applyPacked acc)
      word14State44 = word14State45 := by decide +kernel

private def word14Chunk45 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word14State46 : PackedMat2 :=
    ⟨⟨⟨((2544628069 : Dyadic) * half ^ 35),
        ((2689880113 : Dyadic) * half ^ 34)⟩,
       ⟨((13546088019 : Dyadic) * half ^ 35),
        ((13169659103 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((16985437157 : Dyadic) * half ^ 35),
        ((-11725395559 : Dyadic) * half ^ 35)⟩,
       ⟨((-2485163163 : Dyadic) * half ^ 35),
        ((-711635281 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((8878854435 : Dyadic) * half ^ 35),
        ((-152114065 : Dyadic) * half ^ 29)⟩,
       ⟨((-14571936683 : Dyadic) * half ^ 35),
        ((7250136997 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-7789898877 : Dyadic) * half ^ 35),
        ((-5500729975 : Dyadic) * half ^ 35)⟩,
       ⟨((-18549419329 : Dyadic) * half ^ 35),
        ((-2011339511 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word14Step45 :
    word14Chunk45.foldl (fun acc a => a.applyPacked acc)
      word14State45 = word14State46 := by decide +kernel

private def word14Chunk46 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word14State47 : PackedMat2 :=
    ⟨⟨⟨((-2635865365 : Dyadic) * half ^ 35),
        ((-6735786079 : Dyadic) * half ^ 35)⟩,
       ⟨((5733672929 : Dyadic) * half ^ 33),
        ((3600226343 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-17255857987 : Dyadic) * half ^ 35),
        ((3331159589 : Dyadic) * half ^ 35)⟩,
       ⟨((1093465855 : Dyadic) * half ^ 33),
        ((-4897579737 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-1093465855 : Dyadic) * half ^ 33),
        ((4897579737 : Dyadic) * half ^ 34)⟩,
       ⟨((17255857987 : Dyadic) * half ^ 35),
        ((-3331159589 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((5733672929 : Dyadic) * half ^ 33),
        ((3600226343 : Dyadic) * half ^ 35)⟩,
       ⟨((-2635865365 : Dyadic) * half ^ 35),
        ((-6735786079 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word14Step46 :
    word14Chunk46.foldl (fun acc a => a.applyPacked acc)
      word14State46 = word14State47 := by decide +kernel

private def word14Chunk47 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word14State48 : PackedMat2 :=
    ⟨⟨⟨((-42870263759 : Dyadic) * half ^ 36),
        ((-25354177983 : Dyadic) * half ^ 37)⟩,
       ⟨((1105681649 : Dyadic) * half ^ 32),
        ((10768089867 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((2712007747 : Dyadic) * half ^ 35),
        ((-35220223377 : Dyadic) * half ^ 37)⟩,
       ⟨((-26510164513 : Dyadic) * half ^ 36),
        ((40980603099 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((2880189861 : Dyadic) * half ^ 36),
        ((-21086149019 : Dyadic) * half ^ 37)⟩,
       ⟨((-19050206619 : Dyadic) * half ^ 35),
        ((31934180007 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((3646522029 : Dyadic) * half ^ 35),
        ((25179357375 : Dyadic) * half ^ 37)⟩,
       ⟨((18061133925 : Dyadic) * half ^ 36),
        ((60561170143 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word14Step47 :
    word14Chunk47.foldl (fun acc a => a.applyPacked acc)
      word14State47 = word14State48 := by decide +kernel

private def word14Chunk48 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word14State49 : PackedMat2 :=
    ⟨⟨⟨((9998413311 : Dyadic) * half ^ 37),
        ((-33530615523 : Dyadic) * half ^ 37)⟩,
       ⟨((-105954627439 : Dyadic) * half ^ 37),
        ((-14683722609 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-9721220161 : Dyadic) * half ^ 37),
        ((12838289415 : Dyadic) * half ^ 36)⟩,
       ⟨((52875503793 : Dyadic) * half ^ 37),
        ((-4590725669 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((9721220161 : Dyadic) * half ^ 37),
        ((-12838289415 : Dyadic) * half ^ 36)⟩,
       ⟨((52875503793 : Dyadic) * half ^ 37),
        ((-4590725669 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((9998413311 : Dyadic) * half ^ 37),
        ((-33530615523 : Dyadic) * half ^ 37)⟩,
       ⟨((105954627439 : Dyadic) * half ^ 37),
        ((14683722609 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word14Step48 :
    word14Chunk48.foldl (fun acc a => a.applyPacked acc)
      word14State48 = word14State49 := by decide +kernel

private def word14Chunk49 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word14State50 : PackedMat2 :=
    ⟨⟨⟨((-99394998015 : Dyadic) * half ^ 38),
        ((11006304629 : Dyadic) * half ^ 35)⟩,
       ⟨((-126786014729 : Dyadic) * half ^ 38),
        ((-3642180351 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((2470803411 : Dyadic) * half ^ 38),
        ((-73187238207 : Dyadic) * half ^ 38)⟩,
       ⟨((136948859945 : Dyadic) * half ^ 38),
        ((38250658245 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((2470803411 : Dyadic) * half ^ 38),
        ((-73187238207 : Dyadic) * half ^ 38)⟩,
       ⟨((-136948859945 : Dyadic) * half ^ 38),
        ((-38250658245 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((99394998015 : Dyadic) * half ^ 38),
        ((-11006304629 : Dyadic) * half ^ 35)⟩,
       ⟨((-126786014729 : Dyadic) * half ^ 38),
        ((-3642180351 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word14Step49 :
    word14Chunk49.foldl (fun acc a => a.applyPacked acc)
      word14State49 = word14State50 := by decide +kernel

private def word14Chunk50 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word14State51 : PackedMat2 :=
    ⟨⟨⟨((29757409747 : Dyadic) * half ^ 39),
        ((45156062279 : Dyadic) * half ^ 38)⟩,
       ⟨((27778236387 : Dyadic) * half ^ 39),
        ((-172787661749 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-54938653679 : Dyadic) * half ^ 39),
        ((-132940746325 : Dyadic) * half ^ 39)⟩,
       ⟨((-83717741067 : Dyadic) * half ^ 39),
        ((4677234325 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((54938653679 : Dyadic) * half ^ 39),
        ((132940746325 : Dyadic) * half ^ 39)⟩,
       ⟨((-83717741067 : Dyadic) * half ^ 39),
        ((4677234325 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((29757409747 : Dyadic) * half ^ 39),
        ((45156062279 : Dyadic) * half ^ 38)⟩,
       ⟨((-27778236387 : Dyadic) * half ^ 39),
        ((172787661749 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word14Step50 :
    word14Chunk50.foldl (fun acc a => a.applyPacked acc)
      word14State50 = word14State51 := by decide +kernel

private def word14Chunk51 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word14State52 : PackedMat2 :=
    ⟨⟨⟨((-308222679259 : Dyadic) * half ^ 40),
        ((165857262399 : Dyadic) * half ^ 39)⟩,
       ⟨((-294634060855 : Dyadic) * half ^ 40),
        ((-260930019945 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-129241834359 : Dyadic) * half ^ 40),
        ((-297258302581 : Dyadic) * half ^ 40)⟩,
       ⟨((26739822291 : Dyadic) * half ^ 40),
        ((-61028547399 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-26739822291 : Dyadic) * half ^ 40),
        ((61028547399 : Dyadic) * half ^ 37)⟩,
       ⟨((129241834359 : Dyadic) * half ^ 40),
        ((297258302581 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-294634060855 : Dyadic) * half ^ 40),
        ((-260930019945 : Dyadic) * half ^ 40)⟩,
       ⟨((-308222679259 : Dyadic) * half ^ 40),
        ((165857262399 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word14Step51 :
    word14Chunk51.foldl (fun acc a => a.applyPacked acc)
      word14State51 = word14State52 := by decide +kernel

private def word14Chunk52 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word14State53 : PackedMat2 :=
    ⟨⟨⟨((1091625579857 : Dyadic) * half ^ 41),
        ((555288403393 : Dyadic) * half ^ 41)⟩,
       ⟨((784542469759 : Dyadic) * half ^ 41),
        ((-48920381449 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((65589059767 : Dyadic) * half ^ 41),
        ((-298014429179 : Dyadic) * half ^ 40)⟩,
       ⟨((-679833940433 : Dyadic) * half ^ 41),
        ((-69146028777 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((526882829581 : Dyadic) * half ^ 41),
        ((-93177875025 : Dyadic) * half ^ 39)⟩,
       ⟨((-665174887135 : Dyadic) * half ^ 41),
        ((-307122440333 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((1338014506577 : Dyadic) * half ^ 41),
        ((153541555049 : Dyadic) * half ^ 41)⟩,
       ⟨((227437699791 : Dyadic) * half ^ 41),
        ((-117260503101 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word14Step52 :
    word14Chunk52.foldl (fun acc a => a.applyPacked acc)
      word14State52 = word14State53 := by decide +kernel

private def word14Chunk53 : List Letter := [.t, .h, .t, .h, .t, .h, .s]
private def word14State54 : PackedMat2 :=
    ⟨⟨⟨((372410148721 : Dyadic) * half ^ 41),
        ((1291610485859 : Dyadic) * half ^ 41)⟩,
       ⟨((266259093155 : Dyadic) * half ^ 40),
        ((-188422688735 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-73594793363 : Dyadic) * half ^ 41),
        ((52039377447 : Dyadic) * half ^ 41)⟩,
       ⟨((312663113873 : Dyadic) * half ^ 40),
        ((-442172416093 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((73594793363 : Dyadic) * half ^ 41),
        ((-52039377447 : Dyadic) * half ^ 41)⟩,
       ⟨((312663113873 : Dyadic) * half ^ 40),
        ((-442172416093 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((372410148721 : Dyadic) * half ^ 41),
        ((1291610485859 : Dyadic) * half ^ 41)⟩,
       ⟨((-266259093155 : Dyadic) * half ^ 40),
        ((188422688735 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word14Step53 :
    word14Chunk53.foldl (fun acc a => a.applyPacked acc)
      word14State53 = word14State54 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word14_check : check word14 14 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word14 = word14State54.toMatrix := by
    unfold evalRingPacked
    change ((
      word14Chunk0 ++ word14Chunk1 ++ word14Chunk2 ++ word14Chunk3 ++
      word14Chunk4 ++ word14Chunk5 ++ word14Chunk6 ++ word14Chunk7 ++
      word14Chunk8 ++ word14Chunk9 ++ word14Chunk10 ++ word14Chunk11 ++
      word14Chunk12 ++ word14Chunk13 ++ word14Chunk14 ++ word14Chunk15 ++
      word14Chunk16 ++ word14Chunk17 ++ word14Chunk18 ++ word14Chunk19 ++
      word14Chunk20 ++ word14Chunk21 ++ word14Chunk22 ++ word14Chunk23 ++
      word14Chunk24 ++ word14Chunk25 ++ word14Chunk26 ++ word14Chunk27 ++
      word14Chunk28 ++ word14Chunk29 ++ word14Chunk30 ++ word14Chunk31 ++
      word14Chunk32 ++ word14Chunk33 ++ word14Chunk34 ++ word14Chunk35 ++
      word14Chunk36 ++ word14Chunk37 ++ word14Chunk38 ++ word14Chunk39 ++
      word14Chunk40 ++ word14Chunk41 ++ word14Chunk42 ++ word14Chunk43 ++
      word14Chunk44 ++ word14Chunk45 ++ word14Chunk46 ++ word14Chunk47 ++
      word14Chunk48 ++ word14Chunk49 ++ word14Chunk50 ++ word14Chunk51 ++
      word14Chunk52 ++ word14Chunk53
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word14Step0, word14Step1, word14Step2, word14Step3, word14Step4,
      word14Step5, word14Step6, word14Step7, word14Step8, word14Step9,
      word14Step10, word14Step11, word14Step12, word14Step13, word14Step14,
      word14Step15, word14Step16, word14Step17, word14Step18, word14Step19,
      word14Step20, word14Step21, word14Step22, word14Step23, word14Step24,
      word14Step25, word14Step26, word14Step27, word14Step28, word14Step29,
      word14Step30, word14Step31, word14Step32, word14Step33, word14Step34,
      word14Step35, word14Step36, word14Step37, word14Step38, word14Step39,
      word14Step40, word14Step41, word14Step42, word14Step43, word14Step44,
      word14Step45, word14Step46, word14Step47, word14Step48, word14Step49,
      word14Step50, word14Step51, word14Step52, word14Step53]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
