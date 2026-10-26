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
private def word41Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word41State1 : PackedMat2 :=
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
private lemma word41Step0 :
    word41Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word41State1 := by decide +kernel

private def word41Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word41State2 : PackedMat2 :=
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
private lemma word41Step1 :
    word41Chunk1.foldl (fun acc a => a.applyPacked acc)
      word41State1 = word41State2 := by decide +kernel

private def word41Chunk2 : List Letter := [.h, .s, .s, .s, .t, .h, .s, .t]
private def word41State3 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word41Step2 :
    word41Chunk2.foldl (fun acc a => a.applyPacked acc)
      word41State2 = word41State3 := by decide +kernel

private def word41Chunk3 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word41State4 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word41Step3 :
    word41Chunk3.foldl (fun acc a => a.applyPacked acc)
      word41State3 = word41State4 := by decide +kernel

private def word41Chunk4 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word41State5 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((3 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((3 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word41Step4 :
    word41Chunk4.foldl (fun acc a => a.applyPacked acc)
      word41State4 = word41State5 := by decide +kernel

private def word41Chunk5 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word41State6 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((-5 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((7 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((-7 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word41Step5 :
    word41Chunk5.foldl (fun acc a => a.applyPacked acc)
      word41State5 = word41State6 := by decide +kernel

private def word41Chunk6 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word41State7 : PackedMat2 :=
    ⟨⟨⟨((5 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-7 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((-7 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-7 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((-5 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word41Step6 :
    word41Chunk6.foldl (fun acc a => a.applyPacked acc)
      word41State6 = word41State7 := by decide +kernel

private def word41Chunk7 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word41State8 : PackedMat2 :=
    ⟨⟨⟨((7 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-19 : Dyadic) * half ^ 5),
        ((7 : Dyadic) * half ^ 5)⟩,
       ⟨((-5 : Dyadic) * half ^ 5),
        ((-5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 3)⟩,
       ⟨((-17 : Dyadic) * half ^ 5),
        ((7 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((11 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((13 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word41Step7 :
    word41Chunk7.foldl (fun acc a => a.applyPacked acc)
      word41State7 = word41State8 := by decide +kernel

private def word41Chunk8 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word41State9 : PackedMat2 :=
    ⟨⟨⟨((15 : Dyadic) * half ^ 6),
        ((13 : Dyadic) * half ^ 5)⟩,
       ⟨((25 : Dyadic) * half ^ 6),
        ((-21 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((15 : Dyadic) * half ^ 6),
        ((9 : Dyadic) * half ^ 6)⟩,
       ⟨((25 : Dyadic) * half ^ 6),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((25 : Dyadic) * half ^ 6),
        (0 : Dyadic)⟩,
       ⟨((15 : Dyadic) * half ^ 6),
        ((9 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-25 : Dyadic) * half ^ 6),
        ((21 : Dyadic) * half ^ 6)⟩,
       ⟨((-15 : Dyadic) * half ^ 6),
        ((-13 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word41Step8 :
    word41Chunk8.foldl (fun acc a => a.applyPacked acc)
      word41State8 = word41State9 := by decide +kernel

private def word41Chunk9 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word41State10 : PackedMat2 :=
    ⟨⟨⟨((9 : Dyadic) * half ^ 5),
        ((7 : Dyadic) * half ^ 4)⟩,
       ⟨((-9 : Dyadic) * half ^ 6),
        ((23 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 5),
        ((-5 : Dyadic) * half ^ 7)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((39 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-17 : Dyadic) * half ^ 6),
        ((11 : Dyadic) * half ^ 6)⟩,
       ⟨((11 : Dyadic) * half ^ 5),
        ((-5 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((51 : Dyadic) * half ^ 6),
        ((9 : Dyadic) * half ^ 7)⟩,
       ⟨((5 : Dyadic) * half ^ 6),
        ((27 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word41Step9 :
    word41Chunk9.foldl (fun acc a => a.applyPacked acc)
      word41State9 = word41State10 := by decide +kernel

private def word41Chunk10 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word41State11 : PackedMat2 :=
    ⟨⟨⟨((-61 : Dyadic) * half ^ 7),
        ((13 : Dyadic) * half ^ 6)⟩,
       ⟨((-5 : Dyadic) * half ^ 7),
        ((7 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-23 : Dyadic) * half ^ 6),
        ((-33 : Dyadic) * half ^ 7)⟩,
       ⟨((1 : Dyadic) * half ^ 5),
        ((13 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 5),
        ((-13 : Dyadic) * half ^ 5)⟩,
       ⟨((23 : Dyadic) * half ^ 6),
        ((33 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 7),
        ((7 : Dyadic) * half ^ 5)⟩,
       ⟨((-61 : Dyadic) * half ^ 7),
        ((13 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word41Step10 :
    word41Chunk10.foldl (fun acc a => a.applyPacked acc)
      word41State10 = word41State11 := by decide +kernel

private def word41Chunk11 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word41State12 : PackedMat2 :=
    ⟨⟨⟨((45 : Dyadic) * half ^ 8),
        ((-61 : Dyadic) * half ^ 8)⟩,
       ⟨((83 : Dyadic) * half ^ 8),
        ((-5 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((11 : Dyadic) * half ^ 8),
        ((-77 : Dyadic) * half ^ 8)⟩,
       ⟨((-33 : Dyadic) * half ^ 8),
        ((-67 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-211 : Dyadic) * half ^ 8),
        ((-11 : Dyadic) * half ^ 8)⟩,
       ⟨((57 : Dyadic) * half ^ 8),
        ((11 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((71 : Dyadic) * half ^ 8),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((51 : Dyadic) * half ^ 8),
        ((19 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word41Step11 :
    word41Chunk11.foldl (fun acc a => a.applyPacked acc)
      word41State11 = word41State12 := by decide +kernel

private def word41Chunk12 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word41State13 : PackedMat2 :=
    ⟨⟨⟨((-293 : Dyadic) * half ^ 9),
        ((-133 : Dyadic) * half ^ 9)⟩,
       ⟨((-73 : Dyadic) * half ^ 9),
        ((-15 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((185 : Dyadic) * half ^ 9),
        ((-55 : Dyadic) * half ^ 7)⟩,
       ⟨((-51 : Dyadic) * half ^ 9),
        ((9 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((51 : Dyadic) * half ^ 9),
        ((-9 : Dyadic) * half ^ 9)⟩,
       ⟨((-185 : Dyadic) * half ^ 9),
        ((55 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-73 : Dyadic) * half ^ 9),
        ((-15 : Dyadic) * half ^ 8)⟩,
       ⟨((-293 : Dyadic) * half ^ 9),
        ((-133 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word41Step12 :
    word41Chunk12.foldl (fun acc a => a.applyPacked acc)
      word41State12 = word41State13 := by decide +kernel

private def word41Chunk13 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word41State14 : PackedMat2 :=
    ⟨⟨⟨((-217 : Dyadic) * half ^ 9),
        ((-277 : Dyadic) * half ^ 10)⟩,
       ⟨((-39 : Dyadic) * half ^ 9),
        ((-273 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((49 : Dyadic) * half ^ 9),
        ((-33 : Dyadic) * half ^ 8)⟩,
       ⟨((41 : Dyadic) * half ^ 6),
        ((-49 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-41 : Dyadic) * half ^ 7),
        ((377 : Dyadic) * half ^ 10)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        ((-279 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((275 : Dyadic) * half ^ 9),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 8),
        ((89 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word41Step13 :
    word41Chunk13.foldl (fun acc a => a.applyPacked acc)
      word41State13 = word41State14 := by decide +kernel

private def word41Chunk14 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word41State15 : PackedMat2 :=
    ⟨⟨⟨((45 : Dyadic) * half ^ 9),
        ((749 : Dyadic) * half ^ 11)⟩,
       ⟨((-421 : Dyadic) * half ^ 10),
        ((-539 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-35 : Dyadic) * half ^ 9),
        ((305 : Dyadic) * half ^ 11)⟩,
       ⟨((-441 : Dyadic) * half ^ 10),
        ((619 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((35 : Dyadic) * half ^ 9),
        ((-305 : Dyadic) * half ^ 11)⟩,
       ⟨((-441 : Dyadic) * half ^ 10),
        ((619 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((45 : Dyadic) * half ^ 9),
        ((749 : Dyadic) * half ^ 11)⟩,
       ⟨((421 : Dyadic) * half ^ 10),
        ((539 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word41Step14 :
    word41Chunk14.foldl (fun acc a => a.applyPacked acc)
      word41State14 = word41State15 := by decide +kernel

private def word41Chunk15 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word41State16 : PackedMat2 :=
    ⟨⟨⟨((1045 : Dyadic) * half ^ 11),
        ((-1 : Dyadic) * half ^ 10)⟩,
       ⟨((175 : Dyadic) * half ^ 11),
        ((197 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((111 : Dyadic) * half ^ 9),
        ((49 : Dyadic) * half ^ 10)⟩,
       ⟨((627 : Dyadic) * half ^ 10),
        ((-143 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((241 : Dyadic) * half ^ 11),
        ((-405 : Dyadic) * half ^ 11)⟩,
       ⟨((45 : Dyadic) * half ^ 11),
        ((-849 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((395 : Dyadic) * half ^ 10),
        ((-435 : Dyadic) * half ^ 11)⟩,
       ⟨((393 : Dyadic) * half ^ 10),
        ((305 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word41Step15 :
    word41Chunk15.foldl (fun acc a => a.applyPacked acc)
      word41State15 = word41State16 := by decide +kernel

private def word41Chunk16 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word41State17 : PackedMat2 :=
    ⟨⟨⟨((367 : Dyadic) * half ^ 10),
        ((47 : Dyadic) * half ^ 11)⟩,
       ⟨((35 : Dyadic) * half ^ 11),
        ((229 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-59 : Dyadic) * half ^ 9),
        ((-2149 : Dyadic) * half ^ 12)⟩,
       ⟨((155 : Dyadic) * half ^ 9),
        ((-981 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-59 : Dyadic) * half ^ 9),
        ((-2149 : Dyadic) * half ^ 12)⟩,
       ⟨((-155 : Dyadic) * half ^ 9),
        ((981 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-367 : Dyadic) * half ^ 10),
        ((-47 : Dyadic) * half ^ 11)⟩,
       ⟨((35 : Dyadic) * half ^ 11),
        ((229 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word41Step16 :
    word41Chunk16.foldl (fun acc a => a.applyPacked acc)
      word41State16 = word41State17 := by decide +kernel

private def word41Chunk17 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word41State18 : PackedMat2 :=
    ⟨⟨⟨((-441 : Dyadic) * half ^ 10),
        ((-1167 : Dyadic) * half ^ 13)⟩,
       ⟨((2769 : Dyadic) * half ^ 12),
        ((-437 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-557 : Dyadic) * half ^ 12),
        ((1575 : Dyadic) * half ^ 13)⟩,
       ⟨((-479 : Dyadic) * half ^ 10),
        ((-15 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-795 : Dyadic) * half ^ 12),
        ((-1359 : Dyadic) * half ^ 13)⟩,
       ⟨((195 : Dyadic) * half ^ 10),
        ((-2473 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-365 : Dyadic) * half ^ 12),
        ((-4533 : Dyadic) * half ^ 13)⟩,
       ⟨((401 : Dyadic) * half ^ 11),
        ((-1005 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word41Step17 :
    word41Chunk17.foldl (fun acc a => a.applyPacked acc)
      word41State17 = word41State18 := by decide +kernel

private def word41Chunk18 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word41State19 : PackedMat2 :=
    ⟨⟨⟨((-2583 : Dyadic) * half ^ 13),
        ((-6997 : Dyadic) * half ^ 14)⟩,
       ⟨((699 : Dyadic) * half ^ 11),
        ((-4355 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((851 : Dyadic) * half ^ 13),
        ((715 : Dyadic) * half ^ 14)⟩,
       ⟨((-253 : Dyadic) * half ^ 9),
        ((1607 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((851 : Dyadic) * half ^ 13),
        ((715 : Dyadic) * half ^ 14)⟩,
       ⟨((253 : Dyadic) * half ^ 9),
        ((-1607 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((2583 : Dyadic) * half ^ 13),
        ((6997 : Dyadic) * half ^ 14)⟩,
       ⟨((699 : Dyadic) * half ^ 11),
        ((-4355 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word41Step18 :
    word41Chunk18.foldl (fun acc a => a.applyPacked acc)
      word41State18 = word41State19 := by decide +kernel

private def word41Chunk19 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word41State20 : PackedMat2 :=
    ⟨⟨⟨((-5953 : Dyadic) * half ^ 13),
        ((-393 : Dyadic) * half ^ 12)⟩,
       ⟨((-1257 : Dyadic) * half ^ 13),
        ((-2183 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((3477 : Dyadic) * half ^ 14),
        ((-5543 : Dyadic) * half ^ 14)⟩,
       ⟨((-5547 : Dyadic) * half ^ 14),
        ((889 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-5547 : Dyadic) * half ^ 14),
        ((889 : Dyadic) * half ^ 14)⟩,
       ⟨((3477 : Dyadic) * half ^ 14),
        ((-5543 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((1257 : Dyadic) * half ^ 13),
        ((2183 : Dyadic) * half ^ 14)⟩,
       ⟨((5953 : Dyadic) * half ^ 13),
        ((393 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word41Step19 :
    word41Chunk19.foldl (fun acc a => a.applyPacked acc)
      word41State19 = word41State20 := by decide +kernel

private def word41Chunk20 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word41State21 : PackedMat2 :=
    ⟨⟨⟨((4917 : Dyadic) * half ^ 15),
        ((-2653 : Dyadic) * half ^ 13)⟩,
       ⟨((-19749 : Dyadic) * half ^ 15),
        ((1457 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-8053 : Dyadic) * half ^ 15),
        ((405 : Dyadic) * half ^ 15)⟩,
       ⟨((-6651 : Dyadic) * half ^ 15),
        ((-6331 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((12257 : Dyadic) * half ^ 15),
        ((919 : Dyadic) * half ^ 12)⟩,
       ⟨((-13067 : Dyadic) * half ^ 15),
        ((701 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-9155 : Dyadic) * half ^ 15),
        ((-927 : Dyadic) * half ^ 12)⟩,
       ⟨((-12069 : Dyadic) * half ^ 15),
        ((12333 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word41Step20 :
    word41Chunk20.foldl (fun acc a => a.applyPacked acc)
      word41State20 = word41State21 := by decide +kernel

private def word41Chunk21 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word41State22 : PackedMat2 :=
    ⟨⟨⟨((-3433 : Dyadic) * half ^ 14),
        ((-973 : Dyadic) * half ^ 14)⟩,
       ⟨((10449 : Dyadic) * half ^ 15),
        ((-15531 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((2077 : Dyadic) * half ^ 13),
        ((12025 : Dyadic) * half ^ 16)⟩,
       ⟨((-5327 : Dyadic) * half ^ 14),
        ((-18579 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((2077 : Dyadic) * half ^ 13),
        ((12025 : Dyadic) * half ^ 16)⟩,
       ⟨((5327 : Dyadic) * half ^ 14),
        ((18579 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((3433 : Dyadic) * half ^ 14),
        ((973 : Dyadic) * half ^ 14)⟩,
       ⟨((10449 : Dyadic) * half ^ 15),
        ((-15531 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word41Step21 :
    word41Chunk21.foldl (fun acc a => a.applyPacked acc)
      word41State21 = word41State22 := by decide +kernel

private def word41Chunk22 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word41State23 : PackedMat2 :=
    ⟨⟨⟨((3163 : Dyadic) * half ^ 13),
        ((36601 : Dyadic) * half ^ 17)⟩,
       ⟨((-31515 : Dyadic) * half ^ 16),
        ((33099 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((4063 : Dyadic) * half ^ 16),
        ((42831 : Dyadic) * half ^ 17)⟩,
       ⟨((-7 : Dyadic) * half ^ 8),
        ((31841 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-4063 : Dyadic) * half ^ 16),
        ((-42831 : Dyadic) * half ^ 17)⟩,
       ⟨((-7 : Dyadic) * half ^ 8),
        ((31841 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((3163 : Dyadic) * half ^ 13),
        ((36601 : Dyadic) * half ^ 17)⟩,
       ⟨((31515 : Dyadic) * half ^ 16),
        ((-33099 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word41Step22 :
    word41Chunk22.foldl (fun acc a => a.applyPacked acc)
      word41State22 = word41State23 := by decide +kernel

private def word41Chunk23 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word41State24 : PackedMat2 :=
    ⟨⟨⟨((3899 : Dyadic) * half ^ 17),
        ((-1741 : Dyadic) * half ^ 13)⟩,
       ⟨((89877 : Dyadic) * half ^ 17),
        ((7283 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((1783 : Dyadic) * half ^ 13),
        ((-4027 : Dyadic) * half ^ 15)⟩,
       ⟨((37353 : Dyadic) * half ^ 16),
        ((-9919 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-6189 : Dyadic) * half ^ 17),
        ((-23089 : Dyadic) * half ^ 17)⟩,
       ⟨((26027 : Dyadic) * half ^ 17),
        ((-51617 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((21211 : Dyadic) * half ^ 16),
        ((42989 : Dyadic) * half ^ 17)⟩,
       ⟨((-6645 : Dyadic) * half ^ 16),
        ((5861 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word41Step23 :
    word41Chunk23.foldl (fun acc a => a.applyPacked acc)
      word41State23 = word41State24 := by decide +kernel

private def word41Chunk24 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word41State25 : PackedMat2 :=
    ⟨⟨⟨((-93079 : Dyadic) * half ^ 18),
        ((27555 : Dyadic) * half ^ 18)⟩,
       ⟨((110171 : Dyadic) * half ^ 18),
        ((20329 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-114627 : Dyadic) * half ^ 18),
        ((2439 : Dyadic) * half ^ 18)⟩,
       ⟨((122713 : Dyadic) * half ^ 18),
        ((-24913 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((122713 : Dyadic) * half ^ 18),
        ((-24913 : Dyadic) * half ^ 17)⟩,
       ⟨((-114627 : Dyadic) * half ^ 18),
        ((2439 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-110171 : Dyadic) * half ^ 18),
        ((-20329 : Dyadic) * half ^ 16)⟩,
       ⟨((93079 : Dyadic) * half ^ 18),
        ((-27555 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word41Step24 :
    word41Chunk24.foldl (fun acc a => a.applyPacked acc)
      word41State24 = word41State25 := by decide +kernel

private def word41Chunk25 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word41State26 : PackedMat2 :=
    ⟨⟨⟨((-57687 : Dyadic) * half ^ 19),
        ((-67051 : Dyadic) * half ^ 19)⟩,
       ⟨((244533 : Dyadic) * half ^ 19),
        ((-11515 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-76807 : Dyadic) * half ^ 19),
        ((-142843 : Dyadic) * half ^ 18)⟩,
       ⟨((37621 : Dyadic) * half ^ 19),
        ((-87299 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-37621 : Dyadic) * half ^ 19),
        ((87299 : Dyadic) * half ^ 19)⟩,
       ⟨((76807 : Dyadic) * half ^ 19),
        ((142843 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((244533 : Dyadic) * half ^ 19),
        ((-11515 : Dyadic) * half ^ 16)⟩,
       ⟨((-57687 : Dyadic) * half ^ 19),
        ((-67051 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word41Step25 :
    word41Chunk25.foldl (fun acc a => a.applyPacked acc)
      word41State25 = word41State26 := by decide +kernel

private def word41Chunk26 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word41State27 : PackedMat2 :=
    ⟨⟨⟨((-2825 : Dyadic) * half ^ 19),
        ((27013 : Dyadic) * half ^ 19)⟩,
       ⟨((-10885 : Dyadic) * half ^ 18),
        ((29337 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-192041 : Dyadic) * half ^ 18),
        ((103915 : Dyadic) * half ^ 20)⟩,
       ⟨((-7073 : Dyadic) * half ^ 15),
        ((-399175 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-73815 : Dyadic) * half ^ 18),
        ((-248625 : Dyadic) * half ^ 19)⟩,
       ⟨((251545 : Dyadic) * half ^ 19),
        ((-135457 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-144361 : Dyadic) * half ^ 19),
        ((24595 : Dyadic) * half ^ 20)⟩,
       ⟨((90335 : Dyadic) * half ^ 19),
        ((-18945 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word41Step26 :
    word41Chunk26.foldl (fun acc a => a.applyPacked acc)
      word41State26 = word41State27 := by decide +kernel

private def word41Chunk27 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word41State28 : PackedMat2 :=
    ⟨⟨⟨((38867 : Dyadic) * half ^ 17),
        ((291985 : Dyadic) * half ^ 21)⟩,
       ⟨((-185805 : Dyadic) * half ^ 20),
        ((540691 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-274183 : Dyadic) * half ^ 20),
        ((-18755 : Dyadic) * half ^ 21)⟩,
       ⟨((-419565 : Dyadic) * half ^ 19),
        ((-5401 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((6677 : Dyadic) * half ^ 20),
        ((-564947 : Dyadic) * half ^ 21)⟩,
       ⟨((-6039 : Dyadic) * half ^ 19),
        ((-1113313 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-124353 : Dyadic) * half ^ 20),
        ((496741 : Dyadic) * half ^ 21)⟩,
       ⟨((-208169 : Dyadic) * half ^ 19),
        ((-125131 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word41Step27 :
    word41Chunk27.foldl (fun acc a => a.applyPacked acc)
      word41State27 = word41State28 := by decide +kernel

private def word41Chunk28 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word41State29 : PackedMat2 :=
    ⟨⟨⟨((-544307 : Dyadic) * half ^ 20),
        ((-42667 : Dyadic) * half ^ 19)⟩,
       ⟨((39931 : Dyadic) * half ^ 17),
        ((-71165 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((1292441 : Dyadic) * half ^ 21),
        ((12103 : Dyadic) * half ^ 20)⟩,
       ⟨((241933 : Dyadic) * half ^ 21),
        ((-354663 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((183383 : Dyadic) * half ^ 19),
        ((262627 : Dyadic) * half ^ 20)⟩,
       ⟨((10705 : Dyadic) * half ^ 15),
        ((-767187 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((99503 : Dyadic) * half ^ 21),
        ((863755 : Dyadic) * half ^ 21)⟩,
       ⟨((-241833 : Dyadic) * half ^ 21),
        ((-224859 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word41Step28 :
    word41Chunk28.foldl (fun acc a => a.applyPacked acc)
      word41State28 = word41State29 := by decide +kernel

private def word41Chunk29 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word41State30 : PackedMat2 :=
    ⟨⟨⟨((-2654463 : Dyadic) * half ^ 22),
        ((442825 : Dyadic) * half ^ 22)⟩,
       ⟨((383317 : Dyadic) * half ^ 22),
        ((143397 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((607221 : Dyadic) * half ^ 22),
        ((862789 : Dyadic) * half ^ 21)⟩,
       ⟨((900345 : Dyadic) * half ^ 22),
        ((-346619 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((1378959 : Dyadic) * half ^ 22),
        ((753783 : Dyadic) * half ^ 22)⟩,
       ⟨((2072197 : Dyadic) * half ^ 22),
        ((-73281 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-1590001 : Dyadic) * half ^ 22),
        ((1135573 : Dyadic) * half ^ 22)⟩,
       ⟨((704351 : Dyadic) * half ^ 22),
        ((759445 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word41Step29 :
    word41Chunk29.foldl (fun acc a => a.applyPacked acc)
      word41State29 = word41State30 := by decide +kernel

private def word41Chunk30 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word41State31 : PackedMat2 :=
    ⟨⟨⟨((33969 : Dyadic) * half ^ 17),
        ((-1383313 : Dyadic) * half ^ 23)⟩,
       ⟨((-587031 : Dyadic) * half ^ 21),
        ((-1493305 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((1609547 : Dyadic) * half ^ 22),
        ((-984173 : Dyadic) * half ^ 22)⟩,
       ⟨((45911 : Dyadic) * half ^ 18),
        ((993289 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-1609547 : Dyadic) * half ^ 22),
        ((984173 : Dyadic) * half ^ 22)⟩,
       ⟨((45911 : Dyadic) * half ^ 18),
        ((993289 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((33969 : Dyadic) * half ^ 17),
        ((-1383313 : Dyadic) * half ^ 23)⟩,
       ⟨((587031 : Dyadic) * half ^ 21),
        ((1493305 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word41Step30 :
    word41Chunk30.foldl (fun acc a => a.applyPacked acc)
      word41State30 = word41State31 := by decide +kernel

private def word41Chunk31 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word41State32 : PackedMat2 :=
    ⟨⟨⟨((135033 : Dyadic) * half ^ 21),
        ((16265 : Dyadic) * half ^ 17)⟩,
       ⟨((246989 : Dyadic) * half ^ 23),
        ((-612937 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((444337 : Dyadic) * half ^ 23),
        ((-6792739 : Dyadic) * half ^ 24)⟩,
       ⟨((274335 : Dyadic) * half ^ 23),
        ((9110425 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((1158843 : Dyadic) * half ^ 23),
        ((44917 : Dyadic) * half ^ 20)⟩,
       ⟨((-3975791 : Dyadic) * half ^ 22),
        ((85001 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((92457 : Dyadic) * half ^ 22),
        ((-787121 : Dyadic) * half ^ 24)⟩,
       ⟨((-1133417 : Dyadic) * half ^ 22),
        ((-293143 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word41Step31 :
    word41Chunk31.foldl (fun acc a => a.applyPacked acc)
      word41State31 = word41State32 := by decide +kernel

private def word41Chunk32 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word41State33 : PackedMat2 :=
    ⟨⟨⟨((569817 : Dyadic) * half ^ 22),
        ((-3260727 : Dyadic) * half ^ 25)⟩,
       ⟨((-2185951 : Dyadic) * half ^ 24),
        ((-6534527 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-3803603 : Dyadic) * half ^ 23),
        ((-10303671 : Dyadic) * half ^ 25)⟩,
       ⟨((9801751 : Dyadic) * half ^ 24),
        ((-8695817 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((3803603 : Dyadic) * half ^ 23),
        ((10303671 : Dyadic) * half ^ 25)⟩,
       ⟨((9801751 : Dyadic) * half ^ 24),
        ((-8695817 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((569817 : Dyadic) * half ^ 22),
        ((-3260727 : Dyadic) * half ^ 25)⟩,
       ⟨((2185951 : Dyadic) * half ^ 24),
        ((6534527 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word41Step32 :
    word41Chunk32.foldl (fun acc a => a.applyPacked acc)
      word41State32 = word41State33 := by decide +kernel

private def word41Chunk33 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word41State34 : PackedMat2 :=
    ⟨⟨⟨((-3428783 : Dyadic) * half ^ 25),
        ((-754199 : Dyadic) * half ^ 22)⟩,
       ⟨((16557899 : Dyadic) * half ^ 25),
        ((3019909 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-1930313 : Dyadic) * half ^ 25),
        ((-11748981 : Dyadic) * half ^ 25)⟩,
       ⟨((6379465 : Dyadic) * half ^ 25),
        ((-3659023 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((26385073 : Dyadic) * half ^ 25),
        ((-34759 : Dyadic) * half ^ 19)⟩,
       ⟨((-2887111 : Dyadic) * half ^ 25),
        ((4154889 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-3013683 : Dyadic) * half ^ 25),
        ((3282279 : Dyadic) * half ^ 24)⟩,
       ⟨((-9053501 : Dyadic) * half ^ 25),
        ((-9993341 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word41Step33 :
    word41Chunk33.foldl (fun acc a => a.applyPacked acc)
      word41State33 = word41State34 := by decide +kernel

private def word41Chunk34 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word41State35 : PackedMat2 :=
    ⟨⟨⟨((-1265769 : Dyadic) * half ^ 22),
        ((4769323 : Dyadic) * half ^ 26)⟩,
       ⟨((-4155225 : Dyadic) * half ^ 24),
        ((-17125035 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-623853 : Dyadic) * half ^ 23),
        ((1012287 : Dyadic) * half ^ 22)⟩,
       ⟨((-25626375 : Dyadic) * half ^ 25),
        ((1045889 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-623853 : Dyadic) * half ^ 23),
        ((1012287 : Dyadic) * half ^ 22)⟩,
       ⟨((25626375 : Dyadic) * half ^ 25),
        ((-1045889 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((1265769 : Dyadic) * half ^ 22),
        ((-4769323 : Dyadic) * half ^ 26)⟩,
       ⟨((-4155225 : Dyadic) * half ^ 24),
        ((-17125035 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word41Step34 :
    word41Chunk34.foldl (fun acc a => a.applyPacked acc)
      word41State34 = word41State35 := by decide +kernel

private def word41Chunk35 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word41State36 : PackedMat2 :=
    ⟨⟨⟨((-2020775 : Dyadic) * half ^ 23),
        ((461749 : Dyadic) * half ^ 25)⟩,
       ⟨((48582665 : Dyadic) * half ^ 26),
        ((-9304057 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((3200047 : Dyadic) * half ^ 24),
        ((44489543 : Dyadic) * half ^ 27)⟩,
       ⟨((-6627223 : Dyadic) * half ^ 25),
        ((-27493881 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-8497831 : Dyadic) * half ^ 26),
        ((227129 : Dyadic) * half ^ 26)⟩,
       ⟨((-1124741 : Dyadic) * half ^ 21),
        ((-13027317 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-8380559 : Dyadic) * half ^ 26),
        ((32416465 : Dyadic) * half ^ 27)⟩,
       ⟨((10227555 : Dyadic) * half ^ 26),
        ((-64748865 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word41Step35 :
    word41Chunk35.foldl (fun acc a => a.applyPacked acc)
      word41State35 = word41State36 := by decide +kernel

private def word41Chunk36 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word41State37 : PackedMat2 :=
    ⟨⟨⟨((-33481223 : Dyadic) * half ^ 27),
        ((13769595 : Dyadic) * half ^ 28)⟩,
       ⟨((-23787251 : Dyadic) * half ^ 26),
        ((54522783 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((53163327 : Dyadic) * half ^ 26),
        ((34486143 : Dyadic) * half ^ 28)⟩,
       ⟨((-30859893 : Dyadic) * half ^ 27),
        ((19827647 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((53163327 : Dyadic) * half ^ 26),
        ((34486143 : Dyadic) * half ^ 28)⟩,
       ⟨((30859893 : Dyadic) * half ^ 27),
        ((-19827647 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((33481223 : Dyadic) * half ^ 27),
        ((-13769595 : Dyadic) * half ^ 28)⟩,
       ⟨((-23787251 : Dyadic) * half ^ 26),
        ((54522783 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word41Step36 :
    word41Chunk36.foldl (fun acc a => a.applyPacked acc)
      word41State36 = word41State37 := by decide +kernel

private def word41Chunk37 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word41State38 : PackedMat2 :=
    ⟨⟨⟨((167005785 : Dyadic) * half ^ 28),
        ((-4928239 : Dyadic) * half ^ 27)⟩,
       ⟨((79099361 : Dyadic) * half ^ 28),
        ((-8852285 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-17328145 : Dyadic) * half ^ 27),
        ((34551581 : Dyadic) * half ^ 28)⟩,
       ⟨((29192235 : Dyadic) * half ^ 26),
        ((18081005 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((37772439 : Dyadic) * half ^ 28),
        ((75712615 : Dyadic) * half ^ 28)⟩,
       ⟨((106875601 : Dyadic) * half ^ 28),
        ((41056325 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((30480901 : Dyadic) * half ^ 27),
        ((10988303 : Dyadic) * half ^ 26)⟩,
       ⟨((40337379 : Dyadic) * half ^ 27),
        ((-123052573 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word41Step37 :
    word41Chunk37.foldl (fun acc a => a.applyPacked acc)
      word41State37 = word41State38 := by decide +kernel

private def word41Chunk38 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word41State39 : PackedMat2 :=
    ⟨⟨⟨((-64156027 : Dyadic) * half ^ 29),
        ((50818121 : Dyadic) * half ^ 27)⟩,
       ⟨((142138165 : Dyadic) * half ^ 29),
        ((141566903 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((119340007 : Dyadic) * half ^ 29),
        ((-29209197 : Dyadic) * half ^ 27)⟩,
       ⟨((30892389 : Dyadic) * half ^ 29),
        ((222138801 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-105302013 : Dyadic) * half ^ 29),
        ((-37558099 : Dyadic) * half ^ 28)⟩,
       ⟨((338975589 : Dyadic) * half ^ 29),
        ((-44223809 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((344839387 : Dyadic) * half ^ 29),
        ((38991069 : Dyadic) * half ^ 29)⟩,
       ⟨((61705581 : Dyadic) * half ^ 29),
        ((-12893387 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word41Step38 :
    word41Chunk38.foldl (fun acc a => a.applyPacked acc)
      word41State38 = word41State39 := by decide +kernel

private def word41Chunk39 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word41State40 : PackedMat2 :=
    ⟨⟨⟨((79552395 : Dyadic) * half ^ 29),
        ((-35104891 : Dyadic) * half ^ 27)⟩,
       ⟨((69744171 : Dyadic) * half ^ 27),
        ((37648355 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((40136711 : Dyadic) * half ^ 29),
        ((-63807725 : Dyadic) * half ^ 30)⟩,
       ⟨((312661595 : Dyadic) * half ^ 29),
        ((-189091495 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((40136711 : Dyadic) * half ^ 29),
        ((-63807725 : Dyadic) * half ^ 30)⟩,
       ⟨((-312661595 : Dyadic) * half ^ 29),
        ((189091495 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-79552395 : Dyadic) * half ^ 29),
        ((35104891 : Dyadic) * half ^ 27)⟩,
       ⟨((69744171 : Dyadic) * half ^ 27),
        ((37648355 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word41Step39 :
    word41Chunk39.foldl (fun acc a => a.applyPacked acc)
      word41State39 = word41State40 := by decide +kernel

private def word41Chunk40 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word41State41 : PackedMat2 :=
    ⟨⟨⟨((-293450089 : Dyadic) * half ^ 29),
        ((-492296885 : Dyadic) * half ^ 31)⟩,
       ⟨((-62800823 : Dyadic) * half ^ 30),
        ((-576295195 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((856563 : Dyadic) * half ^ 30),
        ((179798625 : Dyadic) * half ^ 31)⟩,
       ⟨((-194400319 : Dyadic) * half ^ 29),
        ((836611155 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-856563 : Dyadic) * half ^ 30),
        ((-179798625 : Dyadic) * half ^ 31)⟩,
       ⟨((-194400319 : Dyadic) * half ^ 29),
        ((836611155 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-293450089 : Dyadic) * half ^ 29),
        ((-492296885 : Dyadic) * half ^ 31)⟩,
       ⟨((62800823 : Dyadic) * half ^ 30),
        ((576295195 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word41Step40 :
    word41Chunk40.foldl (fun acc a => a.applyPacked acc)
      word41State40 = word41State41 := by decide +kernel

private def word41Chunk41 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word41State42 : PackedMat2 :=
    ⟨⟨⟨((690843593 : Dyadic) * half ^ 31),
        ((91173525 : Dyadic) * half ^ 30)⟩,
       ⟨((-1447196033 : Dyadic) * half ^ 31),
        ((16931779 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-8240037 : Dyadic) * half ^ 25),
        ((-139881183 : Dyadic) * half ^ 29)⟩,
       ⟨((480331457 : Dyadic) * half ^ 30),
        ((-234230705 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-325294027 : Dyadic) * half ^ 31),
        ((-744012641 : Dyadic) * half ^ 31)⟩,
       ⟨((793755437 : Dyadic) * half ^ 31),
        ((-216650273 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-23446409 : Dyadic) * half ^ 30),
        ((-1069019813 : Dyadic) * half ^ 31)⟩,
       ⟨((158900641 : Dyadic) * half ^ 30),
        ((-94544055 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word41Step41 :
    word41Chunk41.foldl (fun acc a => a.applyPacked acc)
      word41State41 = word41State42 := by decide +kernel

private def word41Chunk42 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word41State43 : PackedMat2 :=
    ⟨⟨⟨((1284527765 : Dyadic) * half ^ 32),
        ((-4135371 : Dyadic) * half ^ 32)⟩,
       ⟨((1089143 : Dyadic) * half ^ 32),
        ((-515309139 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-2770555971 : Dyadic) * half ^ 32),
        ((-475478713 : Dyadic) * half ^ 32)⟩,
       ⟨((-2443019811 : Dyadic) * half ^ 32),
        ((268296207 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-2443019811 : Dyadic) * half ^ 32),
        ((268296207 : Dyadic) * half ^ 31)⟩,
       ⟨((-2770555971 : Dyadic) * half ^ 32),
        ((-475478713 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-1089143 : Dyadic) * half ^ 32),
        ((515309139 : Dyadic) * half ^ 31)⟩,
       ⟨((-1284527765 : Dyadic) * half ^ 32),
        ((4135371 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word41Step42 :
    word41Chunk42.foldl (fun acc a => a.applyPacked acc)
      word41State42 = word41State43 := by decide +kernel

private def word41Chunk43 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word41State44 : PackedMat2 :=
    ⟨⟨⟨((-675538453 : Dyadic) * half ^ 31),
        ((1106532687 : Dyadic) * half ^ 32)⟩,
       ⟨((-1260935499 : Dyadic) * half ^ 32),
        ((149226581 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((525051939 : Dyadic) * half ^ 30),
        ((805736497 : Dyadic) * half ^ 33)⟩,
       ⟨((-96934389 : Dyadic) * half ^ 29),
        ((-3614723647 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((1404493575 : Dyadic) * half ^ 32),
        ((-331183161 : Dyadic) * half ^ 31)⟩,
       ⟨((-276278759 : Dyadic) * half ^ 29),
        ((-718920717 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((1703439011 : Dyadic) * half ^ 32),
        ((-2612012405 : Dyadic) * half ^ 33)⟩,
       ⟨((509626363 : Dyadic) * half ^ 32),
        ((-90141407 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word41Step43 :
    word41Chunk43.foldl (fun acc a => a.applyPacked acc)
      word41State43 = word41State44 := by decide +kernel

private def word41Chunk44 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word41State45 : PackedMat2 :=
    ⟨⟨⟨((1255921911 : Dyadic) * half ^ 33),
        ((1063312143 : Dyadic) * half ^ 31)⟩,
       ⟨((1428659551 : Dyadic) * half ^ 33),
        ((848415561 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((2173075937 : Dyadic) * half ^ 32),
        ((-1320960057 : Dyadic) * half ^ 33)⟩,
       ⟨((234657309 : Dyadic) * half ^ 30),
        ((-269655067 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-234657309 : Dyadic) * half ^ 30),
        ((269655067 : Dyadic) * half ^ 31)⟩,
       ⟨((-2173075937 : Dyadic) * half ^ 32),
        ((1320960057 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((1428659551 : Dyadic) * half ^ 33),
        ((848415561 : Dyadic) * half ^ 32)⟩,
       ⟨((1255921911 : Dyadic) * half ^ 33),
        ((1063312143 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word41Step44 :
    word41Chunk44.foldl (fun acc a => a.applyPacked acc)
      word41State44 = word41State45 := by decide +kernel

private def word41Chunk45 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word41State46 : PackedMat2 :=
    ⟨⟨⟨((-4959943261 : Dyadic) * half ^ 34),
        ((8189993621 : Dyadic) * half ^ 34)⟩,
       ⟨((6868372421 : Dyadic) * half ^ 34),
        ((4482372583 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((1874130501 : Dyadic) * half ^ 33),
        ((-4210037 : Dyadic) * half ^ 31)⟩,
       ⟨((2639232945 : Dyadic) * half ^ 33),
        ((1887204007 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((1920884303 : Dyadic) * half ^ 34),
        ((191275611 : Dyadic) * half ^ 32)⟩,
       ⟨((1853523711 : Dyadic) * half ^ 34),
        ((2256681723 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((1853810519 : Dyadic) * half ^ 33),
        ((-5914157841 : Dyadic) * half ^ 34)⟩,
       ⟨((-3168091551 : Dyadic) * half ^ 32),
        ((-238553645 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word41Step45 :
    word41Chunk45.foldl (fun acc a => a.applyPacked acc)
      word41State45 = word41State46 := by decide +kernel

private def word41Chunk46 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word41State47 : PackedMat2 :=
    ⟨⟨⟨((14790080711 : Dyadic) * half ^ 35),
        ((-7555111837 : Dyadic) * half ^ 35)⟩,
       ⟨((7753062907 : Dyadic) * half ^ 35),
        ((7512342873 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-12214198903 : Dyadic) * half ^ 35),
        ((-655328897 : Dyadic) * half ^ 33)⟩,
       ⟨((12482612277 : Dyadic) * half ^ 35),
        ((-2945208027 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-12482612277 : Dyadic) * half ^ 35),
        ((2945208027 : Dyadic) * half ^ 35)⟩,
       ⟨((12214198903 : Dyadic) * half ^ 35),
        ((655328897 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((7753062907 : Dyadic) * half ^ 35),
        ((7512342873 : Dyadic) * half ^ 34)⟩,
       ⟨((14790080711 : Dyadic) * half ^ 35),
        ((-7555111837 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word41Step46 :
    word41Chunk46.foldl (fun acc a => a.applyPacked acc)
      word41State46 = word41State47 := by decide +kernel

private def word41Chunk47 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word41State48 : PackedMat2 :=
    ⟨⟨⟨((-7107452549 : Dyadic) * half ^ 34),
        ((-25099587 : Dyadic) * half ^ 34)⟩,
       ⟨((22581672321 : Dyadic) * half ^ 35),
        ((-1518806815 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-12597408681 : Dyadic) * half ^ 35),
        ((-20540562685 : Dyadic) * half ^ 36)⟩,
       ⟨((2237591313 : Dyadic) * half ^ 35),
        ((6342787787 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-7098887449 : Dyadic) * half ^ 35),
        ((-1294977171 : Dyadic) * half ^ 33)⟩,
       ⟨((-3360418809 : Dyadic) * half ^ 33),
        ((-7417499997 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((3062713217 : Dyadic) * half ^ 34),
        ((-8366767223 : Dyadic) * half ^ 36)⟩,
       ⟨((-3012514043 : Dyadic) * half ^ 34),
        ((36796577419 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word41Step47 :
    word41Chunk47.foldl (fun acc a => a.applyPacked acc)
      word41State47 = word41State48 := by decide +kernel

private def word41Chunk48 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word41State49 : PackedMat2 :=
    ⟨⟨⟨((-4720313293 : Dyadic) * half ^ 35),
        ((-34905541919 : Dyadic) * half ^ 37)⟩,
       ⟨((-56363679089 : Dyadic) * half ^ 36),
        ((5581823401 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((1521784283 : Dyadic) * half ^ 35),
        ((-9003992319 : Dyadic) * half ^ 37)⟩,
       ⟨((-27958915529 : Dyadic) * half ^ 36),
        ((-446590421 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-1521784283 : Dyadic) * half ^ 35),
        ((9003992319 : Dyadic) * half ^ 37)⟩,
       ⟨((-27958915529 : Dyadic) * half ^ 36),
        ((-446590421 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-4720313293 : Dyadic) * half ^ 35),
        ((-34905541919 : Dyadic) * half ^ 37)⟩,
       ⟨((56363679089 : Dyadic) * half ^ 36),
        ((-5581823401 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word41Step48 :
    word41Chunk48.foldl (fun acc a => a.applyPacked acc)
      word41State48 = word41State49 := by decide +kernel

private def word41Chunk49 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word41State50 : PackedMat2 :=
    ⟨⟨⟨((17652380905 : Dyadic) * half ^ 36),
        ((-57647831657 : Dyadic) * half ^ 37)⟩,
       ⟨((-8800853743 : Dyadic) * half ^ 36),
        ((-9475022575 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((35717819311 : Dyadic) * half ^ 37),
        ((716396529 : Dyadic) * half ^ 37)⟩,
       ⟨((-77000325103 : Dyadic) * half ^ 37),
        ((-17435621717 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((77000325103 : Dyadic) * half ^ 37),
        ((17435621717 : Dyadic) * half ^ 37)⟩,
       ⟨((-35717819311 : Dyadic) * half ^ 37),
        ((-716396529 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-8800853743 : Dyadic) * half ^ 36),
        ((-9475022575 : Dyadic) * half ^ 35)⟩,
       ⟨((17652380905 : Dyadic) * half ^ 36),
        ((-57647831657 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word41Step49 :
    word41Chunk49.foldl (fun acc a => a.applyPacked acc)
      word41State49 = word41State50 := by decide +kernel

private def word41Chunk50 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word41State51 : PackedMat2 :=
    ⟨⟨⟨((-20693630725 : Dyadic) * half ^ 38),
        ((90640473827 : Dyadic) * half ^ 38)⟩,
       ⟨((-76213238101 : Dyadic) * half ^ 38),
        ((-9495741959 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((60831410675 : Dyadic) * half ^ 38),
        ((1906668841 : Dyadic) * half ^ 35)⟩,
       ⟨((36151337687 : Dyadic) * half ^ 38),
        ((-133931760231 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-118678409503 : Dyadic) * half ^ 38),
        ((48491374181 : Dyadic) * half ^ 38)⟩,
       ⟨((149185110959 : Dyadic) * half ^ 38),
        ((6170018247 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-14674538155 : Dyadic) * half ^ 38),
        ((48453434413 : Dyadic) * half ^ 38)⟩,
       ⟨((-166606409499 : Dyadic) * half ^ 38),
        ((-3469975461 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word41Step50 :
    word41Chunk50.foldl (fun acc a => a.applyPacked acc)
      word41State50 = word41State51 := by decide +kernel

private def word41Chunk51 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word41State52 : PackedMat2 :=
    ⟨⟨⟨((-237437704969 : Dyadic) * half ^ 39),
        ((37418375673 : Dyadic) * half ^ 39)⟩,
       ⟨((275810506007 : Dyadic) * half ^ 39),
        ((-13779185379 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((271474335617 : Dyadic) * half ^ 39),
        ((46224192309 : Dyadic) * half ^ 38)⟩,
       ⟨((-205880134679 : Dyadic) * half ^ 39),
        ((-68927107545 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((205880134679 : Dyadic) * half ^ 39),
        ((68927107545 : Dyadic) * half ^ 39)⟩,
       ⟨((-271474335617 : Dyadic) * half ^ 39),
        ((-46224192309 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((275810506007 : Dyadic) * half ^ 39),
        ((-13779185379 : Dyadic) * half ^ 36)⟩,
       ⟨((-237437704969 : Dyadic) * half ^ 39),
        ((37418375673 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word41Step51 :
    word41Chunk51.foldl (fun acc a => a.applyPacked acc)
      word41State51 = word41State52 := by decide +kernel

private def word41Chunk52 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word41State53 : PackedMat2 :=
    ⟨⟨⟨((-44363119397 : Dyadic) * half ^ 38),
        ((-23601780367 : Dyadic) * half ^ 38)⟩,
       ⟨((-148264589435 : Dyadic) * half ^ 39),
        ((137976529207 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((231796005637 : Dyadic) * half ^ 39),
        ((321215042643 : Dyadic) * half ^ 40)⟩,
       ⟨((-7015869089 : Dyadic) * half ^ 39),
        ((143192355427 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((232203699035 : Dyadic) * half ^ 39),
        ((56195034137 : Dyadic) * half ^ 38)⟩,
       ⟨((11126417951 : Dyadic) * half ^ 36),
        ((119405937363 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-14296843605 : Dyadic) * half ^ 35),
        ((236990828229 : Dyadic) * half ^ 40)⟩,
       ⟨((80789154787 : Dyadic) * half ^ 37),
        ((-59538350641 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word41Step52 :
    word41Chunk52.foldl (fun acc a => a.applyPacked acc)
      word41State52 = word41State53 := by decide +kernel

private def word41Chunk53 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word41State54 : PackedMat2 :=
    ⟨⟨⟨((71413368401 : Dyadic) * half ^ 38),
        ((-408143551773 : Dyadic) * half ^ 41)⟩,
       ⟨((470195747123 : Dyadic) * half ^ 40),
        ((-534128655765 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((208478575263 : Dyadic) * half ^ 39),
        ((414806777315 : Dyadic) * half ^ 41)⟩,
       ⟨((226723771629 : Dyadic) * half ^ 40),
        ((859089421293 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-208478575263 : Dyadic) * half ^ 39),
        ((-414806777315 : Dyadic) * half ^ 41)⟩,
       ⟨((226723771629 : Dyadic) * half ^ 40),
        ((859089421293 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((71413368401 : Dyadic) * half ^ 38),
        ((-408143551773 : Dyadic) * half ^ 41)⟩,
       ⟨((-470195747123 : Dyadic) * half ^ 40),
        ((534128655765 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word41Step53 :
    word41Chunk53.foldl (fun acc a => a.applyPacked acc)
      word41State53 = word41State54 := by decide +kernel

private def word41Chunk54 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word41State55 : PackedMat2 :=
    ⟨⟨⟨((-30173899949 : Dyadic) * half ^ 38),
        ((218639565641 : Dyadic) * half ^ 39)⟩,
       ⟨((-235308252075 : Dyadic) * half ^ 40),
        ((361240660685 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((659219109455 : Dyadic) * half ^ 41),
        ((-97628042621 : Dyadic) * half ^ 39)⟩,
       ⟨((1213054019823 : Dyadic) * half ^ 41),
        ((263199148523 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-458455233765 : Dyadic) * half ^ 40),
        ((-17307340949 : Dyadic) * half ^ 37)⟩,
       ⟨((-67943063281 : Dyadic) * half ^ 40),
        ((-936136564639 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-513317601879 : Dyadic) * half ^ 41),
        ((-114612652279 : Dyadic) * half ^ 41)⟩,
       ⟨((1235798923249 : Dyadic) * half ^ 41),
        ((-356003851871 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word41Step54 :
    word41Chunk54.foldl (fun acc a => a.applyPacked acc)
      word41State54 = word41State55 := by decide +kernel

private def word41Chunk55 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word41State56 : PackedMat2 :=
    ⟨⟨⟨((2878952138733 : Dyadic) * half ^ 42),
        ((-993144030761 : Dyadic) * half ^ 42)⟩,
       ⟨((-731963898045 : Dyadic) * half ^ 42),
        ((-15307067329 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-1752687161199 : Dyadic) * half ^ 42),
        ((-741737450155 : Dyadic) * half ^ 42)⟩,
       ⟨((1241399199397 : Dyadic) * half ^ 42),
        ((147972813753 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((442045059869 : Dyadic) * half ^ 42),
        ((-255643980901 : Dyadic) * half ^ 42)⟩,
       ⟨((-1925519960179 : Dyadic) * half ^ 42),
        ((-748521590149 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((1115600569393 : Dyadic) * half ^ 42),
        ((-134186765043 : Dyadic) * half ^ 39)⟩,
       ⟨((870687492129 : Dyadic) * half ^ 42),
        ((-1805458018389 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word41Step55 :
    word41Chunk55.foldl (fun acc a => a.applyPacked acc)
      word41State55 = word41State56 := by decide +kernel

private def word41Chunk56 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word41State57 : PackedMat2 :=
    ⟨⟨⟨((-74536920219 : Dyadic) * half ^ 37),
        ((2179321137627 : Dyadic) * half ^ 43)⟩,
       ⟨((313479066997 : Dyadic) * half ^ 41),
        ((-980975881809 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((-2146592068555 : Dyadic) * half ^ 42),
        ((-472972104703 : Dyadic) * half ^ 42)⟩,
       ⟨((-821001299693 : Dyadic) * half ^ 41),
        ((-71988139991 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((1624782344559 : Dyadic) * half ^ 42),
        ((3788594667941 : Dyadic) * half ^ 43)⟩,
       ⟨((-678838135153 : Dyadic) * half ^ 42),
        ((504589469169 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((599172627909 : Dyadic) * half ^ 42),
        ((-879111656507 : Dyadic) * half ^ 42)⟩,
       ⟨((790074254859 : Dyadic) * half ^ 41),
        ((-1506069790501 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word41Step56 :
    word41Chunk56.foldl (fun acc a => a.applyPacked acc)
      word41State56 = word41State57 := by decide +kernel

private def word41Chunk57 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word41State58 : PackedMat2 :=
    ⟨⟨⟨((2118816183971 : Dyadic) * half ^ 42),
        ((113429928429 : Dyadic) * half ^ 43)⟩,
       ⟨((3920169826511 : Dyadic) * half ^ 43),
        ((-2127899668169 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((-1433248556373 : Dyadic) * half ^ 43),
        ((738761547561 : Dyadic) * half ^ 44)⟩,
       ⟨((-2261868936365 : Dyadic) * half ^ 43),
        ((-7419057808939 : Dyadic) * half ^ 44)⟩⟩,
     ⟨⟨((-3340148130689 : Dyadic) * half ^ 43),
        ((-1847558746369 : Dyadic) * half ^ 43)⟩,
       ⟨((2039454839125 : Dyadic) * half ^ 42),
        ((103577547499 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((503617434935 : Dyadic) * half ^ 41),
        ((-8157802194453 : Dyadic) * half ^ 44)⟩,
       ⟨((-1120664798299 : Dyadic) * half ^ 42),
        ((-317462541431 : Dyadic) * half ^ 44)⟩⟩⟩
private lemma word41Step57 :
    word41Chunk57.foldl (fun acc a => a.applyPacked acc)
      word41State57 = word41State58 := by decide +kernel

private def word41Chunk58 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word41State59 : PackedMat2 :=
    ⟨⟨⟨((410785233095 : Dyadic) * half ^ 42),
        ((16335578880387 : Dyadic) * half ^ 45)⟩,
       ⟨((1837562919605 : Dyadic) * half ^ 44),
        ((-5175022400903 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((-4525997490437 : Dyadic) * half ^ 44),
        ((12620504058215 : Dyadic) * half ^ 45)⟩,
       ⟨((-2766348787195 : Dyadic) * half ^ 43),
        ((-7191454099939 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((4525997490437 : Dyadic) * half ^ 44),
        ((-12620504058215 : Dyadic) * half ^ 45)⟩,
       ⟨((-2766348787195 : Dyadic) * half ^ 43),
        ((-7191454099939 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((410785233095 : Dyadic) * half ^ 42),
        ((16335578880387 : Dyadic) * half ^ 45)⟩,
       ⟨((-1837562919605 : Dyadic) * half ^ 44),
        ((5175022400903 : Dyadic) * half ^ 45)⟩⟩⟩
private lemma word41Step58 :
    word41Chunk58.foldl (fun acc a => a.applyPacked acc)
      word41State58 = word41State59 := by decide +kernel

private def word41Chunk59 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word41State60 : PackedMat2 :=
    ⟨⟨⟨((2945872745411 : Dyadic) * half ^ 43),
        ((9259999665245 : Dyadic) * half ^ 45)⟩,
       ⟨((-839866284225 : Dyadic) * half ^ 41),
        ((4751001158911 : Dyadic) * half ^ 44)⟩⟩,
     ⟨⟨((23733479872347 : Dyadic) * half ^ 45),
        ((810081485525 : Dyadic) * half ^ 45)⟩,
       ⟨((-962150949731 : Dyadic) * half ^ 45),
        ((680343461105 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((32434506105 : Dyadic) * half ^ 43),
        ((12347815411039 : Dyadic) * half ^ 45)⟩,
       ⟨((-745212473315 : Dyadic) * half ^ 44),
        ((-2846416115327 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((242002652577 : Dyadic) * half ^ 45),
        ((-6305337882311 : Dyadic) * half ^ 44)⟩,
       ⟨((18762001983067 : Dyadic) * half ^ 45),
        ((-413592391489 : Dyadic) * half ^ 44)⟩⟩⟩
private lemma word41Step59 :
    word41Chunk59.foldl (fun acc a => a.applyPacked acc)
      word41State59 = word41State60 := by decide +kernel

private def word41Chunk60 : List Letter := [.t, .h]
private def word41State61 : PackedMat2 :=
    ⟨⟨⟨((5035040575385 : Dyadic) * half ^ 44),
        ((35516970853991 : Dyadic) * half ^ 46)⟩,
       ⟨((8821658856717 : Dyadic) * half ^ 45),
        ((-12475709597869 : Dyadic) * half ^ 46)⟩⟩,
     ⟨⟨((-1056239772465 : Dyadic) * half ^ 42),
        ((11949988890703 : Dyadic) * half ^ 46)⟩,
       ⟨((10182345778927 : Dyadic) * half ^ 45),
        ((-14400011497331 : Dyadic) * half ^ 46)⟩⟩,
     ⟨⟨((1056239772465 : Dyadic) * half ^ 42),
        ((-11949988890703 : Dyadic) * half ^ 46)⟩,
       ⟨((10182345778927 : Dyadic) * half ^ 45),
        ((-14400011497331 : Dyadic) * half ^ 46)⟩⟩,
     ⟨⟨((5035040575385 : Dyadic) * half ^ 44),
        ((35516970853991 : Dyadic) * half ^ 46)⟩,
       ⟨((-8821658856717 : Dyadic) * half ^ 45),
        ((12475709597869 : Dyadic) * half ^ 46)⟩⟩⟩
private lemma word41Step60 :
    word41Chunk60.foldl (fun acc a => a.applyPacked acc)
      word41State60 = word41State61 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word41_check : check word41 41 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word41 = word41State61.toMatrix := by
    unfold evalRingPacked
    change ((
      word41Chunk0 ++ word41Chunk1 ++ word41Chunk2 ++ word41Chunk3 ++
      word41Chunk4 ++ word41Chunk5 ++ word41Chunk6 ++ word41Chunk7 ++
      word41Chunk8 ++ word41Chunk9 ++ word41Chunk10 ++ word41Chunk11 ++
      word41Chunk12 ++ word41Chunk13 ++ word41Chunk14 ++ word41Chunk15 ++
      word41Chunk16 ++ word41Chunk17 ++ word41Chunk18 ++ word41Chunk19 ++
      word41Chunk20 ++ word41Chunk21 ++ word41Chunk22 ++ word41Chunk23 ++
      word41Chunk24 ++ word41Chunk25 ++ word41Chunk26 ++ word41Chunk27 ++
      word41Chunk28 ++ word41Chunk29 ++ word41Chunk30 ++ word41Chunk31 ++
      word41Chunk32 ++ word41Chunk33 ++ word41Chunk34 ++ word41Chunk35 ++
      word41Chunk36 ++ word41Chunk37 ++ word41Chunk38 ++ word41Chunk39 ++
      word41Chunk40 ++ word41Chunk41 ++ word41Chunk42 ++ word41Chunk43 ++
      word41Chunk44 ++ word41Chunk45 ++ word41Chunk46 ++ word41Chunk47 ++
      word41Chunk48 ++ word41Chunk49 ++ word41Chunk50 ++ word41Chunk51 ++
      word41Chunk52 ++ word41Chunk53 ++ word41Chunk54 ++ word41Chunk55 ++
      word41Chunk56 ++ word41Chunk57 ++ word41Chunk58 ++ word41Chunk59 ++
      word41Chunk60
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word41Step0, word41Step1, word41Step2, word41Step3, word41Step4,
      word41Step5, word41Step6, word41Step7, word41Step8, word41Step9,
      word41Step10, word41Step11, word41Step12, word41Step13, word41Step14,
      word41Step15, word41Step16, word41Step17, word41Step18, word41Step19,
      word41Step20, word41Step21, word41Step22, word41Step23, word41Step24,
      word41Step25, word41Step26, word41Step27, word41Step28, word41Step29,
      word41Step30, word41Step31, word41Step32, word41Step33, word41Step34,
      word41Step35, word41Step36, word41Step37, word41Step38, word41Step39,
      word41Step40, word41Step41, word41Step42, word41Step43, word41Step44,
      word41Step45, word41Step46, word41Step47, word41Step48, word41Step49,
      word41Step50, word41Step51, word41Step52, word41Step53, word41Step54,
      word41Step55, word41Step56, word41Step57, word41Step58, word41Step59,
      word41Step60]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
