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
private def word10Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word10State1 : PackedMat2 :=
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
private lemma word10Step0 :
    word10Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word10State1 := by decide +kernel

private def word10Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word10State2 : PackedMat2 :=
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
private lemma word10Step1 :
    word10Chunk1.foldl (fun acc a => a.applyPacked acc)
      word10State1 = word10State2 := by decide +kernel

private def word10Chunk2 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word10State3 : PackedMat2 :=
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
private lemma word10Step2 :
    word10Chunk2.foldl (fun acc a => a.applyPacked acc)
      word10State2 = word10State3 := by decide +kernel

private def word10Chunk3 : List Letter := [.s, .s, .t, .h, .t, .h, .s, .t]
private def word10State4 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word10Step3 :
    word10Chunk3.foldl (fun acc a => a.applyPacked acc)
      word10State3 = word10State4 := by decide +kernel

private def word10Chunk4 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word10State5 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((-3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((3 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word10Step4 :
    word10Chunk4.foldl (fun acc a => a.applyPacked acc)
      word10State4 = word10State5 := by decide +kernel

private def word10Chunk5 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word10State6 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-3 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 1)⟩⟩⟩
private lemma word10Step5 :
    word10Chunk5.foldl (fun acc a => a.applyPacked acc)
      word10State5 = word10State6 := by decide +kernel

private def word10Chunk6 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word10State7 : PackedMat2 :=
    ⟨⟨⟨((7 : Dyadic) * half ^ 4),
        (0 : Dyadic)⟩,
       ⟨((5 : Dyadic) * half ^ 4),
        ((-5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((-3 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 4),
        (0 : Dyadic)⟩,
       ⟨((5 : Dyadic) * half ^ 4),
        ((-5 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word10Step6 :
    word10Chunk6.foldl (fun acc a => a.applyPacked acc)
      word10State6 = word10State7 := by decide +kernel

private def word10Chunk7 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word10State8 : PackedMat2 :=
    ⟨⟨⟨((-3 : Dyadic) * half ^ 4),
        ((5 : Dyadic) * half ^ 5)⟩,
       ⟨((7 : Dyadic) * half ^ 4),
        ((-5 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((7 : Dyadic) * half ^ 4)⟩,
       ⟨((-5 : Dyadic) * half ^ 4),
        ((-5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 4),
        ((-5 : Dyadic) * half ^ 4)⟩,
       ⟨(0 : Dyadic),
        ((7 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 4),
        ((5 : Dyadic) * half ^ 5)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        ((-5 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word10Step7 :
    word10Chunk7.foldl (fun acc a => a.applyPacked acc)
      word10State7 = word10State8 := by decide +kernel

private def word10Chunk8 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word10State9 : PackedMat2 :=
    ⟨⟨⟨((-15 : Dyadic) * half ^ 5),
        ((-15 : Dyadic) * half ^ 6)⟩,
       ⟨((19 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((-5 : Dyadic) * half ^ 5)⟩,
       ⟨((7 : Dyadic) * half ^ 5),
        ((-9 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 6)⟩,
       ⟨((7 : Dyadic) * half ^ 4),
        ((-15 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 5),
        ((17 : Dyadic) * half ^ 5)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word10Step8 :
    word10Chunk8.foldl (fun acc a => a.applyPacked acc)
      word10State8 = word10State9 := by decide +kernel

private def word10Chunk9 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word10State10 : PackedMat2 :=
    ⟨⟨⟨((-7 : Dyadic) * half ^ 5),
        ((-11 : Dyadic) * half ^ 6)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((-11 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((11 : Dyadic) * half ^ 6),
        ((-7 : Dyadic) * half ^ 5)⟩,
       ⟨((33 : Dyadic) * half ^ 6),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((11 : Dyadic) * half ^ 6),
        ((-7 : Dyadic) * half ^ 5)⟩,
       ⟨((-33 : Dyadic) * half ^ 6),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 5),
        ((11 : Dyadic) * half ^ 6)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((-11 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word10Step9 :
    word10Chunk9.foldl (fun acc a => a.applyPacked acc)
      word10State9 = word10State10 := by decide +kernel

private def word10Chunk10 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word10State11 : PackedMat2 :=
    ⟨⟨⟨((-29 : Dyadic) * half ^ 7),
        ((3 : Dyadic) * half ^ 7)⟩,
       ⟨((-73 : Dyadic) * half ^ 7),
        ((-3 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-85 : Dyadic) * half ^ 7),
        ((3 : Dyadic) * half ^ 6)⟩,
       ⟨((-53 : Dyadic) * half ^ 7),
        ((-3 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-9 : Dyadic) * half ^ 7),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((3 : Dyadic) * half ^ 7),
        ((-69 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 7),
        ((11 : Dyadic) * half ^ 6)⟩,
       ⟨((3 : Dyadic) * half ^ 7),
        ((51 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word10Step10 :
    word10Chunk10.foldl (fun acc a => a.applyPacked acc)
      word10State10 = word10State11 := by decide +kernel

private def word10Chunk11 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word10State12 : PackedMat2 :=
    ⟨⟨⟨((11 : Dyadic) * half ^ 5),
        ((-39 : Dyadic) * half ^ 8)⟩,
       ⟨((-11 : Dyadic) * half ^ 6),
        ((-1 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 5),
        ((-13 : Dyadic) * half ^ 5)⟩,
       ⟨((-47 : Dyadic) * half ^ 7),
        ((-49 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((47 : Dyadic) * half ^ 7),
        ((49 : Dyadic) * half ^ 7)⟩,
       ⟨((-7 : Dyadic) * half ^ 5),
        ((13 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-11 : Dyadic) * half ^ 6),
        ((-1 : Dyadic) * half ^ 8)⟩,
       ⟨((11 : Dyadic) * half ^ 5),
        ((-39 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word10Step11 :
    word10Chunk11.foldl (fun acc a => a.applyPacked acc)
      word10State11 = word10State12 := by decide +kernel

private def word10Chunk12 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word10State13 : PackedMat2 :=
    ⟨⟨⟨((67 : Dyadic) * half ^ 8),
        ((225 : Dyadic) * half ^ 9)⟩,
       ⟨((63 : Dyadic) * half ^ 8),
        ((57 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((69 : Dyadic) * half ^ 8),
        ((-81 : Dyadic) * half ^ 8)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((39 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((15 : Dyadic) * half ^ 5),
        ((-165 : Dyadic) * half ^ 9)⟩,
       ⟨((-21 : Dyadic) * half ^ 7),
        ((-27 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((21 : Dyadic) * half ^ 6),
        ((1 : Dyadic) * half ^ 7)⟩,
       ⟨((-141 : Dyadic) * half ^ 8),
        ((-65 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word10Step12 :
    word10Chunk12.foldl (fun acc a => a.applyPacked acc)
      word10State12 = word10State13 := by decide +kernel

private def word10Chunk13 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word10State14 : PackedMat2 :=
    ⟨⟨⟨((93 : Dyadic) * half ^ 9),
        ((239 : Dyadic) * half ^ 10)⟩,
       ⟨((7 : Dyadic) * half ^ 7),
        ((429 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 9),
        ((285 : Dyadic) * half ^ 10)⟩,
       ⟨((21 : Dyadic) * half ^ 7),
        ((-411 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-21 : Dyadic) * half ^ 7),
        ((411 : Dyadic) * half ^ 10)⟩,
       ⟨((-1 : Dyadic) * half ^ 9),
        ((-285 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 7),
        ((429 : Dyadic) * half ^ 10)⟩,
       ⟨((93 : Dyadic) * half ^ 9),
        ((239 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word10Step13 :
    word10Chunk13.foldl (fun acc a => a.applyPacked acc)
      word10State13 = word10State14 := by decide +kernel

private def word10Chunk14 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word10State15 : PackedMat2 :=
    ⟨⟨⟨((-137 : Dyadic) * half ^ 10),
        ((-5 : Dyadic) * half ^ 6)⟩,
       ⟨((459 : Dyadic) * half ^ 10),
        ((95 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((53 : Dyadic) * half ^ 9),
        ((239 : Dyadic) * half ^ 10)⟩,
       ⟨((-93 : Dyadic) * half ^ 7),
        ((83 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((405 : Dyadic) * half ^ 10),
        ((-319 : Dyadic) * half ^ 10)⟩,
       ⟨((73 : Dyadic) * half ^ 10),
        ((425 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-55 : Dyadic) * half ^ 9),
        ((-161 : Dyadic) * half ^ 10)⟩,
       ⟨((135 : Dyadic) * half ^ 9),
        ((149 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word10Step14 :
    word10Chunk14.foldl (fun acc a => a.applyPacked acc)
      word10State14 = word10State15 := by decide +kernel

private def word10Chunk15 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word10State16 : PackedMat2 :=
    ⟨⟨⟨((125 : Dyadic) * half ^ 11),
        ((-493 : Dyadic) * half ^ 11)⟩,
       ⟨((137 : Dyadic) * half ^ 11),
        ((35 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((1681 : Dyadic) * half ^ 11),
        ((65 : Dyadic) * half ^ 10)⟩,
       ⟨((301 : Dyadic) * half ^ 11),
        ((-585 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-715 : Dyadic) * half ^ 11),
        ((-345 : Dyadic) * half ^ 10)⟩,
       ⟨((-455 : Dyadic) * half ^ 11),
        ((991 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-633 : Dyadic) * half ^ 11),
        ((-3 : Dyadic) * half ^ 10)⟩,
       ⟨((353 : Dyadic) * half ^ 11),
        ((-131 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word10Step15 :
    word10Chunk15.foldl (fun acc a => a.applyPacked acc)
      word10State15 = word10State16 := by decide +kernel

private def word10Chunk16 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word10State17 : PackedMat2 :=
    ⟨⟨⟨((-297 : Dyadic) * half ^ 11),
        ((-119 : Dyadic) * half ^ 11)⟩,
       ⟨((329 : Dyadic) * half ^ 10),
        ((-93 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-351 : Dyadic) * half ^ 10),
        ((1005 : Dyadic) * half ^ 12)⟩,
       ⟨((25 : Dyadic) * half ^ 7),
        ((2199 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-597 : Dyadic) * half ^ 11),
        ((-551 : Dyadic) * half ^ 11)⟩,
       ⟨((-801 : Dyadic) * half ^ 10),
        ((151 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-67 : Dyadic) * half ^ 11),
        ((955 : Dyadic) * half ^ 12)⟩,
       ⟨((-305 : Dyadic) * half ^ 11),
        ((361 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word10Step16 :
    word10Chunk16.foldl (fun acc a => a.applyPacked acc)
      word10State16 = word10State17 := by decide +kernel

private def word10Chunk17 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word10State18 : PackedMat2 :=
    ⟨⟨⟨((-799 : Dyadic) * half ^ 11),
        ((783 : Dyadic) * half ^ 13)⟩,
       ⟨((-1069 : Dyadic) * half ^ 12),
        ((-1121 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((451 : Dyadic) * half ^ 11),
        ((-3365 : Dyadic) * half ^ 13)⟩,
       ⟨((2155 : Dyadic) * half ^ 12),
        ((1433 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-483 : Dyadic) * half ^ 11),
        ((3057 : Dyadic) * half ^ 13)⟩,
       ⟨((-2399 : Dyadic) * half ^ 12),
        ((-1253 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((169 : Dyadic) * half ^ 12),
        ((2667 : Dyadic) * half ^ 13)⟩,
       ⟨((-119 : Dyadic) * half ^ 9),
        ((529 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word10Step17 :
    word10Chunk17.foldl (fun acc a => a.applyPacked acc)
      word10State17 = word10State18 := by decide +kernel

private def word10Chunk18 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word10State19 : PackedMat2 :=
    ⟨⟨⟨((25 : Dyadic) * half ^ 13),
        ((307 : Dyadic) * half ^ 14)⟩,
       ⟨((-107 : Dyadic) * half ^ 10),
        ((-9771 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-645 : Dyadic) * half ^ 13),
        ((-2607 : Dyadic) * half ^ 14)⟩,
       ⟨((-1159 : Dyadic) * half ^ 12),
        ((4337 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((1159 : Dyadic) * half ^ 12),
        ((-4337 : Dyadic) * half ^ 14)⟩,
       ⟨((645 : Dyadic) * half ^ 13),
        ((2607 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-107 : Dyadic) * half ^ 10),
        ((-9771 : Dyadic) * half ^ 14)⟩,
       ⟨((25 : Dyadic) * half ^ 13),
        ((307 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word10Step18 :
    word10Chunk18.foldl (fun acc a => a.applyPacked acc)
      word10State18 = word10State19 := by decide +kernel

private def word10Chunk19 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word10State20 : PackedMat2 :=
    ⟨⟨⟨((4635 : Dyadic) * half ^ 14),
        ((2037 : Dyadic) * half ^ 13)⟩,
       ⟨((-8881 : Dyadic) * half ^ 14),
        ((-273 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((2375 : Dyadic) * half ^ 13),
        ((-2373 : Dyadic) * half ^ 14)⟩,
       ⟨((1053 : Dyadic) * half ^ 11),
        ((-1603 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((2375 : Dyadic) * half ^ 13),
        ((-2373 : Dyadic) * half ^ 14)⟩,
       ⟨((-1053 : Dyadic) * half ^ 11),
        ((1603 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-4635 : Dyadic) * half ^ 14),
        ((-2037 : Dyadic) * half ^ 13)⟩,
       ⟨((-8881 : Dyadic) * half ^ 14),
        ((-273 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word10Step19 :
    word10Chunk19.foldl (fun acc a => a.applyPacked acc)
      word10State19 = word10State20 := by decide +kernel

private def word10Chunk20 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word10State21 : PackedMat2 :=
    ⟨⟨⟨((2109 : Dyadic) * half ^ 15),
        ((14935 : Dyadic) * half ^ 15)⟩,
       ⟨((-4175 : Dyadic) * half ^ 15),
        ((-4357 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-103 : Dyadic) * half ^ 14),
        ((-14285 : Dyadic) * half ^ 15)⟩,
       ⟨((-5211 : Dyadic) * half ^ 14),
        ((2525 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((103 : Dyadic) * half ^ 14),
        ((14285 : Dyadic) * half ^ 15)⟩,
       ⟨((-5211 : Dyadic) * half ^ 14),
        ((2525 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((2109 : Dyadic) * half ^ 15),
        ((14935 : Dyadic) * half ^ 15)⟩,
       ⟨((4175 : Dyadic) * half ^ 15),
        ((4357 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word10Step20 :
    word10Chunk20.foldl (fun acc a => a.applyPacked acc)
      word10State20 = word10State21 := by decide +kernel

private def word10Chunk21 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word10State22 : PackedMat2 :=
    ⟨⟨⟨((40693 : Dyadic) * half ^ 16),
        ((-49 : Dyadic) * half ^ 8)⟩,
       ⟨((7627 : Dyadic) * half ^ 16),
        ((12945 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((10585 : Dyadic) * half ^ 16),
        ((17485 : Dyadic) * half ^ 16)⟩,
       ⟨((-9597 : Dyadic) * half ^ 16),
        ((-369 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((10585 : Dyadic) * half ^ 16),
        ((17485 : Dyadic) * half ^ 16)⟩,
       ⟨((9597 : Dyadic) * half ^ 16),
        ((369 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-40693 : Dyadic) * half ^ 16),
        ((49 : Dyadic) * half ^ 8)⟩,
       ⟨((7627 : Dyadic) * half ^ 16),
        ((12945 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word10Step21 :
    word10Chunk21.foldl (fun acc a => a.applyPacked acc)
      word10State21 = word10State22 := by decide +kernel

private def word10Chunk22 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word10State23 : PackedMat2 :=
    ⟨⟨⟨((-19423 : Dyadic) * half ^ 16),
        ((14121 : Dyadic) * half ^ 16)⟩,
       ⟨((26921 : Dyadic) * half ^ 15),
        ((2587 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((22083 : Dyadic) * half ^ 16),
        ((10041 : Dyadic) * half ^ 17)⟩,
       ⟨((-5579 : Dyadic) * half ^ 16),
        ((-8645 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-5579 : Dyadic) * half ^ 16),
        ((-8645 : Dyadic) * half ^ 17)⟩,
       ⟨((22083 : Dyadic) * half ^ 16),
        ((10041 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-26921 : Dyadic) * half ^ 15),
        ((-2587 : Dyadic) * half ^ 16)⟩,
       ⟨((19423 : Dyadic) * half ^ 16),
        ((-14121 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word10Step22 :
    word10Chunk22.foldl (fun acc a => a.applyPacked acc)
      word10State22 = word10State23 := by decide +kernel

private def word10Chunk23 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word10State24 : PackedMat2 :=
    ⟨⟨⟨((-22187 : Dyadic) * half ^ 17),
        ((-90177 : Dyadic) * half ^ 18)⟩,
       ⟨((-23607 : Dyadic) * half ^ 16),
        ((85149 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-23869 : Dyadic) * half ^ 17),
        ((-8153 : Dyadic) * half ^ 18)⟩,
       ⟨((8413 : Dyadic) * half ^ 16),
        ((108455 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-50151 : Dyadic) * half ^ 17),
        ((7043 : Dyadic) * half ^ 18)⟩,
       ⟨((911 : Dyadic) * half ^ 11),
        ((40695 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-1257 : Dyadic) * half ^ 16),
        ((-69401 : Dyadic) * half ^ 18)⟩,
       ⟨((-87663 : Dyadic) * half ^ 17),
        ((25027 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word10Step23 :
    word10Chunk23.foldl (fun acc a => a.applyPacked acc)
      word10State23 = word10State24 := by decide +kernel

private def word10Chunk24 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word10State25 : PackedMat2 :=
    ⟨⟨⟨((-39335 : Dyadic) * half ^ 16),
        ((43445 : Dyadic) * half ^ 19)⟩,
       ⟨((14459 : Dyadic) * half ^ 18),
        ((71205 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-97921 : Dyadic) * half ^ 17),
        ((-32071 : Dyadic) * half ^ 19)⟩,
       ⟨((36361 : Dyadic) * half ^ 18),
        ((-13057 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((36361 : Dyadic) * half ^ 18),
        ((-13057 : Dyadic) * half ^ 19)⟩,
       ⟨((-97921 : Dyadic) * half ^ 17),
        ((-32071 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-14459 : Dyadic) * half ^ 18),
        ((-71205 : Dyadic) * half ^ 19)⟩,
       ⟨((39335 : Dyadic) * half ^ 16),
        ((-43445 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word10Step24 :
    word10Chunk24.foldl (fun acc a => a.applyPacked acc)
      word10State24 = word10State25 := by decide +kernel

private def word10Chunk25 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word10State26 : PackedMat2 :=
    ⟨⟨⟨((19479 : Dyadic) * half ^ 19),
        ((-77261 : Dyadic) * half ^ 17)⟩,
       ⟨((-63571 : Dyadic) * half ^ 19),
        ((57961 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-6819 : Dyadic) * half ^ 16),
        ((-51707 : Dyadic) * half ^ 18)⟩,
       ⟨((-75787 : Dyadic) * half ^ 18),
        ((-51115 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((6819 : Dyadic) * half ^ 16),
        ((51707 : Dyadic) * half ^ 18)⟩,
       ⟨((-75787 : Dyadic) * half ^ 18),
        ((-51115 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((19479 : Dyadic) * half ^ 19),
        ((-77261 : Dyadic) * half ^ 17)⟩,
       ⟨((63571 : Dyadic) * half ^ 19),
        ((-57961 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word10Step25 :
    word10Chunk25.foldl (fun acc a => a.applyPacked acc)
      word10State25 = word10State26 := by decide +kernel

private def word10Chunk26 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word10State27 : PackedMat2 :=
    ⟨⟨⟨((8933 : Dyadic) * half ^ 17),
        ((91713 : Dyadic) * half ^ 20)⟩,
       ⟨((-14139 : Dyadic) * half ^ 15),
        ((5165 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-512589 : Dyadic) * half ^ 20),
        ((-226267 : Dyadic) * half ^ 20)⟩,
       ⟨((-670767 : Dyadic) * half ^ 20),
        ((168745 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-28761 : Dyadic) * half ^ 19),
        ((-295839 : Dyadic) * half ^ 19)⟩,
       ⟨((-98753 : Dyadic) * half ^ 18),
        ((79089 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-112373 : Dyadic) * half ^ 20),
        ((47623 : Dyadic) * half ^ 18)⟩,
       ⟨((-71053 : Dyadic) * half ^ 20),
        ((-65489 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word10Step26 :
    word10Chunk26.foldl (fun acc a => a.applyPacked acc)
      word10State26 = word10State27 := by decide +kernel

private def word10Chunk27 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word10State28 : PackedMat2 :=
    ⟨⟨⟨((1031297 : Dyadic) * half ^ 21),
        ((-1551 : Dyadic) * half ^ 14)⟩,
       ⟨((-509559 : Dyadic) * half ^ 21),
        ((-741261 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((171709 : Dyadic) * half ^ 21),
        ((-362367 : Dyadic) * half ^ 20)⟩,
       ⟨((-900717 : Dyadic) * half ^ 21),
        ((53881 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((778615 : Dyadic) * half ^ 21),
        ((-536213 : Dyadic) * half ^ 21)⟩,
       ⟨((-670853 : Dyadic) * half ^ 21),
        ((-45563 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((542733 : Dyadic) * half ^ 21),
        ((192607 : Dyadic) * half ^ 19)⟩,
       ⟨((939789 : Dyadic) * half ^ 21),
        ((-260869 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word10Step27 :
    word10Chunk27.foldl (fun acc a => a.applyPacked acc)
      word10State27 = word10State28 := by decide +kernel

private def word10Chunk28 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word10State29 : PackedMat2 :=
    ⟨⟨⟨((2961371 : Dyadic) * half ^ 22),
        ((106343 : Dyadic) * half ^ 21)⟩,
       ⟨((-1708165 : Dyadic) * half ^ 22),
        ((-220345 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((1656171 : Dyadic) * half ^ 22),
        ((-439399 : Dyadic) * half ^ 21)⟩,
       ⟨((-1020999 : Dyadic) * half ^ 22),
        ((-439973 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((1656171 : Dyadic) * half ^ 22),
        ((-439399 : Dyadic) * half ^ 21)⟩,
       ⟨((1020999 : Dyadic) * half ^ 22),
        ((439973 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-2961371 : Dyadic) * half ^ 22),
        ((-106343 : Dyadic) * half ^ 21)⟩,
       ⟨((-1708165 : Dyadic) * half ^ 22),
        ((-220345 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word10Step28 :
    word10Chunk28.foldl (fun acc a => a.applyPacked acc)
      word10State28 = word10State29 := by decide +kernel

private def word10Chunk29 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word10State30 : PackedMat2 :=
    ⟨⟨⟨((298357 : Dyadic) * half ^ 20),
        ((-2192475 : Dyadic) * half ^ 23)⟩,
       ⟨((-468867 : Dyadic) * half ^ 22),
        ((1553211 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((2558069 : Dyadic) * half ^ 22),
        ((1358729 : Dyadic) * half ^ 23)⟩,
       ⟨((-137923 : Dyadic) * half ^ 18),
        ((59323 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((354513 : Dyadic) * half ^ 21),
        ((351301 : Dyadic) * half ^ 23)⟩,
       ⟨((649703 : Dyadic) * half ^ 22),
        ((4764837 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((19977 : Dyadic) * half ^ 18),
        ((-724561 : Dyadic) * half ^ 23)⟩,
       ⟨((1872843 : Dyadic) * half ^ 22),
        ((-1662295 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word10Step29 :
    word10Chunk29.foldl (fun acc a => a.applyPacked acc)
      word10State29 = word10State30 := by decide +kernel

private def word10Chunk30 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word10State31 : PackedMat2 :=
    ⟨⟨⟨((-39335 : Dyadic) * half ^ 23),
        ((7149 : Dyadic) * half ^ 15)⟩,
       ⟨((3549431 : Dyadic) * half ^ 23),
        ((-12033 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-447513 : Dyadic) * half ^ 22),
        ((1384815 : Dyadic) * half ^ 22)⟩,
       ⟨((1251249 : Dyadic) * half ^ 21),
        ((1601959 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((447513 : Dyadic) * half ^ 22),
        ((-1384815 : Dyadic) * half ^ 22)⟩,
       ⟨((1251249 : Dyadic) * half ^ 21),
        ((1601959 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-39335 : Dyadic) * half ^ 23),
        ((7149 : Dyadic) * half ^ 15)⟩,
       ⟨((-3549431 : Dyadic) * half ^ 23),
        ((12033 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word10Step30 :
    word10Chunk30.foldl (fun acc a => a.applyPacked acc)
      word10State30 = word10State31 := by decide +kernel

private def word10Chunk31 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word10State32 : PackedMat2 :=
    ⟨⟨⟨((-1307399 : Dyadic) * half ^ 24),
        ((216427 : Dyadic) * half ^ 22)⟩,
       ⟨((1072743 : Dyadic) * half ^ 24),
        ((7180401 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((428069 : Dyadic) * half ^ 24),
        ((-9115983 : Dyadic) * half ^ 24)⟩,
       ⟨((-1818353 : Dyadic) * half ^ 24),
        ((183451 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((428069 : Dyadic) * half ^ 24),
        ((-9115983 : Dyadic) * half ^ 24)⟩,
       ⟨((1818353 : Dyadic) * half ^ 24),
        ((-183451 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((1307399 : Dyadic) * half ^ 24),
        ((-216427 : Dyadic) * half ^ 22)⟩,
       ⟨((1072743 : Dyadic) * half ^ 24),
        ((7180401 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word10Step31 :
    word10Chunk31.foldl (fun acc a => a.applyPacked acc)
      word10State31 = word10State32 := by decide +kernel

private def word10Chunk32 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word10State33 : PackedMat2 :=
    ⟨⟨⟨((-11039 : Dyadic) * half ^ 16),
        ((-18352163 : Dyadic) * half ^ 25)⟩,
       ⟨((233885 : Dyadic) * half ^ 20),
        ((-7899629 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-1971477 : Dyadic) * half ^ 23),
        ((3952939 : Dyadic) * half ^ 24)⟩,
       ⟨((-2164605 : Dyadic) * half ^ 24),
        ((-1024583 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-6002105 : Dyadic) * half ^ 24),
        ((1778349 : Dyadic) * half ^ 25)⟩,
       ⟨((1903773 : Dyadic) * half ^ 24),
        ((-6107559 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-5226267 : Dyadic) * half ^ 24),
        ((-410509 : Dyadic) * half ^ 21)⟩,
       ⟨((1640737 : Dyadic) * half ^ 21),
        ((-57261 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word10Step32 :
    word10Chunk32.foldl (fun acc a => a.applyPacked acc)
      word10State32 = word10State33 := by decide +kernel

private def word10Chunk33 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word10State34 : PackedMat2 :=
    ⟨⟨⟨((-13691935 : Dyadic) * half ^ 25),
        ((-11314707 : Dyadic) * half ^ 26)⟩,
       ⟨((2119335 : Dyadic) * half ^ 24),
        ((-13576089 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((5351691 : Dyadic) * half ^ 25),
        ((12464795 : Dyadic) * half ^ 26)⟩,
       ⟨((-3154445 : Dyadic) * half ^ 22),
        ((6502071 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-9483433 : Dyadic) * half ^ 25),
        ((19883869 : Dyadic) * half ^ 26)⟩,
       ⟨((-1490681 : Dyadic) * half ^ 24),
        ((-30587251 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-6222699 : Dyadic) * half ^ 24),
        ((-9453265 : Dyadic) * half ^ 26)⟩,
       ⟨((1130691 : Dyadic) * half ^ 25),
        ((-17930605 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word10Step33 :
    word10Chunk33.foldl (fun acc a => a.applyPacked acc)
      word10State33 = word10State34 := by decide +kernel

private def word10Chunk34 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word10State35 : PackedMat2 :=
    ⟨⟨⟨((-6807965 : Dyadic) * half ^ 26),
        ((-16793015 : Dyadic) * half ^ 27)⟩,
       ⟨((3523827 : Dyadic) * half ^ 25),
        ((-74432415 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((10351115 : Dyadic) * half ^ 25),
        ((25859091 : Dyadic) * half ^ 27)⟩,
       ⟨((-26883685 : Dyadic) * half ^ 26),
        ((4653127 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-26883685 : Dyadic) * half ^ 26),
        ((4653127 : Dyadic) * half ^ 27)⟩,
       ⟨((10351115 : Dyadic) * half ^ 25),
        ((25859091 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-3523827 : Dyadic) * half ^ 25),
        ((74432415 : Dyadic) * half ^ 27)⟩,
       ⟨((6807965 : Dyadic) * half ^ 26),
        ((16793015 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word10Step34 :
    word10Chunk34.foldl (fun acc a => a.applyPacked acc)
      word10State34 = word10State35 := by decide +kernel

private def word10Chunk35 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word10State36 : PackedMat2 :=
    ⟨⟨⟨((848163 : Dyadic) * half ^ 26),
        ((41011469 : Dyadic) * half ^ 27)⟩,
       ⟨((-4845763 : Dyadic) * half ^ 24),
        ((20934545 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((9736783 : Dyadic) * half ^ 27),
        ((1429783 : Dyadic) * half ^ 22)⟩,
       ⟨((69649989 : Dyadic) * half ^ 27),
        ((7954381 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-30830909 : Dyadic) * half ^ 26),
        ((-19846693 : Dyadic) * half ^ 26)⟩,
       ⟨((-14922147 : Dyadic) * half ^ 26),
        ((29956603 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((82880559 : Dyadic) * half ^ 27),
        ((-18534889 : Dyadic) * half ^ 27)⟩,
       ⟨((-857621 : Dyadic) * half ^ 27),
        ((20231215 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word10Step35 :
    word10Chunk35.foldl (fun acc a => a.applyPacked acc)
      word10State35 = word10State36 := by decide +kernel

private def word10Chunk36 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word10State37 : PackedMat2 :=
    ⟨⟨⟨((-25449661 : Dyadic) * half ^ 28),
        ((-51171365 : Dyadic) * half ^ 27)⟩,
       ⟨((93498695 : Dyadic) * half ^ 28),
        ((10564093 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((33338081 : Dyadic) * half ^ 28),
        ((-55076655 : Dyadic) * half ^ 27)⟩,
       ⟨((890991 : Dyadic) * half ^ 28),
        ((89768895 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((33338081 : Dyadic) * half ^ 28),
        ((-55076655 : Dyadic) * half ^ 27)⟩,
       ⟨((-890991 : Dyadic) * half ^ 28),
        ((-89768895 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((25449661 : Dyadic) * half ^ 28),
        ((51171365 : Dyadic) * half ^ 27)⟩,
       ⟨((93498695 : Dyadic) * half ^ 28),
        ((10564093 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word10Step36 :
    word10Chunk36.foldl (fun acc a => a.applyPacked acc)
      word10State36 = word10State37 := by decide +kernel

private def word10Chunk37 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word10State38 : PackedMat2 :=
    ⟨⟨⟨((-69449935 : Dyadic) * half ^ 27),
        ((-26564145 : Dyadic) * half ^ 28)⟩,
       ⟨((97800365 : Dyadic) * half ^ 28),
        ((-6266895 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-39122031 : Dyadic) * half ^ 26),
        ((-22406297 : Dyadic) * half ^ 29)⟩,
       ⟨((12496131 : Dyadic) * half ^ 26),
        ((-168736497 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((12496131 : Dyadic) * half ^ 26),
        ((-168736497 : Dyadic) * half ^ 29)⟩,
       ⟨((-39122031 : Dyadic) * half ^ 26),
        ((-22406297 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-97800365 : Dyadic) * half ^ 28),
        ((6266895 : Dyadic) * half ^ 27)⟩,
       ⟨((69449935 : Dyadic) * half ^ 27),
        ((26564145 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word10Step37 :
    word10Chunk37.foldl (fun acc a => a.applyPacked acc)
      word10State37 = word10State38 := by decide +kernel

private def word10Chunk38 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word10State39 : PackedMat2 :=
    ⟨⟨⟨((-68502247 : Dyadic) * half ^ 29),
        ((-265007965 : Dyadic) * half ^ 30)⟩,
       ⟨((-101316535 : Dyadic) * half ^ 28),
        ((-275632863 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((218766635 : Dyadic) * half ^ 29),
        ((25769651 : Dyadic) * half ^ 30)⟩,
       ⟨((-144006845 : Dyadic) * half ^ 28),
        ((276526835 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-151148243 : Dyadic) * half ^ 29),
        ((69247055 : Dyadic) * half ^ 30)⟩,
       ⟨((3918081 : Dyadic) * half ^ 24),
        ((-506780325 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-135160207 : Dyadic) * half ^ 28),
        ((-271135317 : Dyadic) * half ^ 30)⟩,
       ⟨((5312449 : Dyadic) * half ^ 29),
        ((134130823 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word10Step38 :
    word10Chunk38.foldl (fun acc a => a.applyPacked acc)
      word10State38 = word10State39 := by decide +kernel

private def word10Chunk39 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word10State40 : PackedMat2 :=
    ⟨⟨⟨((376884933 : Dyadic) * half ^ 30),
        ((-401207673 : Dyadic) * half ^ 31)⟩,
       ⟨((-148908883 : Dyadic) * half ^ 29),
        ((-1053617457 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((67161993 : Dyadic) * half ^ 29),
        ((114590053 : Dyadic) * half ^ 31)⟩,
       ⟨((-307503619 : Dyadic) * half ^ 30),
        ((578754369 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-307503619 : Dyadic) * half ^ 30),
        ((578754369 : Dyadic) * half ^ 31)⟩,
       ⟨((67161993 : Dyadic) * half ^ 29),
        ((114590053 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((148908883 : Dyadic) * half ^ 29),
        ((1053617457 : Dyadic) * half ^ 31)⟩,
       ⟨((-376884933 : Dyadic) * half ^ 30),
        ((401207673 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word10Step39 :
    word10Chunk39.foldl (fun acc a => a.applyPacked acc)
      word10State39 = word10State40 := by decide +kernel

private def word10Chunk40 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word10State41 : PackedMat2 :=
    ⟨⟨⟨((254793753 : Dyadic) * half ^ 31),
        ((76361291 : Dyadic) * half ^ 31)⟩,
       ⟨((-381461711 : Dyadic) * half ^ 31),
        ((-1122058941 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((245341025 : Dyadic) * half ^ 30),
        ((-845480703 : Dyadic) * half ^ 31)⟩,
       ⟨((217893729 : Dyadic) * half ^ 30),
        ((-18711357 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-245341025 : Dyadic) * half ^ 30),
        ((845480703 : Dyadic) * half ^ 31)⟩,
       ⟨((217893729 : Dyadic) * half ^ 30),
        ((-18711357 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((254793753 : Dyadic) * half ^ 31),
        ((76361291 : Dyadic) * half ^ 31)⟩,
       ⟨((381461711 : Dyadic) * half ^ 31),
        ((1122058941 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word10Step40 :
    word10Chunk40.foldl (fun acc a => a.applyPacked acc)
      word10State40 = word10State41 := by decide +kernel

private def word10Chunk41 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word10State42 : PackedMat2 :=
    ⟨⟨⟨((1024866343 : Dyadic) * half ^ 32),
        ((531371991 : Dyadic) * half ^ 32)⟩,
       ⟨((-2425111587 : Dyadic) * half ^ 32),
        ((-14390937 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-2381542617 : Dyadic) * half ^ 32),
        ((489166187 : Dyadic) * half ^ 32)⟩,
       ⟨((-40470517 : Dyadic) * half ^ 32),
        ((-765876093 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((2020918373 : Dyadic) * half ^ 32),
        ((-585268025 : Dyadic) * half ^ 31)⟩,
       ⟨((1042585999 : Dyadic) * half ^ 32),
        ((1211006567 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-761626983 : Dyadic) * half ^ 32),
        ((-1724988965 : Dyadic) * half ^ 32)⟩,
       ⟨((301116999 : Dyadic) * half ^ 32),
        ((-350061311 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word10Step41 :
    word10Chunk41.foldl (fun acc a => a.applyPacked acc)
      word10State41 = word10State42 := by decide +kernel

private def word10Chunk42 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word10State43 : PackedMat2 :=
    ⟨⟨⟨((829210363 : Dyadic) * half ^ 33),
        ((-1519486065 : Dyadic) * half ^ 33)⟩,
       ⟨((210185161 : Dyadic) * half ^ 33),
        ((593330173 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-272130733 : Dyadic) * half ^ 33),
        ((-2889038377 : Dyadic) * half ^ 33)⟩,
       ⟨((5575279 : Dyadic) * half ^ 33),
        ((-2247361201 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((272130733 : Dyadic) * half ^ 33),
        ((2889038377 : Dyadic) * half ^ 33)⟩,
       ⟨((5575279 : Dyadic) * half ^ 33),
        ((-2247361201 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((829210363 : Dyadic) * half ^ 33),
        ((-1519486065 : Dyadic) * half ^ 33)⟩,
       ⟨((-210185161 : Dyadic) * half ^ 33),
        ((-593330173 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word10Step42 :
    word10Chunk42.foldl (fun acc a => a.applyPacked acc)
      word10State42 = word10State43 := by decide +kernel

private def word10Chunk43 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word10State44 : PackedMat2 :=
    ⟨⟨⟨((-821736633 : Dyadic) * half ^ 33),
        ((-1682963335 : Dyadic) * half ^ 34)⟩,
       ⟨((6479806263 : Dyadic) * half ^ 33),
        ((-1176023177 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-472711319 : Dyadic) * half ^ 32),
        ((978269767 : Dyadic) * half ^ 32)⟩,
       ⟨((-4203870455 : Dyadic) * half ^ 33),
        ((-295470667 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((1569211101 : Dyadic) * half ^ 32),
        ((3258447817 : Dyadic) * half ^ 34)⟩,
       ⟨((-387328433 : Dyadic) * half ^ 32),
        ((5149293093 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((253470079 : Dyadic) * half ^ 33),
        ((456346431 : Dyadic) * half ^ 30)⟩,
       ⟨((-178686657 : Dyadic) * half ^ 30),
        ((2829034815 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word10Step43 :
    word10Chunk43.foldl (fun acc a => a.applyPacked acc)
      word10State43 = word10State44 := by decide +kernel

private def word10Chunk44 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word10State45 : PackedMat2 :=
    ⟨⟨⟨((-3958899143 : Dyadic) * half ^ 34),
        ((1896315247 : Dyadic) * half ^ 35)⟩,
       ⟨((-263084293 : Dyadic) * half ^ 32),
        ((7363570123 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((7298377893 : Dyadic) * half ^ 33),
        ((-703103117 : Dyadic) * half ^ 35)⟩,
       ⟨((-4130924607 : Dyadic) * half ^ 34),
        ((-6177625177 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-4130924607 : Dyadic) * half ^ 34),
        ((-6177625177 : Dyadic) * half ^ 35)⟩,
       ⟨((7298377893 : Dyadic) * half ^ 33),
        ((-703103117 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((263084293 : Dyadic) * half ^ 32),
        ((-7363570123 : Dyadic) * half ^ 35)⟩,
       ⟨((3958899143 : Dyadic) * half ^ 34),
        ((-1896315247 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word10Step44 :
    word10Chunk44.foldl (fun acc a => a.applyPacked acc)
      word10State44 = word10State45 := by decide +kernel

private def word10Chunk45 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word10State46 : PackedMat2 :=
    ⟨⟨⟨((5854305321 : Dyadic) * half ^ 35),
        ((-2150433007 : Dyadic) * half ^ 35)⟩,
       ⟨((-16874364663 : Dyadic) * half ^ 35),
        ((6434775229 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((7117489537 : Dyadic) * half ^ 34),
        ((11651961681 : Dyadic) * half ^ 35)⟩,
       ⟨((1884835503 : Dyadic) * half ^ 34),
        ((-92625365 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-7117489537 : Dyadic) * half ^ 34),
        ((-11651961681 : Dyadic) * half ^ 35)⟩,
       ⟨((1884835503 : Dyadic) * half ^ 34),
        ((-92625365 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((5854305321 : Dyadic) * half ^ 35),
        ((-2150433007 : Dyadic) * half ^ 35)⟩,
       ⟨((16874364663 : Dyadic) * half ^ 35),
        ((-6434775229 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word10Step45 :
    word10Chunk45.foldl (fun acc a => a.applyPacked acc)
      word10State45 = word10State46 := by decide +kernel

private def word10Chunk46 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word10State47 : PackedMat2 :=
    ⟨⟨⟨((-11663031147 : Dyadic) * half ^ 35),
        ((-1427700611 : Dyadic) * half ^ 35)⟩,
       ⟨((-6657428177 : Dyadic) * half ^ 34),
        ((-23507783679 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((27637422639 : Dyadic) * half ^ 36),
        ((-5216161125 : Dyadic) * half ^ 35)⟩,
       ⟨((32507574295 : Dyadic) * half ^ 36),
        ((-6218370675 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-1429316475 : Dyadic) * half ^ 32),
        ((30072498467 : Dyadic) * half ^ 36)⟩,
       ⟨((501104775 : Dyadic) * half ^ 34),
        ((-608768957 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((26363184901 : Dyadic) * half ^ 36),
        ((24977887501 : Dyadic) * half ^ 36)⟩,
       ⟨((-20652382457 : Dyadic) * half ^ 36),
        ((-1651825207 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word10Step46 :
    word10Chunk46.foldl (fun acc a => a.applyPacked acc)
      word10State46 = word10State47 := by decide +kernel

private def word10Chunk47 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word10State48 : PackedMat2 :=
    ⟨⟨⟨((-190470887 : Dyadic) * half ^ 37),
        ((-34398003511 : Dyadic) * half ^ 37)⟩,
       ⟨((-72612576559 : Dyadic) * half ^ 37),
        ((-3197491785 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-54102400157 : Dyadic) * half ^ 37),
        ((3549515033 : Dyadic) * half ^ 36)⟩,
       ⟨((78792960291 : Dyadic) * half ^ 37),
        ((-18782162565 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((54102400157 : Dyadic) * half ^ 37),
        ((-3549515033 : Dyadic) * half ^ 36)⟩,
       ⟨((78792960291 : Dyadic) * half ^ 37),
        ((-18782162565 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-190470887 : Dyadic) * half ^ 37),
        ((-34398003511 : Dyadic) * half ^ 37)⟩,
       ⟨((72612576559 : Dyadic) * half ^ 37),
        ((3197491785 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word10Step47 :
    word10Chunk47.foldl (fun acc a => a.applyPacked acc)
      word10State47 = word10State48 := by decide +kernel

private def word10Chunk48 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word10State49 : PackedMat2 :=
    ⟨⟨⟨((3874925509 : Dyadic) * half ^ 36),
        ((6522091663 : Dyadic) * half ^ 37)⟩,
       ⟨((-38615766039 : Dyadic) * half ^ 37),
        ((-20281449923 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-62286418975 : Dyadic) * half ^ 37),
        ((-71721761315 : Dyadic) * half ^ 38)⟩,
       ⟨((-50242397259 : Dyadic) * half ^ 37),
        ((122103043193 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-48456201127 : Dyadic) * half ^ 36),
        ((-3011005429 : Dyadic) * half ^ 36)⟩,
       ⟨((-25190640939 : Dyadic) * half ^ 37),
        ((56264408117 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-13401770793 : Dyadic) * half ^ 36),
        ((-46365617057 : Dyadic) * half ^ 38)⟩,
       ⟨((-3439839565 : Dyadic) * half ^ 35),
        ((-30865915021 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word10Step48 :
    word10Chunk48.foldl (fun acc a => a.applyPacked acc)
      word10State48 = word10State49 := by decide +kernel

private def word10Chunk49 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word10State50 : PackedMat2 :=
    ⟨⟨⟨((-5313234805 : Dyadic) * half ^ 37),
        ((-15659159433 : Dyadic) * half ^ 39)⟩,
       ⟨((17429348431 : Dyadic) * half ^ 38),
        ((-186290391945 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-14614607537 : Dyadic) * half ^ 37),
        ((-259720064469 : Dyadic) * half ^ 39)⟩,
       ⟨((21200858179 : Dyadic) * half ^ 38),
        ((-212769455679 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-118122380037 : Dyadic) * half ^ 37),
        ((-8028356895 : Dyadic) * half ^ 39)⟩,
       ⟨((-23475304395 : Dyadic) * half ^ 38),
        ((-50430073253 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((100974775689 : Dyadic) * half ^ 38),
        ((-6802878821 : Dyadic) * half ^ 39)⟩,
       ⟨((-166632063 : Dyadic) * half ^ 29),
        ((28055818041 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word10Step49 :
    word10Chunk49.foldl (fun acc a => a.applyPacked acc)
      word10State49 = word10State50 := by decide +kernel

private def word10Chunk50 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word10State51 : PackedMat2 :=
    ⟨⟨⟨((49283522361 : Dyadic) * half ^ 39),
        ((-21456582783 : Dyadic) * half ^ 38)⟩,
       ⟨((-150231451909 : Dyadic) * half ^ 39),
        ((97550891753 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-2410238945 : Dyadic) * half ^ 38),
        ((54714825791 : Dyadic) * half ^ 37)⟩,
       ⟨((-8413921403 : Dyadic) * half ^ 34),
        ((-120634678815 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-98224624349 : Dyadic) * half ^ 39),
        ((137032981393 : Dyadic) * half ^ 39)⟩,
       ⟨((-339493981979 : Dyadic) * half ^ 39),
        ((-132212503503 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((38047154485 : Dyadic) * half ^ 37),
        ((-25236982387 : Dyadic) * half ^ 38)⟩,
       ⟨((-14875934317 : Dyadic) * half ^ 35),
        ((99757487135 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word10Step50 :
    word10Chunk50.foldl (fun acc a => a.applyPacked acc)
      word10State50 = word10State51 := by decide +kernel

private def word10Chunk51 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word10State52 : PackedMat2 :=
    ⟨⟨⟨((-204840364119 : Dyadic) * half ^ 40),
        ((-33306617495 : Dyadic) * half ^ 37)⟩,
       ⟨((434666611483 : Dyadic) * half ^ 40),
        ((25714685689 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((857195543133 : Dyadic) * half ^ 40),
        ((-79287582581 : Dyadic) * half ^ 40)⟩,
       ⟨((-295373357881 : Dyadic) * half ^ 40),
        ((-3736508083 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-71814566415 : Dyadic) * half ^ 40),
        ((576284450507 : Dyadic) * half ^ 40)⟩,
       ⟨((86760598747 : Dyadic) * half ^ 40),
        ((-140455546313 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((292167625649 : Dyadic) * half ^ 40),
        ((319753487801 : Dyadic) * half ^ 40)⟩,
       ⟨((-240738254271 : Dyadic) * half ^ 40),
        ((57456561841 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word10Step51 :
    word10Chunk51.foldl (fun acc a => a.applyPacked acc)
      word10State51 = word10State52 := by decide +kernel

private def word10Chunk52 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word10State53 : PackedMat2 :=
    ⟨⟨⟨((-56655128783 : Dyadic) * half ^ 39),
        ((-17885554341 : Dyadic) * half ^ 39)⟩,
       ⟨((-868720386503 : Dyadic) * half ^ 40),
        ((-48983459693 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-24871267523 : Dyadic) * half ^ 38),
        ((688759734943 : Dyadic) * half ^ 41)⟩,
       ⟨((215241984537 : Dyadic) * half ^ 39),
        ((-57356413749 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((215241984537 : Dyadic) * half ^ 39),
        ((-57356413749 : Dyadic) * half ^ 41)⟩,
       ⟨((-24871267523 : Dyadic) * half ^ 38),
        ((688759734943 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((868720386503 : Dyadic) * half ^ 40),
        ((48983459693 : Dyadic) * half ^ 40)⟩,
       ⟨((56655128783 : Dyadic) * half ^ 39),
        ((17885554341 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word10Step52 :
    word10Chunk52.foldl (fun acc a => a.applyPacked acc)
      word10State52 = word10State53 := by decide +kernel

private def word10Chunk53 : List Letter := [.h, .s, .t, .h, .s, .t, .h]
private def word10State54 : PackedMat2 :=
    ⟨⟨⟨((1310944655677 : Dyadic) * half ^ 41),
        ((1255918164669 : Dyadic) * half ^ 42)⟩,
       ⟨((260928408727 : Dyadic) * half ^ 39),
        ((-1485574981213 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((126813743739 : Dyadic) * half ^ 41),
        ((-179341716291 : Dyadic) * half ^ 42)⟩,
       ⟨((-56869932395 : Dyadic) * half ^ 39),
        ((321704918737 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-126813743739 : Dyadic) * half ^ 41),
        ((179341716291 : Dyadic) * half ^ 42)⟩,
       ⟨((-56869932395 : Dyadic) * half ^ 39),
        ((321704918737 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((1310944655677 : Dyadic) * half ^ 41),
        ((1255918164669 : Dyadic) * half ^ 42)⟩,
       ⟨((-260928408727 : Dyadic) * half ^ 39),
        ((1485574981213 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word10Step53 :
    word10Chunk53.foldl (fun acc a => a.applyPacked acc)
      word10State53 = word10State54 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word10_check : check word10 10 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word10 = word10State54.toMatrix := by
    unfold evalRingPacked
    change ((
      word10Chunk0 ++ word10Chunk1 ++ word10Chunk2 ++ word10Chunk3 ++
      word10Chunk4 ++ word10Chunk5 ++ word10Chunk6 ++ word10Chunk7 ++
      word10Chunk8 ++ word10Chunk9 ++ word10Chunk10 ++ word10Chunk11 ++
      word10Chunk12 ++ word10Chunk13 ++ word10Chunk14 ++ word10Chunk15 ++
      word10Chunk16 ++ word10Chunk17 ++ word10Chunk18 ++ word10Chunk19 ++
      word10Chunk20 ++ word10Chunk21 ++ word10Chunk22 ++ word10Chunk23 ++
      word10Chunk24 ++ word10Chunk25 ++ word10Chunk26 ++ word10Chunk27 ++
      word10Chunk28 ++ word10Chunk29 ++ word10Chunk30 ++ word10Chunk31 ++
      word10Chunk32 ++ word10Chunk33 ++ word10Chunk34 ++ word10Chunk35 ++
      word10Chunk36 ++ word10Chunk37 ++ word10Chunk38 ++ word10Chunk39 ++
      word10Chunk40 ++ word10Chunk41 ++ word10Chunk42 ++ word10Chunk43 ++
      word10Chunk44 ++ word10Chunk45 ++ word10Chunk46 ++ word10Chunk47 ++
      word10Chunk48 ++ word10Chunk49 ++ word10Chunk50 ++ word10Chunk51 ++
      word10Chunk52 ++ word10Chunk53
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word10Step0, word10Step1, word10Step2, word10Step3, word10Step4,
      word10Step5, word10Step6, word10Step7, word10Step8, word10Step9,
      word10Step10, word10Step11, word10Step12, word10Step13, word10Step14,
      word10Step15, word10Step16, word10Step17, word10Step18, word10Step19,
      word10Step20, word10Step21, word10Step22, word10Step23, word10Step24,
      word10Step25, word10Step26, word10Step27, word10Step28, word10Step29,
      word10Step30, word10Step31, word10Step32, word10Step33, word10Step34,
      word10Step35, word10Step36, word10Step37, word10Step38, word10Step39,
      word10Step40, word10Step41, word10Step42, word10Step43, word10Step44,
      word10Step45, word10Step46, word10Step47, word10Step48, word10Step49,
      word10Step50, word10Step51, word10Step52, word10Step53]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
