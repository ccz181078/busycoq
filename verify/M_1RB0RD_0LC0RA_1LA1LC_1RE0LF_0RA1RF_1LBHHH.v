(* 1RB0RD_0LC0RA_1LA1LC_1RE0LF_0RA1RF_1LB--- never halts. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Lia ZifyNat PeanoNat String List.
Import ListNotations.

Open Scope list.
Open Scope sym.

Definition tm := Eval compute in
  (TM_from_str "1RB0RD_0LC0RA_1LA1LC_1RE0LF_0RA1RF_1LB---").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(* ---------- Composite mode transitions ---------- *)

Lemma tr_init_18 :
  c0 -->* (0inf {{A}}> (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0inf)).
Proof.
  change (0inf {{A}}> (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0inf))
    with ((0inf <* []) {{A}}> ([1; 1; 0; 1; 0; 1; 0] *> 0inf)).
  solve_init.
Qed.

Lemma tr_L0_A (X B_r : side) :
  (0 >> 1 >> B_r) {{A}}> (0 >> 0 >> 1 >> 0 >> X) -->+
  B_r {{A}}> (1 >> 1 >> 1 >> 0 >> 1 >> 0 >> X).
Proof. es. Qed.

Lemma tr_L0_B (X B_r : side) :
  (0 >> 1 >> B_r) {{A}}> (0 >> 1 >> 0 >> 1 >> 0 >> X) -->+
  (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> B_r) {{A}}> (0 >> X).
Proof. es. Qed.

Lemma tr_L10_A (X B_r : side) :
  (0 >> 1 >> B_r) {{A}}> (1 >> 0 >> 0 >> 1 >> 0 >> X) -->+
  (0 >> 1 >> 0 >> 0 >> 1 >> B_r) {{A}}> (1 >> 0 >> X).
Proof. es. Qed.

Lemma tr_L10_B (X B_r : side) :
  (0 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> X) -->+
  (0 >> 1 >> 0 >> 0 >> 1 >> 1 >> B_r) {{A}}> (1 >> 0 >> X).
Proof. es. Qed.

Lemma tr_L10_bot10 (B_r : side) :
  (0 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> 0inf) -->+
  (0 >> 0 >> 1 >> 0 >> 0 >> 1 >> B_r) {{A}}> (1 >> 1 >> 1 >> 0 >> 0inf).
Proof. es. Qed.

Lemma tr_L1010_A (X B_r : side) :
  (0 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> X) -->+
  (0 >> 1 >> 0 >> 0 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> X).
Proof. es. Qed.

Lemma tr_L1010_B (X B_r : side) :
  (0 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> X) -->+
  (0 >> 1 >> 0 >> 0 >> 1 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> X).
Proof. es. Qed.

Lemma tr_L1010_bot10 (B_r : side) :
  (0 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0inf) -->+
  (0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> B_r) {{A}}> (1 >> 1 >> 1 >> 0 >> 0inf).
Proof. es. Qed.

Lemma tr_R11_emp (X : side) :
  0inf {{A}}> (1 >> 1 >> X) -->+
  (0 >> 1 >> 0 >> 1 >> 0inf) {{A}}> (0 >> X).
Proof. es. Qed.

Lemma tr_R11_01 (X : side) :
  (0 >> 1 >> 0inf) {{A}}> (1 >> 1 >> X) -->+
  (0 >> 1 >> 0inf) {{A}}> (1 >> 0 >> 1 >> 0 >> X).
Proof. es. Qed.

Lemma tr_R11_0101 (X B_r : side) :
  (0 >> 1 >> 0 >> 1 >> B_r) {{A}}> (1 >> 1 >> X) -->+
  B_r {{A}}> (1 >> 1 >> 1 >> 0 >> 1 >> 0 >> X).
Proof. es. Qed.

Lemma tr_R11_001 (X B_r : side) :
  (0 >> 0 >> 1 >> B_r) {{A}}> (1 >> 1 >> X) -->+
  B_r {{A}}> (1 >> 1 >> 0 >> 1 >> 0 >> X).
Proof. es. Qed.

Lemma tr_R11_0011 (X B_r : side) :
  (0 >> 0 >> 1 >> 1 >> B_r) {{A}}> (1 >> 1 >> X) -->+
  (0 >> 1 >> 0 >> 0 >> B_r) {{A}}> (1 >> 0 >> X).
Proof. es. Qed.

Lemma tr_R11_00001 (X B_r : side) :
  (0 >> 0 >> 0 >> 0 >> 1 >> B_r) {{A}}> (1 >> 1 >> X) -->+
  (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> B_r) {{A}}> (0 >> X).
Proof. es. Qed.

Lemma tr_R11_1_B (X B_r : side) :
  (1 >> B_r) {{A}}> (1 >> 1 >> 1 >> 0 >> 1 >> 0 >> X) -->+
  (0 >> 1 >> 0 >> 0 >> 1 >> B_r) {{A}}> (1 >> 0 >> X).
Proof. es. Qed.

Lemma tr_L0_BB (X B_r : side) :
  (0 >> 1 >> B_r) {{A}}> (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> X) -->+
  (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> B_r) {{A}}> (0 >> X).
Proof.
  eapply progress_trans; [apply (tr_L0_B (1 >> 0 >> 1 >> 0 >> X) B_r) |].
  apply (tr_L0_B X (0 >> 1 >> 0 >> 1 >> B_r)).
Qed.

Lemma tr_L10_BB (X B_r : side) :
  (0 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> X) -->+
  (0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 1 >> B_r) {{A}}> (1 >> 0 >> X).
Proof.
  eapply progress_trans; [apply (tr_L10_B (1 >> 0 >> 1 >> 0 >> X) B_r) |].
  apply (tr_L10_B X (0 >> 0 >> 1 >> 1 >> B_r)).
Qed.

Lemma tr_L1010_BB (X B_r : side) :
  (0 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> X) -->+
  (0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> X).
Proof.
  eapply progress_trans; [apply (tr_L1010_B (1 >> 0 >> 1 >> 0 >> X) B_r) |].
  apply (tr_L1010_B X (0 >> 0 >> 1 >> 1 >> B_r)).
Qed.

Lemma tr_R11_0011_emp (X : side) :
  (0 >> 0 >> 1 >> 1 >> 0inf) {{A}}> (1 >> 1 >> X) -->+
  (0 >> 1 >> 0inf) {{A}}> (1 >> 0 >> X).
Proof. es. Qed.

Lemma tr_R11_0101_pair (X B_r : side) :
  (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> B_r) {{A}}> (1 >> 1 >> X) -->+
  B_r {{A}}> (1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> X).
Proof.
  eapply progress_trans; [apply (tr_R11_0101 X (0 >> 1 >> 0 >> 1 >> B_r)) |].
  apply (tr_R11_0101 (1 >> 0 >> 1 >> 0 >> X) B_r).
Qed.

Lemma tr_R11_01_B (X : side) :
  (0 >> 1 >> 0inf) {{A}}> (1 >> 1 >> 1 >> 0 >> 1 >> 0 >> X) -->+
  (0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 0inf) {{A}}> (1 >> 0 >> 1 >> 0 >> X).
Proof.
  eapply progress_trans; [apply (tr_R11_01 (1 >> 0 >> 1 >> 0 >> X)) |].
  apply (tr_L1010_B X 0inf).
Qed.

Lemma tr_R11_01011_B (X B_r : side) :
  (0 >> 1 >> 0 >> 1 >> 1 >> B_r) {{A}}> (1 >> 1 >> 1 >> 0 >> 1 >> 0 >> X) -->+
  (0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> B_r) {{A}}> (1 >> 0 >> X).
Proof.
  eapply progress_trans; [apply (tr_R11_0101 (1 >> 0 >> 1 >> 0 >> X) (1 >> B_r)) |].
  eapply progress_trans; [apply (tr_R11_1_B (1 >> 0 >> 1 >> 0 >> X) B_r) |].
  apply (tr_L10_B X (0 >> 0 >> 1 >> B_r)).
Qed.

(* ---------- Closed two-stack grammar and inductive invariant ---------- *)

Inductive StackL : nat -> side -> Prop :=
  | bot10 : StackL O (1 >> 0 >> 0inf)
  | pushA {a : nat} {X : side} :
      StackL a X -> StackL (S a) (0 >> 1 >> 0 >> X)
  | pushBB {a : nat} {X : side} :
      StackL a X -> StackL a (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> X).

Inductive StackR : nat -> side -> Prop :=
  | SR_emp {a : nat} : StackR (S a) 0inf
  | SR_c0011_emp {a : nat} : StackR a (0 >> 0 >> 1 >> 1 >> 0inf)
  | SR_c001 {a : nat} {B : side} :
      StackR (S a) B -> StackR a (0 >> 0 >> 1 >> B)
  | SR_c0011_001 {a : nat} {B : side} :
      StackR (S a) B -> StackR a (0 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> B)
  | SR_c0011_0011 {a : nat} {B : side} :
      StackR a B -> StackR a (0 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 1 >> B)
  | SR_c00001 {a : nat} {B : side} :
      StackR a B -> StackR (S a) (0 >> 0 >> 0 >> 0 >> 1 >> B)
  | SR_c000011 {a : nat} {B : side} :
      StackR a B -> StackR (S a) (0 >> 0 >> 0 >> 0 >> 1 >> 1 >> B).

Lemma StackR_weaken {a : nat} {B : side} (h : StackR a B) : StackR (S a) B.
Proof.
  induction h.
  - exact SR_emp.
  - exact SR_c0011_emp.
  - exact (SR_c001 IHh).
  - exact (SR_c0011_001 IHh).
  - exact (SR_c0011_0011 IHh).
  - exact (SR_c00001 IHh).
  - exact (SR_c000011 IHh).
Qed.

Inductive StackR1010 : nat -> side -> Prop :=
  | SR1010_emp {a : nat} : StackR1010 (S a) 0inf
  | SR1010_c0011_emp {a : nat} : StackR1010 (S a) (0 >> 0 >> 1 >> 1 >> 0inf)
  | SR1010_c001 {a : nat} {B : side} :
      StackR1010 (S a) B -> StackR1010 a (0 >> 0 >> 1 >> B)
  | SR1010_c0011_0011 {a : nat} {B : side} :
      StackR1010 a B -> StackR1010 a (0 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 1 >> B).

Lemma StackR1010_toStackR {a : nat} {B : side} (h : StackR1010 a B) : StackR a B.
Proof.
  induction h.
  - exact SR_emp.
  - exact SR_c0011_emp.
  - exact (SR_c001 IHh).
  - exact (SR_c0011_0011 IHh).
Qed.

Lemma StackR1010_push0011 {a : nat} {B : side} (h : StackR1010 a B) :
  StackR a (0 >> 0 >> 1 >> 1 >> B).
Proof.
  induction h.
  - exact SR_c0011_emp.
  - exact (SR_c0011_0011 SR_emp).
  - exact (SR_c0011_001 (StackR1010_toStackR h)).
  - exact (SR_c0011_0011 IHh).
Qed.

Inductive PopTarget : nat -> side -> Prop :=
  | PT_emp {a : nat} : PopTarget a (0 >> 1 >> 0inf)
  | PT_c0101 {a : nat} {B_0 : side} :
      StackR a B_0 -> PopTarget a (0 >> 1 >> 0 >> 1 >> B_0)
  | PT_c01011 {a : nat} {B_0 : side} :
      StackR a B_0 -> PopTarget a (0 >> 1 >> 0 >> 1 >> 1 >> B_0).

Inductive R0101 : nat -> side -> Prop :=
  | R0101_base {a : nat} {B : side} : PopTarget a B -> R0101 a B
  | R0101_step {a : nat} {B : side} :
      R0101 a B -> R0101 a (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> B).

Inductive Inv : Q * tape -> Prop :=
  | Mode_L0 {a : nat} {X B : side} :
      StackL (S a) X -> R0101 a B ->
      Inv ((0 >> 1 >> B) {{A}}> (0 >> X))
  | Mode_L10 {a : nat} {X B : side} :
      StackL a X -> StackR (S (S a)) B ->
      Inv ((0 >> 1 >> B) {{A}}> (1 >> 0 >> X))
  | Mode_L1010 {a : nat} {X B : side} :
      StackL a X -> StackR1010 (S a) B ->
      Inv ((0 >> 1 >> B) {{A}}> (1 >> 0 >> 1 >> 0 >> X))
  | Mode_R11 {a : nat} {X B : side} :
      StackL a X -> StackR a B ->
      Inv (B {{A}}> (1 >> 1 >> X))
  | Mode_R11_pop {a : nat} {X B : side} :
      StackL a X -> R0101 a B ->
      Inv (B {{A}}> (1 >> 1 >> 1 >> 0 >> 1 >> 0 >> X)).

Lemma step_Inv : forall c : Q * tape, Inv c -> exists c' : Q * tape, Inv c' /\ c -->+ c'.
Proof.
  intros c hc.
  destruct hc as [a X B hX hB | a X B hX hB | a X B hX hB | a X B hX hB | a X B hX hB].
  - inverts hX as hX'.
    + eexists. split; [exact (Mode_R11_pop hX' hB) | apply tr_L0_A].
    + eexists. split; [exact (Mode_L0 hX' (R0101_step hB)) | apply tr_L0_BB].
  - inverts hX as hX'.
    + eexists. split; [exact (Mode_R11 bot10 (SR_c001 (SR_c001 hB))) | apply tr_L10_bot10].
    + eexists. split; [exact (Mode_L10 hX' (SR_c001 hB)) | apply tr_L10_A].
    + eexists. split; [exact (Mode_L10 hX' (SR_c0011_0011 hB)) | apply tr_L10_BB].
  - inverts hX as hX'.
    + eexists. split; [exact (Mode_R11 bot10 (SR_c001 (StackR1010_push0011 hB))) | apply tr_L1010_bot10].
    + eexists. split; [exact (Mode_L1010 hX' (SR1010_c001 hB)) | apply tr_L1010_A].
    + eexists. split; [exact (Mode_L1010 hX' (SR1010_c0011_0011 hB)) | apply tr_L1010_BB].
  - inverts hB as hB'.
    + eexists. split; [exact (Mode_L0 hX (R0101_base PT_emp)) | apply tr_R11_emp].
    + eexists. split; [exact (Mode_L10 hX SR_emp) | apply tr_R11_0011_emp].
    + eexists. split; [exact (Mode_R11 (pushA hX) hB') | apply tr_R11_001].
    + eexists. split; [exact (Mode_L10 hX (SR_c00001 hB')) | apply tr_R11_0011].
    + eexists. split; [exact (Mode_L10 hX (SR_c000011 (StackR_weaken hB'))) | apply tr_R11_0011].
    + eexists. split; [exact (Mode_L0 hX (R0101_base (PT_c0101 hB'))) | apply tr_R11_00001].
    + eexists. split; [exact (Mode_L0 hX (R0101_base (PT_c01011 hB'))) | apply tr_R11_00001].
  - inverts hB as hB'.
    + inverts hB' as hT.
      * eexists. split; [exact (Mode_L1010 hX SR1010_c0011_emp) | apply tr_R11_01_B].
      * eexists. split; [exact (Mode_R11 (pushBB hX) hT) | apply tr_R11_0101].
      * eexists. split;
          [exact (Mode_L10 hX (SR_c0011_001 (StackR_weaken (StackR_weaken (StackR_weaken hT)))))
          | apply tr_R11_01011_B].
    + eexists. split; [exact (Mode_R11_pop (pushBB hX) hB') | apply tr_R11_0101_pair].
Qed.

Lemma nonhalt : ~ halts tm c0.
Proof.
  eapply multistep_nonhalt.
  - exact tr_init_18.
  - apply progress_nonhalt with (P := Inv).
    + exact step_Inv.
    + exact (Mode_R11 (pushA bot10) SR_emp).
Qed.

Print Assumptions nonhalt.
