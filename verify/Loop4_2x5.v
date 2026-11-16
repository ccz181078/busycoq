From BusyCoq Require Import Individual25.
Require Import Lia.
Require Import ZArith.
Require Import String.

Open Scope list.

Ltac flia := repeat (lia || f_equal).


Module V1.
Section V1.
Hypothesis tm:TM.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Hypothesis S0: nat->nat->nat->Q*tape.
Hypothesis S1: nat->nat->Q*tape.

Hypothesis Inc0:
  forall a b c,
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.

Lemma Incs0 n a b c:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Hypothesis LOv0:
  forall b c,
  S0 0 b (3+c) -->*
  S0 (2+b) 2 c.

Hypothesis Inc1:
  forall a b,
  S1 (1+a) b -->*
  S1 a (3+b).

Lemma Incs1 a b:
  S1 a b -->*
  S1 0 (a*3+b).
Proof.
  gen b.
  ind a Inc1.
Qed.

Hypothesis ROv:
  forall a b,
  S0 (1+a) b 0 -->*
  S1 a (2+b).

Hypothesis LOv1:
  forall b,
  S1 0 b -->+
  S0 1 2 (1+b).

Lemma Inc a c:
  S0 a 2 (a+(3+c)) -->*
  S0 (4+a*2) 2 c.
Proof.
  follow (Incs0 a 0 2 (3+c)).
  follow LOv0.
  finish.
Qed.

Lemma Ov a c:
  S0 (c+(1+a)) 2 c -->+
  S0 1 2 (5+a*3+c*2).
Proof.
  follow (Incs0 c (1+a) 2 0).
  follow ROv.
  follow Incs1.
  follow10 LOv1.
  finish.
Qed.

Definition P1 a c :=
  forall c1,
  S0 1 2 (c1+c) -->*
  S0 a 2 c1.

Lemma P1_S a c:
  P1 a c ->
  P1 (4+a*2) (3+a+c).
Proof.
  unfold P1.
  intros HP1 c1.
  follow (HP1 (c1+a+3)).
  follow (Inc a c1).
  finish.
Qed.

Lemma P1_O:
  P1 6 4.
Proof. 
  apply (P1_S 1 0).
  unfold P1; intros; finish.
Qed.

Lemma BigStep a c c1:
  c1+1 <= a ->
  P1 a c ->
  S0 1 2 (c1+c) -->+
  S0 1 2 (2+a*3-c1).
Proof.
  unfold P1.
  intros Hc1 HP1.
  follow HP1.
  applys_eq (Ov (a-c1-1) c1); flia.
Qed.

Definition config(x:nat*nat*nat) := let '(a,c,c1):=x in S0 1 2 (c1+c).

Hypothesis init:
  c0 -->* config (6,4,2)%nat.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (6,4,2)%nat).
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(a,c,c1) => c1+1<=a /\ 3+a+c<=2+a*3-c1 /\ P1 a c).
  2: repeat split; try lia.
  2: apply P1_O.
  intros [[a c] c1] [Hc1 [Hc1' HP1]].
  exists (4+a*2,3+a+c,(2+a*3-c1)-(3+a+c)).
  split.
  - unfold config.
    applys_eq (BigStep _ _ _ Hc1 HP1).
    1: flia.
  - repeat split; try lia.
    apply P1_S,HP1.
Qed.
End V1.
End V1.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB3LA3LA2RA2RA_2LB2RA---4RB1LB").
Lemma nonhalt: ~halts tm c0.
Proof.
  apply V1.nonhalt with
    (S0 := fun a b c => 0inf <* [1] <* [4]^^a <* [2]^^(1+b) {{A}}> [1]^^c *> [2] *> 0inf)
    (S1 := fun a b => 0inf <* [1] <* [4]^^a <* [2]^^(1+b) {{A}}> 0inf).
  all: es.
Qed.
End TM1.

Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB3LA3LA1RA2RA_2LB2RA---4RB1LB").
Lemma nonhalt: ~halts tm c0.
Proof.
  apply V1.nonhalt with
    (S0 := fun a b c => 0inf <* [1] <* [4]^^a <* [2] <* [1]^^b {{A}}> [1]^^c *> [2] *> 0inf)
    (S1 := fun a b => 0inf <* [1] <* [4]^^a <* [2] <* [1]^^b {{A}}> 0inf).
  all: es.
Qed.
End TM2.

Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB3LA3LA4LB1RA_2LB2RA---4RB1LB").
Lemma nonhalt: ~halts tm c0.
Proof.
  apply V1.nonhalt with
    (S0 := fun a b c => 0inf <* [1] <* [4]^^a <* [2]^^b <* [1] {{A}}> [1]^^c *> [2] *> 0inf)
    (S1 := fun a b => 0inf <* [1] <* [4]^^a <* [2]^^b <* [1] {{A}}> 0inf).
  all: es.
Qed.
End TM3.

Module TM4.
Definition tm := Eval compute in (TM_from_str "1RB3LA3LA2RA1RA_2LB2RA---4RB1LB").
Lemma nonhalt: ~halts tm c0.
Proof.
  apply V1.nonhalt with
    (S0 := fun a b c => 0inf <* [1] <* [4]^^a <* [1] <* [2]^^b {{A}}> [1]^^c *> [2] *> 0inf)
    (S1 := fun a b => 0inf <* [1] <* [4]^^a <* [1] <* [2]^^b {{A}}> 0inf).
  all: es.
Qed.
End TM4.

Module TM5.
Definition tm := Eval compute in (TM_from_str "1RB3LA3LA1RA1RA_2LB2RA---4RB1LB").
Lemma nonhalt: ~halts tm c0.
Proof.
  apply V1.nonhalt with
    (S0 := fun a b c => 0inf <* [1] <* [4]^^a <* [1] <* [1]^^b {{A}}> [1]^^c *> [2] *> 0inf)
    (S1 := fun a b => 0inf <* [1] <* [4]^^a <* [1] <* [1]^^b {{A}}> 0inf).
  all: es.
Qed.
End TM5.

Module TM6.
Definition tm := Eval compute in (TM_from_str "1RB3LA1LB4LB1RA_2LB1RA---4RB1LB").
Lemma nonhalt: ~halts tm c0.
Proof.
  apply V1.nonhalt with
    (S0 := fun a b c => 0inf <* [1] <* [4]^^a <* [1] <* [1]^^b {{A}}> [1]^^c *> [2] *> 0inf)
    (S1 := fun a b => 0inf <* [1] <* [4]^^a <* [1] <* [1]^^b {{A}}> 0inf).
  all: es.
Qed.
End TM6.

Module TM7.
Definition tm := Eval compute in (TM_from_str "1RB3LA1LB1RA1RA_2LB1RA---4RB1LB").
Lemma nonhalt: ~halts tm c0.
Proof.
  apply V1.nonhalt with
    (S0 := fun a b c => 0inf <* [1] <* [4]^^a <* [1] <* [1]^^b {{A}}> [1]^^c *> [2] *> 0inf)
    (S1 := fun a b => 0inf <* [1] <* [4]^^a <* [1] <* [1]^^b {{A}}> 0inf).
  all: es.
Qed.
End TM7.

Module TM8.
Definition tm := Eval compute in (TM_from_str "1RB3LA3LA2RA2RA_2LB1RA---4RB1LB").
Lemma nonhalt: ~halts tm c0.
Proof.
  apply V1.nonhalt with
    (S0 := fun a b c => 0inf <* [1] <* [4]^^a <* [2]^^(1+b) {{A}}> [1]^^c *> [2] *> 0inf)
    (S1 := fun a b => 0inf <* [1] <* [4]^^a <* [2]^^(1+b) {{A}}> 0inf).
  all: es.
Qed.
End TM8.

Module TM9.
Definition tm := Eval compute in (TM_from_str "1RB3LA3LA1RA2RA_2LB1RA---4RB1LB").
Lemma nonhalt: ~halts tm c0.
Proof.
  apply V1.nonhalt with
    (S0 := fun a b c => 0inf <* [1] <* [4]^^a <* [2] <* [1]^^b {{A}}> [1]^^c *> [2] *> 0inf)
    (S1 := fun a b => 0inf <* [1] <* [4]^^a <* [2] <* [1]^^b {{A}}> 0inf).
  all: es.
Qed.
End TM9.

Module TM10.
Definition tm := Eval compute in (TM_from_str "1RB3LA3LA4LB1RA_2LB1RA---4RB1LB").
Lemma nonhalt: ~halts tm c0.
Proof.
  apply V1.nonhalt with
    (S0 := fun a b c => 0inf <* [1] <* [4]^^a <* [1] <* [1]^^b {{A}}> [1]^^c *> [2] *> 0inf)
    (S1 := fun a b => 0inf <* [1] <* [4]^^a <* [1] <* [1]^^b {{A}}> 0inf).
  all: es.
Qed.
End TM10.

Module TM11.
Definition tm := Eval compute in (TM_from_str "1RB3LA3LA2RA1RA_2LB1RA---4RB1LB").
Lemma nonhalt: ~halts tm c0.
Proof.
  apply V1.nonhalt with
    (S0 := fun a b c => 0inf <* [1] <* [4]^^a <* [1] <* [2]^^b {{A}}> [1]^^c *> [2] *> 0inf)
    (S1 := fun a b => 0inf <* [1] <* [4]^^a <* [1] <* [2]^^b {{A}}> 0inf).
  all: es.
Qed.
End TM11.

Module TM12.
Definition tm := Eval compute in (TM_from_str "1RB3LA3LA1RA1RA_2LB1RA---4RB1LB").
Lemma nonhalt: ~halts tm c0.
Proof.
  apply V1.nonhalt with
    (S0 := fun a b c => 0inf <* [1] <* [4]^^a <* [1] <* [1]^^b {{A}}> [1]^^c *> [2] *> 0inf)
    (S1 := fun a b => 0inf <* [1] <* [4]^^a <* [1] <* [1]^^b {{A}}> 0inf).
  all: es.
Qed.
End TM12.

Module V2.
Section V2.
Hypothesis tm:TM.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Hypothesis S0: nat->nat->nat->Q*tape.
Hypothesis S1: nat->nat->Q*tape.

Hypothesis Inc0:
  forall a b c,
  S0 (1+a) b (2+c) -->*
  S0 a (3+b) c.

Lemma Incs0 n a b c:
  S0 (n+a) b (n*2+c) -->*
  S0 a (n*3+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Hypothesis LOv0:
  forall b c,
  S0 0 b (4+c) -->*
  S0 (2+b) 3 c.

Hypothesis Inc1:
  forall a b,
  S1 (1+a) b -->*
  S1 a (5+b).

Lemma Incs1 a b:
  S1 a b -->*
  S1 0 (a*5+b).
Proof.
  gen b.
  ind a Inc1.
Qed.

Hypothesis ROv_0:
  forall a b,
  S0 (1+a) b 0 -->*
  S1 a (4+b).

Hypothesis ROv_1:
  forall a b,
  S0 (1+a) b 1 -->*
  S1 a (3+b).

Hypothesis LOv1:
  forall b,
  S1 0 b -->+
  S0 1 3 b.

Lemma Inc a c:
  S0 a 3 (a*2+(4+c)) -->*
  S0 (5+a*3) 3 c.
Proof.
  follow (Incs0 a 0 3 (4+c)).
  follow LOv0.
  finish.
Qed.

Lemma Ov_0 a c:
  S0 (c+(1+a)) 3 (c*2+0) -->+
  S0 1 3 (7+a*5+c*3).
Proof.
  follow (Incs0 c (1+a) 3 0).
  follow ROv_0.
  follow Incs1.
  follow10 LOv1.
  finish.
Qed.

Lemma Ov_1 a c:
  S0 (c+(1+a)) 3 (c*2+1) -->+
  S0 1 3 (6+a*5+c*3).
Proof.
  follow (Incs0 c (1+a) 3 1).
  follow ROv_1.
  follow Incs1.
  follow10 LOv1.
  finish.
Qed.

Definition P1 a c :=
  forall c1,
  S0 1 3 (c1+c) -->*
  S0 a 3 c1.

Lemma P1_S a c:
  P1 a c ->
  P1 (5+a*3) (4+a*2+c).
Proof.
  unfold P1.
  intros HP1 c1.
  follow (HP1 (c1+a*2+4)).
  follow (Inc a c1).
  finish.
Qed.

Lemma P1_O:
  P1 8 6.
Proof.
  apply (P1_S 1 0).
  unfold P1; intros; finish.
Qed.

Lemma BigStep a c c1:
  c1+1 <= a*2 ->
  P1 a c ->
  S0 1 3 (c1+c) -->+
  S0 1 3 (2+a*5-c1).
Proof.
  unfold P1.
  intros Hc1 HP1.
  pose proof (Nat.Div0.div_mod c1 2).
  pose proof (Nat.mod_upper_bound c1 2).
  remember (c1/2) as c2.
  remember (c1 mod 2) as c3.
  destruct c3 as [|[|]].
  3: lia.
  - follow HP1.
    applys_eq (Ov_0 (a-c2-1) c2); flia.
  - follow HP1.
    applys_eq (Ov_1 (a-c2-1) c2); flia.
Qed.

Definition config(x:nat*nat*nat) := let '(a,c,c1):=x in S0 1 3 (c1+c).

Hypothesis init:
  c0 -->*
  config (8,6,3)%nat.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (8,6,3)%nat).
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(a,c,c1) => c1+1<=a*2 /\ 4+a*2+c<=2+a*5-c1 /\ P1 a c).
  2: repeat split; try lia; apply P1_O.
  intros [[a c] c1] [Hc1 [Hc1' HP1]].
  exists (5+a*3,4+a*2+c,(2+a*5-c1)-(4+a*2+c)).
  split.
  - unfold config.
    applys_eq (BigStep _ _ _ Hc1 HP1).
    1: flia.
  - repeat split; try lia.
    apply P1_S,HP1.
Qed.
End V2.
End V2.

Module TM13.
Definition tm := Eval compute in (TM_from_str "1RB3LA3LA1RA3RA_2LB1RA---4RB1LB").
Lemma nonhalt: ~halts tm c0.
Proof.
  apply V2.nonhalt with
    (S0 := fun a b c => 0inf <* [1] <* [4]^^a <* [1] <* [1]^^b {{A}}> [1]^^c *> [2] *> 0inf)
    (S1 := fun a b => 0inf <* [1] <* [4]^^a <* [1] <* [1]^^b {{A}}> 0inf).
  all: es.
Qed.
End TM13.

Module TM14.
Definition tm := Eval compute in (TM_from_str "1RB3LA1LB1RA3RA_2LB1RA---4RB1LB").
Lemma nonhalt: ~halts tm c0.
Proof.
  apply V2.nonhalt with
    (S0 := fun a b c => 0inf <* [1] <* [4]^^a <* [1] <* [1]^^b {{A}}> [1]^^c *> [2] *> 0inf)
    (S1 := fun a b => 0inf <* [1] <* [4]^^a <* [1] <* [1]^^b {{A}}> 0inf).
  all: es.
Qed.
End TM14.

Module TM15.
Definition tm := Eval compute in (TM_from_str "1RB3LA3LA2RA3RA_2LB1RA---4RB1LB").
Lemma nonhalt: ~halts tm c0.
Proof.
  apply V2.nonhalt with
    (S0 := fun a b c => 0inf <* [1] <* [4]^^a <* [2] <* [2]^^b {{A}}> [1]^^c *> [2] *> 0inf)
    (S1 := fun a b => 0inf <* [1] <* [4]^^a <* [2] <* [2]^^b {{A}}> 0inf).
  all: es.
Qed.
End TM15.

Module TM16.
Definition tm := Eval compute in (TM_from_str "1RB3LA3LA1RA3RA_2LB2RA---4RB1LB").
Lemma nonhalt: ~halts tm c0.
Proof.
  apply V2.nonhalt with
    (S0 := fun a b c => 0inf <* [1] <* [4]^^a <* [1] <* [1]^^b {{A}}> [1]^^c *> [2] *> 0inf)
    (S1 := fun a b => 0inf <* [1] <* [4]^^a <* [1] <* [1]^^b {{A}}> 0inf).
  all: es.
Qed.
End TM16.

Module TM17.
Definition tm := Eval compute in (TM_from_str "1RB3LA3LA2RA3RA_2LB2RA---4RB1LB").
Lemma nonhalt: ~halts tm c0.
Proof.
  apply V2.nonhalt with
    (S0 := fun a b c => 0inf <* [1] <* [4]^^a <* [2] <* [2]^^b {{A}}> [1]^^c *> [2] *> 0inf)
    (S1 := fun a b => 0inf <* [1] <* [4]^^a <* [2] <* [2]^^b {{A}}> 0inf).
  all: es.
Qed.
End TM17.


Module TM18.

Definition tm := Eval compute in (TM_from_str "1LB3RA0RB4LA3RA_2RA3LB---1LA1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  0inf <* [1]^^a <* [3]^^(2+b) {{A}}> [3]^^c *> [1] *> 0inf.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof. es. Qed.

Lemma Incs0 n a b c:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma LOv0 b c:
  S0 0 b (3+c) -->*
  S0 (4+b) 0 c.
Proof. es. Qed.

Definition S1 a b :=
  0inf <* [1]^^a <* [3]^^(3+b) {{A}}> 0inf.

Lemma Inc1 a b:
  S1 (1+a) b -->*
  S1 a (2+b).
Proof. es. Qed.

Lemma Incs1 a b:
  S1 a b -->*
  S1 0 (a*2+b).
Proof.
  gen b.
  ind a Inc1.
Qed.

Lemma ROv a b:
  S0 a b 0 -->*
  S1 a b.
Proof. es. Qed.

Lemma LOv1 b:
  S1 0 b -->+
  S0 0 0 (3+b).
Proof. es. Qed.

Lemma Inc a c:
  S0 a 0 (a+(3+c)) -->*
  S0 (4+a*2) 0 c.
Proof.
  follow (Incs0 a 0 0 (3+c)).
  follow LOv0.
  finish.
Qed.

Lemma Ov a c:
  S0 (c+a) 0 (c) -->+
  S0 0 0 (3+a*2+c*2).
Proof.
  follow (Incs0 c a 0 0).
  follow ROv.
  follow Incs1.
  follow10 LOv1.
  finish.
Qed.

Definition P1 a c :=
  forall c1,
  S0 0 0 (c1+c) -->*
  S0 a 0 c1.

Lemma P1_S a c:
  P1 a c ->
  P1 (4+a*2) (3+a+c).
Proof.
  unfold P1.
  intros HP1 c1.
  follow (HP1 (c1+a+3)).
  follow (Inc a c1).
  finish.
Qed.

Lemma BigStep a c c1:
  c1 <= a ->
  P1 a c ->
  S0 0 0 (c1+c) -->+
  S0 0 0 (3+a*2).
Proof.
  unfold P1.
  intros Hc1 HP1.
  follow HP1.
  applys_eq (Ov (a-c1) c1); flia.
Qed.

Definition config(x:nat*nat*nat) := let '(a,c,c1):=x in S0 0 0 (c1+c).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (12,10,0)%nat).
  1: es.
  eapply progress_nonhalt_cond with (P:=fun '(a,c,c1) => c1<=a /\ 3+a+c<=3+a*2 /\ P1 a c).
  2: repeat split; try lia; unfold P1; es.
  intros [[a c] c1] [Hc1 [Hc1' HP1]].
  exists (4+a*2,3+a+c,(3+a*2)-(3+a+c)).
  split.
  - unfold config.
    applys_eq (BigStep _ _ _ Hc1 HP1).
    1: flia.
  - repeat split; try lia.
    apply P1_S,HP1.
Qed.

End TM18.

Module TM19.

Definition tm := Eval compute in (TM_from_str "1LB3RA0RB4LA3RA_2RA3LB---4LA1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  0inf <* [1]^^a <* [3]^^(2+b) {{A}}> [3]^^c *> 0inf.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof. es. Qed.

Lemma Incs0 n a b c:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma LOv0 b c:
  S0 0 b (3+c) -->*
  S0 (4+b) 0 c.
Proof. es. Qed.

Definition S1 a b :=
  0inf <* [1]^^a <* [3]^^(2+b) {{A}}> 0inf.

Lemma Inc1 a b:
  S1 (1+a) b -->*
  S1 a (2+b).
Proof. es. Qed.

Lemma Incs1 a b:
  S1 a b -->*
  S1 0 (a*2+b).
Proof.
  gen b.
  ind a Inc1.
Qed.

Lemma ROv a b:
  S0 a b 0 -->*
  S1 a b.
Proof. es. Qed.

Lemma LOv1 b:
  S1 0 b -->+
  S0 0 0 (3+b).
Proof. es. Qed.

Lemma Inc a c:
  S0 a 0 (a+(3+c)) -->*
  S0 (4+a*2) 0 c.
Proof.
  follow (Incs0 a 0 0 (3+c)).
  follow LOv0.
  finish.
Qed.

Lemma Ov a c:
  S0 (c+a) 0 (c) -->+
  S0 0 0 (3+a*2+c*2).
Proof.
  follow (Incs0 c a 0 0).
  follow ROv.
  follow Incs1.
  follow10 LOv1.
  finish.
Qed.

Definition P1 a c :=
  forall c1,
  S0 0 0 (c1+c) -->*
  S0 a 0 c1.

Lemma P1_S a c:
  P1 a c ->
  P1 (4+a*2) (3+a+c).
Proof.
  unfold P1.
  intros HP1 c1.
  follow (HP1 (c1+a+3)).
  follow (Inc a c1).
  finish.
Qed.

Lemma BigStep a c c1:
  c1 <= a ->
  P1 a c ->
  S0 0 0 (c1+c) -->+
  S0 0 0 (3+a*2).
Proof.
  unfold P1.
  intros Hc1 HP1.
  follow HP1.
  applys_eq (Ov (a-c1) c1); flia.
Qed.

Definition config(x:nat*nat*nat) := let '(a,c,c1):=x in S0 0 0 (c1+c).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (12,10,1)%nat).
  1: es.
  eapply progress_nonhalt_cond with (P:=fun '(a,c,c1) => c1<=a /\ 3+a+c<=3+a*2 /\ P1 a c).
  2: repeat split; try lia; unfold P1; es.
  intros [[a c] c1] [Hc1 [Hc1' HP1]].
  exists (4+a*2,3+a+c,(3+a*2)-(3+a+c)).
  split.
  - unfold config.
    applys_eq (BigStep _ _ _ Hc1 HP1).
    1: flia.
  - repeat split; try lia.
    apply P1_S,HP1.
Qed.

End TM19.


Module TM20.

Definition tm := Eval compute in (TM_from_str "1LB3RA3RB4LA3RA_2RA3LB---3LA1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  0inf <* [3] <* [1]^^a <* [3]^^(3+b) {{A}}> [3]^^c *> 0inf.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof. es. Qed.

Lemma Incs0 n a b c:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma LOv0 b c:
  S0 0 b (3+c) -->*
  S0 (5+b) 0 c.
Proof. es. Qed.

Definition S1 a b :=
  0inf <* [3] <* [1]^^a <* [3]^^(3+b) {{A}}> 0inf.

Lemma Inc1 a b:
  S1 (2+a) b -->*
  S1 a (3+b).
Proof. es. Qed.

Lemma Incs1 n a b:
  S1 (n*2+a) b -->*
  S1 a (n*3+b).
Proof.
  gen a b.
  ind n Inc1.
Qed.

Lemma ROv a b:
  S0 a b 0 -->*
  S1 a b.
Proof. es. Qed.

Lemma LOv1_0 b:
  S1 0 b -->+
  S0 0 0 (5+b).
Proof. es. Qed.

Lemma LOv1_1 b:
  S1 1 b -->+
  S1 (4+b) 1.
Proof. es. Qed.

Lemma Inc a c:
  S0 a 0 (a+(3+c)) -->*
  S0 (5+a*2) 0 c.
Proof.
  follow (Incs0 a 0 0 (3+c)).
  follow LOv0.
  finish.
Qed.

Lemma init:
  c0 -->*
  S0 0 0 3.
Proof. es. Qed.

Lemma Ov a c:
  S0 (c+a*4+1) 0 (c) -->+
  S0 0 0 (12+a*9+c*3).
Proof.
  follow (Incs0 c (a*2*2+1) 0 0).
  follow ROv.
  follow Incs1.
  follow10 LOv1_1.
  follow (Incs1 (2+a*3+c) 0 1).
  follow100 LOv1_0.
  finish.
Qed.

Definition P1 a c :=
  forall c1,
  S0 0 0 (c1+c) -->*
  S0 a 0 c1.

Lemma P1_S a c:
  P1 a c ->
  P1 (5+a*2) (3+a+c).
Proof.
  unfold P1.
  intros HP1 c1.
  follow (HP1 (c1+a+3)).
  follow (Inc a c1).
  finish.
Qed.

Lemma BigStep a c c1:
  P1 (c1+a*4+1) c ->
  S0 0 0 (c1+c) -->+
  S0 0 0 (12+a*9+c1*3).
Proof.
  unfold P1.
  intros HP1.
  follow HP1.
  follow10 Ov.
  finish.
Qed.


Definition a0_ i := (2^i)*2-i*2-1.
Definition c_ i := (2^i)*10-i*2-7.
Definition c1_ i := (2^i)*2+i*8-2.
Definition a_ i := c1_ i + a0_ i * 4 + 1.

Definition config i := S0 0 0 (c1_ i + c_ i).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config O).
  1: es.
  eapply progress_nonhalt_cond with (P:=fun i => 2^i >= i+1 /\ P1 (a_ i) (c_ i)).
  2: repeat split; cbn; try lia; unfold P1; es.
  intros i [Hpow2 HP1].
  exists (S i).
  repeat split.
  - unfold config.
    applys_eq (BigStep _ _ _ HP1).
    f_equal; unfold a_,a0_,c_,c1_; cbn[Nat.pow].
    lia.
  - cbn; lia.
  - applys_eq (P1_S _ _ HP1);
    f_equal; unfold a_,a0_,c_,c1_; cbn[Nat.pow];
    lia.
Qed.

End TM20.

Module TM21.

Definition tm := Eval compute in (TM_from_str "1LB3RA1RB1LA3RA_2RA4RB---4LA3LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  0inf <* [1] <* [4]^^a <* [3]^^(2+b) {{A}}> [3]^^c *> [1] *> 0inf.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof. es. Qed.

Lemma Incs0 n a b c:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma LOv0 b c:
  S0 0 b (4+c) -->*
  S0 (6+b) 0 c.
Proof. es. Qed.

Definition S1 a b :=
  0inf <* [1] <* [4]^^a <* [3]^^(2+b) {{A}}> [1] *> 0inf.

Lemma Inc1 a b:
  S1 (1+a) b -->*
  S1 a (2+b).
Proof. es. Qed.

Lemma Incs1 a b:
  S1 a b -->*
  S1 0 (a*2+b).
Proof.
  gen b.
  ind a Inc1.
Qed.

Lemma ROv a b:
  S0 a b 0 -->*
  S1 a b.
Proof. es. Qed.

Lemma LOv1 b:
  S1 0 b -->+
  S0 4 0 (3+b).
Proof. es. Qed.

Lemma Inc a c:
  S0 a 0 (a+(4+c)) -->*
  S0 (6+a*2) 0 c.
Proof.
  follow (Incs0 a 0 0 (4+c)).
  follow LOv0.
  finish.
Qed.

Lemma Ov a c:
  S0 (c+a) 0 (c) -->+
  S0 4 0 (3+a*2+c*2).
Proof.
  follow (Incs0 c a 0 0).
  follow ROv.
  follow Incs1.
  follow10 LOv1.
  finish.
Qed.

Definition P1 a c :=
  forall c1,
  S0 4 0 (c1+c) -->*
  S0 a 0 c1.

Lemma P1_S a c:
  P1 a c ->
  P1 (6+a*2) (4+a+c).
Proof.
  unfold P1.
  intros HP1 c1.
  follow (HP1 (c1+a+4)).
  follow (Inc a c1).
  finish.
Qed.

Lemma BigStep a c c1:
  c1 <= a ->
  P1 a c ->
  S0 4 0 (c1+c) -->+
  S0 4 0 (3+a*2).
Proof.
  unfold P1.
  intros Hc1 HP1.
  follow HP1.
  applys_eq (Ov (a-c1) c1); flia.
Qed.

Definition config(x:nat*nat*nat) := let '(a,c,c1):=x in S0 4 0 (c1+c).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (4,0,1)%nat).
  1: es.
  eapply progress_nonhalt_cond with (P:=fun '(a,c,c1) => c1<=a /\ 4+a+c<=3+a*2 /\ P1 a c).
  2: repeat split; try lia; unfold P1; es.
  intros [[a c] c1] [Hc1 [Hc1' HP1]].
  exists (6+a*2,4+a+c,(3+a*2)-(4+a+c)).
  split.
  - unfold config.
    applys_eq (BigStep _ _ _ Hc1 HP1).
    1: flia.
  - repeat split; try lia.
    apply P1_S,HP1.
Qed.

End TM21.


Module TM22.

Definition tm := Eval compute in (TM_from_str "1LB3RA3RB4LA3RA_2RA3LB---4LA1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  0inf <* [3] <* [1]^^a <* [3]^^(2+b) {{A}}> [3]^^c *> 0inf.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof. es. Qed.

Lemma Incs0 n a b c:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma LOv0 b c:
  S0 0 b (3+c) -->*
  S0 (5+b) 0 c.
Proof. es. Qed.

Definition S1 a b :=
  0inf <* [3] <* [1]^^a <* [3]^^(2+b) {{A}}> 0inf.

Lemma Inc1 a b:
  S1 (1+a) b -->*
  S1 a (2+b).
Proof. es. Qed.

Lemma Incs1 a b:
  S1 a b -->*
  S1 0 (a*2+b).
Proof.
  gen b.
  ind a Inc1.
Qed.

Lemma ROv a b:
  S0 a b 0 -->*
  S1 a b.
Proof. es. Qed.

Lemma LOv1 b:
  S1 0 b -->+
  S0 2 0 (4+b).
Proof. es. Qed.

Lemma Inc a c:
  S0 a 0 (a+(3+c)) -->*
  S0 (5+a*2) 0 c.
Proof.
  follow (Incs0 a 0 0 (3+c)).
  follow LOv0.
  finish.
Qed.

Lemma Ov a c:
  S0 (c+a) 0 (c) -->+
  S0 2 0 (4+a*2+c*2).
Proof.
  follow (Incs0 c a 0 0).
  follow ROv.
  follow Incs1.
  follow10 LOv1.
  finish.
Qed.

Definition P1 a c :=
  forall c1,
  S0 2 0 (c1+c) -->*
  S0 a 0 c1.

Lemma P1_S a c:
  P1 a c ->
  P1 (5+a*2) (3+a+c).
Proof.
  unfold P1.
  intros HP1 c1.
  follow (HP1 (c1+a+3)).
  follow (Inc a c1).
  finish.
Qed.

Lemma BigStep a c c1:
  c1 <= a ->
  P1 a c ->
  S0 2 0 (c1+c) -->+
  S0 2 0 (4+a*2).
Proof.
  unfold P1.
  intros Hc1 HP1.
  follow HP1.
  applys_eq (Ov (a-c1) c1); flia.
Qed.

Definition config(x:nat*nat*nat) := let '(a,c,c1):=x in S0 2 0 (c1+c).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (2,0,0)%nat).
  1: es.
  eapply progress_nonhalt_cond with (P:=fun '(a,c,c1) => c1<=a /\ 3+a+c<=4+a*2 /\ P1 a c).
  2: repeat split; try lia; unfold P1; es.
  intros [[a c] c1] [Hc1 [Hc1' HP1]].
  exists (5+a*2,3+a+c,(4+a*2)-(3+a+c)).
  split.
  - unfold config.
    applys_eq (BigStep _ _ _ Hc1 HP1).
    1: flia.
  - repeat split; try lia.
    apply P1_S,HP1.
Qed.

End TM22.


Module TM23.

Definition tm := Eval compute in (TM_from_str "1LB3RA4RB4LA3RA_2RA3LB---4LA1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  0inf <* [4] <* [1]^^a <* [3]^^(2+b) {{A}}> [3]^^c *> 0inf.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof. es. Qed.

Lemma Incs0 n a b c:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma LOv0 b c:
  S0 0 b (4+c) -->*
  S0 (6+b) 0 c.
Proof. es. Qed.

Definition S1 a b :=
  0inf <* [4] <* [1]^^a <* [3]^^(2+b) {{A}}> 0inf.

Lemma Inc1 a b:
  S1 (1+a) b -->*
  S1 a (2+b).
Proof. es. Qed.

Lemma Incs1 a b:
  S1 a b -->*
  S1 0 (a*2+b).
Proof.
  gen b.
  ind a Inc1.
Qed.

Lemma ROv a b:
  S0 a b 0 -->*
  S1 a b.
Proof. es. Qed.

Lemma LOv1 b:
  S1 0 b -->+
  S0 4 0 (3+b).
Proof. es. Qed.

Lemma Inc a c:
  S0 a 0 (a+(4+c)) -->*
  S0 (6+a*2) 0 c.
Proof.
  follow (Incs0 a 0 0 (4+c)).
  follow LOv0.
  finish.
Qed.

Lemma Ov a c:
  S0 (c+a) 0 (c) -->+
  S0 4 0 (3+a*2+c*2).
Proof.
  follow (Incs0 c a 0 0).
  follow ROv.
  follow Incs1.
  follow10 LOv1.
  finish.
Qed.

Definition P1 a c :=
  forall c1,
  S0 4 0 (c1+c) -->*
  S0 a 0 c1.

Lemma P1_S a c:
  P1 a c ->
  P1 (6+a*2) (4+a+c).
Proof.
  unfold P1.
  intros HP1 c1.
  follow (HP1 (c1+a+4)).
  follow (Inc a c1).
  finish.
Qed.

Lemma BigStep a c c1:
  c1 <= a ->
  P1 a c ->
  S0 4 0 (c1+c) -->+
  S0 4 0 (3+a*2).
Proof.
  unfold P1.
  intros Hc1 HP1.
  follow HP1.
  applys_eq (Ov (a-c1) c1); flia.
Qed.

Definition config(x:nat*nat*nat) := let '(a,c,c1):=x in S0 4 0 (c1+c).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (4,0,1)%nat).
  1: es.
  eapply progress_nonhalt_cond with (P:=fun '(a,c,c1) => c1<=a /\ 4+a+c<=3+a*2 /\ P1 a c).
  2: repeat split; try lia; unfold P1; es.
  intros [[a c] c1] [Hc1 [Hc1' HP1]].
  exists (6+a*2,4+a+c,(3+a*2)-(4+a+c)).
  split.
  - unfold config.
    applys_eq (BigStep _ _ _ Hc1 HP1).
    1: flia.
  - repeat split; try lia.
    apply P1_S,HP1.
Qed.

End TM23.


Module TM24.

Definition tm := Eval compute in (TM_from_str "1LB3RB4RA4LA3RA_2RA---3LB2LA2RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  0inf <* <[2;3] <* [2]^^a <* [3]^^(4+b) {{A}}> [3]^^c *> [1] *> 0inf.

Lemma Inc0 a b c:
  S0 (1+a) b (2+c) -->*
  S0 a (3+b) c.
Proof. es. Qed.

Lemma Incs0 n a b c:
  S0 (n+a) b (n*2+c) -->*
  S0 a (n*3+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma LOv0 b c:
  S0 0 b (6+c) -->*
  S0 (8+b) 0 c.
Proof. es. Qed.

Definition S1 a b :=
  0inf <* <[2;3] <* [2]^^a <* [3]^^(4+b) {{A}}> [1] *> 0inf.

Lemma Inc1 a b:
  S1 (1+a) b -->*
  S1 a (5+b).
Proof. es. Qed.

Lemma Incs1 a b:
  S1 a b -->*
  S1 0 (a*5+b).
Proof.
  gen b.
  ind a Inc1.
Qed.

Lemma ROv_0 a b:
  S0 a b 0 -->*
  S1 a b.
Proof. es. Qed.

Lemma ROv_1 a b:
  S0 (1+a) b 1 -->*
  S1 a (4+b).
Proof. es. Qed.

Lemma LOv1 b:
  S1 0 b -->+
  S0 4 0 (6+b).
Proof. es. Qed.

Lemma Inc a c:
  S0 a 0 (a*2+(6+c)) -->*
  S0 (8+a*3) 0 c.
Proof.
  follow (Incs0 a 0 0 (6+c)).
  follow LOv0.
  finish.
Qed.

Lemma Ov_0 a c:
  S0 (c+a) 0 (c*2+0) -->+
  S0 4 0 (6+a*5+c*3).
Proof.
  follow (Incs0 c a 0 0).
  follow ROv_0.
  follow Incs1.
  follow10 LOv1.
  finish.
Qed.

Lemma Ov_1 a c:
  S0 (c+a+1) 0 (c*2+1) -->+
  S0 4 0 (10+a*5+c*3).
Proof.
  follow (Incs0 c (1+a) 0 1).
  follow ROv_1.
  follow Incs1.
  follow10 LOv1.
  finish.
Qed.

Definition P1 a c :=
  forall c1,
  S0 4 0 (c1+c) -->*
  S0 a 0 c1.

Lemma P1_S a c:
  P1 a c ->
  P1 (8+a*3) (6+a*2+c).
Proof.
  unfold P1.
  intros HP1 c1.
  follow (HP1 (c1+a*2+6)).
  follow (Inc a c1).
  finish.
Qed.

Lemma BigStep a c c1:
  c1+1 <= a*2 ->
  P1 a c ->
  S0 4 0 (c1+c) -->+
  S0 4 0 (6+a*5-c1).
Proof.
  unfold P1.
  intros Hc1 HP1.
  follow HP1.
  pose proof (Nat.Div0.div_mod c1 2).
  pose proof (Nat.mod_upper_bound c1 2).
  remember (c1/2) as c2.
  remember (c1 mod 2) as c3.
  destruct c3 as [|[|]].
  3: lia.
  - applys_eq (Ov_0 (a-c2) c2); flia.
  - applys_eq (Ov_1 (a-c2-1) c2); flia.
Qed.

Definition config(x:nat*nat*nat) := let '(a,c,c1):=x in S0 4 0 (c1+c).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (4,0,1)%nat).
  1: es.
  eapply progress_nonhalt_cond with (P:=fun '(a,c,c1) => c1+1<=a*2 /\ 6+a*2+c<=6+a*5-c1 /\ P1 a c).
  2: repeat split; try lia; unfold P1; es.
  intros [[a c] c1] [Hc1 [Hc1' HP1]].
  exists (8+a*3,6+a*2+c,(6+a*5-c1)-(6+a*2+c)).
  split.
  - unfold config.
    applys_eq (BigStep _ _ _ Hc1 HP1).
    1: flia.
  - repeat split; try lia.
    apply P1_S,HP1.
Qed.

End TM24.


Module TM25.

Definition tm := Eval compute in (TM_from_str "1RB4LA3LA1RA1RA_2LB1RA---1LB3RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  0inf <* [1] <* [3]^^a <* [1]^^(1+b) {{A}}> [1]^^c *> [1] *> 0inf.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof. es. Qed.

Lemma Incs0 n a b c:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma LOv0 b c:
  S0 0 b (3+c) -->*
  S0 (2+b) 2 c.
Proof. es. Qed.

Definition S1 a b :=
  0inf <* [1] <* [3]^^a <* [1]^^(1+b) {{A}}> 0inf.

Lemma Inc1 a b:
  S1 (1+a) b -->*
  S1 a (3+b).
Proof. es. Qed.

Lemma Incs1 a b:
  S1 a b -->*
  S1 0 (a*3+b).
Proof.
  gen b.
  ind a Inc1.
Qed.

Lemma ROv a b:
  S0 (1+a) b 0 -->*
  S1 a (2+b).
Proof. es. Qed.

Lemma LOv1 b:
  S1 0 b -->+
  S0 1 2 (b).
Proof. es. Qed.

Lemma Inc a c:
  S0 a 2 (a+(3+c)) -->*
  S0 (4+a*2) 2 c.
Proof.
  follow (Incs0 a 0 2 (3+c)).
  follow LOv0.
  finish.
Qed.

Lemma Ov a c:
  S0 (c+(1+a)) 2 c -->+
  S0 1 2 (4+a*3+c*2).
Proof.
  follow (Incs0 c (1+a) 2 0).
  follow ROv.
  follow Incs1.
  follow10 LOv1.
  finish.
Qed.

Definition P1 a c :=
  forall c1,
  S0 1 2 (c1+c) -->*
  S0 a 2 c1.

Lemma P1_S a c:
  P1 a c ->
  P1 (4+a*2) (3+a+c).
Proof.
  unfold P1.
  intros HP1 c1.
  follow (HP1 (c1+a+3)).
  follow (Inc a c1).
  finish.
Qed.

Lemma BigStep a c c1:
  c1+1 <= a ->
  P1 a c ->
  S0 1 2 (c1+c) -->+
  S0 1 2 (1+a*3-c1).
Proof.
  unfold P1.
  intros Hc1 HP1.
  follow HP1.
  applys_eq (Ov (a-c1-1) c1); flia.
Qed.

Definition config(x:nat*nat*nat) := let '(a,c,c1):=x in S0 1 2 (c1+c).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (6,4,2)%nat).
  1: es.
  eapply progress_nonhalt_cond with (P:=fun '(a,c,c1) => c1+1<=a /\ 3+a+c<=1+a*3-c1 /\ P1 a c).
  2: repeat split; try lia; unfold P1; es.
  intros [[a c] c1] [Hc1 [Hc1' HP1]].
  exists (4+a*2,3+a+c,(1+a*3-c1)-(3+a+c)).
  split.
  - unfold config.
    applys_eq (BigStep _ _ _ Hc1 HP1).
    1: flia.
  - repeat split; try lia.
    apply P1_S,HP1.
Qed.

End TM25.


Module TM26.

Definition tm := Eval compute in (TM_from_str "1RB4LA3LA1RA3LB_2LB1RA---1LB3RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  0inf <* [1] <* [3]^^a <* [1]^^(1+b) {{A}}> [1]^^c *> [1] *> 0inf.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof. es. Qed.

Lemma Incs0 n a b c:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma LOv0 b c:
  S0 0 b (3+c) -->*
  S0 (2+b) 2 c.
Proof. es. Qed.

Definition S1 a b :=
  0inf <* [1] <* [3]^^a <* [1]^^(1+b) {{A}}> 0inf.

Lemma Inc1 a b:
  S1 (1+a) b -->*
  S1 a (3+b).
Proof. es. Qed.

Lemma Incs1 a b:
  S1 a b -->*
  S1 0 (a*3+b).
Proof.
  gen b.
  ind a Inc1.
Qed.

Lemma ROv a b:
  S0 (1+a) b 0 -->*
  S1 a (2+b).
Proof. es. Qed.

Lemma LOv1 b:
  S1 0 b -->+
  S0 1 2 (b).
Proof. es. Qed.

Lemma Inc a c:
  S0 a 2 (a+(3+c)) -->*
  S0 (4+a*2) 2 c.
Proof.
  follow (Incs0 a 0 2 (3+c)).
  follow LOv0.
  finish.
Qed.

Lemma Ov a c:
  S0 (c+(1+a)) 2 c -->+
  S0 1 2 (4+a*3+c*2).
Proof.
  follow (Incs0 c (1+a) 2 0).
  follow ROv.
  follow Incs1.
  follow10 LOv1.
  finish.
Qed.

Definition P1 a c :=
  forall c1,
  S0 1 2 (c1+c) -->*
  S0 a 2 c1.

Lemma P1_S a c:
  P1 a c ->
  P1 (4+a*2) (3+a+c).
Proof.
  unfold P1.
  intros HP1 c1.
  follow (HP1 (c1+a+3)).
  follow (Inc a c1).
  finish.
Qed.

Lemma BigStep a c c1:
  c1+1 <= a ->
  P1 a c ->
  S0 1 2 (c1+c) -->+
  S0 1 2 (1+a*3-c1).
Proof.
  unfold P1.
  intros Hc1 HP1.
  follow HP1.
  applys_eq (Ov (a-c1-1) c1); flia.
Qed.

Definition config(x:nat*nat*nat) := let '(a,c,c1):=x in S0 1 2 (c1+c).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (6,4,2)%nat).
  1: es.
  eapply progress_nonhalt_cond with (P:=fun '(a,c,c1) => c1+1<=a /\ 3+a+c<=1+a*3-c1 /\ P1 a c).
  2: repeat split; try lia; unfold P1; es.
  intros [[a c] c1] [Hc1 [Hc1' HP1]].
  exists (4+a*2,3+a+c,(1+a*3-c1)-(3+a+c)).
  split.
  - unfold config.
    applys_eq (BigStep _ _ _ Hc1 HP1).
    1: flia.
  - repeat split; try lia.
    apply P1_S,HP1.
Qed.

End TM26.


