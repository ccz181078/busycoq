From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require ES_v2.

Ltac es_v2 := ES_v2.es.
Ltac native_check_eq :=
match goal with
| |- _ = ?a => native_cast_no_check (eq_refl a)
end.

Open Scope list.

Module TM4c.

Definition tm := Eval compute in (TM_from_str "1RB1LE_1LC1RD_1LA0LB_0RB0RC_0LC1LF_---0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c d :=
  0inf <* [1]^^a <* <[1;0]^^b {{C}}> [1]^^c *> [0;1]^^d *> 0inf.

Lemma Inc1 a b c d:
  S1 (1+a) b (3+c) d -->* S1 a (2+b) c d.
Proof.
  es.
Qed.

Lemma Incs1 a b c d n:
  S1 (n+a) b (n*3+c) d -->* S1 a (n*2+b) c d.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition S2 a b c d :=
  0inf <* [1]^^a <{{B}} [0;1]^^(b) *> [0;0] *> [1]^^c *> [0;1]^^d *> 0inf.

Lemma Inc2 a b c d:
  S2 (1+a) (1+b) c d -->* S2 a b (3+c) d.
Proof.
  es.
Qed.

Lemma Incs2 a b c d n:
  S2 (n+a) (n+b) c d -->* S2 a b (n*3+c) d.
Proof.
  gen a b c.
  ind n Inc2.
Qed.

Ltac rem_sub x n :=
  let x':=fresh "x" in
  remember (x-n) as x';
  replace x with (x'+n) in * by lia.

Lemma LOv2 b c d:
  2<=c ->
  S2 0 b c d -->*
  S1 (3+b*2) 2 (c-2) d.
Proof.
  intros.
  rem_sub c 2.
  es.
Qed.

Lemma MOv2 a c d:
  4<=a ->
  S2 a 0 c d -->*
  S1 (a-4) 2 (2+c) d.
Proof.
  intros.
  rem_sub a 4.
  es.
Qed.

Lemma LOv1 b c d:
  2<=c ->
  S1 0 b c d -->*
  S1 (3+b*2) 1 (c-2) d.
Proof.
  intros.
  rem_sub c 2.
  es.
Qed.

Lemma ROv1_1_d1 a b d:
  1<=d ->
  S1 a b 1 d -->*
  S2 a b 1 (d-1).
Proof.
  intros.
  rem_sub d 1%nat.
  es.
Qed.

Lemma ROv1_1_d0 a b:
  S1 a b 1 0 -->*
  S2 a b 0 0.
Proof.
  es.
Qed.

Lemma ROv1_2 a b d:
  S1 a b 2 d -->*
  S2 a (1+b+d) 0 0.
Proof.
  es.
Qed.

Lemma ROv1_0_d0 a b:
  3<=b ->
  S1 a b 0 0 -->*
  S2 a (b-3) 3 2.
Proof.
  intros.
  rem_sub b 3.
  es.
Qed.

Lemma ROv1_0_d1 a b:
  1<=b ->
  S1 a b 0 1 -->*
  S2 a (1+b) 3 0.
Proof.
  intros.
  replace (1+b) with (2+(b-1)) by lia.
  rem_sub b 1%nat.
  es.
Qed.

Lemma ROv1_0_d2 a b:
  1<=b ->
  S1 a b 0 2 -->*
  S2 a (b-1) 9 0.
Proof.
  intros.
  rem_sub b 1%nat.
  es.
Qed.

Lemma init:
  c0 -->* S2 0 8 0 0.
Proof.
  unfold S1,S2.
  esx.
Qed.

Lemma LOv2_c0_d0 b:
  S2 0 b 0 0 -->*
  S1 (b*2) 2 2 0.
Proof.
  es.
Qed.

Lemma MOv2_a1 c d:
  S2 1 0 c d -->*
  S1 1 2 (1+c) d.
Proof.
  es.
Qed.

Lemma MOv2_a2 c d:
  halts tm (S2 2 0 c d).
Proof.
  esx.
Qed.

Lemma MOv2_a3 c d:
  S2 3 0 c d -->*
  S1 0 1 (2+c) d.
Proof.
  es.
Qed.

Lemma ROv1_0_b1_d0 a:
  1<=a ->
  S1 a 1 0 0 -->*
  S1 (a-1) 2 2 0.
Proof.
  intros.
  rem_sub a 1%nat.
  es.
Qed.

Lemma Incs1' a b c d:
  let n:=Nat.min a (c/3) in
  S1 a b c d -->*
  S1 (a-n) (b+n*2) (c-n*3) d.
Proof.
  intros n.
  follow (Incs1 (a-n) b (c-n*3) d n).
  finish.
Qed.

Lemma Incs2' a b c d:
  let n:=Nat.min a b in
  S2 a b c d -->*
  S2 (a-n) (b-n) (c+n*3) d.
Proof.
  intros n.
  follow (Incs2 (a-n) (b-n) c d n).
  finish.
Qed.

(* ~2e8 steps *)


Require Uint63.
Import Eqb.
Notation "a + b" := (Uint63.add a b).
Notation "a - b" := (Uint63.sub a b).
Notation "a '-c' b" := (Uint63.subc a b) (at level 50).
Notation "a * b" := (Uint63.mul a b).
Notation "a / b" := (Uint63.div a b).
Notation "a 'mod' b" := (Uint63.mod a b).
Notation "a '=?' b" := (Uint63.eqb a b).
Notation "a '<=?' b" := (Uint63.leb a b).
Notation "'int'" := PrimInt63.int.

Definition v0 := Eval compute in Uint63.of_Z 0.
Definition v1 := Eval compute in Uint63.of_Z 1.
Definition v2 := Eval compute in Uint63.of_Z 2.
Definition v3 := Eval compute in Uint63.of_Z 3.
Definition v4 := Eval compute in Uint63.of_Z 4.
Definition v5 := Eval compute in Uint63.of_Z 5.
Definition v6 := Eval compute in Uint63.of_Z 6.
Definition v8 := Eval compute in Uint63.of_Z 8.
Definition v9 := Eval compute in Uint63.of_Z 9.


Inductive Tp := t1 | t2 | t1x | t2x.

Fixpoint steps(a b c d:int)(T:nat)(tp:Tp) :=
match T with
| O => (a,b,c,d,tp)
| S T =>
  match tp with
  | t1 =>
    let n := Uint63.min a (c/v3) in
    steps (a-n) (b+n*v2) (c-n*v3) d T t1x
  | t2 =>
    let n := Uint63.min a b in
    steps (a-n) (b-n) (c+n*v3) d T t2x
  | t1x =>
    if c=?v0 then
      if d=?v0 then
        if v3<=?b then
          steps a (b-v3) v3 v2 T t2
        else if b=?v1 then
          if v1<=?a then
            steps (a-v1) v2 v2 v0 T t1
          else (a,b,c,d,tp)
        else (a,b,c,d,tp)
      else if d=?v1 then
        if v1<=?b then
          steps a (v1+b) v3 v0 T t2
        else (a,b,c,d,tp)
      else if d=?v2 then
        if v1<=?b then
          steps a (b-v1) v9 v0 T t2
        else (a,b,c,d,tp)
      else (a,b,c,d,tp)
    else if c=?v1 then
      if d=?v0 then
        steps a b v0 v0 T t2
      else if v1<=?d then
        steps a b v1 (d-v1) T t2
      else (a,b,c,d,tp)
    else if c=?v2 then
      steps a (v1+b+d) v0 v0 T t2
    else if a=?v0 then
      if v2<=?c then
        steps (v3+b*v2) v1 (c-v2) d T t1
      else (a,b,c,d,tp)
    else (a,b,c,d,tp)
  | t2x =>
    if a=?v0 then
      if v2<=?c then
        steps (v3+b*v2) v2 (c-v2) d T t1
      else if c=?v0 then
        if d=?v0 then
          steps (b*v2) v2 v2 v0 T t1
        else (a,b,c,d,tp)
      else (a,b,c,d,tp)
    else if b=?v0 then
      if v4<=?a then
        steps (a-v4) v2 (v2+c) d T t1
      else if a=?v3 then
        steps v0 v1 (v2+c) d T t1
      else if a=?v1 then
        steps v1 v2 (v1+c) d T t1
      else (a,b,c,d,tp)
    else (a,b,c,d,tp)
  end
end.

Definition S' a b c d t :=
match t with
| t1 | t1x => S1 a b c d
| t2 | t2x => S2 a b c d
end.

Definition to_nat(x:int):nat := Z.to_nat (Uint63.to_Z x).

Inductive WF: int->int->int->int->nat->Tp->Prop :=
| WF_intro a b c d T t
  (Ha:c0 -->* S' (to_nat a) (to_nat b) (to_nat c) (to_nat d) t)
  (Hb:(to_nat a) + (to_nat b)*2 + (to_nat c) + (to_nat d)*2 + T*1000 < 2^60):
  WF a b c d T t.

Lemma WF_mono a b c d T0 T t:
  WF a b c d T0 t ->
  T<=T0 ->
  WF a b c d T t.
Proof.
  intros.
  inverts H.
  econstructor; eauto; lia.
Qed.

Require Import ZifyN ZifyUint63 Zify.

Lemma leb_to_nat a b:
  (a <=? b) = (to_nat a <=? to_nat b)%nat.
Proof.
  rewrite leb_le.
  unfold to_nat.
  lia.
Qed.

Lemma eqb_to_nat a b:
  (a =? b) = (to_nat a =? to_nat b)%nat.
Proof.
  rewrite eqb_eq.
  unfold to_nat.
  lia.
Qed.

Lemma add_to_nat a b:
  to_nat a + to_nat b < 2^63 ->
  to_nat (a+b) = (to_nat a + to_nat b)%nat.
Proof.
  unfold to_nat.
  rewrite Uint63.add_spec.
  unfold Uint63.wB.
  unfold Uint63.size.
  intros.
  rewrite Z.mod_small; lia.
Qed.

Lemma mul_to_nat a b:
  to_nat a * to_nat b < 2^63 ->
  to_nat (a*b) = (to_nat a * to_nat b)%nat.
Proof.
  unfold to_nat.
  rewrite Uint63.mul_spec.
  unfold Uint63.wB.
  unfold Uint63.size.
  intros.
  rewrite Z.mod_small; lia.
Qed.

Lemma div_to_nat a b:
  to_nat (a/b) = (to_nat a / to_nat b)%nat.
Proof.
  unfold to_nat.
  rewrite Uint63.div_spec.
  rewrite Z2Nat.inj_div; lia.
Qed.

Lemma sub_to_nat a b:
  to_nat b <= to_nat a ->
  to_nat (a-b) = (to_nat a - to_nat b)%nat.
Proof.
  unfold to_nat.
  rewrite Uint63.sub_spec.
  unfold Uint63.wB.
  unfold Uint63.size.
  intros.
  rewrite Z.mod_small; lia.
Qed.

Lemma min_to_nat a b:
  to_nat (Uint63.min a b) = Nat.min (to_nat a) (to_nat b).
Proof.
  unfold to_nat.
  rewrite Uint63.min_spec.
  lia.
Qed.

Ltac rw_uint :=
  repeat (
  rewrite leb_to_nat in * ||
  rewrite eqb_to_nat in * ||
  rewrite div_to_nat in * ||
  rewrite min_to_nat in *).

Ltac rw_uint' :=
  repeat (
  rewrite add_to_nat in * ||
  rewrite sub_to_nat in * ||
  rewrite mul_to_nat in * ||
  rewrite div_to_nat in * ||
  rewrite min_to_nat in *).

Ltac rw_uint'_in_goal :=
  repeat (
  rewrite add_to_nat ||
  rewrite sub_to_nat ||
  rewrite mul_to_nat).

Ltac is_app x :=
  match x with
  | _ _ => idtac
  end.

Ltac simpl_to_nat_a a :=
  tryif (is_var a)+(is_app a) then fail else
  let E := fresh "E" in
  eassert (to_nat a = _) as E by (vm_compute; reflexivity);
  rewrite E in *;
  clear E.

Ltac simpl_to_nat :=
  repeat
  match goal with
  | [ H: context[to_nat ?a] |- _] =>
    simpl_to_nat_a a
  | |- context[to_nat ?a] =>
    simpl_to_nat_a a
  end.

Ltac solve_uint :=
  rw_uint';
  simpl_to_nat;
  try lia.

Ltac solve_uint_in_goal :=
  rw_uint'_in_goal;
  simpl_to_nat;
  try lia.

Ltac solve_v1 Ha Hx :=
  econstructor;
  [ follow Ha;
    repeat
    match goal with
    | [H: to_nat ?a = _ |- _] =>
      rewrite H;
      clear H
    end;
    unfold S';
    follow Hx; finish; f_equal; solve_uint
  | solve_uint ].

Ltac solve_v2 H0 :=
  inverts H0;
  eapply WF_mono; eauto; lia.

Ltac leb_eqb_cases :=
  rw_uint;
  repeat
  match goal with
  | [H: (if (?a <=? ?b)%nat then _ else _) = _ |- _] =>
    destruct (Nat.leb_spec a b)
  | [H: (if (?a =? ?b)%nat then _ else _) = _ |- _] =>
    destruct (Nat.eqb_spec a b)
  end;
  unfold v0,v1,v2,v3,v4,v5 in *.

Lemma steps_spec a b c d T T' tp a0 b0 c0 d0 tp0:
  WF a b c d (T+T') tp ->
  steps a b c d T tp =
  (a0,b0,c0,d0,tp0) ->
  WF a0 b0 c0 d0 T' tp0.
Proof.
  gen a0 b0 c0 d0 tp0.
  gen a b c d T' tp.
  induction T; cbn[steps]; intros.
  - inverts H0.
    apply H.
  - destruct tp.
    + eapply IHT.
      2: apply H0.
      inverts H.
      unfold v3 in *.
      econstructor.
      * follow Ha.
        solve_uint.
        2: pose proof (Nat.div_mod (to_nat c) 3); lia.
        unfold S'.
        apply Incs1'.
      * solve_uint;
        pose proof (Nat.div_mod (to_nat c) 3); lia.
    + eapply IHT.
      2: apply H0.
      inverts H.
      unfold v3 in *.
      econstructor.
      * follow Ha.
        solve_uint.
        unfold S'.
        apply Incs2'.
      * solve_uint.
    + leb_eqb_cases.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha ROv1_0_d0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha ROv1_0_b1_d0.
      * solve_v2 H0.
      * solve_v2 H0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha ROv1_0_d1.
      * solve_v2 H0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha ROv1_0_d2.
      * solve_v2 H0.
      * solve_v2 H0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha ROv1_1_d0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha ROv1_1_d1.
      * solve_v2 H0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha ROv1_2.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha LOv1.
      * solve_v2 H0.
      * solve_v2 H0.
    + leb_eqb_cases.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha LOv2.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha LOv2_c0_d0.
      * solve_v2 H0.
      * solve_v2 H0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha MOv2.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha MOv2_a3.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha MOv2_a1.
      * solve_v2 H0.
      * solve_v2 H0.
Qed.

Definition steps' s :=
  let '(a,b,c,d,t,T):=s in
  if (a=?v2) && (b=?v0) && (match t with t2x => true | _ => false end) then inr tt
  else if (T=?0)%N then inl s
  else inl (steps a b c d 1000 t,(T-1)%N).

Definition steps'' T :=
  N_iter_until steps' (inl (v0,v8,v0,v0,t2,(10^12)%N)) T.

Lemma steps''_spec T:
  match steps'' T with
  | inl (a,b,c,d,t,T0) =>
    WF a b c d (N.to_nat (T0*1000)) t
  | inr _ => halts tm c0
  end.
Proof.
  eapply N_iter_until_spec
  with
  (P:=fun s => 
  let '(a,b,c,d,t,T0):=s in
    WF a b c d (N.to_nat (T0*1000)) t)
  (P':=fun _ => halts tm c0).
  - intros [[[[[a b] c] d] t] T0] HWF.
    unfold steps'.
    destruct ((a=?v2)&&(b=?v0)&&(match t with t2x => true | _ => false end)) eqn:E.
    + repeat rewrite and_true_iff in E.
      destruct E as [[E1 E2] E3].
      destruct t; try congruence.
      rw_uint.
      rewrite Nat.eqb_eq in *.
      inverts HWF.
      eapply halts_evstep.
      2: apply Ha.
      rewrite E1,E2.
      apply MOv2_a2.
    + destruct (N.eqb_spec T0 N0).
      1: apply HWF.
      destruct (steps a b c d 1000 t) as [[[[a0 b0] c1] d0] t0] eqn:E'.
      eapply steps_spec in E'.
      1: apply E'.
      applys_eq HWF; lia.
  - econstructor.
    + apply init.
    + simpl_to_nat; lia.
Qed.

Lemma steps''_spec' T:
  steps'' T = inr tt ->
  halts tm c0.
Proof.
  intros H.
  epose proof (steps''_spec T) as I.
  rewrite H in I.
  apply I.
Qed.

Lemma halt: halts tm c0.
Proof.
  apply (steps''_spec' (10^9)).
  native_check_eq.
Time Qed.

End TM4c.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LA_1RA1LE_0RA0RB_0LF0RA_---0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1]^^a <* <[1;0]^^b {{A}}> [1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 (1+a) b (3+c) -->* S1 a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs1 a b c n:
  S1 (n+a) b (n*3+c) -->* S1 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition S2 a b c :=
  0inf <* [1]^^a <{{A}} [0;1]^^(b) *> [0;0] *> [1]^^c *> 0inf.

Lemma Inc2 a b c:
  S2 (1+a) (1+b) c -->* S2 a b (3+c).
Proof.
  es.
Qed.

Lemma Incs2 a b c n:
  S2 (n+a) (n+b) c -->* S2 a b (n*3+c).
Proof.
  gen a b c.
  ind n Inc2.
Qed.

Ltac rem_sub x n :=
  let x':=fresh "x" in
  remember (x-n) as x';
  replace x with (x'+n) in * by lia.

Lemma LOv2 b c:
  S2 0 b c -->*
  S1 (3+b*2) 1 c.
Proof.
  es.
Qed.

Lemma MOv2 a c:
  3<=a ->
  S2 a 0 c -->*
  S1 (a-3) 1 (3+c).
Proof.
  intros.
  rem_sub a 3.
  es.
Qed.

Lemma MOv2_2 c:
  S2 2 0 c -->*
  S1 0 0 (3+c).
Proof.
  es.
Qed.

Lemma MOv2_1 c:
  halts tm (S2 1 0 c).
Proof.
  unfold S1,S2.
  esx.
Qed.

Lemma LOv1 b c:
  3<=c ->
  S1 0 b c -->*
  S1 (5+b*2) 0 (c-2).
Proof.
  intros.
  replace (c-2) with (1+(c-3)) by lia.
  rem_sub c 3.
  unfold S1.
  es_v2.
Qed.

Lemma ROv1_2 a b:
  S1 a b 2 -->*
  S2 a (2+b) 0.
Proof.
  es.
Qed.

Lemma ROv1_1 a b:
  1<=b ->
  S1 a b 1 -->*
  S2 a (b-1) 3.
Proof.
  intros.
  rem_sub b 1%nat.
  es.
Qed.

Lemma ROv1_1_b0 a:
  2<=a ->
  S1 a 0 1 -->*
  S1 (a-2) 1 3.
Proof.
  intros.
  rem_sub a 2.
  es.
Qed.

Lemma ROv1_0 a b:
  2<=b ->
  S1 a b 0 -->*
  S2 a (b-2) 3.
Proof.
  intros.
  rem_sub b 2.
  es.
Qed.

Lemma ROv1_0_b1 a:
  2<=a ->
  S1 a 1 0 -->*
  S1 (a-2) 1 3.
Proof.
  intros.
  rem_sub a 2.
  es.
Qed.

Lemma init:
  c0 -->* S1 5 1 3.
Proof.
  unfold S1,S2.
  esx.
Qed.

Lemma Incs1' a b c:
  let n:=Nat.min a (c/3) in
  S1 a b c -->*
  S1 (a-n) (b+n*2) (c-n*3).
Proof.
  intros n.
  follow (Incs1 (a-n) b (c-n*3) n).
  finish.
Qed.

Lemma Incs2' a b c:
  let n:=Nat.min a b in
  S2 a b c -->*
  S2 (a-n) (b-n) (c+n*3).
Proof.
  intros n.
  follow (Incs2 (a-n) (b-n) c n).
  finish.
Qed.

(* ~3e8 steps *)

Require Uint63.
Import Eqb.
Notation "a + b" := (Uint63.add a b).
Notation "a - b" := (Uint63.sub a b).
Notation "a '-c' b" := (Uint63.subc a b) (at level 50).
Notation "a * b" := (Uint63.mul a b).
Notation "a / b" := (Uint63.div a b).
Notation "a 'mod' b" := (Uint63.mod a b).
Notation "a '=?' b" := (Uint63.eqb a b).
Notation "a '<=?' b" := (Uint63.leb a b).
Notation "'int'" := PrimInt63.int.

Definition v0 := Eval compute in Uint63.of_Z 0.
Definition v1 := Eval compute in Uint63.of_Z 1.
Definition v2 := Eval compute in Uint63.of_Z 2.
Definition v3 := Eval compute in Uint63.of_Z 3.
Definition v4 := Eval compute in Uint63.of_Z 4.
Definition v5 := Eval compute in Uint63.of_Z 5.


Inductive Tp := t1 | t2 | t1x | t2x.

Fixpoint steps(a b c:int)(T:nat)(tp:Tp) :=
match T with
| O => (a,b,c,tp)
| S T =>
  match tp with
  | t1 =>
    let n := Uint63.min a (c/v3) in
    steps (a-n) (b+n*v2) (c-n*v3) T t1x
  | t2 =>
    let n := Uint63.min a b in
    steps (a-n) (b-n) (c+n*v3) T t2x
  | t1x =>
    if c=?v0 then
      if v2<=?b then
        steps a (b-v2) v3 T t2
      else if b=?v1 then
        if v2<=?a then
          steps (a-v2) v1 v3 T t1
        else (a,b,c,tp)
      else (a,b,c,tp)
    else if v3<=?c then
      if a=?v0 then
        steps (v5+b*v2) v0 (c-v2) T t1
      else (a,b,c,tp)
    else if c=?v1 then
      if v1<=?b then
        steps a (b-v1) v3 T t2
      else if b=?v0 then
        if v2<=?a then
          steps (a-v2) v1 v3 T t1
        else (a,b,c,tp)
      else (a,b,c,tp)
    else if c=?v2 then
      steps a (v2+b) v0 T t2
    else (a,b,c,tp)
  | t2x =>
    if b=?v0 then
      if v3<=?a then
        steps (a-v3) v1 (v3+c) T t1
      else if a=?v2 then
        steps v0 v0 (v3+c) T t1
      else if a=?v0 then
        steps v3 v1 c T t1
      else (a,b,c,tp)
    else if a=?v0 then
      steps (v3+b*v2) v1 c T t1
    else (a,b,c,tp)
  end
end.

Definition S' a b c t :=
match t with
| t1 | t1x => S1 a b c
| t2 | t2x => S2 a b c
end.

Definition to_nat(x:int):nat := Z.to_nat (Uint63.to_Z x).

Inductive WF: int->int->int->nat->Tp->Prop :=
| WF_intro a b c T t
  (Ha:c0 -->* S' (to_nat a) (to_nat b) (to_nat c) t)
  (Hb:(to_nat a) + (to_nat b)*2 + (to_nat c) + T*1000 < 2^60):
  WF a b c T t.

Lemma WF_mono a b c T0 T t:
  WF a b c T0 t ->
  T<=T0 ->
  WF a b c T t.
Proof.
  intros.
  inverts H.
  econstructor; eauto; lia.
Qed.

Require Import ZifyN ZifyUint63 Zify.

Lemma leb_to_nat a b:
  (a <=? b) = (to_nat a <=? to_nat b)%nat.
Proof.
  rewrite leb_le.
  unfold to_nat.
  lia.
Qed.

Lemma eqb_to_nat a b:
  (a =? b) = (to_nat a =? to_nat b)%nat.
Proof.
  rewrite eqb_eq.
  unfold to_nat.
  lia.
Qed.

Lemma add_to_nat a b:
  to_nat a + to_nat b < 2^63 ->
  to_nat (a+b) = (to_nat a + to_nat b)%nat.
Proof.
  unfold to_nat.
  rewrite Uint63.add_spec.
  unfold Uint63.wB.
  unfold Uint63.size.
  intros.
  rewrite Z.mod_small; lia.
Qed.

Lemma mul_to_nat a b:
  to_nat a * to_nat b < 2^63 ->
  to_nat (a*b) = (to_nat a * to_nat b)%nat.
Proof.
  unfold to_nat.
  rewrite Uint63.mul_spec.
  unfold Uint63.wB.
  unfold Uint63.size.
  intros.
  rewrite Z.mod_small; lia.
Qed.

Lemma div_to_nat a b:
  to_nat (a/b) = (to_nat a / to_nat b)%nat.
Proof.
  unfold to_nat.
  rewrite Uint63.div_spec.
  rewrite Z2Nat.inj_div; lia.
Qed.

Lemma sub_to_nat a b:
  to_nat b <= to_nat a ->
  to_nat (a-b) = (to_nat a - to_nat b)%nat.
Proof.
  unfold to_nat.
  rewrite Uint63.sub_spec.
  unfold Uint63.wB.
  unfold Uint63.size.
  intros.
  rewrite Z.mod_small; lia.
Qed.

Lemma min_to_nat a b:
  to_nat (Uint63.min a b) = Nat.min (to_nat a) (to_nat b).
Proof.
  unfold to_nat.
  rewrite Uint63.min_spec.
  lia.
Qed.

Ltac rw_uint :=
  repeat (
  rewrite leb_to_nat in * ||
  rewrite eqb_to_nat in * ||
  rewrite div_to_nat in * ||
  rewrite min_to_nat in *).

Ltac rw_uint' :=
  repeat (
  rewrite add_to_nat in * ||
  rewrite sub_to_nat in * ||
  rewrite mul_to_nat in * ||
  rewrite div_to_nat in * ||
  rewrite min_to_nat in *).

Ltac rw_uint'_in_goal :=
  repeat (
  rewrite add_to_nat ||
  rewrite sub_to_nat ||
  rewrite mul_to_nat).

Ltac is_app x :=
  match x with
  | _ _ => idtac
  end.

Ltac simpl_to_nat_a a :=
  tryif (is_var a)+(is_app a) then fail else
  let E := fresh "E" in
  eassert (to_nat a = _) as E by (vm_compute; reflexivity);
  rewrite E in *;
  clear E.

Ltac simpl_to_nat :=
  repeat
  match goal with
  | [ H: context[to_nat ?a] |- _] =>
    simpl_to_nat_a a
  | |- context[to_nat ?a] =>
    simpl_to_nat_a a
  end.

Ltac solve_uint :=
  rw_uint';
  simpl_to_nat;
  try lia.

Ltac solve_uint_in_goal :=
  rw_uint'_in_goal;
  simpl_to_nat;
  try lia.

Ltac solve_v1 Ha Hx :=
  econstructor;
  [ follow Ha;
    repeat
    match goal with
    | [H: to_nat ?a = _ |- _] =>
      rewrite H;
      clear H
    end;
    unfold S';
    follow Hx; finish; f_equal; solve_uint
  | solve_uint ].

Ltac solve_v2 H0 :=
  inverts H0;
  eapply WF_mono; eauto; lia.

Ltac leb_eqb_cases :=
  rw_uint;
  repeat
  match goal with
  | [H: (if (?a <=? ?b)%nat then _ else _) = _ |- _] =>
    destruct (Nat.leb_spec a b)
  | [H: (if (?a =? ?b)%nat then _ else _) = _ |- _] =>
    destruct (Nat.eqb_spec a b)
  end;
  unfold v0,v1,v2,v3,v4,v5 in *.

Lemma steps_spec a b c T T' tp a0 b0 c0 tp0:
  WF a b c (T+T') tp ->
  steps a b c T tp =
  (a0,b0,c0,tp0) ->
  WF a0 b0 c0 T' tp0.
Proof.
  gen a0 b0 c0 tp0.
  gen a b c T' tp.
  induction T; cbn[steps]; intros.
  - inverts H0.
    apply H.
  - destruct tp.
    + eapply IHT.
      2: apply H0.
      inverts H.
      unfold v3 in *.
      econstructor.
      * follow Ha.
        solve_uint.
        2: pose proof (Nat.div_mod (to_nat c) 3); lia.
        unfold S'.
        apply Incs1'.
      * solve_uint;
        pose proof (Nat.div_mod (to_nat c) 3); lia.
    + eapply IHT.
      2: apply H0.
      inverts H.
      unfold v3 in *.
      econstructor.
      * follow Ha.
        solve_uint.
        unfold S'.
        apply Incs2'.
      * solve_uint.
    + leb_eqb_cases.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha ROv1_0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha ROv1_0_b1.
      * solve_v2 H0.
      * solve_v2 H0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha LOv1.
      * solve_v2 H0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha ROv1_1.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha ROv1_1_b0.
      * solve_v2 H0.
      * solve_v2 H0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha ROv1_2.
      * solve_v2 H0.
    + leb_eqb_cases.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha MOv2.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha MOv2_2.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha LOv2.
      * solve_v2 H0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha LOv2.
      * solve_v2 H0.
Qed.

Definition steps' s :=
  let '(a,b,c,t,T):=s in
  if (a=?v1) && (b=?v0) && (match t with t2x => true | _ => false end) then inr tt
  else if (T=?0)%N then inl s
  else inl (steps a b c 1000 t,(T-1)%N).

Definition steps'' T :=
N_iter_until steps' (inl (v5,v1,v3,t1,(10^12)%N)) T.

Lemma steps''_spec T:
  match steps'' T with
  | inl (a,b,c,t,T0) =>
    WF a b c (N.to_nat (T0*1000)) t
  | inr _ => halts tm c0
  end.
Proof.
  eapply N_iter_until_spec
  with
  (P:=fun s => 
  let '(a,b,c,t,T0):=s in
    WF a b c (N.to_nat (T0*1000)) t)
  (P':=fun _ => halts tm c0).
  - intros [[[[a b] c] t] T0] HWF.
    unfold steps'.
    destruct ((a=?v1)&&(b=?v0)&&(match t with t2x => true | _ => false end)) eqn:E.
    + repeat rewrite and_true_iff in E.
      destruct E as [[E1 E2] E3].
      destruct t; try congruence.
      rw_uint.
      rewrite Nat.eqb_eq in *.
      inverts HWF.
      eapply halts_evstep.
      2: apply Ha.
      rewrite E1,E2.
      apply MOv2_1.
    + destruct (N.eqb_spec T0 N0).
      1: apply HWF.
      destruct (steps a b c 1000 t) as [[[a0 b0] c1] t0] eqn:E'.
      eapply steps_spec in E'.
      1: apply E'.
      applys_eq HWF; lia.
  - econstructor.
    + apply init.
    + simpl_to_nat; lia.
Qed.

Lemma steps''_spec' T:
  steps'' T = inr tt ->
  halts tm c0.
Proof.
  intros H.
  epose proof (steps''_spec T) as I.
  rewrite H in I.
  apply I.
Qed.

Lemma halt: halts tm c0.
Proof.
  apply (steps''_spec' (10^9)).
  native_check_eq.
Time Qed.

End TM4.


Module TM5b.

Definition tm := Eval compute in (TM_from_str "1LB1LD_0RC0LD_1RD1RC_1LA1RE_0LE0LF_---0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1]^^a <{{D}} [1;1]^^b *> [0] *> [1;1;1;1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 (2+a) (1+b) c -->* S1 a b (1+c).
Proof.
  es.
Qed.

Lemma Incs1 a b c n:
  S1 (n*2+a) (n+b) c -->* S1 a b (n+c).
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Ltac rem_sub x n :=
  let x':=fresh "x" in
  remember (x-n) as x';
  replace x with (x'+n) in * by lia.

Lemma MOv a c:
  3<=a ->
  S1 a 0 c -->*
  S1 (a-3) (2+c*2) 0.
Proof.
  intros.
  rem_sub a 3.
  es.
Qed.

Lemma MOv_2 c:
  S1 2 0 c -->*
  S1 0 (1+c*2) 0.
Proof.
  es.
Qed.

Lemma LOv_1 b c:
  2<=b ->
  S1 1 b c -->*
  S1 (b*2-2) (3+c*2) 0.
Proof.
  intros.
  rem_sub b 2.
  replace ((x+2)*2-2) with (2+x*2) by lia.
  es.
Qed.

Lemma LOv_0 b c:
  S1 0 b c -->*
  S1 (2+b*2) (1+c*2) 0.
Proof.
  es.
Qed.

Lemma LOv_1_b1 c:
  S1 1 1 c -->*
  S1 2 0 c.
Proof.
  es.
Qed.

Lemma LOv_1_b0 c:
  halts tm (S1 1 0 c).
Proof.
  unfold S1.
  esx.
Qed.

Lemma init:
  c0 -->*
  S1 3 4 0.
Proof.
  unfold S1.
  esx.
Qed.

Lemma Incs1' a b c:
  let n:=Nat.min (a/2) b in
  S1 a b c -->*
  S1 (a-n*2) (b-n) (c+n).
Proof.
  intros n.
  follow (Incs1 (a-n*2) (b-n) c n).
  finish.
Qed.

(* ~2.5e8 steps *)

Require Uint63.
Import Eqb.
Notation "a + b" := (Uint63.add a b).
Notation "a - b" := (Uint63.sub a b).
Notation "a '-c' b" := (Uint63.subc a b) (at level 50).
Notation "a * b" := (Uint63.mul a b).
Notation "a / b" := (Uint63.div a b).
Notation "a 'mod' b" := (Uint63.mod a b).
Notation "a '=?' b" := (Uint63.eqb a b).
Notation "a '<=?' b" := (Uint63.leb a b).
Notation "'int'" := PrimInt63.int.

Definition v0 := Eval compute in Uint63.of_Z 0.
Definition v1 := Eval compute in Uint63.of_Z 1.
Definition v2 := Eval compute in Uint63.of_Z 2.
Definition v3 := Eval compute in Uint63.of_Z 3.
Definition v4 := Eval compute in Uint63.of_Z 4.
Definition v5 := Eval compute in Uint63.of_Z 5.


Inductive Tp := t1 | t1x.

Fixpoint steps(a b c:int)(T:nat)(tp:Tp) :=
match T with
| O => (a,b,c,tp)
| S T =>
  match tp with
  | t1 =>
    let n := Uint63.min (a/v2) b in
    steps (a-n*v2) (b-n) (c+n) T t1x
  | t1x =>
    if a=?v0 then
      steps (v2+b*v2) (v1+c*v2) v0 T t1
    else if a=?v1 then
      if b=?v1 then
        steps v2 v0 c T t1
      else if v2<=?b then
        steps (b*v2-v2) (v3+c*v2) v0 T t1
      else (a,b,c,tp)
    else if b=?v0 then
      if a=?v2 then
        steps v0 (v1+c*v2) v0 T t1
      else if v3<=?a then
        steps (a-v3) (v2+c*v2) v0 T t1
      else (a,b,c,tp)
    else (a,b,c,tp)
  end
end.

Definition S' a b c t :=
match t with
| t1 | t1x => S1 a b c
end.

Definition to_nat(x:int):nat := Z.to_nat (Uint63.to_Z x).

Inductive WF: int->int->int->nat->Tp->Prop :=
| WF_intro a b c T t
  (Ha:c0 -->* S' (to_nat a) (to_nat b) (to_nat c) t)
  (Hb:(to_nat a) + (to_nat b)*2 + (to_nat c)*4 + T*1000 < 2^60):
  WF a b c T t.

Lemma WF_mono a b c T0 T t:
  WF a b c T0 t ->
  T<=T0 ->
  WF a b c T t.
Proof.
  intros.
  inverts H.
  econstructor; eauto; lia.
Qed.

Require Import ZifyN ZifyUint63 Zify.

Lemma leb_to_nat a b:
  (a <=? b) = (to_nat a <=? to_nat b)%nat.
Proof.
  rewrite leb_le.
  unfold to_nat.
  lia.
Qed.

Lemma eqb_to_nat a b:
  (a =? b) = (to_nat a =? to_nat b)%nat.
Proof.
  rewrite eqb_eq.
  unfold to_nat.
  lia.
Qed.

Lemma add_to_nat a b:
  to_nat a + to_nat b < 2^63 ->
  to_nat (a+b) = (to_nat a + to_nat b)%nat.
Proof.
  unfold to_nat.
  rewrite Uint63.add_spec.
  unfold Uint63.wB.
  unfold Uint63.size.
  intros.
  rewrite Z.mod_small; lia.
Qed.

Lemma mul_to_nat a b:
  to_nat a * to_nat b < 2^63 ->
  to_nat (a*b) = (to_nat a * to_nat b)%nat.
Proof.
  unfold to_nat.
  rewrite Uint63.mul_spec.
  unfold Uint63.wB.
  unfold Uint63.size.
  intros.
  rewrite Z.mod_small; lia.
Qed.

Lemma div_to_nat a b:
  to_nat (a/b) = (to_nat a / to_nat b)%nat.
Proof.
  unfold to_nat.
  rewrite Uint63.div_spec.
  rewrite Z2Nat.inj_div; lia.
Qed.

Lemma sub_to_nat a b:
  to_nat b <= to_nat a ->
  to_nat (a-b) = (to_nat a - to_nat b)%nat.
Proof.
  unfold to_nat.
  rewrite Uint63.sub_spec.
  unfold Uint63.wB.
  unfold Uint63.size.
  intros.
  rewrite Z.mod_small; lia.
Qed.

Lemma min_to_nat a b:
  to_nat (Uint63.min a b) = Nat.min (to_nat a) (to_nat b).
Proof.
  unfold to_nat.
  rewrite Uint63.min_spec.
  lia.
Qed.

Ltac rw_uint :=
  repeat (
  rewrite leb_to_nat in * ||
  rewrite eqb_to_nat in * ||
  rewrite div_to_nat in * ||
  rewrite min_to_nat in *).

Ltac rw_uint' :=
  repeat (
  rewrite add_to_nat in * ||
  rewrite sub_to_nat in * ||
  rewrite mul_to_nat in * ||
  rewrite div_to_nat in * ||
  rewrite min_to_nat in *).

Ltac rw_uint'_in_goal :=
  repeat (
  rewrite add_to_nat ||
  rewrite sub_to_nat ||
  rewrite mul_to_nat).

Ltac is_app x :=
  match x with
  | _ _ => idtac
  end.

Ltac simpl_to_nat_a a :=
  tryif (is_var a)+(is_app a) then fail else
  let E := fresh "E" in
  eassert (to_nat a = _) as E by (vm_compute; reflexivity);
  rewrite E in *;
  clear E.

Ltac simpl_to_nat :=
  repeat
  match goal with
  | [ H: context[to_nat ?a] |- _] =>
    simpl_to_nat_a a
  | |- context[to_nat ?a] =>
    simpl_to_nat_a a
  end.

Ltac solve_uint :=
  rw_uint';
  simpl_to_nat;
  try lia.

Ltac solve_uint_in_goal :=
  rw_uint'_in_goal;
  simpl_to_nat;
  try lia.

Ltac solve_v1 Ha Hx :=
  econstructor;
  [ follow Ha;
    repeat
    match goal with
    | [H: to_nat ?a = _ |- _] =>
      rewrite H;
      clear H
    end;
    unfold S';
    follow Hx; finish; f_equal; solve_uint
  | solve_uint ].

Ltac solve_v2 H0 :=
  inverts H0;
  eapply WF_mono; eauto; lia.

Ltac leb_eqb_cases :=
  rw_uint;
  repeat
  match goal with
  | [H: (if (?a <=? ?b)%nat then _ else _) = _ |- _] =>
    destruct (Nat.leb_spec a b)
  | [H: (if (?a =? ?b)%nat then _ else _) = _ |- _] =>
    destruct (Nat.eqb_spec a b)
  end;
  unfold v0,v1,v2,v3,v4,v5 in *.

Lemma steps_spec a b c T T' tp a0 b0 c0 tp0:
  WF a b c (T+T') tp ->
  steps a b c T tp =
  (a0,b0,c0,tp0) ->
  WF a0 b0 c0 T' tp0.
Proof.
  gen a0 b0 c0 tp0.
  gen a b c T' tp.
  induction T; cbn[steps]; intros.
  - inverts H0.
    apply H.
  - destruct tp.
    + eapply IHT.
      2: apply H0.
      inverts H.
      unfold v3 in *.
      econstructor.
      * follow Ha.
        solve_uint.
        2: pose proof (Nat.div_mod (to_nat a) 2); lia.
        unfold S'.
        apply Incs1'.
      * solve_uint;
        pose proof (Nat.div_mod (to_nat a) 2); lia.
    + leb_eqb_cases.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha LOv_0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha LOv_1_b1.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha LOv_1.
      * solve_v2 H0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha MOv_2.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha MOv.
      * solve_v2 H0.
      * solve_v2 H0.
Qed.

Definition steps' s :=
  let '(a,b,c,t,T):=s in
  if (a=?v1) && (b=?v0) && (match t with t1x => true | _ => false end) then inr tt
  else if (T=?0)%N then inl s
  else inl (steps a b c 1000 t,(T-1)%N).

Definition steps'' T :=
N_iter_until steps' (inl (v3,v4,v0,t1,(10^12)%N)) T.

Lemma steps''_spec T:
  match steps'' T with
  | inl (a,b,c,t,T0) =>
    WF a b c (N.to_nat (T0*1000)) t
  | inr _ => halts tm c0
  end.
Proof.
  eapply N_iter_until_spec
  with
  (P:=fun s => 
  let '(a,b,c,t,T0):=s in
    WF a b c (N.to_nat (T0*1000)) t)
  (P':=fun _ => halts tm c0).
  - intros [[[[a b] c] t] T0] HWF.
    unfold steps'.
    destruct ((a=?v1)&&(b=?v0)&&(match t with t1x => true | _ => false end)) eqn:E.
    + repeat rewrite and_true_iff in E.
      destruct E as [[E1 E2] E3].
      destruct t; try congruence.
      rw_uint.
      rewrite Nat.eqb_eq in *.
      inverts HWF.
      eapply halts_evstep.
      2: apply Ha.
      rewrite E1,E2.
      apply LOv_1_b0.
    + destruct (N.eqb_spec T0 N0).
      1: apply HWF.
      destruct (steps a b c 1000 t) as [[[a0 b0] c1] t0] eqn:E'.
      eapply steps_spec in E'.
      1: apply E'.
      applys_eq HWF; lia.
  - econstructor.
    + apply init.
    + simpl_to_nat; lia.
Qed.

Lemma steps''_spec' T:
  steps'' T = inr tt ->
  halts tm c0.
Proof.
  intros H.
  epose proof (steps''_spec T) as I.
  rewrite H in I.
  apply I.
Qed.

Lemma halt: halts tm c0.
Proof.
  apply (steps''_spec' (10^9)).
  native_check_eq.
Time Qed.

End TM5b.


Module TM6.
Definition tm := Eval compute in (TM_from_str "1RB1LC_1LC1RF_0RD0LB_0RE1LE_1LA---_0RB0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1]^^a <{{B}} [0;1]^^b *> [1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 (1+a) b (3+c) -->*
  S1 a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs1 a b c n:
  S1 (n+a) b (n*3+c) -->*
  S1 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition S2 a b c :=
  0inf <* [1]^^a <{{B}} [0;1]^^b *> [1]^^c *> [0;1;1;1] *> 0inf.

Lemma Inc2 a b c:
  S2 (1+a) b (3+c) -->*
  S2 a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 a b c n:
  S2 (n+a) b (n*3+c) -->*
  S2 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc2.
Qed.

Ltac rem_sub x n :=
  let x':=fresh "x" in
  remember (x-n) as x';
  replace x with (x'+n) in * by lia.

Lemma LOv1 b c:
  2<=c ->
  S1 0 b c -->*
  S1 (1+b*2) 2 (c-2).
Proof.
  intros.
  rem_sub c 2.
  es.
Qed.

Lemma LOv2 b c:
  2<=c ->
  S2 0 b c -->*
  S2 (1+b*2) 2 (c-2).
Proof.
  intros.
  rem_sub c 2.
  es.
Qed.

Lemma ROv1_0 a b:
  2<=a ->
  S1 a b 0 -->*
  S1 (a-2) 1 (2+b*2).
Proof.
  intros.
  rem_sub a 2.
  es.
Qed.

Lemma ROv1_2 a b:
  1<=a ->
  S1 a b 2 -->*
  S1 (a-1) (1+b) 0.
Proof.
  intros.
  rem_sub a 1%nat.
  es.
Qed.

Lemma ROv1_1 a b:
  2<=a ->
  S1 a b 1 -->*
  S2 (a-2) 1 (2+b*2).
Proof.
  intros.
  rem_sub a 2.
  es.
Qed.

Lemma ROv2_0 a b:
  S2 a b 0 -->*
  S1 a (1+b) 2.
Proof.
  es.
Qed.

Lemma ROv2_2 a b:
  3<=a ->
  S2 a b 2 -->*
  S1 (a-3) 1 (7+b*2).
Proof.
  intros.
  rem_sub a 3.
  es.
Qed.

Lemma ROv2_1 a b:
  1<=a ->
  S2 a b 1 -->*
  S1 (a-1) (1+b) 6.
Proof.
  intros.
  rem_sub a 1%nat.
  es.
Qed.

Lemma init:
  c0 -->*
  S1 0 4 4.
Proof.
  unfold S1.
  esx.
Qed.

Lemma LOv1_c0 b:
  S1 0 b 0 -->*
  S2 (b*2) 1 2.
Proof.
  es.
Qed.

Lemma ROv1_0_a1 b:
  S1 1 b 0 -->*
  S1 1 2 (b*2).
Proof.
  es.
Qed.

Lemma ROv2_2_a2 b:
  S2 2 b 2 -->*
  S1 1 2 (5+b*2).
Proof.
  es.
Qed.

Lemma LOv1_c1 b:
  S1 0 b 1 -->*
  S1 (1+b*2) 1 0.
Proof.
  es.
Qed.

Lemma ROv2_2_a1 b:
  halts tm (S2 1 b 2).
Proof.
  esx.
Qed.

Lemma Incs1' a b c:
  let n:=Nat.min a (c/3) in
  S1 a b c -->*
  S1 (a-n) (b+n*2) (c-n*3).
Proof.
  intros n.
  follow (Incs1 (a-n) b (c-n*3) n).
  finish.
Qed.

Lemma Incs2' a b c:
  let n:=Nat.min a (c/3) in
  S2 a b c -->*
  S2 (a-n) (b+n*2) (c-n*3).
Proof.
  intros n.
  follow (Incs2 (a-n) b (c-n*3) n).
  finish.
Qed.

(* ~2e9 steps *)

Require Uint63.
Import Eqb.
Notation "a + b" := (Uint63.add a b).
Notation "a - b" := (Uint63.sub a b).
Notation "a '-c' b" := (Uint63.subc a b) (at level 50).
Notation "a * b" := (Uint63.mul a b).
Notation "a / b" := (Uint63.div a b).
Notation "a 'mod' b" := (Uint63.mod a b).
Notation "a '=?' b" := (Uint63.eqb a b).
Notation "a '<=?' b" := (Uint63.leb a b).
Notation "'int'" := PrimInt63.int.

Definition v0 := Eval compute in Uint63.of_Z 0.
Definition v1 := Eval compute in Uint63.of_Z 1.
Definition v2 := Eval compute in Uint63.of_Z 2.
Definition v3 := Eval compute in Uint63.of_Z 3.
Definition v4 := Eval compute in Uint63.of_Z 4.
Definition v5 := Eval compute in Uint63.of_Z 5.
Definition v6 := Eval compute in Uint63.of_Z 6.
Definition v7 := Eval compute in Uint63.of_Z 7.


Inductive Tp := t1 | t2 | t1x | t2x.

Fixpoint steps(a b c:int)(T:nat)(tp:Tp) :=
match T with
| O => (a,b,c,tp)
| S T =>
  match tp with
  | t1 =>
    let n := Uint63.min a (c/v3) in
    steps (a-n) (b+n*v2) (c-n*v3) T t1x
  | t2 =>
    let n := Uint63.min a (c/v3) in
    steps (a-n) (b+n*v2) (c-n*v3) T t2x
  | t1x =>
    if a=?v0 then
      if v2<=?c then
        steps (v1+b*v2) v2 (c-v2) T t1
      else if c=?v1 then
        steps (v1+b*v2) v1 v0 T t1
      else if c=?v0 then
        steps (b*v2) v1 v2 T t2
      else (a,b,c,tp)
    else if c=?v0 then
      if v2<=?a then
        steps (a-v2) v1 (v2+b*v2) T t1
      else if a=?v1 then
        steps v1 v2 (b*v2) T t1
      else (a,b,c,tp)
    else if c=?v1 then
      if v2<=?a then
        steps (a-v2) v1 (v2+b*v2) T t2
      else (a,b,c,tp)
    else if c=?v2 then
      if v1<=?a then
        steps (a-v1) (v1+b) v0 T t1x
      else (a,b,c,tp)
    else (a,b,c,tp)
  | t2x =>
    if a=?v0 then
      if v2<=?c then
        steps (v1+b*v2) v2 (c-v2) T t2
      else if c=?v0 then
        steps v0 (v1+b) v2 T t1
      else (a,b,c,tp)
    else if c=?v2 then
      if v3<=?a then
        steps (a-v3) v1 (v7+b*v2) T t1
      else if a=?v2 then
        steps v1 v2 (v5+b*v2) T t1
      else (a,b,c,tp)
    else if c=?v0 then
      steps a (v1+b) v2 T t1x
    else if c=?v1 then
      if v1<=?a then
        steps (a-v1) (v1+b) v6 T t1
      else (a,b,c,tp)
    else (a,b,c,tp)
  end
end.

Definition S' a b c t :=
match t with
| t1 | t1x => S1 a b c
| t2 | t2x => S2 a b c
end.

Definition to_nat(x:int):nat := Z.to_nat (Uint63.to_Z x).

Inductive WF: int->int->int->nat->Tp->Prop :=
| WF_intro a b c T t
  (Ha:c0 -->* S' (to_nat a) (to_nat b) (to_nat c) t)
  (Hb:(to_nat a) + (to_nat b)*2 + (to_nat c) + T*1000 < 2^60):
  WF a b c T t.

Lemma WF_mono a b c T0 T t:
  WF a b c T0 t ->
  T<=T0 ->
  WF a b c T t.
Proof.
  intros.
  inverts H.
  econstructor; eauto; lia.
Qed.

Require Import ZifyN ZifyUint63 Zify.

Lemma leb_to_nat a b:
  (a <=? b) = (to_nat a <=? to_nat b)%nat.
Proof.
  rewrite leb_le.
  unfold to_nat.
  lia.
Qed.

Lemma eqb_to_nat a b:
  (a =? b) = (to_nat a =? to_nat b)%nat.
Proof.
  rewrite eqb_eq.
  unfold to_nat.
  lia.
Qed.

Lemma add_to_nat a b:
  to_nat a + to_nat b < 2^63 ->
  to_nat (a+b) = (to_nat a + to_nat b)%nat.
Proof.
  unfold to_nat.
  rewrite Uint63.add_spec.
  unfold Uint63.wB.
  unfold Uint63.size.
  intros.
  rewrite Z.mod_small; lia.
Qed.

Lemma mul_to_nat a b:
  to_nat a * to_nat b < 2^63 ->
  to_nat (a*b) = (to_nat a * to_nat b)%nat.
Proof.
  unfold to_nat.
  rewrite Uint63.mul_spec.
  unfold Uint63.wB.
  unfold Uint63.size.
  intros.
  rewrite Z.mod_small; lia.
Qed.

Lemma div_to_nat a b:
  to_nat (a/b) = (to_nat a / to_nat b)%nat.
Proof.
  unfold to_nat.
  rewrite Uint63.div_spec.
  rewrite Z2Nat.inj_div; lia.
Qed.

Lemma sub_to_nat a b:
  to_nat b <= to_nat a ->
  to_nat (a-b) = (to_nat a - to_nat b)%nat.
Proof.
  unfold to_nat.
  rewrite Uint63.sub_spec.
  unfold Uint63.wB.
  unfold Uint63.size.
  intros.
  rewrite Z.mod_small; lia.
Qed.

Lemma min_to_nat a b:
  to_nat (Uint63.min a b) = Nat.min (to_nat a) (to_nat b).
Proof.
  unfold to_nat.
  rewrite Uint63.min_spec.
  lia.
Qed.

Ltac rw_uint :=
  repeat (
  rewrite leb_to_nat in * ||
  rewrite eqb_to_nat in * ||
  rewrite div_to_nat in * ||
  rewrite min_to_nat in *).

Ltac rw_uint' :=
  repeat (
  rewrite add_to_nat in * ||
  rewrite sub_to_nat in * ||
  rewrite mul_to_nat in * ||
  rewrite div_to_nat in * ||
  rewrite min_to_nat in *).

Ltac rw_uint'_in_goal :=
  repeat (
  rewrite add_to_nat ||
  rewrite sub_to_nat ||
  rewrite mul_to_nat).

Ltac is_app x :=
  match x with
  | _ _ => idtac
  end.

Ltac simpl_to_nat_a a :=
  tryif (is_var a)+(is_app a) then fail else
  let E := fresh "E" in
  eassert (to_nat a = _) as E by (vm_compute; reflexivity);
  rewrite E in *;
  clear E.

Ltac simpl_to_nat :=
  repeat
  match goal with
  | [ H: context[to_nat ?a] |- _] =>
    simpl_to_nat_a a
  | |- context[to_nat ?a] =>
    simpl_to_nat_a a
  end.

Ltac solve_uint :=
  rw_uint';
  simpl_to_nat;
  try lia.

Ltac solve_uint_in_goal :=
  rw_uint'_in_goal;
  simpl_to_nat;
  try lia.

Ltac solve_v1 Ha Hx :=
  econstructor;
  [ follow Ha;
    repeat
    match goal with
    | [H: to_nat ?a = _ |- _] =>
      rewrite H;
      clear H
    end;
    unfold S';
    follow Hx; finish; f_equal; solve_uint
  | solve_uint ].

Ltac solve_v2 H0 :=
  inverts H0;
  eapply WF_mono; eauto; lia.

Ltac leb_eqb_cases :=
  rw_uint;
  repeat
  match goal with
  | [H: (if (?a <=? ?b)%nat then _ else _) = _ |- _] =>
    destruct (Nat.leb_spec a b)
  | [H: (if (?a =? ?b)%nat then _ else _) = _ |- _] =>
    destruct (Nat.eqb_spec a b)
  end;
  unfold v0,v1,v2,v3,v4,v5 in *.

Lemma steps_spec a b c T T' tp a0 b0 c0 tp0:
  WF a b c (T+T') tp ->
  steps a b c T tp =
  (a0,b0,c0,tp0) ->
  WF a0 b0 c0 T' tp0.
Proof.
  gen a0 b0 c0 tp0.
  gen a b c T' tp.
  induction T; cbn[steps]; intros.
  - inverts H0.
    apply H.
  - destruct tp.
    + eapply IHT.
      2: apply H0.
      inverts H.
      unfold v3 in *.
      econstructor.
      * follow Ha.
        solve_uint.
        2: pose proof (Nat.div_mod (to_nat c) 3); lia.
        unfold S'.
        apply Incs1'.
      * solve_uint;
        pose proof (Nat.div_mod (to_nat c) 3); lia.
    + eapply IHT.
      2: apply H0.
      inverts H.
      unfold v3 in *.
      econstructor.
      * follow Ha.
        solve_uint.
        2: pose proof (Nat.div_mod (to_nat c) 3); lia.
        unfold S'.
        apply Incs2'.
      * solve_uint;
        pose proof (Nat.div_mod (to_nat c) 3); lia.
    + leb_eqb_cases.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha LOv1.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha LOv1_c1.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha LOv1_c0.
      * solve_v2 H0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha ROv1_0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha ROv1_0_a1.
      * solve_v2 H0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha ROv1_1.
      * solve_v2 H0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha ROv1_2.
      * solve_v2 H0.
      * solve_v2 H0.
    + leb_eqb_cases.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha LOv2.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha ROv2_0.
      * solve_v2 H0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha ROv2_2.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha ROv2_2_a2.
      * solve_v2 H0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha ROv2_0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha ROv2_1.
      * solve_v2 H0.
      * solve_v2 H0.
Qed.

Definition steps' s :=
  let '(a,b,c,t,T):=s in
  if (a=?v1) && (c=?v2) && (match t with t2x => true | _ => false end) then inr tt
  else if (T=?0)%N then inl s
  else inl (steps a b c 1000 t,(T-1)%N).

Definition steps'' T :=
N_iter_until steps' (inl (v0,v4,v4,t1,(10^12)%N)) T.

Lemma steps''_spec T:
  match steps'' T with
  | inl (a,b,c,t,T0) =>
    WF a b c (N.to_nat (T0*1000)) t
  | inr _ => halts tm c0
  end.
Proof.
  eapply N_iter_until_spec
  with
  (P:=fun s => 
  let '(a,b,c,t,T0):=s in
    WF a b c (N.to_nat (T0*1000)) t)
  (P':=fun _ => halts tm c0).
  - intros [[[[a b] c] t] T0] HWF.
    unfold steps'.
    destruct ((a=?v1)&&(c=?v2)&&(match t with t2x => true | _ => false end)) eqn:E.
    + repeat rewrite and_true_iff in E.
      destruct E as [[E1 E2] E3].
      destruct t; try congruence.
      rw_uint.
      rewrite Nat.eqb_eq in *.
      inverts HWF.
      eapply halts_evstep.
      2: apply Ha.
      rewrite E1,E2.
      apply ROv2_2_a1.
    + destruct (N.eqb_spec T0 N0).
      1: apply HWF.
      destruct (steps a b c 1000 t) as [[[a0 b0] c1] t0] eqn:E'.
      eapply steps_spec in E'.
      1: apply E'.
      applys_eq HWF; lia.
  - econstructor.
    + apply init.
    + simpl_to_nat; lia.
Qed.

Lemma steps''_spec' T:
  steps'' T = inr tt ->
  halts tm c0.
Proof.
  intros H.
  epose proof (steps''_spec T) as I.
  rewrite H in I.
  apply I.
Qed.

Lemma halt: halts tm c0.
Proof.
  apply (steps''_spec' (10^9)).
  native_check_eq.
Time Qed.

End TM6.


Module TM4a.

Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LA_1RA1LE_0RA0RB_0LF0LA_---0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1]^^a <* <[1;0]^^b {{A}}> [1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 (1+a) b (3+c) -->* S1 a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs1 a b c n:
  S1 (n+a) b (n*3+c) -->* S1 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition S2 a b c :=
  0inf <* [1]^^a <{{A}} [0;1]^^(b) *> [0;0] *> [1]^^c *> 0inf.

Lemma Inc2 a b c:
  S2 (1+a) (1+b) c -->* S2 a b (3+c).
Proof.
  es.
Qed.

Lemma Incs2 a b c n:
  S2 (n+a) (n+b) c -->* S2 a b (n*3+c).
Proof.
  gen a b c.
  ind n Inc2.
Qed.

Ltac rem_sub x n :=
  let x':=fresh "x" in
  remember (x-n) as x';
  replace x with (x'+n) in * by lia.

Lemma LOv2 b c:
  S2 0 b c -->*
  S1 (3+b*2) 1 c.
Proof.
  es.
Qed.

Lemma MOv2 a c:
  3<=a ->
  S2 a 0 c -->*
  S1 (a-3) 1 (3+c).
Proof.
  intros.
  rem_sub a 3.
  es.
Qed.

Lemma MOv2_2 c:
  S2 2 0 c -->*
  S1 3 0 (4+c).
Proof.
  es.
Qed.

Lemma MOv2_1 c:
  halts tm (S2 1 0 c).
Proof.
  esx.
Qed.

Lemma LOv1 b c:
  3<=c ->
  S1 0 b c -->*
  S1 (5+b*2) 0 (c-2).
Proof.
  intros.
  replace (c-2) with (1+(c-3)) by lia.
  rem_sub c 3.
  unfold S1.
  es_v2.
Qed.

Lemma ROv1_2 a b:
  S1 a b 2 -->*
  S2 a (2+b) 0.
Proof.
  es.
Qed.

Lemma ROv1_1 a b:
  1<=b ->
  S1 a b 1 -->*
  S2 a (b-1) 3.
Proof.
  intros.
  rem_sub b 1%nat.
  es.
Qed.

Lemma ROv1_1_b0 a:
  2<=a ->
  S1 a 0 1 -->*
  S1 (a-2) 1 3.
Proof.
  intros.
  rem_sub a 2.
  es.
Qed.

Lemma ROv1_0 a b:
  2<=b ->
  S1 a b 0 -->*
  S2 a (b-2) 3.
Proof.
  intros.
  rem_sub b 2.
  es.
Qed.

Lemma ROv1_0_b1 a:
  2<=a ->
  S1 a 1 0 -->*
  S1 (a-2) 1 3.
Proof.
  intros.
  rem_sub a 2.
  es.
Qed.

Lemma init:
  c0 -->* S1 5 1 3.
Proof.
  unfold S1,S2.
  esx.
Qed.

Lemma Incs1' a b c:
  let n:=Nat.min a (c/3) in
  S1 a b c -->*
  S1 (a-n) (b+n*2) (c-n*3).
Proof.
  intros n.
  follow (Incs1 (a-n) b (c-n*3) n).
  finish.
Qed.

Lemma Incs2' a b c:
  let n:=Nat.min a b in
  S2 a b c -->*
  S2 (a-n) (b-n) (c+n*3).
Proof.
  intros n.
  follow (Incs2 (a-n) (b-n) c n).
  finish.
Qed.

Require Uint63.
Import Eqb.
Notation "a + b" := (Uint63.add a b).
Notation "a - b" := (Uint63.sub a b).
Notation "a '-c' b" := (Uint63.subc a b) (at level 50).
Notation "a * b" := (Uint63.mul a b).
Notation "a / b" := (Uint63.div a b).
Notation "a 'mod' b" := (Uint63.mod a b).
Notation "a '=?' b" := (Uint63.eqb a b).
Notation "a '<=?' b" := (Uint63.leb a b).
Notation "'int'" := PrimInt63.int.

Definition v0 := Eval compute in Uint63.of_Z 0.
Definition v1 := Eval compute in Uint63.of_Z 1.
Definition v2 := Eval compute in Uint63.of_Z 2.
Definition v3 := Eval compute in Uint63.of_Z 3.
Definition v4 := Eval compute in Uint63.of_Z 4.
Definition v5 := Eval compute in Uint63.of_Z 5.


Inductive Tp := t1 | t2 | t1x | t2x.

Fixpoint steps(a b c:int)(T:nat)(tp:Tp) :=
match T with
| O => (a,b,c,tp)
| S T =>
  match tp with
  | t1 =>
    let n := Uint63.min a (c/v3) in
    steps (a-n) (b+n*v2) (c-n*v3) T t1x
  | t2 =>
    let n := Uint63.min a b in
    steps (a-n) (b-n) (c+n*v3) T t2x
  | t1x =>
    if c=?v0 then
      if v2<=?b then
        steps a (b-v2) v3 T t2
      else if b=?v1 then
        if v2<=?a then
          steps (a-v2) v1 v3 T t1
        else (a,b,c,tp)
      else (a,b,c,tp)
    else if v3<=?c then
      if a=?v0 then
        steps (v5+b*v2) v0 (c-v2) T t1
      else (a,b,c,tp)
    else if c=?v1 then
      if v1<=?b then
        steps a (b-v1) v3 T t2
      else if b=?v0 then
        if v2<=?a then
          steps (a-v2) v1 v3 T t1
        else (a,b,c,tp)
      else (a,b,c,tp)
    else if c=?v2 then
      steps a (v2+b) v0 T t2
    else (a,b,c,tp)
  | t2x =>
    if b=?v0 then
      if v3<=?a then
        steps (a-v3) v1 (v3+c) T t1
      else if a=?v2 then
        steps v3 v0 (v4+c) T t1
      else if a=?v0 then
        steps v3 v1 c T t1
      else (a,b,c,tp)
    else if a=?v0 then
      steps (v3+b*v2) v1 c T t1
    else (a,b,c,tp)
  end
end.

Definition S' a b c t :=
match t with
| t1 | t1x => S1 a b c
| t2 | t2x => S2 a b c
end.

Definition to_nat(x:int):nat := Z.to_nat (Uint63.to_Z x).

Inductive WF: int->int->int->nat->Tp->Prop :=
| WF_intro a b c T t
  (Ha:c0 -->* S' (to_nat a) (to_nat b) (to_nat c) t)
  (Hb:(to_nat a) + (to_nat b)*2 + (to_nat c) + T*1000 < 2^60):
  WF a b c T t.

Lemma WF_mono a b c T0 T t:
  WF a b c T0 t ->
  T<=T0 ->
  WF a b c T t.
Proof.
  intros.
  inverts H.
  econstructor; eauto; lia.
Qed.

Require Import ZifyN ZifyUint63 Zify.

Lemma leb_to_nat a b:
  (a <=? b) = (to_nat a <=? to_nat b)%nat.
Proof.
  rewrite leb_le.
  unfold to_nat.
  lia.
Qed.

Lemma eqb_to_nat a b:
  (a =? b) = (to_nat a =? to_nat b)%nat.
Proof.
  rewrite eqb_eq.
  unfold to_nat.
  lia.
Qed.

Lemma add_to_nat a b:
  to_nat a + to_nat b < 2^63 ->
  to_nat (a+b) = (to_nat a + to_nat b)%nat.
Proof.
  unfold to_nat.
  rewrite Uint63.add_spec.
  unfold Uint63.wB.
  unfold Uint63.size.
  intros.
  rewrite Z.mod_small; lia.
Qed.

Lemma mul_to_nat a b:
  to_nat a * to_nat b < 2^63 ->
  to_nat (a*b) = (to_nat a * to_nat b)%nat.
Proof.
  unfold to_nat.
  rewrite Uint63.mul_spec.
  unfold Uint63.wB.
  unfold Uint63.size.
  intros.
  rewrite Z.mod_small; lia.
Qed.

Lemma div_to_nat a b:
  to_nat (a/b) = (to_nat a / to_nat b)%nat.
Proof.
  unfold to_nat.
  rewrite Uint63.div_spec.
  rewrite Z2Nat.inj_div; lia.
Qed.

Lemma sub_to_nat a b:
  to_nat b <= to_nat a ->
  to_nat (a-b) = (to_nat a - to_nat b)%nat.
Proof.
  unfold to_nat.
  rewrite Uint63.sub_spec.
  unfold Uint63.wB.
  unfold Uint63.size.
  intros.
  rewrite Z.mod_small; lia.
Qed.

Lemma min_to_nat a b:
  to_nat (Uint63.min a b) = Nat.min (to_nat a) (to_nat b).
Proof.
  unfold to_nat.
  rewrite Uint63.min_spec.
  lia.
Qed.

Ltac rw_uint :=
  repeat (
  rewrite leb_to_nat in * ||
  rewrite eqb_to_nat in * ||
  rewrite div_to_nat in * ||
  rewrite min_to_nat in *).

Ltac rw_uint' :=
  repeat (
  rewrite add_to_nat in * ||
  rewrite sub_to_nat in * ||
  rewrite mul_to_nat in * ||
  rewrite div_to_nat in * ||
  rewrite min_to_nat in *).

Ltac rw_uint'_in_goal :=
  repeat (
  rewrite add_to_nat ||
  rewrite sub_to_nat ||
  rewrite mul_to_nat).

Ltac is_app x :=
  match x with
  | _ _ => idtac
  end.

Ltac simpl_to_nat_a a :=
  tryif (is_var a)+(is_app a) then fail else
  let E := fresh "E" in
  eassert (to_nat a = _) as E by (vm_compute; reflexivity);
  rewrite E in *;
  clear E.

Ltac simpl_to_nat :=
  repeat
  match goal with
  | [ H: context[to_nat ?a] |- _] =>
    simpl_to_nat_a a
  | |- context[to_nat ?a] =>
    simpl_to_nat_a a
  end.

Ltac solve_uint :=
  rw_uint';
  simpl_to_nat;
  try lia.

Ltac solve_uint_in_goal :=
  rw_uint'_in_goal;
  simpl_to_nat;
  try lia.

Ltac solve_v1 Ha Hx :=
  econstructor;
  [ follow Ha;
    repeat
    match goal with
    | [H: to_nat ?a = _ |- _] =>
      rewrite H;
      clear H
    end;
    unfold S';
    follow Hx; finish; f_equal; solve_uint
  | solve_uint ].

Ltac solve_v2 H0 :=
  inverts H0;
  eapply WF_mono; eauto; lia.

Ltac leb_eqb_cases :=
  rw_uint;
  repeat
  match goal with
  | [H: (if (?a <=? ?b)%nat then _ else _) = _ |- _] =>
    destruct (Nat.leb_spec a b)
  | [H: (if (?a =? ?b)%nat then _ else _) = _ |- _] =>
    destruct (Nat.eqb_spec a b)
  end;
  unfold v0,v1,v2,v3,v4,v5 in *.

Lemma steps_spec a b c T T' tp a0 b0 c0 tp0:
  WF a b c (T+T') tp ->
  steps a b c T tp =
  (a0,b0,c0,tp0) ->
  WF a0 b0 c0 T' tp0.
Proof.
  gen a0 b0 c0 tp0.
  gen a b c T' tp.
  induction T; cbn[steps]; intros.
  - inverts H0.
    apply H.
  - destruct tp.
    + eapply IHT.
      2: apply H0.
      inverts H.
      unfold v3 in *.
      econstructor.
      * follow Ha.
        solve_uint.
        2: pose proof (Nat.div_mod (to_nat c) 3); lia.
        unfold S'.
        apply Incs1'.
      * solve_uint;
        pose proof (Nat.div_mod (to_nat c) 3); lia.
    + eapply IHT.
      2: apply H0.
      inverts H.
      unfold v3 in *.
      econstructor.
      * follow Ha.
        solve_uint.
        unfold S'.
        apply Incs2'.
      * solve_uint.
    + leb_eqb_cases.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha ROv1_0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha ROv1_0_b1.
      * solve_v2 H0.
      * solve_v2 H0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha LOv1.
      * solve_v2 H0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha ROv1_1.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha ROv1_1_b0.
      * solve_v2 H0.
      * solve_v2 H0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha ROv1_2.
      * solve_v2 H0.
    + leb_eqb_cases.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha MOv2.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha MOv2_2.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha LOv2.
      * solve_v2 H0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha LOv2.
      * solve_v2 H0.
Qed.

Definition steps' s :=
  let '(a,b,c,t,T):=s in
  if (a=?v1) && (b=?v0) && (match t with t2x => true | _ => false end) then inr tt
  else if (T=?0)%N then inl s
  else inl (steps a b c 1000 t,(T-1)%N).

Definition steps'' T :=
N_iter_until steps' (inl (v5,v1,v3,t1,(10^12)%N)) T.

Lemma steps''_spec T:
  match steps'' T with
  | inl (a,b,c,t,T0) =>
    WF a b c (N.to_nat (T0*1000)) t
  | inr _ => halts tm c0
  end.
Proof.
  eapply N_iter_until_spec
  with
  (P:=fun s => 
  let '(a,b,c,t,T0):=s in
    WF a b c (N.to_nat (T0*1000)) t)
  (P':=fun _ => halts tm c0).
  - intros [[[[a b] c] t] T0] HWF.
    unfold steps'.
    destruct ((a=?v1)&&(b=?v0)&&(match t with t2x => true | _ => false end)) eqn:E.
    + repeat rewrite and_true_iff in E.
      destruct E as [[E1 E2] E3].
      destruct t; try congruence.
      rw_uint.
      rewrite Nat.eqb_eq in *.
      inverts HWF.
      eapply halts_evstep.
      2: apply Ha.
      rewrite E1,E2.
      apply MOv2_1.
    + destruct (N.eqb_spec T0 N0).
      1: apply HWF.
      destruct (steps a b c 1000 t) as [[[a0 b0] c1] t0] eqn:E'.
      eapply steps_spec in E'.
      1: apply E'.
      applys_eq HWF; lia.
  - econstructor.
    + apply init.
    + simpl_to_nat; lia.
Qed.

Lemma steps''_spec' T:
  steps'' T = inr tt ->
  halts tm c0.
Proof.
  intros H.
  epose proof (steps''_spec T) as I.
  rewrite H in I.
  apply I.
Qed.

Lemma halt: halts tm c0.
Proof.
  apply (steps''_spec' (10^9)).
  native_check_eq.
Time Qed.

End TM4a.

