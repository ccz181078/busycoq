From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require ES_v2.

Ltac es_v2 := ES_v2.es.
Ltac flia := repeat (lia || f_equal).

Ltac native_check_eq :=
match goal with
| |- _ = ?a => native_cast_no_check (eq_refl a)
end.


Module TM3c.
Definition tm := Eval compute in (TM_from_str "1LB1RF_0LC0LE_1RD0LA_1RE---_1LC1LA_0RA0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  0inf <* [1]^^a <{{A}} [0;1;0;1]^^(b) *> [0;0] *> [1]^^c *> 0inf.

Definition S1 a b c :=
  0inf <* [1]^^a <* <[1;0;1;0]^^(b) {{A}}> [1]^^c *> 0inf.

Lemma Inc0 a b c:
  S0 (1+a) b c -->*
  S0 a b (1+c).
Proof.
  es.
Qed.

Lemma Incs0 a b c:
  S0 a b c -->*
  S0 0 b (a+c).
Proof.
  gen b c.
  ind a Inc0.
Qed.

Lemma Inc1 a b c:
  S1 (1+a) b (3+c) -->*
  S1 a (1+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n+a) b (n*3+c) -->*
  S1 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma LOv0 b c:
  S0 0 b (3+c) -->*
  S1 (6+b*4) 0 (2+c).
Proof.
  es.
Qed.

Lemma LOv0_1 b:
  S0 0 (1+b) 1 -->*
  S1 10 0 (9+b*4).
Proof.
  mid (S0 (10+b*4) 1 0).
  1: es.
  follow Incs0.
  replace (10+b*4+0) with (3+(7+b*4)) by lia.
  follow LOv0.
  finish.
Qed.

Lemma LOv0_2 b:
  S0 0 (1+b) 2 -->*
  S1 10 0 (13+b*4).
Proof.
  mid (S0 (14+b*4) 1 0).
  1: es.
  follow Incs0.
  replace (14+b*4+0) with (3+(11+b*4)) by lia.
  follow LOv0.
  finish.
Qed.

Lemma ROv_2 a b:
  1<=a ->
  S1 a b 2 -->*
  S1 (10+b*4) 0 (5+a).
Proof.
  intros.
  remember (a-1) as a'.
  replace a with (1+a') by lia.
  mid (S0 a' (1+b) 7).
  1: es.
  follow Incs0.
  follow (LOv0 (1+b) (4+a')).
  finish.
Qed.

Lemma ROv_1 a b:
  2<=a ->
  S1 a b 1 -->*
  S1 (6+b*4) 0 a.
Proof.
  intros.
  remember (a-2) as a'.
  replace a with (2+a') by lia.
  mid (S0 (2+a') b 1).
  1: es.
  follow Incs0.
  follow (LOv0 b a').
  finish.
Qed.

Lemma ROv_1_a0 b:
  1<=b ->
  S1 0 b 1 -->*
  S1 10 0 (5+b*4).
Proof.
  intros.
  remember (b-1) as b'.
  replace b with (1+b') by lia.
  mid (S0 0 (1+b') 1).
  1: unfold S1,S0; es_v2.
  follow LOv0_1.
  finish.
Qed.

Lemma ROv_1_a1 b:
  1<=b ->
  S1 1 b 1 -->*
  S1 10 0 (9+b*4).
Proof.
  intros.
  remember (b-1) as b'.
  replace b with (1+b') by lia.
  mid (S0 1 (1+b') 1).
  1: unfold S1,S0; es_v2.
  follow Incs0.
  follow LOv0_2.
  finish.
Qed.

Lemma ROv_0 a b:
  2<=a ->
  1<=b ->
  S1 a b 0 -->*
  S1 10 0 (b*4+a).
Proof.
  intros.
  remember (a-2) as a'.
  replace a with (2+a') by lia.
  remember (b-1) as b'.
  replace b with (1+b') by lia.
  mid (S0 (7+b'*4+a') 1 0).
  1: es.
  follow Incs0.
  follow (LOv0 1 (4+b'*4+a')).
  finish.
Qed.

Lemma ROv_0_a0 b:
  1<=b ->
  halts tm (S1 1 b 0).
Proof.
  destruct b. 1: lia.
  unfold S1.
  esx.
Qed.

Lemma LOv b c:
  4<=c ->
  S1 0 b c -->*
  S1 (5+b*4) 0 (c-2).
Proof.
  intros.
  remember (c-4) as c'.
  replace (c-2) with (2+c') by lia.
  replace c with (4+c') by lia.
  unfold S1.
  es_v2.
Qed.

Lemma init:
  c0 -->*
  S1 10 0 16.
Proof.
  unfold S1,S0.
  esx.
Qed.

Definition P x y :=
  forall c,
  S1 10 0 (2+y+c) -->*
  S1 x 0 (2+c).

Lemma P_O: P 10 0.
Proof.
  unfold P.
  es.
Qed.

Lemma P_S x y:
  P x y ->
  P (5+x*4) (2+x*3+y).
Proof.
  unfold P.
  intros HP c.
  follow (HP (2+x*3+c)).
  follow (Incs1 x 0 0 (4+c)).
  follow LOv.
  1: lia.
  finish.
Qed.

Lemma P_spec x y c:
  P x y ->
  2+y<=c ->
  S1 10 0 c -->*
  S1 x 0 (c-y).
Proof.
  intros HP Hc.
  specialize (HP (c-y-2)).
  follow HP.
  finish.
Qed.

Lemma Incs1' a b c:
  let n:=Nat.min a (c/3) in
  S1 a b c -->*
  S1 (a-n) (b+n) (c-n*3).
Proof.
  intros n.
  follow (Incs1 n (a-n) b (c-n*3)).
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
Definition v6 := Eval compute in Uint63.of_Z 6.
Definition v9 := Eval compute in Uint63.of_Z 9.
Definition v10 := Eval compute in Uint63.of_Z 10.
Definition v16 := Eval compute in Uint63.of_Z 16.
Definition v1010 := Eval compute in Uint63.of_Z 1010.
Definition v2_60 := Eval compute in Uint63.of_Z (2^60).


Inductive Tp := t0 | t1 | t2.

Fixpoint steps(a b c x y:int)(T:nat)(tp:Tp) :=
match T with
| O => (a,b,c,x,y)
| S T =>
  match tp with
  | t0 =>
    let n := Uint63.min a (c/v3) in
    steps (a-n) (b+n) (c-n*v3) x y T t1
  | t1 =>
    if c<=?v2 then
      if c=?v0 then
        if v2<=?a then
        if v1<=?b then
          steps v10 v0 (b*v4+a) x y T t2
        else (a,b,c,x,y)
        else (a,b,c,x,y)
      else if c=?v1 then
        if v2<=?a then
          steps (v6+b*v4) v0 a x y T t0
        else if a=?v0 then
          if v1<=?b then
            steps v10 v0 (v5+b*v4) x y T t2
          else (a,b,c,x,y)
        else if a=?v1 then
          if v1<=?b then
            steps v10 v0 (v9+b*v4) x y T t2
          else (a,b,c,x,y)
        else (a,b,c,x,y)
      else if c=?v2 then
        if v1<=?a then
          steps (v10+b*v4) v0 (v5+a) x y T t0
        else (a,b,c,x,y)
      else (a,b,c,x,y)
    else if a=?v0 then
      if v4<=?c then
        steps (v5+b*v4) v0 (c-v2) x y T t2
      else (a,b,c,x,y)
    else (a,b,c,x,y)
  | t2 =>
    if a=?v10 then
    if b=?v0 then
    if x*v3+y+v2<=?c then
      let x':=v5+x*v4 in
      let y':=v2+x*v3+y in
      if x'<=?y'+v1010 then
      if y'<=?v2_60 then
      steps a b c x' y' T t2
      else steps a b c x y T t0
      else steps a b c x y T t0
    else if y+v2<=?c then
      steps x v0 (c-y) x y T t0
    else steps a b c x y T t0
    else steps a b c x y T t0
    else steps a b c x y T t0
  end
end.

Definition to_nat(x:int):nat := Z.to_nat (Uint63.to_Z x).

Inductive WF: int->int->int->int->int->nat->Prop :=
| WF_intro a b c x y T
  (Ha:c0 -->* S1 (to_nat a) (to_nat b) (to_nat c))
  (Hb:P (to_nat x) (to_nat y))
  (Hc:(to_nat a) + (to_nat b)*4 + (to_nat c) + T*1000 < 2^60)
  (Hd:(to_nat x) <= (to_nat y) + 1010)
  (Hy:(to_nat y) <= 2^60):
  WF a b c x y T.

Lemma WF_mono a b c x y T0 T:
  WF a b c x y T0 ->
  T<=T0 ->
  WF a b c x y T.
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

Ltac simpl_to_nat :=
  repeat
  match goal with
  | |- context[to_nat ?a] =>
     tryif (is_var a)+(is_app a) then fail else
     let E := fresh "E" in
     eassert (to_nat a = _) as E by (vm_compute; reflexivity);
     rewrite E;
     clear E
  end.

Ltac solve_uint :=
  rw_uint';
  simpl_to_nat;
  try lia.

Ltac solve_uint_in_goal :=
  rw_uint'_in_goal;
  simpl_to_nat;
  try lia.

Ltac solve_v1 Ha Hb Hx :=
  econstructor;
  [ follow Ha;
    repeat
    match goal with
    | [H: to_nat ?a = _ |- _] =>
      rewrite H;
      clear H
    end;
    follow Hx; finish; f_equal; solve_uint
  | apply Hb
  | solve_uint
  | assumption
  | assumption ].

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
  unfold v0,v1,v2,v3,v4,v5,v6,v9,v10,v1010,v2_60 in *.

Lemma steps_spec a b c x y T T' tp a0 b0 c0 x0 y0:
  WF a b c x y (T+T') ->
  steps a b c x y T tp =
  (a0,b0,c0,x0,y0) ->
  WF a0 b0 c0 x0 y0 T'.
Proof.
  gen a0 b0 c0 x0 y0.
  gen a b c x y T' tp.
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
        2: {
          pose proof (Nat.div_mod (to_nat c) 3).
          lia.
        }
        apply Incs1'.
      * apply Hb.
      * solve_uint;
          pose proof (Nat.div_mod (to_nat c) 3); lia.
      * assumption.
      * assumption.
    + leb_eqb_cases.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha Hb ROv_0.
      * solve_v2 H0.
      * solve_v2 H0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha Hb ROv_1.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha Hb ROv_1_a0.
      * solve_v2 H0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha Hb ROv_1_a1.
      * solve_v2 H0.
      * solve_v2 H0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha Hb ROv_2.
      * solve_v2 H0.
      * solve_v2 H0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha Hb LOv.
        -- gen H1.
           cbn; lia.
        -- gen H1.
           cbn; lia.
      * solve_v2 H0.
      * solve_v2 H0.
    + leb_eqb_cases.
      * eapply IHT.
        2: apply H0.
        inverts H.
        cbn in e,e0.
        rewrite e in *.
        rewrite e0 in *.
        econstructor.
        -- applys_eq Ha; flia.
        -- apply P_S in Hb.
           applys_eq Hb; solve_uint_in_goal.
        -- lia.
        -- etransitivity.
           1: apply H2.
           solve_uint_in_goal.
        -- etransitivity.
           1: apply H3.
           unfold to_nat.
           lia.
      * eapply IHT.
        2: apply H0.
        eapply WF_mono; eauto; lia.
      * eapply IHT.
        2: apply H0.
        eapply WF_mono; eauto; lia.
      * eapply IHT.
        2: apply H0.
        inverts H.
        cbn in e,e0.
        rewrite e in *.
        rewrite e0 in *.
        rewrite add_to_nat in H2.
        2: {
          simpl_to_nat.
          lia.
        }
        cbn in H2.
        econstructor.
        -- follow Ha.
           epose proof (P_spec _ _ (to_nat c) Hb) as Hb'.
           follow Hb'.
           1: lia.
           finish; f_equal.
           solve_uint_in_goal.
        -- apply Hb.
        -- solve_uint_in_goal.
        -- assumption.
        -- assumption.
      * eapply IHT.
        2: apply H0.
        eapply WF_mono; eauto; lia.
      * eapply IHT.
        2: apply H0.
        eapply WF_mono; eauto; lia.
      * eapply IHT.
        2: apply H0.
        eapply WF_mono; eauto; lia.
Qed.

Definition steps' s :=
  let '(a,b,c,x,y,T):=s in
  if (a=?v1) && (v1<=?b) && (c=?v0) then
  inr tt
  else if (T=?0)%N then inl s
  else inl (steps a b c x y 1000 t0,(T-1)%N).

Definition steps'' T :=
N_iter_until steps' (inl (v10,v0,v16,v10,v0,(10^12)%N)) T.

Lemma steps''_spec T:
  match steps'' T with
  | inl (a,b,c,x,y,T0) =>
    WF a b c x y (N.to_nat (T0*1000))
  | inr _ => halts tm c0
  end.
Proof.
  eapply N_iter_until_spec
  with
  (P:=fun s => 
  let '(a,b,c,x,y,T0):=s in
    WF a b c x y (N.to_nat (T0*1000)))
  (P':=fun _ => halts tm c0).
  - intros [[[[[a b] c] x] y] T0] HWF.
    unfold steps'.
    destruct ((a=?v1)&&(v1<=?b)&&(c=?v0)) eqn:E.
    + repeat rewrite and_true_iff in E.
      destruct E as [[E1 E2] E3].
      rw_uint.
      rewrite Nat.eqb_eq in *.
      rewrite Nat.leb_le in *.
      inverts HWF.
      eapply halts_evstep.
      2: apply Ha.
      rewrite E1,E3.
      apply ROv_0_a0,E2.
    + destruct (N.eqb_spec T0 N0).
      1: apply HWF.
      destruct (steps a b c x y 1000 t0) as [[[[a0 b0] c1] x0] y0] eqn:E'.
      eapply steps_spec in E'.
      1: apply E'.
      applys_eq HWF; lia.
  - econstructor.
    + apply init.
    + apply P_O.
    + simpl_to_nat; lia.
    + simpl_to_nat; lia.
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

End TM3c.


Module TM3d.
Definition tm := Eval compute in (TM_from_str "1RB---_1LC1LD_1RA0LD_1LE1RF_0LC0LB_0RD0RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  0inf <* [1]^^a <{{D}} [0;1;0;1]^^(b) *> [0;0] *> [1]^^c *> 0inf.

Definition S1 a b c :=
  0inf <* [1]^^a <* <[1;0;1;0]^^(b) {{D}}> [1]^^c *> 0inf.

Lemma Inc0 a b c:
  S0 (1+a) b c -->*
  S0 a b (1+c).
Proof.
  es.
Qed.

Lemma Incs0 a b c:
  S0 a b c -->*
  S0 0 b (a+c).
Proof.
  gen b c.
  ind a Inc0.
Qed.

Lemma Inc1 a b c:
  S1 (1+a) b (3+c) -->*
  S1 a (1+b) c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 (n+a) b (n*3+c) -->*
  S1 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma LOv0 b c:
  S0 0 b (3+c) -->*
  S1 (6+b*4) 0 (2+c).
Proof.
  es.
Qed.

Lemma LOv0_1 b:
  S0 0 (1+b) 1 -->*
  S1 10 0 (9+b*4).
Proof.
  mid (S0 (10+b*4) 1 0).
  1: es.
  follow Incs0.
  replace (10+b*4+0) with (3+(7+b*4)) by lia.
  follow LOv0.
  finish.
Qed.

Lemma LOv0_2 b:
  S0 0 (1+b) 2 -->*
  S1 10 0 (13+b*4).
Proof.
  mid (S0 (14+b*4) 1 0).
  1: es.
  follow Incs0.
  replace (14+b*4+0) with (3+(11+b*4)) by lia.
  follow LOv0.
  finish.
Qed.

Lemma ROv_2 a b:
  1<=a ->
  S1 a b 2 -->*
  S1 (10+b*4) 0 (5+a).
Proof.
  intros.
  remember (a-1) as a'.
  replace a with (1+a') by lia.
  mid (S0 a' (1+b) 7).
  1: es.
  follow Incs0.
  follow (LOv0 (1+b) (4+a')).
  finish.
Qed.

Lemma ROv_1 a b:
  2<=a ->
  S1 a b 1 -->*
  S1 (6+b*4) 0 a.
Proof.
  intros.
  remember (a-2) as a'.
  replace a with (2+a') by lia.
  mid (S0 (2+a') b 1).
  1: es.
  follow Incs0.
  follow (LOv0 b a').
  finish.
Qed.

Lemma ROv_1_a0 b:
  1<=b ->
  S1 0 b 1 -->*
  S1 10 0 (5+b*4).
Proof.
  intros.
  remember (b-1) as b'.
  replace b with (1+b') by lia.
  mid (S0 0 (1+b') 1).
  1: unfold S1,S0; es_v2.
  follow LOv0_1.
  finish.
Qed.

Lemma ROv_1_a1 b:
  1<=b ->
  S1 1 b 1 -->*
  S1 10 0 (9+b*4).
Proof.
  intros.
  remember (b-1) as b'.
  replace b with (1+b') by lia.
  mid (S0 1 (1+b') 1).
  1: unfold S1,S0; es_v2.
  follow Incs0.
  follow LOv0_2.
  finish.
Qed.

Lemma ROv_0 a b:
  2<=a ->
  1<=b ->
  S1 a b 0 -->*
  S1 10 0 (b*4+a).
Proof.
  intros.
  remember (a-2) as a'.
  replace a with (2+a') by lia.
  remember (b-1) as b'.
  replace b with (1+b') by lia.
  mid (S0 (7+b'*4+a') 1 0).
  1: es.
  follow Incs0.
  follow (LOv0 1 (4+b'*4+a')).
  finish.
Qed.

Lemma ROv_0_a0 b:
  1<=b ->
  halts tm (S1 1 b 0).
Proof.
  destruct b. 1: lia.
  unfold S1.
  esx.
Qed.

Lemma LOv b c:
  4<=c ->
  S1 0 b c -->*
  S1 (5+b*4) 0 (c-2).
Proof.
  intros.
  remember (c-4) as c'.
  replace (c-2) with (2+c') by lia.
  replace c with (4+c') by lia.
  unfold S1.
  es_v2.
Qed.

Lemma init:
  c0 -->*
  S1 18 0 13.
Proof.
  unfold S1,S0.
  esx.
Qed.

Definition P x y :=
  forall c,
  S1 10 0 (2+y+c) -->*
  S1 x 0 (2+c).

Lemma P_O: P 10 0.
Proof.
  unfold P.
  es.
Qed.

Lemma P_S x y:
  P x y ->
  P (5+x*4) (2+x*3+y).
Proof.
  unfold P.
  intros HP c.
  follow (HP (2+x*3+c)).
  follow (Incs1 x 0 0 (4+c)).
  follow LOv.
  1: lia.
  finish.
Qed.

Lemma P_spec x y c:
  P x y ->
  2+y<=c ->
  S1 10 0 c -->*
  S1 x 0 (c-y).
Proof.
  intros HP Hc.
  specialize (HP (c-y-2)).
  follow HP.
  finish.
Qed.

Lemma Incs1' a b c:
  let n:=Nat.min a (c/3) in
  S1 a b c -->*
  S1 (a-n) (b+n) (c-n*3).
Proof.
  intros n.
  follow (Incs1 n (a-n) b (c-n*3)).
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
Definition v6 := Eval compute in Uint63.of_Z 6.
Definition v9 := Eval compute in Uint63.of_Z 9.
Definition v10 := Eval compute in Uint63.of_Z 10.
Definition v13 := Eval compute in Uint63.of_Z 13.
Definition v18 := Eval compute in Uint63.of_Z 18.
Definition v1010 := Eval compute in Uint63.of_Z 1010.
Definition v2_60 := Eval compute in Uint63.of_Z (2^60).


Inductive Tp := t0 | t1 | t2.

Fixpoint steps(a b c x y:int)(T:nat)(tp:Tp) :=
match T with
| O => (a,b,c,x,y)
| S T =>
  match tp with
  | t0 =>
    let n := Uint63.min a (c/v3) in
    steps (a-n) (b+n) (c-n*v3) x y T t1
  | t1 =>
    if c<=?v2 then
      if c=?v0 then
        if v2<=?a then
        if v1<=?b then
          steps v10 v0 (b*v4+a) x y T t2
        else (a,b,c,x,y)
        else (a,b,c,x,y)
      else if c=?v1 then
        if v2<=?a then
          steps (v6+b*v4) v0 a x y T t0
        else if a=?v0 then
          if v1<=?b then
            steps v10 v0 (v5+b*v4) x y T t2
          else (a,b,c,x,y)
        else if a=?v1 then
          if v1<=?b then
            steps v10 v0 (v9+b*v4) x y T t2
          else (a,b,c,x,y)
        else (a,b,c,x,y)
      else if c=?v2 then
        if v1<=?a then
          steps (v10+b*v4) v0 (v5+a) x y T t0
        else (a,b,c,x,y)
      else (a,b,c,x,y)
    else if a=?v0 then
      if v4<=?c then
        steps (v5+b*v4) v0 (c-v2) x y T t2
      else (a,b,c,x,y)
    else (a,b,c,x,y)
  | t2 =>
    if a=?v10 then
    if b=?v0 then
    if x*v3+y+v2<=?c then
      let x':=v5+x*v4 in
      let y':=v2+x*v3+y in
      if x'<=?y'+v1010 then
      if y'<=?v2_60 then
      steps a b c x' y' T t2
      else steps a b c x y T t0
      else steps a b c x y T t0
    else if y+v2<=?c then
      steps x v0 (c-y) x y T t0
    else steps a b c x y T t0
    else steps a b c x y T t0
    else steps a b c x y T t0
  end
end.

Definition to_nat(x:int):nat := Z.to_nat (Uint63.to_Z x).

Inductive WF: int->int->int->int->int->nat->Prop :=
| WF_intro a b c x y T
  (Ha:c0 -->* S1 (to_nat a) (to_nat b) (to_nat c))
  (Hb:P (to_nat x) (to_nat y))
  (Hc:(to_nat a) + (to_nat b)*4 + (to_nat c) + T*1000 < 2^60)
  (Hd:(to_nat x) <= (to_nat y) + 1010)
  (Hy:(to_nat y) <= 2^60):
  WF a b c x y T.

Lemma WF_mono a b c x y T0 T:
  WF a b c x y T0 ->
  T<=T0 ->
  WF a b c x y T.
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

Ltac simpl_to_nat :=
  repeat
  match goal with
  | |- context[to_nat ?a] =>
     tryif (is_var a)+(is_app a) then fail else
     let E := fresh "E" in
     eassert (to_nat a = _) as E by (vm_compute; reflexivity);
     rewrite E;
     clear E
  end.

Ltac solve_uint :=
  rw_uint';
  simpl_to_nat;
  try lia.

Ltac solve_uint_in_goal :=
  rw_uint'_in_goal;
  simpl_to_nat;
  try lia.

Ltac solve_v1 Ha Hb Hx :=
  econstructor;
  [ follow Ha;
    repeat
    match goal with
    | [H: to_nat ?a = _ |- _] =>
      rewrite H;
      clear H
    end;
    follow Hx; finish; f_equal; solve_uint
  | apply Hb
  | solve_uint
  | assumption
  | assumption ].

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
  unfold v0,v1,v2,v3,v4,v5,v6,v9,v10,v1010,v2_60 in *.

Lemma steps_spec a b c x y T T' tp a0 b0 c0 x0 y0:
  WF a b c x y (T+T') ->
  steps a b c x y T tp =
  (a0,b0,c0,x0,y0) ->
  WF a0 b0 c0 x0 y0 T'.
Proof.
  gen a0 b0 c0 x0 y0.
  gen a b c x y T' tp.
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
        2: {
          pose proof (Nat.div_mod (to_nat c) 3).
          lia.
        }
        apply Incs1'.
      * apply Hb.
      * solve_uint;
          pose proof (Nat.div_mod (to_nat c) 3); lia.
      * assumption.
      * assumption.
    + leb_eqb_cases.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha Hb ROv_0.
      * solve_v2 H0.
      * solve_v2 H0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha Hb ROv_1.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha Hb ROv_1_a0.
      * solve_v2 H0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha Hb ROv_1_a1.
      * solve_v2 H0.
      * solve_v2 H0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha Hb ROv_2.
      * solve_v2 H0.
      * solve_v2 H0.
      * eapply IHT.
        2: apply H0.
        inverts H.
        solve_v1 Ha Hb LOv.
        -- gen H1.
           cbn; lia.
        -- gen H1.
           cbn; lia.
      * solve_v2 H0.
      * solve_v2 H0.
    + leb_eqb_cases.
      * eapply IHT.
        2: apply H0.
        inverts H.
        cbn in e,e0.
        rewrite e in *.
        rewrite e0 in *.
        econstructor.
        -- applys_eq Ha; flia.
        -- apply P_S in Hb.
           applys_eq Hb; solve_uint_in_goal.
        -- lia.
        -- etransitivity.
           1: apply H2.
           solve_uint_in_goal.
        -- etransitivity.
           1: apply H3.
           unfold to_nat.
           lia.
      * eapply IHT.
        2: apply H0.
        eapply WF_mono; eauto; lia.
      * eapply IHT.
        2: apply H0.
        eapply WF_mono; eauto; lia.
      * eapply IHT.
        2: apply H0.
        inverts H.
        cbn in e,e0.
        rewrite e in *.
        rewrite e0 in *.
        rewrite add_to_nat in H2.
        2: {
          simpl_to_nat.
          lia.
        }
        cbn in H2.
        econstructor.
        -- follow Ha.
           epose proof (P_spec _ _ (to_nat c) Hb) as Hb'.
           follow Hb'.
           1: lia.
           finish; f_equal.
           solve_uint_in_goal.
        -- apply Hb.
        -- solve_uint_in_goal.
        -- assumption.
        -- assumption.
      * eapply IHT.
        2: apply H0.
        eapply WF_mono; eauto; lia.
      * eapply IHT.
        2: apply H0.
        eapply WF_mono; eauto; lia.
      * eapply IHT.
        2: apply H0.
        eapply WF_mono; eauto; lia.
Qed.

Definition steps' s :=
  let '(a,b,c,x,y,T):=s in
  if (a=?v1) && (v1<=?b) && (c=?v0) then
  inr tt
  else if (T=?0)%N then inl s
  else inl (steps a b c x y 1000 t0,(T-1)%N).

Definition steps'' T :=
N_iter_until steps' (inl (v18,v0,v13,v10,v0,(10^12)%N)) T.

Lemma steps''_spec T:
  match steps'' T with
  | inl (a,b,c,x,y,T0) =>
    WF a b c x y (N.to_nat (T0*1000))
  | inr _ => halts tm c0
  end.
Proof.
  eapply N_iter_until_spec
  with
  (P:=fun s => 
  let '(a,b,c,x,y,T0):=s in
    WF a b c x y (N.to_nat (T0*1000)))
  (P':=fun _ => halts tm c0).
  - intros [[[[[a b] c] x] y] T0] HWF.
    unfold steps'.
    destruct ((a=?v1)&&(v1<=?b)&&(c=?v0)) eqn:E.
    + repeat rewrite and_true_iff in E.
      destruct E as [[E1 E2] E3].
      rw_uint.
      rewrite Nat.eqb_eq in *.
      rewrite Nat.leb_le in *.
      inverts HWF.
      eapply halts_evstep.
      2: apply Ha.
      rewrite E1,E3.
      apply ROv_0_a0,E2.
    + destruct (N.eqb_spec T0 N0).
      1: apply HWF.
      destruct (steps a b c x y 1000 t0) as [[[[a0 b0] c1] x0] y0] eqn:E'.
      eapply steps_spec in E'.
      1: apply E'.
      applys_eq HWF; lia.
  - econstructor.
    + apply init.
    + apply P_O.
    + simpl_to_nat; lia.
    + simpl_to_nat; lia.
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

End TM3d.

