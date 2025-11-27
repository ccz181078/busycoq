From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.


Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC0RD_---1RA_1LE1RD_0LE1LF_1LC0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{A}} [1]^^b *> [0] *> [1]^^(1+c) *> r.

Lemma Inc1 a b c r:
  S1 a (3+b) c r -->*
  S1 (1+a) b (2+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*3+b) c r -->*
  S1 (n+a) b (n*2+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov1 a c r:
  S1 (1+a) 1 c r -->*
  S1 0 a 0 ([0] *> [1]^^(2+c) *> r).
Proof.
  es.
Qed.

Lemma Ov1_0 c r:
  halts tm (S1 0 1 c r).
Proof.
  esx.
Qed.

Lemma Ov0 a c d r:
  S1 a 0 c ([0] *> [1]^^d *> r) -->+
  S1 1 (a+c) (1+d) r.
Proof.
  es.
Qed.

Lemma Ov2 a c d r:
  S1 a 2 c ([0] *> [1]^^d *> r) -->+
  S1 1 (2+a+c) (1+d) r.
Proof.
  es.
Qed.

Close Scope sym.

Inductive v3: nat->nat->Prop :=
| v3_0 x:
  v3 (x*3+0) 0
| v3_2 x:
  v3 (x*3+2) 0
| v3_1 x i:
  v3 x i ->
  v3 ((1+x)*3+1) (S i).

Inductive v3': nat->nat->Prop :=
| v3'_0 x:
  v3' (x*3+0) 0
| v3'_2 x:
  v3' (x*3+2) 0
| v3'_1 x i:
  v3 x i ->
  v3' (x*3+1) (S i).

Lemma v3_v3 y i:
  y<3^i ->
  exists i',
  (forall x, v3 x i -> v3 (x+y) i') /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/3) as y1.
    remember (y mod 3) as y2.
    replace y with (y1*3+y2) in * by lia.
    destruct y2 as [|[|[|]]].
    4: lia.
    + unshelve epose proof (IHi (y1) _) as [i' [Hi' Hi0']].
      1: lia.
      eexists; split.
      * intros.
        inverts H0.
        specialize (Hi' _ H3).
        applys_eq (v3_1 _ _ Hi'); flia.
      * lia.
    + eexists; split.
      * intros.
        inverts H0.
        applys_eq (v3_2 (x0+y1+1)); flia.
      * lia.
    + eexists; split.
      * intros.
        inverts H0.
        applys_eq (v3_0 (x0+y1+2)); flia.
      * lia.
Qed.

Lemma v3_add3_v3' x i:
  v3 (x+3) i ->
  v3' x i.
Proof.
  intros.
  inverts H.
  - applys_eq (v3'_0 (x0-1)); flia.
  - applys_eq (v3'_2 (x0-1)); flia.
  - applys_eq (v3'_1 x0).
    1: flia.
    assumption.
Qed.


Lemma v3_v3' y i:
  y+3<3^i ->
  exists i',
  (forall x, v3 x i -> v3' (x+y) i') /\
  (i'<=i).
Proof.
  intros H.
  unshelve epose proof (v3_v3 (y+3) i _) as [i' [I1 I2]].
  1: lia.
  exists i'; split.
  2: lia.
  intros.
  apply v3_add3_v3'.
  applys_eq (I1 _ H0); flia.
Qed.

Inductive P: nat->Prop :=
| P_intro i y i'
  (Hv3a:forall x, v3 x i ->
    forall d r,
    S1 0 x 0 ([0] *> [1]^^d *> r)%sym -->+
    S1 1 (x+y*2) (1+d) r)
  (Hv3'a:forall x, v3' x i ->
    forall c d r,
    S1 1 x c ([0] *> [1]^^d *> r)%sym -->+
    S1 1 (x+c+y*2+1) (1+d) r)
  (Hi'a:forall x, v3 x i -> v3' (x+y*2) i')
  (Hi'b:i'<=i)
  (Hi'c:match i with
        | O => y=O /\ i'=O
        | S O => y=1 /\ i'=O
        | S (S i0) => y*2+3<3^i
        end)
  :
    P i.

Lemma P_i i:
  P i.
Proof.
  induction i using lt_wf_ind.
  destruct i.
  - eapply P_intro with (y:=O) (i':=O).
    + intros x Hx d r.
      inverts Hx.
      * follow Incs1.
        follow10 Ov0.
        finish.
      * follow Incs1.
        follow10 Ov2.
        finish.
    + intros x Hx c d r.
      inverts Hx.
      * follow Incs1.
        follow10 Ov0.
        finish.
      * follow Incs1.
        follow10 Ov2.
        finish.
    + intros.
      rewrite Nat.add_0_r.
      inverts H0.
      * apply v3'_0.
      * apply v3'_2.
    + lia.
    + lia.
  - epose proof (H i _) as I1.
    inverts I1.
    epose proof (H i' _) as I1.
    inverts I1.
    destruct i.
    {
      destruct Hi'c; subst.
      destruct Hi'c0; subst.
      eapply P_intro with (y:=1) (i':=O).
      + intros x Hx d r.
        inverts Hx.
        follow Incs1.
        rewrite Nat.add_0_r.
        follow Ov1.
        specialize (Hv3a _ H2).
        follow10 Hv3a.
        specialize (Hi'a _ H2).
        specialize (Hv3'a0 _ Hi'a).
        follow100 Hv3'a0.
        finish.
      + intros x Hx c d r.
        inverts Hx.
        follow Incs1.
        rewrite Nat.add_comm.
        follow Ov1.
        specialize (Hv3a _ H2).
        follow10 Hv3a.
        specialize (Hi'a _ H2).
        specialize (Hv3'a0 _ Hi'a).
        follow100 Hv3'a0.
        finish.
      + intros x Hx.
        inverts Hx.
        inverts H2.
        * applys_eq (v3'_0 (x*3+2)); flia.
        * applys_eq (v3'_0 (x*3+4)); flia.
      + lia.
      + lia.
    }
    {
      eassert ((y0 + y + 1)*2 + 3 < 3 ^ S (S i)) as E0. {
        destruct i.
        - destruct Hi'c; subst.
          destruct Hi'c0; subst.
          lia.
        - destruct i' as [|[|]];
          cbn[Nat.pow] in *.
          1,2: lia.
          pose proof (Nat.pow_le_mono_r 3 n i).
          lia.
      }
      epose proof (v3_v3' _ _ E0) as [i'' [E1 E2]].
      eapply P_intro with (y:=y+y0+1) (i':=i'').
      + intros x Hx d r.
        inverts Hx.
        follow Incs1.
        rewrite Nat.add_0_r.
        follow Ov1.
        specialize (Hv3a _ H2).
        follow10 Hv3a.
        specialize (Hi'a _ H2).
        specialize (Hv3'a0 _ Hi'a).
        follow100 Hv3'a0.
        finish.
      + intros x Hx c d r.
        inverts Hx.
        follow Incs1.
        rewrite Nat.add_comm.
        follow Ov1.
        specialize (Hv3a _ H2).
        follow10 Hv3a.
        specialize (Hi'a _ H2).
        specialize (Hv3'a0 _ Hi'a).
        follow100 Hv3'a0.
        finish.
      + intros.
        applys_eq (E1 _ H0); flia.
      + lia.
      + lia.
    }
  Unshelve.
  all: lia.
Qed.

Lemma v3_even x:
  exists i,
  v3 (x*2) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/3) as x1.
  remember (x mod 3) as x2.
  replace x with (x1*3+x2) in * by lia.
  destruct x2 as [|[|[|]]].
  4: lia.
  - exists O.
    applys_eq (v3_0 (x1*2)); flia.
  - exists O.
    applys_eq (v3_2 (x1*2)); flia.
  - unshelve epose proof (H x1 _) as [i I1].
    1: lia.
    exists (S i).
    applys_eq (v3_1 (x1*2)).
    1: flia.
    assumption.
Qed.

Lemma v3'_odd x:
  exists i,
  v3' (x*2+1) i.
Proof.
  epose proof (v3_even (x+2)) as [i I1].
  exists i.
  apply v3_add3_v3'.
  applys_eq I1; flia.
Qed.

Definition S n := S1 1 (n*2+1) 1 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  intros x.
  epose proof (v3'_odd x) as [i I1].
  epose proof (P_i i) as HP.
  inverts HP.
  specialize (Hv3'a _ I1 1 0 0inf%sym).
  cbn in Hv3'a.
  rewrite <-const_unfold in Hv3'a.
  unfold S.
  exists (x+y+1).
  follow10 Hv3'a.
  finish.
Qed.

End TM1.


Module TM31.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC0RD_---1LA_1LE1RD_0LE1LF_1LC0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{A}} [1]^^b *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (3+b) c r -->*
  S1 (1+a) b (2+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*3+b) c r -->*
  S1 (n+a) b (n*2+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d r:
  S1 a 0 c ([0] *> [1]^^d *> r) -->+
  S1 0 (2+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov2 a c d r:
  S1 a 2 c ([0] *> [1]^^d *> r) -->+
  S1 0 (4+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov1 a c r:
  S1 (1+a) 1 c r -->+
  S1 0 a 1 ([0] *> [1]^^(1+c) *> r).
Proof.
  es.
Qed.

Lemma Ov1_0 c r:
  halts tm (S1 0 1 c r).
Proof.
  unfold S1.
  esx.
Qed.

Close Scope sym.

Inductive v3: nat->nat->Prop :=
| v3_0 x:
  v3 (x*3+0) 0
| v3_2 x:
  v3 (x*3+2) 0
| v3_1 x i:
  v3 x i ->
  v3 ((1+x)*3+1) (S i).

Lemma v3_v3 y i:
  y<3^i ->
  exists i',
  (forall x, v3 x i -> v3 (x+y) i') /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/3) as y1.
    remember (y mod 3) as y2.
    replace y with (y1*3+y2) in * by lia.
    destruct y2 as [|[|[|]]].
    4: lia.
    + unshelve epose proof (IHi (y1) _) as [i' [Hi' Hi0']].
      1: lia.
      eexists; split.
      * intros.
        inverts H0.
        specialize (Hi' _ H3).
        applys_eq (v3_1 _ _ Hi'); flia.
      * lia.
    + eexists; split.
      * intros.
        inverts H0.
        applys_eq (v3_2 (x0+y1+1)); flia.
      * lia.
    + eexists; split.
      * intros.
        inverts H0.
        applys_eq (v3_0 (x0+y1+2)); flia.
      * lia.
Qed.


Inductive P: nat->Prop :=
| P_intro i y i'
  (Hv3a:forall x, v3 x i ->
    forall c d r,
    S1 0 x c ([0] *> [1]^^d *> r)%sym -->+
    S1 0 (x+c+y*2) d r)
  (Hi'a:forall x, v3 x i -> v3 (x+1+y*2) i')
  (Hi'b:i'<=i)
  (Hi'c:match i with
        | O => y=1 /\ i'=O
        | S O => y=2 /\ i'=O
        | S (S i0) => y*2<3^i
        end)
  :
    P i.

Lemma P_i i:
  P i.
Proof.
  induction i using lt_wf_ind.
  destruct i.
  - eapply P_intro with (y:=1).
    + intros x Hx c d r.
      inverts Hx.
      * follow Incs1.
        follow10 Ov0.
        finish.
      * follow Incs1.
        follow10 Ov2.
        finish.
    + intros x Hx.
      inverts Hx.
      * applys_eq (v3_0 (x0+1)); flia.
      * applys_eq (v3_2 (x0+1)); flia.
    + lia.
    + lia.
  - epose proof (H i _) as I1.
    inverts I1.
    epose proof (H i' _) as I1.
    inverts I1.
    destruct i.
    {
      destruct Hi'c; subst.
      destruct Hi'c0; subst.
      eapply P_intro with (y:=2) (i':=0).
      + intros x Hx c d r.
        inverts Hx.
        follow Incs1.
        rewrite Nat.add_0_r.
        follow10 Ov1.
        specialize (Hv3a _ H2).
        follow100 Hv3a.
        specialize (Hi'a _ H2).
        specialize (Hv3a0 _ Hi'a).
        follow100 Hv3a0.
        finish.
      + intros x Hx.
        inverts Hx.
        inverts H2.
        * applys_eq (v3_0 (x*3+3)); flia.
        * applys_eq (v3_0 (x*3+5)); flia.
      + lia.
      + lia.
    }
    {
      eassert ((y+y0)*2 + 1 < 3 ^ S (S i)) as E0. {
        destruct i.
        - destruct Hi'c; subst.
          destruct Hi'c0; subst.
          lia.
        - destruct i' as [|[|]];
          cbn[Nat.pow] in *.
          1,2: lia.
          pose proof (Nat.pow_le_mono_r 3 n i).
          lia.
      }
      epose proof (v3_v3 _ _ E0) as [i'' [E1 E2]].
      eapply P_intro with (y:=y+y0) (i':=_).
      + intros x Hx c d r.
        inverts Hx.
        follow Incs1.
        rewrite Nat.add_0_r.
        follow10 Ov1.
        specialize (Hv3a _ H2).
        follow100 Hv3a.
        specialize (Hi'a _ H2).
        specialize (Hv3a0 _ Hi'a).
        follow100 Hv3a0.
        finish.
      + intros x Hx.
        applys_eq (E1 _ Hx); flia.
      + lia.
      + lia.
    }
  Unshelve.
  all: lia.
Qed.

Lemma v3_even x:
  exists i,
  v3 (x*2) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/3) as x1.
  remember (x mod 3) as x2.
  replace x with (x1*3+x2) in * by lia.
  destruct x2 as [|[|[|]]].
  4: lia.
  - exists O.
    applys_eq (v3_0 (x1*2)); flia.
  - exists O.
    applys_eq (v3_2 (x1*2)); flia.
  - unshelve epose proof (H x1 _) as [i I1].
    1: lia.
    exists (S i).
    applys_eq (v3_1 (x1*2)).
    1: flia.
    assumption.
Qed.

Definition S n := S1 0 (n*2) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  intros x.
  epose proof (v3_even x) as [i I1].
  epose proof (P_i i) as HP.
  inverts HP.
  specialize (Hv3a _ I1 0 0 0inf%sym).
  cbn in Hv3a.
  rewrite <-const_unfold in Hv3a.
  unfold S.
  exists (x+y).
  follow10 Hv3a.
  finish.
Qed.

End TM31.


Module TM29.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LA0RC_1LD1RC_0LD1LE_1LF0LA_---1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{A}} [1]^^b *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (3+b) c r -->*
  S1 (1+a) b (2+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*3+b) c r -->*
  S1 (n+a) b (n*2+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d r:
  S1 a 0 c ([0] *> [1]^^d *> r) -->+
  S1 0 (2+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov2 a c d r:
  S1 a 2 c ([0] *> [1]^^d *> r) -->+
  S1 0 (4+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov1 a c r:
  S1 (1+a) 1 c r -->+
  S1 0 a 1 ([0] *> [1]^^(1+c) *> r).
Proof.
  es.
Qed.

Lemma Ov1_0 c r:
  halts tm (S1 0 1 c r).
Proof.
  unfold S1.
  esx.
Qed.

Close Scope sym.

Inductive v3: nat->nat->Prop :=
| v3_0 x:
  v3 (x*3+0) 0
| v3_2 x:
  v3 (x*3+2) 0
| v3_1 x i:
  v3 x i ->
  v3 ((1+x)*3+1) (S i).

Lemma v3_v3 y i:
  y<3^i ->
  exists i',
  (forall x, v3 x i -> v3 (x+y) i') /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/3) as y1.
    remember (y mod 3) as y2.
    replace y with (y1*3+y2) in * by lia.
    destruct y2 as [|[|[|]]].
    4: lia.
    + unshelve epose proof (IHi (y1) _) as [i' [Hi' Hi0']].
      1: lia.
      eexists; split.
      * intros.
        inverts H0.
        specialize (Hi' _ H3).
        applys_eq (v3_1 _ _ Hi'); flia.
      * lia.
    + eexists; split.
      * intros.
        inverts H0.
        applys_eq (v3_2 (x0+y1+1)); flia.
      * lia.
    + eexists; split.
      * intros.
        inverts H0.
        applys_eq (v3_0 (x0+y1+2)); flia.
      * lia.
Qed.


Inductive P: nat->Prop :=
| P_intro i y i'
  (Hv3a:forall x, v3 x i ->
    forall c d r,
    S1 0 x c ([0] *> [1]^^d *> r)%sym -->+
    S1 0 (x+c+y*2) d r)
  (Hi'a:forall x, v3 x i -> v3 (x+1+y*2) i')
  (Hi'b:i'<=i)
  (Hi'c:match i with
        | O => y=1 /\ i'=O
        | S O => y=2 /\ i'=O
        | S (S i0) => y*2<3^i
        end)
  :
    P i.

Lemma P_i i:
  P i.
Proof.
  induction i using lt_wf_ind.
  destruct i.
  - eapply P_intro with (y:=1).
    + intros x Hx c d r.
      inverts Hx.
      * follow Incs1.
        follow10 Ov0.
        finish.
      * follow Incs1.
        follow10 Ov2.
        finish.
    + intros x Hx.
      inverts Hx.
      * applys_eq (v3_0 (x0+1)); flia.
      * applys_eq (v3_2 (x0+1)); flia.
    + lia.
    + lia.
  - epose proof (H i _) as I1.
    inverts I1.
    epose proof (H i' _) as I1.
    inverts I1.
    destruct i.
    {
      destruct Hi'c; subst.
      destruct Hi'c0; subst.
      eapply P_intro with (y:=2) (i':=0).
      + intros x Hx c d r.
        inverts Hx.
        follow Incs1.
        rewrite Nat.add_0_r.
        follow10 Ov1.
        specialize (Hv3a _ H2).
        follow100 Hv3a.
        specialize (Hi'a _ H2).
        specialize (Hv3a0 _ Hi'a).
        follow100 Hv3a0.
        finish.
      + intros x Hx.
        inverts Hx.
        inverts H2.
        * applys_eq (v3_0 (x*3+3)); flia.
        * applys_eq (v3_0 (x*3+5)); flia.
      + lia.
      + lia.
    }
    {
      eassert ((y+y0)*2 + 1 < 3 ^ S (S i)) as E0. {
        destruct i.
        - destruct Hi'c; subst.
          destruct Hi'c0; subst.
          lia.
        - destruct i' as [|[|]];
          cbn[Nat.pow] in *.
          1,2: lia.
          pose proof (Nat.pow_le_mono_r 3 n i).
          lia.
      }
      epose proof (v3_v3 _ _ E0) as [i'' [E1 E2]].
      eapply P_intro with (y:=y+y0) (i':=_).
      + intros x Hx c d r.
        inverts Hx.
        follow Incs1.
        rewrite Nat.add_0_r.
        follow10 Ov1.
        specialize (Hv3a _ H2).
        follow100 Hv3a.
        specialize (Hi'a _ H2).
        specialize (Hv3a0 _ Hi'a).
        follow100 Hv3a0.
        finish.
      + intros x Hx.
        applys_eq (E1 _ Hx); flia.
      + lia.
      + lia.
    }
  Unshelve.
  all: lia.
Qed.

Lemma v3_even x:
  exists i,
  v3 (x*2) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/3) as x1.
  remember (x mod 3) as x2.
  replace x with (x1*3+x2) in * by lia.
  destruct x2 as [|[|[|]]].
  4: lia.
  - exists O.
    applys_eq (v3_0 (x1*2)); flia.
  - exists O.
    applys_eq (v3_2 (x1*2)); flia.
  - unshelve epose proof (H x1 _) as [i I1].
    1: lia.
    exists (S i).
    applys_eq (v3_1 (x1*2)).
    1: flia.
    assumption.
Qed.

Definition S n := S1 0 (n*2) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  intros x.
  epose proof (v3_even x) as [i I1].
  epose proof (P_i i) as HP.
  inverts HP.
  specialize (Hv3a _ I1 0 0 0inf%sym).
  cbn in Hv3a.
  rewrite <-const_unfold in Hv3a.
  unfold S.
  exists (x+y).
  follow10 Hv3a.
  finish.
Qed.

End TM29.


Module TM24.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LA0RC_1LD1RC_0LD1LE_0LF0LA_---1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{A}} [1]^^b *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (3+b) c r -->*
  S1 (1+a) b (2+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*3+b) c r -->*
  S1 (n+a) b (n*2+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d r:
  S1 a 0 c ([0] *> [1]^^d *> r) -->+
  S1 0 (2+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov2 a c d r:
  S1 a 2 c ([0] *> [1]^^d *> r) -->+
  S1 0 (4+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov1 a c r:
  S1 (1+a) 1 c r -->+
  S1 0 a 1 ([0] *> [1]^^(1+c) *> r).
Proof.
  es.
Qed.

Lemma Ov1_0 c r:
  halts tm (S1 0 1 c r).
Proof.
  unfold S1.
  esx.
Qed.

Close Scope sym.

Inductive v3: nat->nat->Prop :=
| v3_0 x:
  v3 (x*3+0) 0
| v3_2 x:
  v3 (x*3+2) 0
| v3_1 x i:
  v3 x i ->
  v3 ((1+x)*3+1) (S i).

Lemma v3_v3 y i:
  y<3^i ->
  exists i',
  (forall x, v3 x i -> v3 (x+y) i') /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/3) as y1.
    remember (y mod 3) as y2.
    replace y with (y1*3+y2) in * by lia.
    destruct y2 as [|[|[|]]].
    4: lia.
    + unshelve epose proof (IHi (y1) _) as [i' [Hi' Hi0']].
      1: lia.
      eexists; split.
      * intros.
        inverts H0.
        specialize (Hi' _ H3).
        applys_eq (v3_1 _ _ Hi'); flia.
      * lia.
    + eexists; split.
      * intros.
        inverts H0.
        applys_eq (v3_2 (x0+y1+1)); flia.
      * lia.
    + eexists; split.
      * intros.
        inverts H0.
        applys_eq (v3_0 (x0+y1+2)); flia.
      * lia.
Qed.


Inductive P: nat->Prop :=
| P_intro i y i'
  (Hv3a:forall x, v3 x i ->
    forall c d r,
    S1 0 x c ([0] *> [1]^^d *> r)%sym -->+
    S1 0 (x+c+y*2) d r)
  (Hi'a:forall x, v3 x i -> v3 (x+1+y*2) i')
  (Hi'b:i'<=i)
  (Hi'c:match i with
        | O => y=1 /\ i'=O
        | S O => y=2 /\ i'=O
        | S (S i0) => y*2<3^i
        end)
  :
    P i.

Lemma P_i i:
  P i.
Proof.
  induction i using lt_wf_ind.
  destruct i.
  - eapply P_intro with (y:=1).
    + intros x Hx c d r.
      inverts Hx.
      * follow Incs1.
        follow10 Ov0.
        finish.
      * follow Incs1.
        follow10 Ov2.
        finish.
    + intros x Hx.
      inverts Hx.
      * applys_eq (v3_0 (x0+1)); flia.
      * applys_eq (v3_2 (x0+1)); flia.
    + lia.
    + lia.
  - epose proof (H i _) as I1.
    inverts I1.
    epose proof (H i' _) as I1.
    inverts I1.
    destruct i.
    {
      destruct Hi'c; subst.
      destruct Hi'c0; subst.
      eapply P_intro with (y:=2) (i':=0).
      + intros x Hx c d r.
        inverts Hx.
        follow Incs1.
        rewrite Nat.add_0_r.
        follow10 Ov1.
        specialize (Hv3a _ H2).
        follow100 Hv3a.
        specialize (Hi'a _ H2).
        specialize (Hv3a0 _ Hi'a).
        follow100 Hv3a0.
        finish.
      + intros x Hx.
        inverts Hx.
        inverts H2.
        * applys_eq (v3_0 (x*3+3)); flia.
        * applys_eq (v3_0 (x*3+5)); flia.
      + lia.
      + lia.
    }
    {
      eassert ((y+y0)*2 + 1 < 3 ^ S (S i)) as E0. {
        destruct i.
        - destruct Hi'c; subst.
          destruct Hi'c0; subst.
          lia.
        - destruct i' as [|[|]];
          cbn[Nat.pow] in *.
          1,2: lia.
          pose proof (Nat.pow_le_mono_r 3 n i).
          lia.
      }
      epose proof (v3_v3 _ _ E0) as [i'' [E1 E2]].
      eapply P_intro with (y:=y+y0) (i':=_).
      + intros x Hx c d r.
        inverts Hx.
        follow Incs1.
        rewrite Nat.add_0_r.
        follow10 Ov1.
        specialize (Hv3a _ H2).
        follow100 Hv3a.
        specialize (Hi'a _ H2).
        specialize (Hv3a0 _ Hi'a).
        follow100 Hv3a0.
        finish.
      + intros x Hx.
        applys_eq (E1 _ Hx); flia.
      + lia.
      + lia.
    }
  Unshelve.
  all: lia.
Qed.

Lemma v3_even x:
  exists i,
  v3 (x*2) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/3) as x1.
  remember (x mod 3) as x2.
  replace x with (x1*3+x2) in * by lia.
  destruct x2 as [|[|[|]]].
  4: lia.
  - exists O.
    applys_eq (v3_0 (x1*2)); flia.
  - exists O.
    applys_eq (v3_2 (x1*2)); flia.
  - unshelve epose proof (H x1 _) as [i I1].
    1: lia.
    exists (S i).
    applys_eq (v3_1 (x1*2)).
    1: flia.
    assumption.
Qed.

Definition S n := S1 0 (n*2) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  intros x.
  epose proof (v3_even x) as [i I1].
  epose proof (P_i i) as HP.
  inverts HP.
  specialize (Hv3a _ I1 0 0 0inf%sym).
  cbn in Hv3a.
  rewrite <-const_unfold in Hv3a.
  unfold S.
  exists (x+y).
  follow10 Hv3a.
  finish.
Qed.

End TM24.


Module TM11.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LA0RC_1LD1RC_0LD1LE_1LF0LA_---1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{A}} [1]^^b *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (3+b) c r -->*
  S1 (1+a) b (2+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*3+b) c r -->*
  S1 (n+a) b (n*2+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d r:
  S1 a 0 c ([0] *> [1]^^d *> r) -->+
  S1 0 (2+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov2 a c d r:
  S1 a 2 c ([0] *> [1]^^d *> r) -->+
  S1 0 (4+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov1 a c r:
  S1 (1+a) 1 c r -->+
  S1 0 a 1 ([0] *> [1]^^(1+c) *> r).
Proof.
  es.
Qed.

Lemma Ov1_0 c r:
  halts tm (S1 0 1 c r).
Proof.
  unfold S1.
  esx.
Qed.

Close Scope sym.

Inductive v3: nat->nat->Prop :=
| v3_0 x:
  v3 (x*3+0) 0
| v3_2 x:
  v3 (x*3+2) 0
| v3_1 x i:
  v3 x i ->
  v3 ((1+x)*3+1) (S i).

Lemma v3_v3 y i:
  y<3^i ->
  exists i',
  (forall x, v3 x i -> v3 (x+y) i') /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/3) as y1.
    remember (y mod 3) as y2.
    replace y with (y1*3+y2) in * by lia.
    destruct y2 as [|[|[|]]].
    4: lia.
    + unshelve epose proof (IHi (y1) _) as [i' [Hi' Hi0']].
      1: lia.
      eexists; split.
      * intros.
        inverts H0.
        specialize (Hi' _ H3).
        applys_eq (v3_1 _ _ Hi'); flia.
      * lia.
    + eexists; split.
      * intros.
        inverts H0.
        applys_eq (v3_2 (x0+y1+1)); flia.
      * lia.
    + eexists; split.
      * intros.
        inverts H0.
        applys_eq (v3_0 (x0+y1+2)); flia.
      * lia.
Qed.


Inductive P: nat->Prop :=
| P_intro i y i'
  (Hv3a:forall x, v3 x i ->
    forall c d r,
    S1 0 x c ([0] *> [1]^^d *> r)%sym -->+
    S1 0 (x+c+y*2) d r)
  (Hi'a:forall x, v3 x i -> v3 (x+1+y*2) i')
  (Hi'b:i'<=i)
  (Hi'c:match i with
        | O => y=1 /\ i'=O
        | S O => y=2 /\ i'=O
        | S (S i0) => y*2<3^i
        end)
  :
    P i.

Lemma P_i i:
  P i.
Proof.
  induction i using lt_wf_ind.
  destruct i.
  - eapply P_intro with (y:=1).
    + intros x Hx c d r.
      inverts Hx.
      * follow Incs1.
        follow10 Ov0.
        finish.
      * follow Incs1.
        follow10 Ov2.
        finish.
    + intros x Hx.
      inverts Hx.
      * applys_eq (v3_0 (x0+1)); flia.
      * applys_eq (v3_2 (x0+1)); flia.
    + lia.
    + lia.
  - epose proof (H i _) as I1.
    inverts I1.
    epose proof (H i' _) as I1.
    inverts I1.
    destruct i.
    {
      destruct Hi'c; subst.
      destruct Hi'c0; subst.
      eapply P_intro with (y:=2) (i':=0).
      + intros x Hx c d r.
        inverts Hx.
        follow Incs1.
        rewrite Nat.add_0_r.
        follow10 Ov1.
        specialize (Hv3a _ H2).
        follow100 Hv3a.
        specialize (Hi'a _ H2).
        specialize (Hv3a0 _ Hi'a).
        follow100 Hv3a0.
        finish.
      + intros x Hx.
        inverts Hx.
        inverts H2.
        * applys_eq (v3_0 (x*3+3)); flia.
        * applys_eq (v3_0 (x*3+5)); flia.
      + lia.
      + lia.
    }
    {
      eassert ((y+y0)*2 + 1 < 3 ^ S (S i)) as E0. {
        destruct i.
        - destruct Hi'c; subst.
          destruct Hi'c0; subst.
          lia.
        - destruct i' as [|[|]];
          cbn[Nat.pow] in *.
          1,2: lia.
          pose proof (Nat.pow_le_mono_r 3 n i).
          lia.
      }
      epose proof (v3_v3 _ _ E0) as [i'' [E1 E2]].
      eapply P_intro with (y:=y+y0) (i':=_).
      + intros x Hx c d r.
        inverts Hx.
        follow Incs1.
        rewrite Nat.add_0_r.
        follow10 Ov1.
        specialize (Hv3a _ H2).
        follow100 Hv3a.
        specialize (Hi'a _ H2).
        specialize (Hv3a0 _ Hi'a).
        follow100 Hv3a0.
        finish.
      + intros x Hx.
        applys_eq (E1 _ Hx); flia.
      + lia.
      + lia.
    }
  Unshelve.
  all: lia.
Qed.

Lemma v3_even x:
  exists i,
  v3 (x*2) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/3) as x1.
  remember (x mod 3) as x2.
  replace x with (x1*3+x2) in * by lia.
  destruct x2 as [|[|[|]]].
  4: lia.
  - exists O.
    applys_eq (v3_0 (x1*2)); flia.
  - exists O.
    applys_eq (v3_2 (x1*2)); flia.
  - unshelve epose proof (H x1 _) as [i I1].
    1: lia.
    exists (S i).
    applys_eq (v3_1 (x1*2)).
    1: flia.
    assumption.
Qed.

Definition S n := S1 0 (n*2) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  intros x.
  epose proof (v3_even x) as [i I1].
  epose proof (P_i i) as HP.
  inverts HP.
  specialize (Hv3a _ I1 0 0 0inf%sym).
  cbn in Hv3a.
  rewrite <-const_unfold in Hv3a.
  unfold S.
  exists (x+y).
  follow10 Hv3a.
  finish.
Qed.

End TM11.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB1LA_0LB0RC_1LD1RC_1RA1LE_1LF0LA_---0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{A}} [1]^^b *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (3+b) c r -->*
  S1 (1+a) b (2+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*3+b) c r -->*
  S1 (n+a) b (n*2+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d r:
  S1 a 0 c ([0] *> [1]^^d *> r) -->+
  S1 0 (2+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov1 a c d r:
  S1 a 1 c ([0] *> [1]^^d *> r) -->+
  S1 0 (3+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov2 a c r:
  S1 (2+a) 2 c r -->+
  S1 0 a 1 ([0] *> [1]^^(3+c) *> r).
Proof.
  es.
Qed.

Lemma Ov2_1 c r:
  halts tm (S1 1 2 c r).
Proof.
  esx.
Qed.

Lemma Ov2_0 c d r:
  S1 0 2 c ([0] *> [1]^^d *> r) -->+
  S1 1 (3+c) d r.
Proof.
  es.
Qed.

Definition P x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*2+c) d r.

Lemma Step0 x:
  P (x*3+0) 1.
Proof.
  unfold P; intros.
  follow Incs1.
  follow10 Ov0.
  finish.
Qed.

Lemma Step1 x:
  P (x*3+1) 1.
Proof.
  unfold P; intros.
  follow Incs1.
  follow10 Ov1.
  finish.
Qed.

Lemma Step2 x y y0:
  P x y ->
  P (x+y*2+1) y0 ->
  P ((2+x)*3+2) (y+y0).
Proof.
  unfold P; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov2.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step2_0:
  P 14 2.
Proof.
  unfold P; intros.
  change 14 with ((2+2)*3+2).
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov2.
  follow100 Ov2_0.
  change (3+1) with (1*3+1).
  follow Incs1.
  follow100 Ov1.
  finish.
Qed.

Inductive v3: nat->nat->Prop :=
| v3_0 x: v3 (x*3+0) 0
| v3_1 x: v3 (x*3+1) 0
| v3_2 x i:
  v3 x i ->
  v3 ((2+x)*3+2) (S i)
| v3_2_0:
  v3 14 1
.

Lemma v3_v3 y i:
  y<3^i ->
  forall x,
  v3 x i ->
  exists i',
  v3 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/3) as y1.
    remember (y mod 3) as y2.
    replace y with (y1*3+y2) in * by lia.
    destruct y2 as [|[|[|]]].
    4: lia.
    + inverts H0.
      {
        unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
        1: lia.
        eexists; split.
        * applys_eq (v3_2 _ _ Hi'); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_2_0).
        * lia.
      }
    + inverts H0.
      {
        eexists; split.
        * applys_eq (v3_0 (x0+y1+3)); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_0 5).
        * lia.
      }
    + inverts H0.
      {
        eexists; split.
        * applys_eq (v3_1 (x0+y1+3)); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_1 5).
        * lia.
      }
Qed.


Inductive P': nat->nat->Prop :=
| P'_intro x i y i0
  (Ha:P x y)
  (Hb:v3 (x+y*2+1) i0)
  (Hc:i0 <= i)
  (Hd:(match i with
  | O => y=1 /\ i0=O
  | S O => y=2 /\ i0=O
  | S (S _) => y*2<3^i
  end)%nat)
  :
  P' x i.

Lemma P_i i x:
  v3 x i -> P' x i.
Proof.
  gen x.
  induction i using lt_wf_ind.
  intros x Hx.
  pose proof Hx as Hx'.
  inverts Hx.
  - econstructor.
    + apply Step0.
    + applys_eq (v3_0 (x0+1)); flia.
    + lia.
    + lia.
  - econstructor.
    + apply Step1.
    + applys_eq (v3_1 (x0+1)); flia.
    + lia.
    + lia.
  - unshelve epose proof (H _ _ _ H0) as I1.
    1: lia.
    inverts I1.
    unshelve epose proof (H _ _ _ Hb) as I1.
    1: lia.
    inverts I1.
    destruct i0 as [|[|]].
    + destruct Hd; subst.
      destruct Hd0; subst.
      econstructor.
      * eapply Step2; eassumption.
      * applys_eq (v3_1 (x0+4)); flia.
      * lia.
      * lia.
    + destruct Hd; subst.
      destruct Hd0; subst.
      econstructor.
      * eapply Step2; eassumption.
      * applys_eq (v3_0 (x0+5)); flia.
      * lia.
      * lia.
    + assert ((y+y0)*2+1<3^S (S (S n))) as E0. {
        destruct i1 as [|[|]]; cbn[Nat.pow] in *.
        1,2: lia.
        pose proof (Nat.pow_le_mono_r 3 n0 n).
        lia.
      }
      epose proof (v3_v3 _ _ E0 _ Hx') as [i' [E1 E2]].
      econstructor.
      * eapply Step2; eassumption.
      * applys_eq E1; flia.
      * lia.
      * lia.
  - econstructor.
    + apply Step2_0.
    + apply (v3_1 6).
    + lia.
    + lia.
  Unshelve.
Qed.

Lemma v3_even x:
  x<>1%nat ->
  exists i,
  v3 (x*2) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/3) as x1.
  remember (x mod 3) as x2.
  replace x with (x1*3+x2) in * by lia.
  destruct x2 as [|[|[|]]].
  4: lia.
  - exists O.
    applys_eq (v3_0 (x1*2)); flia.
  - destruct x1.
    1: lia.
    intros.
    destruct (Nat.eqb_spec x1 1).
    + subst.
      eexists.
      apply v3_2_0.
    + unshelve epose proof (H x1 _ _) as [i I1].
      1,2: lia.
      eexists.
      applys_eq (v3_2 _ _ I1); flia.
  - exists O.
    applys_eq (v3_1 (x1*2+1)); flia.
Qed.

Definition S n := S1 0 ((n+2)*2) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 1).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros x.
  epose proof (v3_even (x+2)) as [i I1].
  1: lia.
  epose proof (P_i i _ I1) as HP.
  inverts HP.
  unfold P in Ha.
  specialize (Ha O O 0inf).
  exists (x+y).
  cbn in Ha.
  rewrite <-const_unfold in Ha.
  follow10 Ha.
  finish.
Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1LB1RA_1LC1LE_1RD1LC_0LD0RA_1LF0LC_---0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{C}} [1]^^b *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (3+b) c r -->*
  S1 (1+a) b (2+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*3+b) c r -->*
  S1 (n+a) b (n*2+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d r:
  S1 a 0 c ([0] *> [1]^^d *> r) -->+
  S1 0 (2+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov1 a c d r:
  S1 a 1 c ([0] *> [1]^^d *> r) -->+
  S1 0 (3+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov2 a c r:
  S1 (2+a) 2 c r -->+
  S1 0 a 1 ([0] *> [1]^^(3+c) *> r).
Proof.
  es.
Qed.

Lemma Ov2_1 c r:
  halts tm (S1 1 2 c r).
Proof.
  esx.
Qed.

Lemma Ov2_0 c r:
  S1 0 2 c r -->+
  S1 0 1 (3+c) r.
Proof.
  es.
Qed.

Definition P x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*2+c) d r.

Lemma Step0 x:
  P (x*3+0) 1.
Proof.
  unfold P; intros.
  follow Incs1.
  follow10 Ov0.
  finish.
Qed.

Lemma Step1 x:
  P (x*3+1) 1.
Proof.
  unfold P; intros.
  follow Incs1.
  follow10 Ov1.
  finish.
Qed.

Lemma Step2 x y y0:
  P x y ->
  P (x+y*2+1) y0 ->
  P ((2+x)*3+2) (y+y0).
Proof.
  unfold P; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov2.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step2_0:
  P 2 2.
Proof.
  unfold P; intros.
  follow10 Ov2_0.
  follow100 Ov1.
  finish.
Qed.

Inductive v3: nat->nat->Prop :=
| v3_0 x: v3 (x*3+0) 0
| v3_1 x: v3 (x*3+1) 0
| v3_2 x i:
  v3 x i ->
  v3 ((2+x)*3+2) (S i)
| v3_2_0:
  v3 2 1
.

Lemma v3_v3 y i:
  y<3^i ->
  forall x,
  v3 x i ->
  exists i',
  v3 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/3) as y1.
    remember (y mod 3) as y2.
    replace y with (y1*3+y2) in * by lia.
    destruct y2 as [|[|[|]]].
    4: lia.
    + inverts H0.
      {
        unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
        1: lia.
        eexists; split.
        * applys_eq (v3_2 _ _ Hi'); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_2_0).
        * lia.
      }
    + inverts H0.
      {
        eexists; split.
        * applys_eq (v3_0 (x0+y1+3)); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_0 1).
        * lia.
      }
    + inverts H0.
      {
        eexists; split.
        * applys_eq (v3_1 (x0+y1+3)); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_1 1).
        * lia.
      }
Qed.


Inductive P': nat->nat->Prop :=
| P'_intro x i y i0
  (Ha:P x y)
  (Hb:v3 (x+y*2+1) i0)
  (Hc:i0 <= i)
  (Hd:(match i with
  | O => y=1 /\ i0=O
  | S O => y=2 /\ i0=O
  | S (S _) => y*2<3^i
  end)%nat)
  :
  P' x i.

Lemma P_i i x:
  v3 x i -> P' x i.
Proof.
  gen x.
  induction i using lt_wf_ind.
  intros x Hx.
  pose proof Hx as Hx'.
  inverts Hx.
  - econstructor.
    + apply Step0.
    + applys_eq (v3_0 (x0+1)); flia.
    + lia.
    + lia.
  - econstructor.
    + apply Step1.
    + applys_eq (v3_1 (x0+1)); flia.
    + lia.
    + lia.
  - unshelve epose proof (H _ _ _ H0) as I1.
    1: lia.
    inverts I1.
    unshelve epose proof (H _ _ _ Hb) as I1.
    1: lia.
    inverts I1.
    destruct i0 as [|[|]].
    + destruct Hd; subst.
      destruct Hd0; subst.
      econstructor.
      * eapply Step2; eassumption.
      * applys_eq (v3_1 (x0+4)); flia.
      * lia.
      * lia.
    + destruct Hd; subst.
      destruct Hd0; subst.
      econstructor.
      * eapply Step2; eassumption.
      * applys_eq (v3_0 (x0+5)); flia.
      * lia.
      * lia.
    + assert ((y+y0)*2+1<3^S (S (S n))) as E0. {
        destruct i1 as [|[|]]; cbn[Nat.pow] in *.
        1,2: lia.
        pose proof (Nat.pow_le_mono_r 3 n0 n).
        lia.
      }
      epose proof (v3_v3 _ _ E0 _ Hx') as [i' [E1 E2]].
      econstructor.
      * eapply Step2; eassumption.
      * applys_eq E1; flia.
      * lia.
      * lia.
  - econstructor.
    + apply Step2_0.
    + apply (v3_1 2).
    + lia.
    + lia.
Qed.

Lemma v3_even x:
  exists i,
  v3 (x*2) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/3) as x1.
  remember (x mod 3) as x2.
  replace x with (x1*3+x2) in * by lia.
  destruct x2 as [|[|[|]]].
  4: lia.
  - exists O.
    applys_eq (v3_0 (x1*2)); flia.
  - destruct x1.
    + eexists.
      apply v3_2_0.
    + unshelve epose proof (H x1 _) as [i I1].
      1: lia.
      eexists.
      applys_eq (v3_2 _ _ I1); flia.
  - exists O.
    applys_eq (v3_1 (x1*2+1)); flia.
Qed.

Definition S n := S1 0 (n*2) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 1).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros x.
  epose proof (v3_even (x)) as [i I1].
  epose proof (P_i i _ I1) as HP.
  inverts HP.
  unfold P in Ha.
  specialize (Ha O O 0inf).
  exists (x+y).
  cbn in Ha.
  rewrite <-const_unfold in Ha.
  follow10 Ha.
  finish.
Qed.

End TM3.


Module TM6.
Definition tm := Eval compute in (TM_from_str "1LB1RA_1RC1LE_1RD1LC_1LC0RA_1LF0LC_---0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{C}} [1]^^b *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (3+b) c r -->*
  S1 (1+a) b (2+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*3+b) c r -->*
  S1 (n+a) b (n*2+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d r:
  S1 a 0 c ([0] *> [1]^^d *> r) -->+
  S1 0 (2+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov1 a c d r:
  S1 a 1 c ([0] *> [1]^^d *> r) -->+
  S1 0 (3+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov2 a c r:
  S1 (2+a) 2 c r -->+
  S1 0 a 1 ([0] *> [1]^^(3+c) *> r).
Proof.
  es.
Qed.

Lemma Ov2_1 c r:
  halts tm (S1 1 2 c r).
Proof.
  esx.
Qed.

Lemma Ov2_0 c d r:
  S1 0 2 c ([0] *> [1]^^d *> r) -->+
  S1 1 (3+c) d r.
Proof.
  es.
Qed.

Definition P x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*2+c) d r.

Lemma Step0 x:
  P (x*3+0) 1.
Proof.
  unfold P; intros.
  follow Incs1.
  follow10 Ov0.
  finish.
Qed.

Lemma Step1 x:
  P (x*3+1) 1.
Proof.
  unfold P; intros.
  follow Incs1.
  follow10 Ov1.
  finish.
Qed.

Lemma Step2 x y y0:
  P x y ->
  P (x+y*2+1) y0 ->
  P ((2+x)*3+2) (y+y0).
Proof.
  unfold P; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov2.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step2_0:
  P 14 2.
Proof.
  unfold P; intros.
  change 14 with ((2+2)*3+2).
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov2.
  follow100 Ov2_0.
  change (3+1) with (1*3+1).
  follow Incs1.
  follow100 Ov1.
  finish.
Qed.


Inductive v3: nat->nat->Prop :=
| v3_0 x: v3 (x*3+0) 0
| v3_1 x: v3 (x*3+1) 0
| v3_2 x i:
  v3 x i ->
  v3 ((2+x)*3+2) (S i)
| v3_2_0:
  v3 14 1
.

Lemma v3_v3 y i:
  y<3^i ->
  forall x,
  v3 x i ->
  exists i',
  v3 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/3) as y1.
    remember (y mod 3) as y2.
    replace y with (y1*3+y2) in * by lia.
    destruct y2 as [|[|[|]]].
    4: lia.
    + inverts H0.
      {
        unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
        1: lia.
        eexists; split.
        * applys_eq (v3_2 _ _ Hi'); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_2_0).
        * lia.
      }
    + inverts H0.
      {
        eexists; split.
        * applys_eq (v3_0 (x0+y1+3)); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_0 5).
        * lia.
      }
    + inverts H0.
      {
        eexists; split.
        * applys_eq (v3_1 (x0+y1+3)); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_1 5).
        * lia.
      }
Qed.


Inductive P': nat->nat->Prop :=
| P'_intro x i y i0
  (Ha:P x y)
  (Hb:v3 (x+y*2+1) i0)
  (Hc:i0 <= i)
  (Hd:(match i with
  | O => y=1 /\ i0=O
  | S O => y=2 /\ i0=O
  | S (S _) => y*2<3^i
  end)%nat)
  :
  P' x i.

Lemma P_i i x:
  v3 x i -> P' x i.
Proof.
  gen x.
  induction i using lt_wf_ind.
  intros x Hx.
  pose proof Hx as Hx'.
  inverts Hx.
  - econstructor.
    + apply Step0.
    + applys_eq (v3_0 (x0+1)); flia.
    + lia.
    + lia.
  - econstructor.
    + apply Step1.
    + applys_eq (v3_1 (x0+1)); flia.
    + lia.
    + lia.
  - unshelve epose proof (H _ _ _ H0) as I1.
    1: lia.
    inverts I1.
    unshelve epose proof (H _ _ _ Hb) as I1.
    1: lia.
    inverts I1.
    destruct i0 as [|[|]].
    + destruct Hd; subst.
      destruct Hd0; subst.
      econstructor.
      * eapply Step2; eassumption.
      * applys_eq (v3_1 (x0+4)); flia.
      * lia.
      * lia.
    + destruct Hd; subst.
      destruct Hd0; subst.
      econstructor.
      * eapply Step2; eassumption.
      * applys_eq (v3_0 (x0+5)); flia.
      * lia.
      * lia.
    + assert ((y+y0)*2+1<3^S (S (S n))) as E0. {
        destruct i1 as [|[|]]; cbn[Nat.pow] in *.
        1,2: lia.
        pose proof (Nat.pow_le_mono_r 3 n0 n).
        lia.
      }
      epose proof (v3_v3 _ _ E0 _ Hx') as [i' [E1 E2]].
      econstructor.
      * eapply Step2; eassumption.
      * applys_eq E1; flia.
      * lia.
      * lia.
  - econstructor.
    + apply Step2_0.
    + apply (v3_1 6).
    + lia.
    + lia.
  Unshelve.
Qed.

Lemma v3_even x:
  x<>1%nat ->
  exists i,
  v3 (x*2) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/3) as x1.
  remember (x mod 3) as x2.
  replace x with (x1*3+x2) in * by lia.
  destruct x2 as [|[|[|]]].
  4: lia.
  - exists O.
    applys_eq (v3_0 (x1*2)); flia.
  - destruct x1.
    1: lia.
    intros.
    destruct (Nat.eqb_spec x1 1).
    + subst.
      eexists.
      apply v3_2_0.
    + unshelve epose proof (H x1 _ _) as [i I1].
      1,2: lia.
      eexists.
      applys_eq (v3_2 _ _ I1); flia.
  - exists O.
    applys_eq (v3_1 (x1*2+1)); flia.
Qed.

Definition S n := S1 0 ((n+2)*2) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 1).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros x.
  epose proof (v3_even (x+2)) as [i I1].
  1: lia.
  epose proof (P_i i _ I1) as HP.
  inverts HP.
  unfold P in Ha.
  specialize (Ha O O 0inf).
  exists (x+y).
  cbn in Ha.
  rewrite <-const_unfold in Ha.
  follow10 Ha.
  finish.
Qed.

End TM6.

Module TM7.
Definition tm := Eval compute in (TM_from_str "1LB1RA_1LC1LE_1RD1LC_1LC0RA_1LF0LC_---0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{C}} [1]^^b *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (3+b) c r -->*
  S1 (1+a) b (2+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*3+b) c r -->*
  S1 (n+a) b (n*2+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d r:
  S1 a 0 c ([0] *> [1]^^d *> r) -->+
  S1 0 (2+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov1 a c d r:
  S1 a 1 c ([0] *> [1]^^d *> r) -->+
  S1 0 (3+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov2 a c r:
  S1 (2+a) 2 c r -->+
  S1 0 a 1 ([0] *> [1]^^(3+c) *> r).
Proof.
  es.
Qed.

Lemma Ov2_1 c r:
  halts tm (S1 1 2 c r).
Proof.
  esx.
Qed.

Lemma Ov2_0 c r:
  S1 0 2 c r -->+
  S1 0 1 (3+c) r.
Proof.
  es.
Qed.

Definition P x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*2+c) d r.

Lemma Step0 x:
  P (x*3+0) 1.
Proof.
  unfold P; intros.
  follow Incs1.
  follow10 Ov0.
  finish.
Qed.

Lemma Step1 x:
  P (x*3+1) 1.
Proof.
  unfold P; intros.
  follow Incs1.
  follow10 Ov1.
  finish.
Qed.

Lemma Step2 x y y0:
  P x y ->
  P (x+y*2+1) y0 ->
  P ((2+x)*3+2) (y+y0).
Proof.
  unfold P; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov2.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step2_0:
  P 2 2.
Proof.
  unfold P; intros.
  follow10 Ov2_0.
  follow100 Ov1.
  finish.
Qed.

Inductive v3: nat->nat->Prop :=
| v3_0 x: v3 (x*3+0) 0
| v3_1 x: v3 (x*3+1) 0
| v3_2 x i:
  v3 x i ->
  v3 ((2+x)*3+2) (S i)
| v3_2_0:
  v3 2 1
.

Lemma v3_v3 y i:
  y<3^i ->
  forall x,
  v3 x i ->
  exists i',
  v3 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/3) as y1.
    remember (y mod 3) as y2.
    replace y with (y1*3+y2) in * by lia.
    destruct y2 as [|[|[|]]].
    4: lia.
    + inverts H0.
      {
        unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
        1: lia.
        eexists; split.
        * applys_eq (v3_2 _ _ Hi'); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_2_0).
        * lia.
      }
    + inverts H0.
      {
        eexists; split.
        * applys_eq (v3_0 (x0+y1+3)); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_0 1).
        * lia.
      }
    + inverts H0.
      {
        eexists; split.
        * applys_eq (v3_1 (x0+y1+3)); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_1 1).
        * lia.
      }
Qed.


Inductive P': nat->nat->Prop :=
| P'_intro x i y i0
  (Ha:P x y)
  (Hb:v3 (x+y*2+1) i0)
  (Hc:i0 <= i)
  (Hd:(match i with
  | O => y=1 /\ i0=O
  | S O => y=2 /\ i0=O
  | S (S _) => y*2<3^i
  end)%nat)
  :
  P' x i.

Lemma P_i i x:
  v3 x i -> P' x i.
Proof.
  gen x.
  induction i using lt_wf_ind.
  intros x Hx.
  pose proof Hx as Hx'.
  inverts Hx.
  - econstructor.
    + apply Step0.
    + applys_eq (v3_0 (x0+1)); flia.
    + lia.
    + lia.
  - econstructor.
    + apply Step1.
    + applys_eq (v3_1 (x0+1)); flia.
    + lia.
    + lia.
  - unshelve epose proof (H _ _ _ H0) as I1.
    1: lia.
    inverts I1.
    unshelve epose proof (H _ _ _ Hb) as I1.
    1: lia.
    inverts I1.
    destruct i0 as [|[|]].
    + destruct Hd; subst.
      destruct Hd0; subst.
      econstructor.
      * eapply Step2; eassumption.
      * applys_eq (v3_1 (x0+4)); flia.
      * lia.
      * lia.
    + destruct Hd; subst.
      destruct Hd0; subst.
      econstructor.
      * eapply Step2; eassumption.
      * applys_eq (v3_0 (x0+5)); flia.
      * lia.
      * lia.
    + assert ((y+y0)*2+1<3^S (S (S n))) as E0. {
        destruct i1 as [|[|]]; cbn[Nat.pow] in *.
        1,2: lia.
        pose proof (Nat.pow_le_mono_r 3 n0 n).
        lia.
      }
      epose proof (v3_v3 _ _ E0 _ Hx') as [i' [E1 E2]].
      econstructor.
      * eapply Step2; eassumption.
      * applys_eq E1; flia.
      * lia.
      * lia.
  - econstructor.
    + apply Step2_0.
    + apply (v3_1 2).
    + lia.
    + lia.
Qed.

Lemma v3_even x:
  exists i,
  v3 (x*2) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/3) as x1.
  remember (x mod 3) as x2.
  replace x with (x1*3+x2) in * by lia.
  destruct x2 as [|[|[|]]].
  4: lia.
  - exists O.
    applys_eq (v3_0 (x1*2)); flia.
  - destruct x1.
    + eexists.
      apply v3_2_0.
    + unshelve epose proof (H x1 _) as [i I1].
      1: lia.
      eexists.
      applys_eq (v3_2 _ _ I1); flia.
  - exists O.
    applys_eq (v3_1 (x1*2+1)); flia.
Qed.

Definition S n := S1 0 (n*2) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 1).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros x.
  epose proof (v3_even (x)) as [i I1].
  epose proof (P_i i _ I1) as HP.
  inverts HP.
  unfold P in Ha.
  specialize (Ha O O 0inf).
  exists (x+y).
  cbn in Ha.
  rewrite <-const_unfold in Ha.
  follow10 Ha.
  finish.
Qed.

End TM7.


Module TM13.
Definition tm := Eval compute in (TM_from_str "1LB0LF_1RC1LB_---0RD_1LE1RD_0LE1LA_1LC1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{B}} [1]^^(1+b) *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (3+b) c r -->*
  S1 (1+a) b (2+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*3+b) c r -->*
  S1 (n+a) b (n*2+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c r:
  S1 (2+a) 0 c r -->+
  S1 0 a 1 ([0] *> [1]^^(1+c) *> r).
Proof.
  es.
Qed.

Lemma Ov0_1 c r:
  halts tm (S1 1 0 c r).
Proof.
  unfold S1.
  esx.
Qed.

Lemma Ov0_0 c r:
  S1 0 0 c r -->+
  S1 0 1 (1+c) r.
Proof.
  es.
Qed.

Lemma Ov1 a c d r:
  S1 a 1 c ([0] *> [1]^^d *> r) -->+
  S1 0 (3+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov2 a c d r:
  S1 a 2 c ([0] *> [1]^^d *> r) -->+
  S1 0 (4+a+c) d r.
Proof.
  es.
Qed.


Definition P x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*2+c) d r.

Lemma Step2 x:
  P (x*3+2) 1.
Proof.
  unfold P; intros.
  follow Incs1.
  follow10 Ov2.
  finish.
Qed.

Lemma Step1 x:
  P (x*3+1) 1.
Proof.
  unfold P; intros.
  follow Incs1.
  follow10 Ov1.
  finish.
Qed.

Lemma Step0 x y y0:
  P x y ->
  P (x+y*2+1) y0 ->
  P ((2+x)*3+0) (y+y0).
Proof.
  unfold P; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov0.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step2_0:
  P 0 2.
Proof.
  unfold P; intros.
  follow10 Ov0_0.
  follow100 Ov1.
  finish.
Qed.

Inductive v3: nat->nat->Prop :=
| v3_1 x: v3 (x*3+1) 0
| v3_2 x: v3 (x*3+2) 0
| v3_0 x i:
  v3 x i ->
  v3 ((2+x)*3+0) (S i)
| v3_0_0:
  v3 0 1
.

Lemma v3_v3 y i:
  y<3^i ->
  forall x,
  v3 x i ->
  exists i',
  v3 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/3) as y1.
    remember (y mod 3) as y2.
    replace y with (y1*3+y2) in * by lia.
    destruct y2 as [|[|[|]]].
    4: lia.
    + inverts H0.
      {
        unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
        1: lia.
        eexists; split.
        * applys_eq (v3_0 _ _ Hi'); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_0_0).
        * lia.
      }
    + inverts H0.
      {
        eexists; split.
        * applys_eq (v3_1 (x0+y1+2)); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_1 0).
        * lia.
      }
    + inverts H0.
      {
        eexists; split.
        * applys_eq (v3_2 (x0+y1+2)); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_2 0).
        * lia.
      }
Qed.


Inductive P': nat->nat->Prop :=
| P'_intro x i y i0
  (Ha:P x y)
  (Hb:v3 (x+y*2+1) i0)
  (Hc:i0 <= i)
  (Hd:(match i with
  | O => y=1 /\ i0=O
  | S O => y=2 /\ i0=O
  | S (S _) => y*2<3^i
  end)%nat)
  :
  P' x i.

Lemma P_i i x:
  v3 x i -> P' x i.
Proof.
  gen x.
  induction i using lt_wf_ind.
  intros x Hx.
  pose proof Hx as Hx'.
  inverts Hx.
  - econstructor.
    + apply Step1.
    + applys_eq (v3_1 (x0+1)); flia.
    + lia.
    + lia.
  - econstructor.
    + apply Step2.
    + applys_eq (v3_2 (x0+1)); flia.
    + lia.
    + lia.
  - unshelve epose proof (H _ _ _ H0) as I1.
    1: lia.
    inverts I1.
    unshelve epose proof (H _ _ _ Hb) as I1.
    1: lia.
    inverts I1.
    destruct i0 as [|[|]].
    + destruct Hd; subst.
      destruct Hd0; subst.
      econstructor.
      * eapply Step0; eassumption.
      * applys_eq (v3_2 (x0+3)); flia.
      * lia.
      * lia.
    + destruct Hd; subst.
      destruct Hd0; subst.
      econstructor.
      * eapply Step0; eassumption.
      * applys_eq (v3_1 (x0+4)); flia.
      * lia.
      * lia.
    + assert ((y+y0)*2+1<3^S (S (S n))) as E0. {
        destruct i1 as [|[|]]; cbn[Nat.pow] in *.
        1,2: lia.
        pose proof (Nat.pow_le_mono_r 3 n0 n).
        lia.
      }
      epose proof (v3_v3 _ _ E0 _ Hx') as [i' [E1 E2]].
      econstructor.
      * eapply Step0; eassumption.
      * applys_eq E1; flia.
      * lia.
      * lia.
  - econstructor.
    + apply Step2_0.
    + apply (v3_2 1).
    + lia.
    + lia.
Qed.

Lemma v3_even x:
  exists i,
  v3 (x*2) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/3) as x1.
  remember (x mod 3) as x2.
  replace x with (x1*3+x2) in * by lia.
  destruct x2 as [|[|[|]]].
  4: lia.
  - destruct x1.
    + eexists.
      apply v3_0_0.
    + unshelve epose proof (H x1 _) as [i I1].
      1: lia.
      eexists.
      applys_eq (v3_0 _ _ I1); flia.
  - exists O.
    applys_eq (v3_2 (x1*2)); flia.
  - exists O.
    applys_eq (v3_1 (x1*2+1)); flia.
Qed.

Definition S n := S1 0 (n*2) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros x.
  epose proof (v3_even (x)) as [i I1].
  epose proof (P_i i _ I1) as HP.
  inverts HP.
  unfold P in Ha.
  specialize (Ha O O 0inf).
  exists (x+y).
  cbn in Ha.
  rewrite <-const_unfold in Ha.
  follow10 Ha.
  finish.
Qed.

End TM13.


Module TM15.
Definition tm := Eval compute in (TM_from_str "1LB1RA_1LC1LE_1RD1LC_1LF0RA_0LD0LC_---0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{C}} [1]^^b *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (3+b) c r -->*
  S1 (1+a) b (2+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*3+b) c r -->*
  S1 (n+a) b (n*2+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c r:
  S1 (2+a) 0 c r -->+
  S1 0 a 1 ([0] *> [1]^^(1+c) *> r).
Proof.
  es.
Qed.

Lemma Ov0_1 c r:
  halts tm (S1 1 0 c r).
Proof.
  unfold S1.
  esx.
Qed.

Lemma Ov0_0 c r:
  S1 0 0 c r -->+
  S1 0 1 (1+c) r.
Proof.
  es.
Qed.

Lemma Ov1 a c d r:
  S1 a 1 c ([0] *> [1]^^d *> r) -->+
  S1 0 (3+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov2 a c d r:
  S1 a 2 c ([0] *> [1]^^d *> r) -->+
  S1 0 (4+a+c) d r.
Proof.
  es.
Qed.


Definition P x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*2+c) d r.

Lemma Step2 x:
  P (x*3+2) 1.
Proof.
  unfold P; intros.
  follow Incs1.
  follow10 Ov2.
  finish.
Qed.

Lemma Step1 x:
  P (x*3+1) 1.
Proof.
  unfold P; intros.
  follow Incs1.
  follow10 Ov1.
  finish.
Qed.

Lemma Step0 x y y0:
  P x y ->
  P (x+y*2+1) y0 ->
  P ((2+x)*3+0) (y+y0).
Proof.
  unfold P; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov0.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step2_0:
  P 0 2.
Proof.
  unfold P; intros.
  follow10 Ov0_0.
  follow100 Ov1.
  finish.
Qed.

Inductive v3: nat->nat->Prop :=
| v3_1 x: v3 (x*3+1) 0
| v3_2 x: v3 (x*3+2) 0
| v3_0 x i:
  v3 x i ->
  v3 ((2+x)*3+0) (S i)
| v3_0_0:
  v3 0 1
.

Lemma v3_v3 y i:
  y<3^i ->
  forall x,
  v3 x i ->
  exists i',
  v3 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/3) as y1.
    remember (y mod 3) as y2.
    replace y with (y1*3+y2) in * by lia.
    destruct y2 as [|[|[|]]].
    4: lia.
    + inverts H0.
      {
        unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
        1: lia.
        eexists; split.
        * applys_eq (v3_0 _ _ Hi'); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_0_0).
        * lia.
      }
    + inverts H0.
      {
        eexists; split.
        * applys_eq (v3_1 (x0+y1+2)); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_1 0).
        * lia.
      }
    + inverts H0.
      {
        eexists; split.
        * applys_eq (v3_2 (x0+y1+2)); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_2 0).
        * lia.
      }
Qed.


Inductive P': nat->nat->Prop :=
| P'_intro x i y i0
  (Ha:P x y)
  (Hb:v3 (x+y*2+1) i0)
  (Hc:i0 <= i)
  (Hd:(match i with
  | O => y=1 /\ i0=O
  | S O => y=2 /\ i0=O
  | S (S _) => y*2<3^i
  end)%nat)
  :
  P' x i.

Lemma P_i i x:
  v3 x i -> P' x i.
Proof.
  gen x.
  induction i using lt_wf_ind.
  intros x Hx.
  pose proof Hx as Hx'.
  inverts Hx.
  - econstructor.
    + apply Step1.
    + applys_eq (v3_1 (x0+1)); flia.
    + lia.
    + lia.
  - econstructor.
    + apply Step2.
    + applys_eq (v3_2 (x0+1)); flia.
    + lia.
    + lia.
  - unshelve epose proof (H _ _ _ H0) as I1.
    1: lia.
    inverts I1.
    unshelve epose proof (H _ _ _ Hb) as I1.
    1: lia.
    inverts I1.
    destruct i0 as [|[|]].
    + destruct Hd; subst.
      destruct Hd0; subst.
      econstructor.
      * eapply Step0; eassumption.
      * applys_eq (v3_2 (x0+3)); flia.
      * lia.
      * lia.
    + destruct Hd; subst.
      destruct Hd0; subst.
      econstructor.
      * eapply Step0; eassumption.
      * applys_eq (v3_1 (x0+4)); flia.
      * lia.
      * lia.
    + assert ((y+y0)*2+1<3^S (S (S n))) as E0. {
        destruct i1 as [|[|]]; cbn[Nat.pow] in *.
        1,2: lia.
        pose proof (Nat.pow_le_mono_r 3 n0 n).
        lia.
      }
      epose proof (v3_v3 _ _ E0 _ Hx') as [i' [E1 E2]].
      econstructor.
      * eapply Step0; eassumption.
      * applys_eq E1; flia.
      * lia.
      * lia.
  - econstructor.
    + apply Step2_0.
    + apply (v3_2 1).
    + lia.
    + lia.
Qed.

Lemma v3_even x:
  exists i,
  v3 (x*2) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/3) as x1.
  remember (x mod 3) as x2.
  replace x with (x1*3+x2) in * by lia.
  destruct x2 as [|[|[|]]].
  4: lia.
  - destruct x1.
    + eexists.
      apply v3_0_0.
    + unshelve epose proof (H x1 _) as [i I1].
      1: lia.
      eexists.
      applys_eq (v3_0 _ _ I1); flia.
  - exists O.
    applys_eq (v3_2 (x1*2)); flia.
  - exists O.
    applys_eq (v3_1 (x1*2+1)); flia.
Qed.

Definition S n := S1 0 (n*2) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 1).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros x.
  epose proof (v3_even (x)) as [i I1].
  epose proof (P_i i _ I1) as HP.
  inverts HP.
  unfold P in Ha.
  specialize (Ha O O 0inf).
  exists (x+y).
  cbn in Ha.
  rewrite <-const_unfold in Ha.
  follow10 Ha.
  finish.
Qed.

End TM15.


Module TM23.
Definition tm := Eval compute in (TM_from_str "1RB0LB_1LC1LF_---0RD_1LE1RD_0LE1LA_1RC1LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{F}} [1]^^(1+b) *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (3+b) c r -->*
  S1 (1+a) b (2+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*3+b) c r -->*
  S1 (n+a) b (n*2+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c r:
  S1 (2+a) 0 c r -->+
  S1 0 a 1 ([0] *> [1]^^(1+c) *> r).
Proof.
  es.
Qed.

Lemma Ov0_1 c r:
  halts tm (S1 1 0 c r).
Proof.
  unfold S1.
  esx.
Qed.

Lemma Ov0_0 c r:
  S1 0 0 c r -->+
  S1 0 1 (1+c) r.
Proof.
  es.
Qed.

Lemma Ov1 a c d r:
  S1 a 1 c ([0] *> [1]^^d *> r) -->+
  S1 0 (3+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov2 a c d r:
  S1 a 2 c ([0] *> [1]^^d *> r) -->+
  S1 0 (4+a+c) d r.
Proof.
  es.
Qed.


Definition P x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*2+c) d r.

Lemma Step2 x:
  P (x*3+2) 1.
Proof.
  unfold P; intros.
  follow Incs1.
  follow10 Ov2.
  finish.
Qed.

Lemma Step1 x:
  P (x*3+1) 1.
Proof.
  unfold P; intros.
  follow Incs1.
  follow10 Ov1.
  finish.
Qed.

Lemma Step0 x y y0:
  P x y ->
  P (x+y*2+1) y0 ->
  P ((2+x)*3+0) (y+y0).
Proof.
  unfold P; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov0.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step2_0:
  P 0 2.
Proof.
  unfold P; intros.
  follow10 Ov0_0.
  follow100 Ov1.
  finish.
Qed.

Inductive v3: nat->nat->Prop :=
| v3_1 x: v3 (x*3+1) 0
| v3_2 x: v3 (x*3+2) 0
| v3_0 x i:
  v3 x i ->
  v3 ((2+x)*3+0) (S i)
| v3_0_0:
  v3 0 1
.

Lemma v3_v3 y i:
  y<3^i ->
  forall x,
  v3 x i ->
  exists i',
  v3 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/3) as y1.
    remember (y mod 3) as y2.
    replace y with (y1*3+y2) in * by lia.
    destruct y2 as [|[|[|]]].
    4: lia.
    + inverts H0.
      {
        unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
        1: lia.
        eexists; split.
        * applys_eq (v3_0 _ _ Hi'); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_0_0).
        * lia.
      }
    + inverts H0.
      {
        eexists; split.
        * applys_eq (v3_1 (x0+y1+2)); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_1 0).
        * lia.
      }
    + inverts H0.
      {
        eexists; split.
        * applys_eq (v3_2 (x0+y1+2)); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_2 0).
        * lia.
      }
Qed.


Inductive P': nat->nat->Prop :=
| P'_intro x i y i0
  (Ha:P x y)
  (Hb:v3 (x+y*2+1) i0)
  (Hc:i0 <= i)
  (Hd:(match i with
  | O => y=1 /\ i0=O
  | S O => y=2 /\ i0=O
  | S (S _) => y*2<3^i
  end)%nat)
  :
  P' x i.

Lemma P_i i x:
  v3 x i -> P' x i.
Proof.
  gen x.
  induction i using lt_wf_ind.
  intros x Hx.
  pose proof Hx as Hx'.
  inverts Hx.
  - econstructor.
    + apply Step1.
    + applys_eq (v3_1 (x0+1)); flia.
    + lia.
    + lia.
  - econstructor.
    + apply Step2.
    + applys_eq (v3_2 (x0+1)); flia.
    + lia.
    + lia.
  - unshelve epose proof (H _ _ _ H0) as I1.
    1: lia.
    inverts I1.
    unshelve epose proof (H _ _ _ Hb) as I1.
    1: lia.
    inverts I1.
    destruct i0 as [|[|]].
    + destruct Hd; subst.
      destruct Hd0; subst.
      econstructor.
      * eapply Step0; eassumption.
      * applys_eq (v3_2 (x0+3)); flia.
      * lia.
      * lia.
    + destruct Hd; subst.
      destruct Hd0; subst.
      econstructor.
      * eapply Step0; eassumption.
      * applys_eq (v3_1 (x0+4)); flia.
      * lia.
      * lia.
    + assert ((y+y0)*2+1<3^S (S (S n))) as E0. {
        destruct i1 as [|[|]]; cbn[Nat.pow] in *.
        1,2: lia.
        pose proof (Nat.pow_le_mono_r 3 n0 n).
        lia.
      }
      epose proof (v3_v3 _ _ E0 _ Hx') as [i' [E1 E2]].
      econstructor.
      * eapply Step0; eassumption.
      * applys_eq E1; flia.
      * lia.
      * lia.
  - econstructor.
    + apply Step2_0.
    + apply (v3_2 1).
    + lia.
    + lia.
Qed.

Lemma v3_even x:
  exists i,
  v3 (x*2) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/3) as x1.
  remember (x mod 3) as x2.
  replace x with (x1*3+x2) in * by lia.
  destruct x2 as [|[|[|]]].
  4: lia.
  - destruct x1.
    + eexists.
      apply v3_0_0.
    + unshelve epose proof (H x1 _) as [i I1].
      1: lia.
      eexists.
      applys_eq (v3_0 _ _ I1); flia.
  - exists O.
    applys_eq (v3_2 (x1*2)); flia.
  - exists O.
    applys_eq (v3_1 (x1*2+1)); flia.
Qed.

Definition S n := S1 0 (n*2) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 1).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros x.
  epose proof (v3_even (x)) as [i I1].
  epose proof (P_i i _ I1) as HP.
  inverts HP.
  unfold P in Ha.
  specialize (Ha O O 0inf).
  exists (x+y).
  cbn in Ha.
  rewrite <-const_unfold in Ha.
  follow10 Ha.
  finish.
Qed.

End TM23.


Module TM28.
Definition tm := Eval compute in (TM_from_str "1LB0LF_1RC0RE_---0RD_1LE1RD_0LE1LA_1LC1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{B}} [1]^^(1+b) *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (3+b) c r -->*
  S1 (1+a) b (2+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*3+b) c r -->*
  S1 (n+a) b (n*2+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c r:
  S1 (2+a) 0 c r -->+
  S1 0 a 1 ([0] *> [1]^^(1+c) *> r).
Proof.
  es.
Qed.

Lemma Ov0_1 c r:
  halts tm (S1 1 0 c r).
Proof.
  unfold S1.
  esx.
Qed.

Lemma Ov0_0 c r:
  S1 0 0 c r -->+
  S1 0 1 (1+c) r.
Proof.
  es.
Qed.

Lemma Ov1 a c d r:
  S1 a 1 c ([0] *> [1]^^d *> r) -->+
  S1 0 (3+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov2 a c d r:
  S1 a 2 c ([0] *> [1]^^d *> r) -->+
  S1 0 (4+a+c) d r.
Proof.
  es.
Qed.


Definition P x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*2+c) d r.

Lemma Step2 x:
  P (x*3+2) 1.
Proof.
  unfold P; intros.
  follow Incs1.
  follow10 Ov2.
  finish.
Qed.

Lemma Step1 x:
  P (x*3+1) 1.
Proof.
  unfold P; intros.
  follow Incs1.
  follow10 Ov1.
  finish.
Qed.

Lemma Step0 x y y0:
  P x y ->
  P (x+y*2+1) y0 ->
  P ((2+x)*3+0) (y+y0).
Proof.
  unfold P; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov0.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step2_0:
  P 0 2.
Proof.
  unfold P; intros.
  follow10 Ov0_0.
  follow100 Ov1.
  finish.
Qed.

Inductive v3: nat->nat->Prop :=
| v3_1 x: v3 (x*3+1) 0
| v3_2 x: v3 (x*3+2) 0
| v3_0 x i:
  v3 x i ->
  v3 ((2+x)*3+0) (S i)
| v3_0_0:
  v3 0 1
.

Lemma v3_v3 y i:
  y<3^i ->
  forall x,
  v3 x i ->
  exists i',
  v3 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/3) as y1.
    remember (y mod 3) as y2.
    replace y with (y1*3+y2) in * by lia.
    destruct y2 as [|[|[|]]].
    4: lia.
    + inverts H0.
      {
        unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
        1: lia.
        eexists; split.
        * applys_eq (v3_0 _ _ Hi'); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_0_0).
        * lia.
      }
    + inverts H0.
      {
        eexists; split.
        * applys_eq (v3_1 (x0+y1+2)); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_1 0).
        * lia.
      }
    + inverts H0.
      {
        eexists; split.
        * applys_eq (v3_2 (x0+y1+2)); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_2 0).
        * lia.
      }
Qed.


Inductive P': nat->nat->Prop :=
| P'_intro x i y i0
  (Ha:P x y)
  (Hb:v3 (x+y*2+1) i0)
  (Hc:i0 <= i)
  (Hd:(match i with
  | O => y=1 /\ i0=O
  | S O => y=2 /\ i0=O
  | S (S _) => y*2<3^i
  end)%nat)
  :
  P' x i.

Lemma P_i i x:
  v3 x i -> P' x i.
Proof.
  gen x.
  induction i using lt_wf_ind.
  intros x Hx.
  pose proof Hx as Hx'.
  inverts Hx.
  - econstructor.
    + apply Step1.
    + applys_eq (v3_1 (x0+1)); flia.
    + lia.
    + lia.
  - econstructor.
    + apply Step2.
    + applys_eq (v3_2 (x0+1)); flia.
    + lia.
    + lia.
  - unshelve epose proof (H _ _ _ H0) as I1.
    1: lia.
    inverts I1.
    unshelve epose proof (H _ _ _ Hb) as I1.
    1: lia.
    inverts I1.
    destruct i0 as [|[|]].
    + destruct Hd; subst.
      destruct Hd0; subst.
      econstructor.
      * eapply Step0; eassumption.
      * applys_eq (v3_2 (x0+3)); flia.
      * lia.
      * lia.
    + destruct Hd; subst.
      destruct Hd0; subst.
      econstructor.
      * eapply Step0; eassumption.
      * applys_eq (v3_1 (x0+4)); flia.
      * lia.
      * lia.
    + assert ((y+y0)*2+1<3^S (S (S n))) as E0. {
        destruct i1 as [|[|]]; cbn[Nat.pow] in *.
        1,2: lia.
        pose proof (Nat.pow_le_mono_r 3 n0 n).
        lia.
      }
      epose proof (v3_v3 _ _ E0 _ Hx') as [i' [E1 E2]].
      econstructor.
      * eapply Step0; eassumption.
      * applys_eq E1; flia.
      * lia.
      * lia.
  - econstructor.
    + apply Step2_0.
    + apply (v3_2 1).
    + lia.
    + lia.
Qed.

Lemma v3_even x:
  exists i,
  v3 (x*2) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/3) as x1.
  remember (x mod 3) as x2.
  replace x with (x1*3+x2) in * by lia.
  destruct x2 as [|[|[|]]].
  4: lia.
  - destruct x1.
    + eexists.
      apply v3_0_0.
    + unshelve epose proof (H x1 _) as [i I1].
      1: lia.
      eexists.
      applys_eq (v3_0 _ _ I1); flia.
  - exists O.
    applys_eq (v3_2 (x1*2)); flia.
  - exists O.
    applys_eq (v3_1 (x1*2+1)); flia.
Qed.

Definition S n := S1 0 (n*2) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros x.
  epose proof (v3_even (x)) as [i I1].
  epose proof (P_i i _ I1) as HP.
  inverts HP.
  unfold P in Ha.
  specialize (Ha O O 0inf).
  exists (x+y).
  cbn in Ha.
  rewrite <-const_unfold in Ha.
  follow10 Ha.
  finish.
Qed.

End TM28.


Module TM14.
Definition tm := Eval compute in (TM_from_str "1LB1RA_1RC1LE_1RD1LC_1LF0RA_0LD0LC_---0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{C}} [1]^^b *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (3+b) c r -->*
  S1 (1+a) b (2+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*3+b) c r -->*
  S1 (n+a) b (n*2+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c r:
  S1 (2+a) 0 c r -->+
  S1 0 a 1 ([0] *> [1]^^(1+c) *> r).
Proof.
  es.
Qed.

Lemma Ov0_1 c r:
  halts tm (S1 1 0 c r).
Proof.
  unfold S1.
  esx.
Qed.

Lemma Ov0_0 c d r:
  S1 0 0 c ([0] *> [1]^^d *> r) -->+
  S1 1 (1+c) d r.
Proof.
  es.
Qed.

Lemma Ov1 a c d r:
  S1 a 1 c ([0] *> [1]^^d *> r) -->+
  S1 0 (3+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov2 a c d r:
  S1 a 2 c ([0] *> [1]^^d *> r) -->+
  S1 0 (4+a+c) d r.
Proof.
  es.
Qed.


Definition P x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*2+c) d r.

Lemma Step2 x:
  P (x*3+2) 1.
Proof.
  unfold P; intros.
  follow Incs1.
  follow10 Ov2.
  finish.
Qed.

Lemma Step1 x:
  P (x*3+1) 1.
Proof.
  unfold P; intros.
  follow Incs1.
  follow10 Ov1.
  finish.
Qed.

Lemma Step0 x y y0:
  P x y ->
  P (x+y*2+1) y0 ->
  P ((2+x)*3+0) (y+y0).
Proof.
  unfold P; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov0.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step2_0:
  P 6 2.
Proof.
  unfold P; intros.
  change 6 with (2*3+0).
  follow Incs1.
  follow10 Ov0.
  follow100 Ov0_0.
  follow100 Ov2.
  repeat rewrite Nat.add_assoc.
  finish.
Qed.

Inductive v3: nat->nat->Prop :=
| v3_1 x: v3 (x*3+1) 0
| v3_2 x: v3 (x*3+2) 0
| v3_0 x i:
  v3 x i ->
  v3 ((2+x)*3+0) (S i)
| v3_0_0:
  v3 6 1
.

Lemma v3_v3 y i:
  y<3^i ->
  forall x,
  v3 x i ->
  exists i',
  v3 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/3) as y1.
    remember (y mod 3) as y2.
    replace y with (y1*3+y2) in * by lia.
    destruct y2 as [|[|[|]]].
    4: lia.
    + inverts H0.
      {
        unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
        1: lia.
        eexists; split.
        * applys_eq (v3_0 _ _ Hi'); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_0_0).
        * lia.
      }
    + inverts H0.
      {
        eexists; split.
        * applys_eq (v3_1 (x0+y1+2)); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_1 2).
        * lia.
      }
    + inverts H0.
      {
        eexists; split.
        * applys_eq (v3_2 (x0+y1+2)); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_2 2).
        * lia.
      }
Qed.


Inductive P': nat->nat->Prop :=
| P'_intro x i y i0
  (Ha:P x y)
  (Hb:v3 (x+y*2+1) i0)
  (Hc:i0 <= i)
  (Hd:(match i with
  | O => y=1 /\ i0=O
  | S O => y=2 /\ i0=O
  | S (S _) => y*2<3^i
  end)%nat)
  :
  P' x i.

Lemma P_i i x:
  v3 x i -> P' x i.
Proof.
  gen x.
  induction i using lt_wf_ind.
  intros x Hx.
  pose proof Hx as Hx'.
  inverts Hx.
  - econstructor.
    + apply Step1.
    + applys_eq (v3_1 (x0+1)); flia.
    + lia.
    + lia.
  - econstructor.
    + apply Step2.
    + applys_eq (v3_2 (x0+1)); flia.
    + lia.
    + lia.
  - unshelve epose proof (H _ _ _ H0) as I1.
    1: lia.
    inverts I1.
    unshelve epose proof (H _ _ _ Hb) as I1.
    1: lia.
    inverts I1.
    destruct i0 as [|[|]].
    + destruct Hd; subst.
      destruct Hd0; subst.
      econstructor.
      * eapply Step0; eassumption.
      * applys_eq (v3_2 (x0+3)); flia.
      * lia.
      * lia.
    + destruct Hd; subst.
      destruct Hd0; subst.
      econstructor.
      * eapply Step0; eassumption.
      * applys_eq (v3_1 (x0+4)); flia.
      * lia.
      * lia.
    + assert ((y+y0)*2+1<3^S (S (S n))) as E0. {
        destruct i1 as [|[|]]; cbn[Nat.pow] in *.
        1,2: lia.
        pose proof (Nat.pow_le_mono_r 3 n0 n).
        lia.
      }
      epose proof (v3_v3 _ _ E0 _ Hx') as [i' [E1 E2]].
      econstructor.
      * eapply Step0; eassumption.
      * applys_eq E1; flia.
      * lia.
      * lia.
  - econstructor.
    + apply Step2_0.
    + apply (v3_2 3).
    + lia.
    + lia.
Qed.

Lemma v3_even x:
  x<>O ->
  exists i,
  v3 (x*2) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/3) as x1.
  remember (x mod 3) as x2.
  replace x with (x1*3+x2) in * by lia.
  destruct x2 as [|[|[|]]].
  4: lia.
  - destruct x1.
    1: lia.
    intros.
    destruct (Nat.eqb_spec x1 O).
    + subst.
      eexists.
      apply v3_0_0.
    + unshelve epose proof (H x1 _ _) as [i I1].
      1,2: lia.
      eexists.
      applys_eq (v3_0 _ _ I1); flia.
  - exists O.
    applys_eq (v3_2 (x1*2)); flia.
  - exists O.
    applys_eq (v3_1 (x1*2+1)); flia.
Qed.

Definition S n := S1 0 ((n+2)*2) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 1).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros x.
  epose proof (v3_even (x+2)) as [i I1].
  1: lia.
  epose proof (P_i i _ I1) as HP.
  inverts HP.
  unfold P in Ha.
  specialize (Ha O O 0inf).
  exists (x+y).
  cbn in Ha.
  rewrite <-const_unfold in Ha.
  follow10 Ha.
  finish.
Qed.

End TM14.


Ltac rw_pow :=
  repeat rewrite Nat.pow_add_r in * by lia;
  cbn[Nat.pow] in *.

Module TM12.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC0RD_1LA1RC_1LE1RD_0LF0LA_---0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{A}} [1]^^b *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (2+b) c r -->*
  S1 (1+a) b (1+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*2+b) c r -->*
  S1 (n+a) b (n+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d e r:
  S1 a 0 c ([0] *> [1]^^d *> [0] *> [1]^^e *> r) -->+
  S1 0 (3+a+c+d) e r.
Proof.
  es.
Qed.

Lemma Ov1 a c r:
  S1 (1+a) 1 c r -->+
  S1 0 a 1 ([0] *> [1]^^(1+c) *> r).
Proof.
  es.
Qed.

Lemma Ov1_0 c r:
  halts tm (S1 0 1 c r).
Proof.
  unfold S1.
  esx.
Qed.

Definition P2 x y :=
  forall c d e r,
  S1 0 x c ([0] *> [1]^^d *> [0] *> [1]^^e *> r) -->+
  S1 0 (x+y*3+c+d) e r.

Definition P1 x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*3+c) d r.

Lemma Step0 x:
  P2 (x*2+0) 1.
Proof.
  unfold P2; intros.
  follow Incs1.
  follow10 Ov0.
  finish.
Qed.

Lemma Step1 x y:
  P2 x y ->
  P1 ((1+x)*2+1) y.
Proof.
  unfold P1,P2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  finish.
Qed.

Lemma Step1' x y y0:
  P1 x y ->
  P1 (x+y*3+1) y0 ->
  P1 ((1+x)*2+1) (y+y0).
Proof.
  unfold P1,P2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step1'' x y y0:
  P1 x y ->
  P2 (x+y*3+1) y0 ->
  P2 ((1+x)*2+1) (y+y0).
Proof.
  unfold P1,P2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  follow100 H0.
  finish.
Qed.


Inductive v2: nat->nat->Prop :=
| v2_0 x: v2 (x*2+0) 0
| v2_1 x i: v2 x i -> v2 ((1+x)*2+1) (S i)
.

Lemma v2_v2 y i:
  y<2^i ->
  forall x,
  v2 x i ->
  exists i',
  v2 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/2) as y1.
    remember (y mod 2) as y2.
    replace y with (y1*2+y2) in * by lia.
    destruct y2 as [|[|]].
    3: lia.
    + inverts H0.
      unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
      1: lia.
      eexists; split.
      * applys_eq (v2_1 _ _ Hi'); flia.
      * lia.
    + inverts H0.
      eexists; split.
      * applys_eq (v2_0 (x0+y1+2)); flia.
      * lia.
Qed.

Lemma P_0 x:
  v2 x 0 ->
  P2 x 1.
Proof.
  intros Hx.
  inverts Hx.
  apply Step0.
Qed.

Lemma P_1 x:
  v2 x 1 ->
  P1 x 1.
Proof.
  intros Hx.
  inverts Hx.
  apply Step1,P_0,H1.
Qed.

Lemma P_2 x:
  v2 x 2 ->
  P1 x 2.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1' _ 1 1).
  1: apply P_1,H1.
  inverts H1.
  inverts H2.
  applys_eq (P_1 _ (v2_1 _ _ (v2_0 (x0+1)))); flia.
Qed.

Lemma P_3 x:
  v2 x 3 ->
  P2 x 3.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1'' _ 2 1).
  1: apply P_2,H1.
  inverts H1.
  applys_eq (P_0 _ (v2_0 (x+5))); flia.
Qed.

Lemma P_4 x:
  v2 x 4 ->
  P1 x 3.
Proof.
  intros Hx.
  inverts Hx.
  eapply Step1,P_3,H1.
Qed.

Lemma P_i x i:
  v2 x i ->
  exists y, (P1 x y \/ P2 x y) /\ (i>=4 -> y*3+1<2^i).
Proof.
  gen x.
  induction i using lt_wf_ind.
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - right; apply P_0,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - left; apply P_1,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - left; apply P_2,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - right; apply P_3,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - left; apply P_4,Hx.
    - lia.
  }
  { 
    intros x Hx.
    inverts Hx.
    unshelve epose proof (H _ _ _ H2) as [y [I1 I2]].
    1: lia.
    destruct I1 as [I1|I1].
    2: {
      eexists; split.
      * left; eapply Step1,I1.
      * rw_pow; lia.
    }
    unshelve epose proof (v2_v2 _ _ (I2 _) _ H2) as [i' [E1 E2]].
    1: lia.
    destruct i'.
    {
      eexists; split.
      - right; eapply Step1''.
        + apply I1.
        + apply P_0; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - left; eapply Step1'.
        + apply I1.
        + apply P_1; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - left; eapply Step1'.
        + apply I1.
        + apply P_2; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - right; eapply Step1''.
        + apply I1.
        + apply P_3; applys_eq E1; flia.
      - rw_pow; lia.
    }
    {
      unshelve epose proof (H _ _ _ E1) as [y0 [I3 I4]].
      1: lia.
      destruct I3 as [I3|I3].
      {
        eexists; split.
        - left; eapply Step1'.
          + apply I1.
          + applys_eq I3; flia.
        - pose proof (Nat.pow_le_mono_r 2 i' i).
          rw_pow; lia.
      }
      {
        eexists; split.
        - right; eapply Step1''.
          + apply I1.
          + applys_eq I3; flia.
        - pose proof (Nat.pow_le_mono_r 2 i' i).
          rw_pow; lia.
      }
    }
  }
Qed.

Lemma v2_mod3 x:
  exists i,
  v2 (x*3) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/2) as x1.
  remember (x mod 2) as x2.
  replace x with (x1*2+x2) in * by lia.
  destruct x2 as [|[|]].
  3: lia.
  - exists O.
    applys_eq (v2_0 (x1*3)); flia.
  - unshelve epose proof (H x1 _) as [i I1].
    1: lia.
    eexists.
    applys_eq (v2_1 _ _ I1); flia.
Qed.

Definition S n := S1 0 (n*3) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros x.
  epose proof (v2_mod3 x) as [i I1].
  epose proof (P_i _ _ I1) as [y [I2 _]].
  unfold S1.
  destruct I2.
  - specialize (H O O 0inf).
    unfold S1 in H.
    cbn in *.
    repeat rewrite <-const_unfold in *.
    exists (x+y).
    follow10 H.
    finish.
  - specialize (H O O O 0inf).
    unfold S1 in H.
    cbn in *.
    repeat rewrite <-const_unfold in *.
    exists (x+y).
    follow10 H.
    finish.
Qed.

End TM12.


Module TM17.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC0RD_1LA1RC_1LE1RD_0LF0LA_---1LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{A}} [1]^^b *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (2+b) c r -->*
  S1 (1+a) b (1+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*2+b) c r -->*
  S1 (n+a) b (n+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d e r:
  S1 a 0 c ([0] *> [1]^^d *> [0] *> [1]^^e *> r) -->+
  S1 0 (3+a+c+d) e r.
Proof.
  es.
Qed.

Lemma Ov1 a c r:
  S1 (1+a) 1 c r -->+
  S1 0 a 1 ([0] *> [1]^^(1+c) *> r).
Proof.
  es.
Qed.

Lemma Ov1_0 c r:
  halts tm (S1 0 1 c r).
Proof.
  unfold S1.
  esx.
Qed.

Definition P2 x y :=
  forall c d e r,
  S1 0 x c ([0] *> [1]^^d *> [0] *> [1]^^e *> r) -->+
  S1 0 (x+y*3+c+d) e r.

Definition P1 x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*3+c) d r.

Lemma Step0 x:
  P2 (x*2+0) 1.
Proof.
  unfold P2; intros.
  follow Incs1.
  follow10 Ov0.
  finish.
Qed.

Lemma Step1 x y:
  P2 x y ->
  P1 ((1+x)*2+1) y.
Proof.
  unfold P1,P2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  finish.
Qed.

Lemma Step1' x y y0:
  P1 x y ->
  P1 (x+y*3+1) y0 ->
  P1 ((1+x)*2+1) (y+y0).
Proof.
  unfold P1,P2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step1'' x y y0:
  P1 x y ->
  P2 (x+y*3+1) y0 ->
  P2 ((1+x)*2+1) (y+y0).
Proof.
  unfold P1,P2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  follow100 H0.
  finish.
Qed.


Inductive v2: nat->nat->Prop :=
| v2_0 x: v2 (x*2+0) 0
| v2_1 x i: v2 x i -> v2 ((1+x)*2+1) (S i)
.

Lemma v2_v2 y i:
  y<2^i ->
  forall x,
  v2 x i ->
  exists i',
  v2 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/2) as y1.
    remember (y mod 2) as y2.
    replace y with (y1*2+y2) in * by lia.
    destruct y2 as [|[|]].
    3: lia.
    + inverts H0.
      unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
      1: lia.
      eexists; split.
      * applys_eq (v2_1 _ _ Hi'); flia.
      * lia.
    + inverts H0.
      eexists; split.
      * applys_eq (v2_0 (x0+y1+2)); flia.
      * lia.
Qed.

Lemma P_0 x:
  v2 x 0 ->
  P2 x 1.
Proof.
  intros Hx.
  inverts Hx.
  apply Step0.
Qed.

Lemma P_1 x:
  v2 x 1 ->
  P1 x 1.
Proof.
  intros Hx.
  inverts Hx.
  apply Step1,P_0,H1.
Qed.

Lemma P_2 x:
  v2 x 2 ->
  P1 x 2.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1' _ 1 1).
  1: apply P_1,H1.
  inverts H1.
  inverts H2.
  applys_eq (P_1 _ (v2_1 _ _ (v2_0 (x0+1)))); flia.
Qed.

Lemma P_3 x:
  v2 x 3 ->
  P2 x 3.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1'' _ 2 1).
  1: apply P_2,H1.
  inverts H1.
  applys_eq (P_0 _ (v2_0 (x+5))); flia.
Qed.

Lemma P_4 x:
  v2 x 4 ->
  P1 x 3.
Proof.
  intros Hx.
  inverts Hx.
  eapply Step1,P_3,H1.
Qed.

Lemma P_i x i:
  v2 x i ->
  exists y, (P1 x y \/ P2 x y) /\ (i>=4 -> y*3+1<2^i).
Proof.
  gen x.
  induction i using lt_wf_ind.
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - right; apply P_0,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - left; apply P_1,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - left; apply P_2,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - right; apply P_3,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - left; apply P_4,Hx.
    - lia.
  }
  { 
    intros x Hx.
    inverts Hx.
    unshelve epose proof (H _ _ _ H2) as [y [I1 I2]].
    1: lia.
    destruct I1 as [I1|I1].
    2: {
      eexists; split.
      * left; eapply Step1,I1.
      * rw_pow; lia.
    }
    unshelve epose proof (v2_v2 _ _ (I2 _) _ H2) as [i' [E1 E2]].
    1: lia.
    destruct i'.
    {
      eexists; split.
      - right; eapply Step1''.
        + apply I1.
        + apply P_0; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - left; eapply Step1'.
        + apply I1.
        + apply P_1; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - left; eapply Step1'.
        + apply I1.
        + apply P_2; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - right; eapply Step1''.
        + apply I1.
        + apply P_3; applys_eq E1; flia.
      - rw_pow; lia.
    }
    {
      unshelve epose proof (H _ _ _ E1) as [y0 [I3 I4]].
      1: lia.
      destruct I3 as [I3|I3].
      {
        eexists; split.
        - left; eapply Step1'.
          + apply I1.
          + applys_eq I3; flia.
        - pose proof (Nat.pow_le_mono_r 2 i' i).
          rw_pow; lia.
      }
      {
        eexists; split.
        - right; eapply Step1''.
          + apply I1.
          + applys_eq I3; flia.
        - pose proof (Nat.pow_le_mono_r 2 i' i).
          rw_pow; lia.
      }
    }
  }
Qed.

Lemma v2_mod3 x:
  exists i,
  v2 (x*3) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/2) as x1.
  remember (x mod 2) as x2.
  replace x with (x1*2+x2) in * by lia.
  destruct x2 as [|[|]].
  3: lia.
  - exists O.
    applys_eq (v2_0 (x1*3)); flia.
  - unshelve epose proof (H x1 _) as [i I1].
    1: lia.
    eexists.
    applys_eq (v2_1 _ _ I1); flia.
Qed.

Definition S n := S1 0 (n*3) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros x.
  epose proof (v2_mod3 x) as [i I1].
  epose proof (P_i _ _ I1) as [y [I2 _]].
  unfold S1.
  destruct I2.
  - specialize (H O O 0inf).
    unfold S1 in H.
    cbn in *.
    repeat rewrite <-const_unfold in *.
    exists (x+y).
    follow10 H.
    finish.
  - specialize (H O O O 0inf).
    unfold S1 in H.
    cbn in *.
    repeat rewrite <-const_unfold in *.
    exists (x+y).
    follow10 H.
    finish.
Qed.

End TM17.


Module TM19.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1RC0RD_1LA1RC_1LE1RD_0LF0LA_---1LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{A}} [1]^^b *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (2+b) c r -->*
  S1 (1+a) b (1+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*2+b) c r -->*
  S1 (n+a) b (n+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d e r:
  S1 a 0 c ([0] *> [1]^^d *> [0] *> [1]^^e *> r) -->+
  S1 0 (3+a+c+d) e r.
Proof.
  es.
Qed.

Lemma Ov1 a c r:
  S1 (1+a) 1 c r -->+
  S1 0 a 1 ([0] *> [1]^^(1+c) *> r).
Proof.
  es.
Qed.

Lemma Ov1_0 c r:
  halts tm (S1 0 1 c r).
Proof.
  unfold S1.
  esx.
Qed.

Definition P2 x y :=
  forall c d e r,
  S1 0 x c ([0] *> [1]^^d *> [0] *> [1]^^e *> r) -->+
  S1 0 (x+y*3+c+d) e r.

Definition P1 x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*3+c) d r.

Lemma Step0 x:
  P2 (x*2+0) 1.
Proof.
  unfold P2; intros.
  follow Incs1.
  follow10 Ov0.
  finish.
Qed.

Lemma Step1 x y:
  P2 x y ->
  P1 ((1+x)*2+1) y.
Proof.
  unfold P1,P2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  finish.
Qed.

Lemma Step1' x y y0:
  P1 x y ->
  P1 (x+y*3+1) y0 ->
  P1 ((1+x)*2+1) (y+y0).
Proof.
  unfold P1,P2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step1'' x y y0:
  P1 x y ->
  P2 (x+y*3+1) y0 ->
  P2 ((1+x)*2+1) (y+y0).
Proof.
  unfold P1,P2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  follow100 H0.
  finish.
Qed.


Inductive v2: nat->nat->Prop :=
| v2_0 x: v2 (x*2+0) 0
| v2_1 x i: v2 x i -> v2 ((1+x)*2+1) (S i)
.

Lemma v2_v2 y i:
  y<2^i ->
  forall x,
  v2 x i ->
  exists i',
  v2 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/2) as y1.
    remember (y mod 2) as y2.
    replace y with (y1*2+y2) in * by lia.
    destruct y2 as [|[|]].
    3: lia.
    + inverts H0.
      unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
      1: lia.
      eexists; split.
      * applys_eq (v2_1 _ _ Hi'); flia.
      * lia.
    + inverts H0.
      eexists; split.
      * applys_eq (v2_0 (x0+y1+2)); flia.
      * lia.
Qed.

Lemma P_0 x:
  v2 x 0 ->
  P2 x 1.
Proof.
  intros Hx.
  inverts Hx.
  apply Step0.
Qed.

Lemma P_1 x:
  v2 x 1 ->
  P1 x 1.
Proof.
  intros Hx.
  inverts Hx.
  apply Step1,P_0,H1.
Qed.

Lemma P_2 x:
  v2 x 2 ->
  P1 x 2.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1' _ 1 1).
  1: apply P_1,H1.
  inverts H1.
  inverts H2.
  applys_eq (P_1 _ (v2_1 _ _ (v2_0 (x0+1)))); flia.
Qed.

Lemma P_3 x:
  v2 x 3 ->
  P2 x 3.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1'' _ 2 1).
  1: apply P_2,H1.
  inverts H1.
  applys_eq (P_0 _ (v2_0 (x+5))); flia.
Qed.

Lemma P_4 x:
  v2 x 4 ->
  P1 x 3.
Proof.
  intros Hx.
  inverts Hx.
  eapply Step1,P_3,H1.
Qed.

Lemma P_i x i:
  v2 x i ->
  exists y, (P1 x y \/ P2 x y) /\ (i>=4 -> y*3+1<2^i).
Proof.
  gen x.
  induction i using lt_wf_ind.
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - right; apply P_0,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - left; apply P_1,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - left; apply P_2,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - right; apply P_3,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - left; apply P_4,Hx.
    - lia.
  }
  { 
    intros x Hx.
    inverts Hx.
    unshelve epose proof (H _ _ _ H2) as [y [I1 I2]].
    1: lia.
    destruct I1 as [I1|I1].
    2: {
      eexists; split.
      * left; eapply Step1,I1.
      * rw_pow; lia.
    }
    unshelve epose proof (v2_v2 _ _ (I2 _) _ H2) as [i' [E1 E2]].
    1: lia.
    destruct i'.
    {
      eexists; split.
      - right; eapply Step1''.
        + apply I1.
        + apply P_0; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - left; eapply Step1'.
        + apply I1.
        + apply P_1; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - left; eapply Step1'.
        + apply I1.
        + apply P_2; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - right; eapply Step1''.
        + apply I1.
        + apply P_3; applys_eq E1; flia.
      - rw_pow; lia.
    }
    {
      unshelve epose proof (H _ _ _ E1) as [y0 [I3 I4]].
      1: lia.
      destruct I3 as [I3|I3].
      {
        eexists; split.
        - left; eapply Step1'.
          + apply I1.
          + applys_eq I3; flia.
        - pose proof (Nat.pow_le_mono_r 2 i' i).
          rw_pow; lia.
      }
      {
        eexists; split.
        - right; eapply Step1''.
          + apply I1.
          + applys_eq I3; flia.
        - pose proof (Nat.pow_le_mono_r 2 i' i).
          rw_pow; lia.
      }
    }
  }
Qed.

Lemma v2_mod3 x:
  exists i,
  v2 (x*3) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/2) as x1.
  remember (x mod 2) as x2.
  replace x with (x1*2+x2) in * by lia.
  destruct x2 as [|[|]].
  3: lia.
  - exists O.
    applys_eq (v2_0 (x1*3)); flia.
  - unshelve epose proof (H x1 _) as [i I1].
    1: lia.
    eexists.
    applys_eq (v2_1 _ _ I1); flia.
Qed.

Definition S n := S1 0 (n*3) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros x.
  epose proof (v2_mod3 x) as [i I1].
  epose proof (P_i _ _ I1) as [y [I2 _]].
  unfold S1.
  destruct I2.
  - specialize (H O O 0inf).
    unfold S1 in H.
    cbn in *.
    repeat rewrite <-const_unfold in *.
    exists (x+y).
    follow10 H.
    finish.
  - specialize (H O O O 0inf).
    unfold S1 in H.
    cbn in *.
    repeat rewrite <-const_unfold in *.
    exists (x+y).
    follow10 H.
    finish.
Qed.

End TM19.


Module TM30.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1RC0RD_1LA1RC_1LE1RD_0LF0LA_---0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{A}} [1]^^b *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (2+b) c r -->*
  S1 (1+a) b (1+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*2+b) c r -->*
  S1 (n+a) b (n+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d e r:
  S1 a 0 c ([0] *> [1]^^d *> [0] *> [1]^^e *> r) -->+
  S1 0 (3+a+c+d) e r.
Proof.
  es.
Qed.

Lemma Ov1 a c r:
  S1 (1+a) 1 c r -->+
  S1 0 a 1 ([0] *> [1]^^(1+c) *> r).
Proof.
  es.
Qed.

Lemma Ov1_0 c r:
  halts tm (S1 0 1 c r).
Proof.
  unfold S1.
  esx.
Qed.

Definition P2 x y :=
  forall c d e r,
  S1 0 x c ([0] *> [1]^^d *> [0] *> [1]^^e *> r) -->+
  S1 0 (x+y*3+c+d) e r.

Definition P1 x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*3+c) d r.

Lemma Step0 x:
  P2 (x*2+0) 1.
Proof.
  unfold P2; intros.
  follow Incs1.
  follow10 Ov0.
  finish.
Qed.

Lemma Step1 x y:
  P2 x y ->
  P1 ((1+x)*2+1) y.
Proof.
  unfold P1,P2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  finish.
Qed.

Lemma Step1' x y y0:
  P1 x y ->
  P1 (x+y*3+1) y0 ->
  P1 ((1+x)*2+1) (y+y0).
Proof.
  unfold P1,P2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step1'' x y y0:
  P1 x y ->
  P2 (x+y*3+1) y0 ->
  P2 ((1+x)*2+1) (y+y0).
Proof.
  unfold P1,P2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  follow100 H0.
  finish.
Qed.


Inductive v2: nat->nat->Prop :=
| v2_0 x: v2 (x*2+0) 0
| v2_1 x i: v2 x i -> v2 ((1+x)*2+1) (S i)
.

Lemma v2_v2 y i:
  y<2^i ->
  forall x,
  v2 x i ->
  exists i',
  v2 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/2) as y1.
    remember (y mod 2) as y2.
    replace y with (y1*2+y2) in * by lia.
    destruct y2 as [|[|]].
    3: lia.
    + inverts H0.
      unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
      1: lia.
      eexists; split.
      * applys_eq (v2_1 _ _ Hi'); flia.
      * lia.
    + inverts H0.
      eexists; split.
      * applys_eq (v2_0 (x0+y1+2)); flia.
      * lia.
Qed.

Lemma P_0 x:
  v2 x 0 ->
  P2 x 1.
Proof.
  intros Hx.
  inverts Hx.
  apply Step0.
Qed.

Lemma P_1 x:
  v2 x 1 ->
  P1 x 1.
Proof.
  intros Hx.
  inverts Hx.
  apply Step1,P_0,H1.
Qed.

Lemma P_2 x:
  v2 x 2 ->
  P1 x 2.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1' _ 1 1).
  1: apply P_1,H1.
  inverts H1.
  inverts H2.
  applys_eq (P_1 _ (v2_1 _ _ (v2_0 (x0+1)))); flia.
Qed.

Lemma P_3 x:
  v2 x 3 ->
  P2 x 3.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1'' _ 2 1).
  1: apply P_2,H1.
  inverts H1.
  applys_eq (P_0 _ (v2_0 (x+5))); flia.
Qed.

Lemma P_4 x:
  v2 x 4 ->
  P1 x 3.
Proof.
  intros Hx.
  inverts Hx.
  eapply Step1,P_3,H1.
Qed.

Lemma P_i x i:
  v2 x i ->
  exists y, (P1 x y \/ P2 x y) /\ (i>=4 -> y*3+1<2^i).
Proof.
  gen x.
  induction i using lt_wf_ind.
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - right; apply P_0,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - left; apply P_1,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - left; apply P_2,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - right; apply P_3,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - left; apply P_4,Hx.
    - lia.
  }
  { 
    intros x Hx.
    inverts Hx.
    unshelve epose proof (H _ _ _ H2) as [y [I1 I2]].
    1: lia.
    destruct I1 as [I1|I1].
    2: {
      eexists; split.
      * left; eapply Step1,I1.
      * rw_pow; lia.
    }
    unshelve epose proof (v2_v2 _ _ (I2 _) _ H2) as [i' [E1 E2]].
    1: lia.
    destruct i'.
    {
      eexists; split.
      - right; eapply Step1''.
        + apply I1.
        + apply P_0; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - left; eapply Step1'.
        + apply I1.
        + apply P_1; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - left; eapply Step1'.
        + apply I1.
        + apply P_2; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - right; eapply Step1''.
        + apply I1.
        + apply P_3; applys_eq E1; flia.
      - rw_pow; lia.
    }
    {
      unshelve epose proof (H _ _ _ E1) as [y0 [I3 I4]].
      1: lia.
      destruct I3 as [I3|I3].
      {
        eexists; split.
        - left; eapply Step1'.
          + apply I1.
          + applys_eq I3; flia.
        - pose proof (Nat.pow_le_mono_r 2 i' i).
          rw_pow; lia.
      }
      {
        eexists; split.
        - right; eapply Step1''.
          + apply I1.
          + applys_eq I3; flia.
        - pose proof (Nat.pow_le_mono_r 2 i' i).
          rw_pow; lia.
      }
    }
  }
Qed.

Lemma v2_mod3 x:
  exists i,
  v2 (x*3) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/2) as x1.
  remember (x mod 2) as x2.
  replace x with (x1*2+x2) in * by lia.
  destruct x2 as [|[|]].
  3: lia.
  - exists O.
    applys_eq (v2_0 (x1*3)); flia.
  - unshelve epose proof (H x1 _) as [i I1].
    1: lia.
    eexists.
    applys_eq (v2_1 _ _ I1); flia.
Qed.

Definition S n := S1 0 (n*3) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros x.
  epose proof (v2_mod3 x) as [i I1].
  epose proof (P_i _ _ I1) as [y [I2 _]].
  unfold S1.
  destruct I2.
  - specialize (H O O 0inf).
    unfold S1 in H.
    cbn in *.
    repeat rewrite <-const_unfold in *.
    exists (x+y).
    follow10 H.
    finish.
  - specialize (H O O O 0inf).
    unfold S1 in H.
    cbn in *.
    repeat rewrite <-const_unfold in *.
    exists (x+y).
    follow10 H.
    finish.
Qed.

End TM30.


Module TM32.
Definition tm := Eval compute in (TM_from_str "1RB1RE_0RC---_1LD1RC_1LA0LF_1LF1RE_0LC0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{A}} [0] *> [1]^^b *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (2+b) c r -->*
  S1 (1+a) b (1+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*2+b) c r -->*
  S1 (n+a) b (n+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d e r:
  S1 a 0 c ([0] *> [1]^^d *> [0] *> [1]^^e *> r) -->+
  S1 0 (3+a+c+d) e r.
Proof.
  es.
Qed.

Lemma Ov1 a c r:
  S1 (1+a) 1 c r -->+
  S1 0 a 1 ([0] *> [1]^^(1+c) *> r).
Proof.
  es.
Qed.

Lemma Ov1_0 c r:
  halts tm (S1 0 1 c r).
Proof.
  unfold S1.
  esx.
Qed.

Definition P2 x y :=
  forall c d e r,
  S1 0 x c ([0] *> [1]^^d *> [0] *> [1]^^e *> r) -->+
  S1 0 (x+y*3+c+d) e r.

Definition P1 x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*3+c) d r.

Lemma Step0 x:
  P2 (x*2+0) 1.
Proof.
  unfold P2; intros.
  follow Incs1.
  follow10 Ov0.
  finish.
Qed.

Lemma Step1 x y:
  P2 x y ->
  P1 ((1+x)*2+1) y.
Proof.
  unfold P1,P2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  finish.
Qed.

Lemma Step1' x y y0:
  P1 x y ->
  P1 (x+y*3+1) y0 ->
  P1 ((1+x)*2+1) (y+y0).
Proof.
  unfold P1,P2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step1'' x y y0:
  P1 x y ->
  P2 (x+y*3+1) y0 ->
  P2 ((1+x)*2+1) (y+y0).
Proof.
  unfold P1,P2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  follow100 H0.
  finish.
Qed.


Inductive v2: nat->nat->Prop :=
| v2_0 x: v2 (x*2+0) 0
| v2_1 x i: v2 x i -> v2 ((1+x)*2+1) (S i)
.

Lemma v2_v2 y i:
  y<2^i ->
  forall x,
  v2 x i ->
  exists i',
  v2 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/2) as y1.
    remember (y mod 2) as y2.
    replace y with (y1*2+y2) in * by lia.
    destruct y2 as [|[|]].
    3: lia.
    + inverts H0.
      unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
      1: lia.
      eexists; split.
      * applys_eq (v2_1 _ _ Hi'); flia.
      * lia.
    + inverts H0.
      eexists; split.
      * applys_eq (v2_0 (x0+y1+2)); flia.
      * lia.
Qed.

Lemma P_0 x:
  v2 x 0 ->
  P2 x 1.
Proof.
  intros Hx.
  inverts Hx.
  apply Step0.
Qed.

Lemma P_1 x:
  v2 x 1 ->
  P1 x 1.
Proof.
  intros Hx.
  inverts Hx.
  apply Step1,P_0,H1.
Qed.

Lemma P_2 x:
  v2 x 2 ->
  P1 x 2.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1' _ 1 1).
  1: apply P_1,H1.
  inverts H1.
  inverts H2.
  applys_eq (P_1 _ (v2_1 _ _ (v2_0 (x0+1)))); flia.
Qed.

Lemma P_3 x:
  v2 x 3 ->
  P2 x 3.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1'' _ 2 1).
  1: apply P_2,H1.
  inverts H1.
  applys_eq (P_0 _ (v2_0 (x+5))); flia.
Qed.

Lemma P_4 x:
  v2 x 4 ->
  P1 x 3.
Proof.
  intros Hx.
  inverts Hx.
  eapply Step1,P_3,H1.
Qed.

Lemma P_i x i:
  v2 x i ->
  exists y, (P1 x y \/ P2 x y) /\ (i>=4 -> y*3+1<2^i).
Proof.
  gen x.
  induction i using lt_wf_ind.
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - right; apply P_0,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - left; apply P_1,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - left; apply P_2,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - right; apply P_3,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - left; apply P_4,Hx.
    - lia.
  }
  { 
    intros x Hx.
    inverts Hx.
    unshelve epose proof (H _ _ _ H2) as [y [I1 I2]].
    1: lia.
    destruct I1 as [I1|I1].
    2: {
      eexists; split.
      * left; eapply Step1,I1.
      * rw_pow; lia.
    }
    unshelve epose proof (v2_v2 _ _ (I2 _) _ H2) as [i' [E1 E2]].
    1: lia.
    destruct i'.
    {
      eexists; split.
      - right; eapply Step1''.
        + apply I1.
        + apply P_0; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - left; eapply Step1'.
        + apply I1.
        + apply P_1; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - left; eapply Step1'.
        + apply I1.
        + apply P_2; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - right; eapply Step1''.
        + apply I1.
        + apply P_3; applys_eq E1; flia.
      - rw_pow; lia.
    }
    {
      unshelve epose proof (H _ _ _ E1) as [y0 [I3 I4]].
      1: lia.
      destruct I3 as [I3|I3].
      {
        eexists; split.
        - left; eapply Step1'.
          + apply I1.
          + applys_eq I3; flia.
        - pose proof (Nat.pow_le_mono_r 2 i' i).
          rw_pow; lia.
      }
      {
        eexists; split.
        - right; eapply Step1''.
          + apply I1.
          + applys_eq I3; flia.
        - pose proof (Nat.pow_le_mono_r 2 i' i).
          rw_pow; lia.
      }
    }
  }
Qed.

Lemma v2_mod3 x:
  exists i,
  v2 (x*3) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/2) as x1.
  remember (x mod 2) as x2.
  replace x with (x1*2+x2) in * by lia.
  destruct x2 as [|[|]].
  3: lia.
  - exists O.
    applys_eq (v2_0 (x1*3)); flia.
  - unshelve epose proof (H x1 _) as [i I1].
    1: lia.
    eexists.
    applys_eq (v2_1 _ _ I1); flia.
Qed.

Definition S n := S1 0 (n*3) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros x.
  epose proof (v2_mod3 x) as [i I1].
  epose proof (P_i _ _ I1) as [y [I2 _]].
  unfold S1.
  destruct I2.
  - specialize (H O O 0inf).
    unfold S1 in H.
    cbn in *.
    repeat rewrite <-const_unfold in *.
    exists (x+y).
    follow10 H.
    finish.
  - specialize (H O O O 0inf).
    unfold S1 in H.
    cbn in *.
    repeat rewrite <-const_unfold in *.
    exists (x+y).
    follow10 H.
    finish.
Qed.

End TM32.


Module TM33.
Definition tm := Eval compute in (TM_from_str "1RB1RE_0RC---_1LD1RC_1LA0LF_1LF1RE_1LD0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{A}} [0] *> [1]^^b *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (2+b) c r -->*
  S1 (1+a) b (1+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*2+b) c r -->*
  S1 (n+a) b (n+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d e r:
  S1 a 0 c ([0] *> [1]^^d *> [0] *> [1]^^e *> r) -->+
  S1 0 (3+a+c+d) e r.
Proof.
  es.
Qed.

Lemma Ov1 a c r:
  S1 (1+a) 1 c r -->+
  S1 0 a 1 ([0] *> [1]^^(1+c) *> r).
Proof.
  es.
Qed.

Lemma Ov1_0 c r:
  halts tm (S1 0 1 c r).
Proof.
  unfold S1.
  esx.
Qed.

Definition P2 x y :=
  forall c d e r,
  S1 0 x c ([0] *> [1]^^d *> [0] *> [1]^^e *> r) -->+
  S1 0 (x+y*3+c+d) e r.

Definition P1 x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*3+c) d r.

Lemma Step0 x:
  P2 (x*2+0) 1.
Proof.
  unfold P2; intros.
  follow Incs1.
  follow10 Ov0.
  finish.
Qed.

Lemma Step1 x y:
  P2 x y ->
  P1 ((1+x)*2+1) y.
Proof.
  unfold P1,P2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  finish.
Qed.

Lemma Step1' x y y0:
  P1 x y ->
  P1 (x+y*3+1) y0 ->
  P1 ((1+x)*2+1) (y+y0).
Proof.
  unfold P1,P2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step1'' x y y0:
  P1 x y ->
  P2 (x+y*3+1) y0 ->
  P2 ((1+x)*2+1) (y+y0).
Proof.
  unfold P1,P2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  follow100 H0.
  finish.
Qed.


Inductive v2: nat->nat->Prop :=
| v2_0 x: v2 (x*2+0) 0
| v2_1 x i: v2 x i -> v2 ((1+x)*2+1) (S i)
.

Lemma v2_v2 y i:
  y<2^i ->
  forall x,
  v2 x i ->
  exists i',
  v2 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/2) as y1.
    remember (y mod 2) as y2.
    replace y with (y1*2+y2) in * by lia.
    destruct y2 as [|[|]].
    3: lia.
    + inverts H0.
      unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
      1: lia.
      eexists; split.
      * applys_eq (v2_1 _ _ Hi'); flia.
      * lia.
    + inverts H0.
      eexists; split.
      * applys_eq (v2_0 (x0+y1+2)); flia.
      * lia.
Qed.

Lemma P_0 x:
  v2 x 0 ->
  P2 x 1.
Proof.
  intros Hx.
  inverts Hx.
  apply Step0.
Qed.

Lemma P_1 x:
  v2 x 1 ->
  P1 x 1.
Proof.
  intros Hx.
  inverts Hx.
  apply Step1,P_0,H1.
Qed.

Lemma P_2 x:
  v2 x 2 ->
  P1 x 2.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1' _ 1 1).
  1: apply P_1,H1.
  inverts H1.
  inverts H2.
  applys_eq (P_1 _ (v2_1 _ _ (v2_0 (x0+1)))); flia.
Qed.

Lemma P_3 x:
  v2 x 3 ->
  P2 x 3.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1'' _ 2 1).
  1: apply P_2,H1.
  inverts H1.
  applys_eq (P_0 _ (v2_0 (x+5))); flia.
Qed.

Lemma P_4 x:
  v2 x 4 ->
  P1 x 3.
Proof.
  intros Hx.
  inverts Hx.
  eapply Step1,P_3,H1.
Qed.

Lemma P_i x i:
  v2 x i ->
  exists y, (P1 x y \/ P2 x y) /\ (i>=4 -> y*3+1<2^i).
Proof.
  gen x.
  induction i using lt_wf_ind.
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - right; apply P_0,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - left; apply P_1,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - left; apply P_2,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - right; apply P_3,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - left; apply P_4,Hx.
    - lia.
  }
  { 
    intros x Hx.
    inverts Hx.
    unshelve epose proof (H _ _ _ H2) as [y [I1 I2]].
    1: lia.
    destruct I1 as [I1|I1].
    2: {
      eexists; split.
      * left; eapply Step1,I1.
      * rw_pow; lia.
    }
    unshelve epose proof (v2_v2 _ _ (I2 _) _ H2) as [i' [E1 E2]].
    1: lia.
    destruct i'.
    {
      eexists; split.
      - right; eapply Step1''.
        + apply I1.
        + apply P_0; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - left; eapply Step1'.
        + apply I1.
        + apply P_1; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - left; eapply Step1'.
        + apply I1.
        + apply P_2; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - right; eapply Step1''.
        + apply I1.
        + apply P_3; applys_eq E1; flia.
      - rw_pow; lia.
    }
    {
      unshelve epose proof (H _ _ _ E1) as [y0 [I3 I4]].
      1: lia.
      destruct I3 as [I3|I3].
      {
        eexists; split.
        - left; eapply Step1'.
          + apply I1.
          + applys_eq I3; flia.
        - pose proof (Nat.pow_le_mono_r 2 i' i).
          rw_pow; lia.
      }
      {
        eexists; split.
        - right; eapply Step1''.
          + apply I1.
          + applys_eq I3; flia.
        - pose proof (Nat.pow_le_mono_r 2 i' i).
          rw_pow; lia.
      }
    }
  }
Qed.

Lemma v2_mod3 x:
  exists i,
  v2 (x*3) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/2) as x1.
  remember (x mod 2) as x2.
  replace x with (x1*2+x2) in * by lia.
  destruct x2 as [|[|]].
  3: lia.
  - exists O.
    applys_eq (v2_0 (x1*3)); flia.
  - unshelve epose proof (H x1 _) as [i I1].
    1: lia.
    eexists.
    applys_eq (v2_1 _ _ I1); flia.
Qed.

Definition S n := S1 0 (n*3) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros x.
  epose proof (v2_mod3 x) as [i I1].
  epose proof (P_i _ _ I1) as [y [I2 _]].
  unfold S1.
  destruct I2.
  - specialize (H O O 0inf).
    unfold S1 in H.
    cbn in *.
    repeat rewrite <-const_unfold in *.
    exists (x+y).
    follow10 H.
    finish.
  - specialize (H O O O 0inf).
    unfold S1 in H.
    cbn in *.
    repeat rewrite <-const_unfold in *.
    exists (x+y).
    follow10 H.
    finish.
Qed.

End TM33.


Module TM55.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC0RD_1RA1LC_1LE1RD_0LF0LA_---1LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{A}} [1]^^(b) *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (2+b) c r -->*
  S1 (1+a) b (1+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*2+b) c r -->*
  S1 (n+a) b (n+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d r:
  S1 a 0 c ([0] *> [1]^^d *> r) -->+
  S1 0 (3+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov1 a c r:
  S1 (1+a) 1 c r -->+
  S1 0 a 1 ([0] *> [1]^^(1+c) *> r).
Proof.
  es.
Qed.

Definition P1 x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*3+c) d r.

Lemma Step0 x:
  P1 (x*2+0) 1.
Proof.
  unfold P1; intros.
  follow Incs1.
  follow10 Ov0.
  finish.
Qed.

Lemma Step1 x y y0:
  P1 x y ->
  P1 (x+y*3+1) y0 ->
  P1 ((1+x)*2+1) (y+y0).
Proof.
  unfold P1; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Inductive v2: nat->nat->Prop :=
| v2_0 x: v2 (x*2+0) 0
| v2_1 x i: v2 x i -> v2 ((1+x)*2+1) (S i)
.

Lemma v2_v2 y i:
  y<2^i ->
  forall x,
  v2 x i ->
  exists i',
  v2 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/2) as y1.
    remember (y mod 2) as y2.
    replace y with (y1*2+y2) in * by lia.
    destruct y2 as [|[|]].
    3: lia.
    + inverts H0.
      unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
      1: lia.
      eexists; split.
      * applys_eq (v2_1 _ _ Hi'); flia.
      * lia.
    + inverts H0.
      eexists; split.
      * applys_eq (v2_0 (x0+y1+2)); flia.
      * lia.
Qed.

Lemma P_0 x:
  v2 x 0 ->
  P1 x 1.
Proof.
  intros Hx.
  inverts Hx.
  apply Step0.
Qed.

Lemma P_1 x:
  v2 x 1 ->
  P1 x 2.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 1 1).
  - apply P_0,H1.
  - inverts H1.
    applys_eq (P_0 _ (v2_0 (x+2))); flia.
Qed.

Lemma P_2 x:
  v2 x 2 ->
  P1 x 3.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 2 1).
  - apply P_1,H1.
  - inverts H1.
    applys_eq (P_0 _ (v2_0 (x+5))); flia.
Qed.

Lemma P_3 x:
  v2 x 3 ->
  P1 x 5.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 3 2).
  - apply P_2,H1.
  - inverts H1.
    inverts H2.
    apply P_1.
    applys_eq (v2_1 _ _ (v2_0 (x0+4))); flia.
Qed.

Lemma P_4 x:
  v2 x 4 ->
  P1 x 10.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 5 5).
  - apply P_3,H1.
  - inverts H1.
    inverts H2.
    inverts H1.
    inverts H2.
    apply P_3.
    assert (v2 ((1+((1+((1+((x0+1)*2+0))*2+1))*2+1))*2+1) 3) by repeat constructor.
    applys_eq H; flia.
Qed.

Lemma P_5 x:
  v2 x 5 ->
  P1 x 11.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 10 1).
  - apply P_4,H1.
  - inverts H1.
    apply P_0.
    applys_eq (v2_0 (x+17)); flia.
Qed.

Lemma P_6 x:
  v2 x 6 ->
  P1 x 13.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 11 2).
  - apply P_5,H1.
  - inverts H1.
    inverts H2.
    apply P_1.
    applys_eq (v2_1 _ _ (v2_0 (x0+10))); flia.
Qed.
    
Lemma P_i x i:
  v2 x i ->
  exists y, P1 x y /\ (i>=6 -> y*3+1<2^i).
Proof.
  gen x.
  induction i using lt_wf_ind.
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_0,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_1,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_2,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_3,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_4,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_5,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    1: apply P_6,Hx.
    lia.
  }
  { 
    intros x Hx.
    inverts Hx.
    unshelve epose proof (H _ _ _ H2) as [y [I1 I2]].
    1: lia.
    unshelve epose proof (v2_v2 _ _ (I2 _) _ H2) as [i' [E1 E2]].
    1: lia.
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_0; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_1; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_2; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_3; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_4; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_5; applys_eq E1; flia.
      - rw_pow; lia.
    }
    {
      unshelve epose proof (H _ _ _ E1) as [y0 [I3 I4]].
      1: lia.
      {
        eexists; split.
        - eapply Step1.
          + apply I1.
          + applys_eq I3; flia.
        - pose proof (Nat.pow_le_mono_r 2 i' i).
          rw_pow; lia.
      }
    }
  }
Qed.

Lemma v2_mod3 x:
  exists i,
  v2 (x*3) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/2) as x1.
  remember (x mod 2) as x2.
  replace x with (x1*2+x2) in * by lia.
  destruct x2 as [|[|]].
  3: lia.
  - exists O.
    applys_eq (v2_0 (x1*3)); flia.
  - unshelve epose proof (H x1 _) as [i I1].
    1: lia.
    eexists.
    applys_eq (v2_1 _ _ I1); flia.
Qed.

Definition S n := S1 0 (n*3) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros x.
  epose proof (v2_mod3 x) as [i I1].
  epose proof (P_i _ _ I1) as [y [I2 _]].
  unfold S1.
  specialize (I2 O O 0inf).
  unfold S1 in I2.
  cbn in *.
  repeat rewrite <-const_unfold in *.
  exists (x+y).
  follow10 I2.
  finish.
Qed.

End TM55.


Module TM54.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC0RD_1RA1LC_1LE1RD_0LF0LA_---0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{A}} [1]^^(b) *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (2+b) c r -->*
  S1 (1+a) b (1+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*2+b) c r -->*
  S1 (n+a) b (n+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d r:
  S1 a 0 c ([0] *> [1]^^d *> r) -->+
  S1 0 (3+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov1 a c r:
  S1 (1+a) 1 c r -->+
  S1 0 a 1 ([0] *> [1]^^(1+c) *> r).
Proof.
  es.
Qed.

Definition P1 x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*3+c) d r.

Lemma Step0 x:
  P1 (x*2+0) 1.
Proof.
  unfold P1; intros.
  follow Incs1.
  follow10 Ov0.
  finish.
Qed.

Lemma Step1 x y y0:
  P1 x y ->
  P1 (x+y*3+1) y0 ->
  P1 ((1+x)*2+1) (y+y0).
Proof.
  unfold P1; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Inductive v2: nat->nat->Prop :=
| v2_0 x: v2 (x*2+0) 0
| v2_1 x i: v2 x i -> v2 ((1+x)*2+1) (S i)
.

Lemma v2_v2 y i:
  y<2^i ->
  forall x,
  v2 x i ->
  exists i',
  v2 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/2) as y1.
    remember (y mod 2) as y2.
    replace y with (y1*2+y2) in * by lia.
    destruct y2 as [|[|]].
    3: lia.
    + inverts H0.
      unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
      1: lia.
      eexists; split.
      * applys_eq (v2_1 _ _ Hi'); flia.
      * lia.
    + inverts H0.
      eexists; split.
      * applys_eq (v2_0 (x0+y1+2)); flia.
      * lia.
Qed.

Lemma P_0 x:
  v2 x 0 ->
  P1 x 1.
Proof.
  intros Hx.
  inverts Hx.
  apply Step0.
Qed.

Lemma P_1 x:
  v2 x 1 ->
  P1 x 2.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 1 1).
  - apply P_0,H1.
  - inverts H1.
    applys_eq (P_0 _ (v2_0 (x+2))); flia.
Qed.

Lemma P_2 x:
  v2 x 2 ->
  P1 x 3.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 2 1).
  - apply P_1,H1.
  - inverts H1.
    applys_eq (P_0 _ (v2_0 (x+5))); flia.
Qed.

Lemma P_3 x:
  v2 x 3 ->
  P1 x 5.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 3 2).
  - apply P_2,H1.
  - inverts H1.
    inverts H2.
    apply P_1.
    applys_eq (v2_1 _ _ (v2_0 (x0+4))); flia.
Qed.

Lemma P_4 x:
  v2 x 4 ->
  P1 x 10.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 5 5).
  - apply P_3,H1.
  - inverts H1.
    inverts H2.
    inverts H1.
    inverts H2.
    apply P_3.
    assert (v2 ((1+((1+((1+((x0+1)*2+0))*2+1))*2+1))*2+1) 3) by repeat constructor.
    applys_eq H; flia.
Qed.

Lemma P_5 x:
  v2 x 5 ->
  P1 x 11.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 10 1).
  - apply P_4,H1.
  - inverts H1.
    apply P_0.
    applys_eq (v2_0 (x+17)); flia.
Qed.

Lemma P_6 x:
  v2 x 6 ->
  P1 x 13.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 11 2).
  - apply P_5,H1.
  - inverts H1.
    inverts H2.
    apply P_1.
    applys_eq (v2_1 _ _ (v2_0 (x0+10))); flia.
Qed.
    
Lemma P_i x i:
  v2 x i ->
  exists y, P1 x y /\ (i>=6 -> y*3+1<2^i).
Proof.
  gen x.
  induction i using lt_wf_ind.
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_0,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_1,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_2,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_3,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_4,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_5,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    1: apply P_6,Hx.
    lia.
  }
  { 
    intros x Hx.
    inverts Hx.
    unshelve epose proof (H _ _ _ H2) as [y [I1 I2]].
    1: lia.
    unshelve epose proof (v2_v2 _ _ (I2 _) _ H2) as [i' [E1 E2]].
    1: lia.
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_0; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_1; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_2; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_3; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_4; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_5; applys_eq E1; flia.
      - rw_pow; lia.
    }
    {
      unshelve epose proof (H _ _ _ E1) as [y0 [I3 I4]].
      1: lia.
      {
        eexists; split.
        - eapply Step1.
          + apply I1.
          + applys_eq I3; flia.
        - pose proof (Nat.pow_le_mono_r 2 i' i).
          rw_pow; lia.
      }
    }
  }
Qed.

Lemma v2_mod3 x:
  exists i,
  v2 (x*3) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/2) as x1.
  remember (x mod 2) as x2.
  replace x with (x1*2+x2) in * by lia.
  destruct x2 as [|[|]].
  3: lia.
  - exists O.
    applys_eq (v2_0 (x1*3)); flia.
  - unshelve epose proof (H x1 _) as [i I1].
    1: lia.
    eexists.
    applys_eq (v2_1 _ _ I1); flia.
Qed.

Definition S n := S1 0 (n*3) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros x.
  epose proof (v2_mod3 x) as [i I1].
  epose proof (P_i _ _ I1) as [y [I2 _]].
  unfold S1.
  specialize (I2 O O 0inf).
  unfold S1 in I2.
  cbn in *.
  repeat rewrite <-const_unfold in *.
  exists (x+y).
  follow10 I2.
  finish.
Qed.

End TM54.


Module TM53.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC0RD_1LA1LC_1LE1RD_0LF0LA_---1LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{A}} [1]^^(b) *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (2+b) c r -->*
  S1 (1+a) b (1+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*2+b) c r -->*
  S1 (n+a) b (n+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d r:
  S1 a 0 c ([0] *> [1]^^d *> r) -->+
  S1 0 (3+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov1 a c r:
  S1 (1+a) 1 c r -->+
  S1 0 a 1 ([0] *> [1]^^(1+c) *> r).
Proof.
  es.
Qed.

Definition P1 x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*3+c) d r.

Lemma Step0 x:
  P1 (x*2+0) 1.
Proof.
  unfold P1; intros.
  follow Incs1.
  follow10 Ov0.
  finish.
Qed.

Lemma Step1 x y y0:
  P1 x y ->
  P1 (x+y*3+1) y0 ->
  P1 ((1+x)*2+1) (y+y0).
Proof.
  unfold P1; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Inductive v2: nat->nat->Prop :=
| v2_0 x: v2 (x*2+0) 0
| v2_1 x i: v2 x i -> v2 ((1+x)*2+1) (S i)
.

Lemma v2_v2 y i:
  y<2^i ->
  forall x,
  v2 x i ->
  exists i',
  v2 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/2) as y1.
    remember (y mod 2) as y2.
    replace y with (y1*2+y2) in * by lia.
    destruct y2 as [|[|]].
    3: lia.
    + inverts H0.
      unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
      1: lia.
      eexists; split.
      * applys_eq (v2_1 _ _ Hi'); flia.
      * lia.
    + inverts H0.
      eexists; split.
      * applys_eq (v2_0 (x0+y1+2)); flia.
      * lia.
Qed.

Lemma P_0 x:
  v2 x 0 ->
  P1 x 1.
Proof.
  intros Hx.
  inverts Hx.
  apply Step0.
Qed.

Lemma P_1 x:
  v2 x 1 ->
  P1 x 2.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 1 1).
  - apply P_0,H1.
  - inverts H1.
    applys_eq (P_0 _ (v2_0 (x+2))); flia.
Qed.

Lemma P_2 x:
  v2 x 2 ->
  P1 x 3.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 2 1).
  - apply P_1,H1.
  - inverts H1.
    applys_eq (P_0 _ (v2_0 (x+5))); flia.
Qed.

Lemma P_3 x:
  v2 x 3 ->
  P1 x 5.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 3 2).
  - apply P_2,H1.
  - inverts H1.
    inverts H2.
    apply P_1.
    applys_eq (v2_1 _ _ (v2_0 (x0+4))); flia.
Qed.

Lemma P_4 x:
  v2 x 4 ->
  P1 x 10.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 5 5).
  - apply P_3,H1.
  - inverts H1.
    inverts H2.
    inverts H1.
    inverts H2.
    apply P_3.
    assert (v2 ((1+((1+((1+((x0+1)*2+0))*2+1))*2+1))*2+1) 3) by repeat constructor.
    applys_eq H; flia.
Qed.

Lemma P_5 x:
  v2 x 5 ->
  P1 x 11.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 10 1).
  - apply P_4,H1.
  - inverts H1.
    apply P_0.
    applys_eq (v2_0 (x+17)); flia.
Qed.

Lemma P_6 x:
  v2 x 6 ->
  P1 x 13.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 11 2).
  - apply P_5,H1.
  - inverts H1.
    inverts H2.
    apply P_1.
    applys_eq (v2_1 _ _ (v2_0 (x0+10))); flia.
Qed.
    
Lemma P_i x i:
  v2 x i ->
  exists y, P1 x y /\ (i>=6 -> y*3+1<2^i).
Proof.
  gen x.
  induction i using lt_wf_ind.
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_0,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_1,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_2,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_3,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_4,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_5,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    1: apply P_6,Hx.
    lia.
  }
  { 
    intros x Hx.
    inverts Hx.
    unshelve epose proof (H _ _ _ H2) as [y [I1 I2]].
    1: lia.
    unshelve epose proof (v2_v2 _ _ (I2 _) _ H2) as [i' [E1 E2]].
    1: lia.
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_0; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_1; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_2; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_3; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_4; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_5; applys_eq E1; flia.
      - rw_pow; lia.
    }
    {
      unshelve epose proof (H _ _ _ E1) as [y0 [I3 I4]].
      1: lia.
      {
        eexists; split.
        - eapply Step1.
          + apply I1.
          + applys_eq I3; flia.
        - pose proof (Nat.pow_le_mono_r 2 i' i).
          rw_pow; lia.
      }
    }
  }
Qed.

Lemma v2_mod3 x:
  exists i,
  v2 (x*3) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/2) as x1.
  remember (x mod 2) as x2.
  replace x with (x1*2+x2) in * by lia.
  destruct x2 as [|[|]].
  3: lia.
  - exists O.
    applys_eq (v2_0 (x1*3)); flia.
  - unshelve epose proof (H x1 _) as [i I1].
    1: lia.
    eexists.
    applys_eq (v2_1 _ _ I1); flia.
Qed.

Definition S n := S1 0 (n*3) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros x.
  epose proof (v2_mod3 x) as [i I1].
  epose proof (P_i _ _ I1) as [y [I2 _]].
  unfold S1.
  specialize (I2 O O 0inf).
  unfold S1 in I2.
  cbn in *.
  repeat rewrite <-const_unfold in *.
  exists (x+y).
  follow10 I2.
  finish.
Qed.

End TM53.


Module TM52.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC0RD_1LA1LC_1LE1RD_0LF0LA_---0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{A}} [1]^^(b) *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (2+b) c r -->*
  S1 (1+a) b (1+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*2+b) c r -->*
  S1 (n+a) b (n+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d r:
  S1 a 0 c ([0] *> [1]^^d *> r) -->+
  S1 0 (3+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov1 a c r:
  S1 (1+a) 1 c r -->+
  S1 0 a 1 ([0] *> [1]^^(1+c) *> r).
Proof.
  es.
Qed.

Definition P1 x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*3+c) d r.

Lemma Step0 x:
  P1 (x*2+0) 1.
Proof.
  unfold P1; intros.
  follow Incs1.
  follow10 Ov0.
  finish.
Qed.

Lemma Step1 x y y0:
  P1 x y ->
  P1 (x+y*3+1) y0 ->
  P1 ((1+x)*2+1) (y+y0).
Proof.
  unfold P1; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Inductive v2: nat->nat->Prop :=
| v2_0 x: v2 (x*2+0) 0
| v2_1 x i: v2 x i -> v2 ((1+x)*2+1) (S i)
.

Lemma v2_v2 y i:
  y<2^i ->
  forall x,
  v2 x i ->
  exists i',
  v2 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/2) as y1.
    remember (y mod 2) as y2.
    replace y with (y1*2+y2) in * by lia.
    destruct y2 as [|[|]].
    3: lia.
    + inverts H0.
      unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
      1: lia.
      eexists; split.
      * applys_eq (v2_1 _ _ Hi'); flia.
      * lia.
    + inverts H0.
      eexists; split.
      * applys_eq (v2_0 (x0+y1+2)); flia.
      * lia.
Qed.

Lemma P_0 x:
  v2 x 0 ->
  P1 x 1.
Proof.
  intros Hx.
  inverts Hx.
  apply Step0.
Qed.

Lemma P_1 x:
  v2 x 1 ->
  P1 x 2.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 1 1).
  - apply P_0,H1.
  - inverts H1.
    applys_eq (P_0 _ (v2_0 (x+2))); flia.
Qed.

Lemma P_2 x:
  v2 x 2 ->
  P1 x 3.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 2 1).
  - apply P_1,H1.
  - inverts H1.
    applys_eq (P_0 _ (v2_0 (x+5))); flia.
Qed.

Lemma P_3 x:
  v2 x 3 ->
  P1 x 5.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 3 2).
  - apply P_2,H1.
  - inverts H1.
    inverts H2.
    apply P_1.
    applys_eq (v2_1 _ _ (v2_0 (x0+4))); flia.
Qed.

Lemma P_4 x:
  v2 x 4 ->
  P1 x 10.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 5 5).
  - apply P_3,H1.
  - inverts H1.
    inverts H2.
    inverts H1.
    inverts H2.
    apply P_3.
    assert (v2 ((1+((1+((1+((x0+1)*2+0))*2+1))*2+1))*2+1) 3) by repeat constructor.
    applys_eq H; flia.
Qed.

Lemma P_5 x:
  v2 x 5 ->
  P1 x 11.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 10 1).
  - apply P_4,H1.
  - inverts H1.
    apply P_0.
    applys_eq (v2_0 (x+17)); flia.
Qed.

Lemma P_6 x:
  v2 x 6 ->
  P1 x 13.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 11 2).
  - apply P_5,H1.
  - inverts H1.
    inverts H2.
    apply P_1.
    applys_eq (v2_1 _ _ (v2_0 (x0+10))); flia.
Qed.
    
Lemma P_i x i:
  v2 x i ->
  exists y, P1 x y /\ (i>=6 -> y*3+1<2^i).
Proof.
  gen x.
  induction i using lt_wf_ind.
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_0,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_1,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_2,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_3,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_4,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_5,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    1: apply P_6,Hx.
    lia.
  }
  { 
    intros x Hx.
    inverts Hx.
    unshelve epose proof (H _ _ _ H2) as [y [I1 I2]].
    1: lia.
    unshelve epose proof (v2_v2 _ _ (I2 _) _ H2) as [i' [E1 E2]].
    1: lia.
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_0; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_1; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_2; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_3; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_4; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_5; applys_eq E1; flia.
      - rw_pow; lia.
    }
    {
      unshelve epose proof (H _ _ _ E1) as [y0 [I3 I4]].
      1: lia.
      {
        eexists; split.
        - eapply Step1.
          + apply I1.
          + applys_eq I3; flia.
        - pose proof (Nat.pow_le_mono_r 2 i' i).
          rw_pow; lia.
      }
    }
  }
Qed.

Lemma v2_mod3 x:
  exists i,
  v2 (x*3) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/2) as x1.
  remember (x mod 2) as x2.
  replace x with (x1*2+x2) in * by lia.
  destruct x2 as [|[|]].
  3: lia.
  - exists O.
    applys_eq (v2_0 (x1*3)); flia.
  - unshelve epose proof (H x1 _) as [i I1].
    1: lia.
    eexists.
    applys_eq (v2_1 _ _ I1); flia.
Qed.

Definition S n := S1 0 (n*3) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros x.
  epose proof (v2_mod3 x) as [i I1].
  epose proof (P_i _ _ I1) as [y [I2 _]].
  unfold S1.
  specialize (I2 O O 0inf).
  unfold S1 in I2.
  cbn in *.
  repeat rewrite <-const_unfold in *.
  exists (x+y).
  follow10 I2.
  finish.
Qed.

End TM52.


Module TM48.
Definition tm := Eval compute in (TM_from_str "1LB0LC_1RC0RA_0RE1LD_1LF0LB_1LA1RE_---1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{B}} [0] *> [1]^^(1+b) *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (2+b) c r -->*
  S1 (1+a) b (1+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*2+b) c r -->*
  S1 (n+a) b (n+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d r:
  S1 a 0 c ([0] *> [1]^^d *> r) -->+
  S1 0 (3+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov1 a c r:
  S1 (1+a) 1 c r -->+
  S1 0 a 1 ([0] *> [1]^^(1+c) *> r).
Proof.
  es.
Qed.

Definition P1 x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*3+c) d r.

Lemma Step0 x:
  P1 (x*2+0) 1.
Proof.
  unfold P1; intros.
  follow Incs1.
  follow10 Ov0.
  finish.
Qed.

Lemma Step1 x y y0:
  P1 x y ->
  P1 (x+y*3+1) y0 ->
  P1 ((1+x)*2+1) (y+y0).
Proof.
  unfold P1; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Inductive v2: nat->nat->Prop :=
| v2_0 x: v2 (x*2+0) 0
| v2_1 x i: v2 x i -> v2 ((1+x)*2+1) (S i)
.

Lemma v2_v2 y i:
  y<2^i ->
  forall x,
  v2 x i ->
  exists i',
  v2 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/2) as y1.
    remember (y mod 2) as y2.
    replace y with (y1*2+y2) in * by lia.
    destruct y2 as [|[|]].
    3: lia.
    + inverts H0.
      unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
      1: lia.
      eexists; split.
      * applys_eq (v2_1 _ _ Hi'); flia.
      * lia.
    + inverts H0.
      eexists; split.
      * applys_eq (v2_0 (x0+y1+2)); flia.
      * lia.
Qed.

Lemma P_0 x:
  v2 x 0 ->
  P1 x 1.
Proof.
  intros Hx.
  inverts Hx.
  apply Step0.
Qed.

Lemma P_1 x:
  v2 x 1 ->
  P1 x 2.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 1 1).
  - apply P_0,H1.
  - inverts H1.
    applys_eq (P_0 _ (v2_0 (x+2))); flia.
Qed.

Lemma P_2 x:
  v2 x 2 ->
  P1 x 3.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 2 1).
  - apply P_1,H1.
  - inverts H1.
    applys_eq (P_0 _ (v2_0 (x+5))); flia.
Qed.

Lemma P_3 x:
  v2 x 3 ->
  P1 x 5.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 3 2).
  - apply P_2,H1.
  - inverts H1.
    inverts H2.
    apply P_1.
    applys_eq (v2_1 _ _ (v2_0 (x0+4))); flia.
Qed.

Lemma P_4 x:
  v2 x 4 ->
  P1 x 10.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 5 5).
  - apply P_3,H1.
  - inverts H1.
    inverts H2.
    inverts H1.
    inverts H2.
    apply P_3.
    assert (v2 ((1+((1+((1+((x0+1)*2+0))*2+1))*2+1))*2+1) 3) by repeat constructor.
    applys_eq H; flia.
Qed.

Lemma P_5 x:
  v2 x 5 ->
  P1 x 11.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 10 1).
  - apply P_4,H1.
  - inverts H1.
    apply P_0.
    applys_eq (v2_0 (x+17)); flia.
Qed.

Lemma P_6 x:
  v2 x 6 ->
  P1 x 13.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 11 2).
  - apply P_5,H1.
  - inverts H1.
    inverts H2.
    apply P_1.
    applys_eq (v2_1 _ _ (v2_0 (x0+10))); flia.
Qed.
    
Lemma P_i x i:
  v2 x i ->
  exists y, P1 x y /\ (i>=6 -> y*3+1<2^i).
Proof.
  gen x.
  induction i using lt_wf_ind.
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_0,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_1,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_2,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_3,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_4,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_5,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    1: apply P_6,Hx.
    lia.
  }
  { 
    intros x Hx.
    inverts Hx.
    unshelve epose proof (H _ _ _ H2) as [y [I1 I2]].
    1: lia.
    unshelve epose proof (v2_v2 _ _ (I2 _) _ H2) as [i' [E1 E2]].
    1: lia.
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_0; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_1; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_2; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_3; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_4; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_5; applys_eq E1; flia.
      - rw_pow; lia.
    }
    {
      unshelve epose proof (H _ _ _ E1) as [y0 [I3 I4]].
      1: lia.
      {
        eexists; split.
        - eapply Step1.
          + apply I1.
          + applys_eq I3; flia.
        - pose proof (Nat.pow_le_mono_r 2 i' i).
          rw_pow; lia.
      }
    }
  }
Qed.

Lemma v2_mod3 x:
  exists i,
  v2 (x*3) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/2) as x1.
  remember (x mod 2) as x2.
  replace x with (x1*2+x2) in * by lia.
  destruct x2 as [|[|]].
  3: lia.
  - exists O.
    applys_eq (v2_0 (x1*3)); flia.
  - unshelve epose proof (H x1 _) as [i I1].
    1: lia.
    eexists.
    applys_eq (v2_1 _ _ I1); flia.
Qed.

Definition S n := S1 0 (n*3) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros x.
  epose proof (v2_mod3 x) as [i I1].
  epose proof (P_i _ _ I1) as [y [I2 _]].
  unfold S1.
  specialize (I2 O O 0inf).
  unfold S1 in I2.
  cbn in *.
  repeat rewrite <-const_unfold in *.
  exists (x+y).
  follow10 I2.
  finish.
Qed.

End TM48.


Module TM47.
Definition tm := Eval compute in (TM_from_str "1LB0LC_1RC0RA_0RE1LD_0LF0LB_1LA1RE_---1LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{B}} [0] *> [1]^^(1+b) *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (2+b) c r -->*
  S1 (1+a) b (1+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*2+b) c r -->*
  S1 (n+a) b (n+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d r:
  S1 a 0 c ([0] *> [1]^^d *> r) -->+
  S1 0 (3+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov1 a c r:
  S1 (1+a) 1 c r -->+
  S1 0 a 1 ([0] *> [1]^^(1+c) *> r).
Proof.
  es.
Qed.

Definition P1 x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*3+c) d r.

Lemma Step0 x:
  P1 (x*2+0) 1.
Proof.
  unfold P1; intros.
  follow Incs1.
  follow10 Ov0.
  finish.
Qed.

Lemma Step1 x y y0:
  P1 x y ->
  P1 (x+y*3+1) y0 ->
  P1 ((1+x)*2+1) (y+y0).
Proof.
  unfold P1; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Inductive v2: nat->nat->Prop :=
| v2_0 x: v2 (x*2+0) 0
| v2_1 x i: v2 x i -> v2 ((1+x)*2+1) (S i)
.

Lemma v2_v2 y i:
  y<2^i ->
  forall x,
  v2 x i ->
  exists i',
  v2 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/2) as y1.
    remember (y mod 2) as y2.
    replace y with (y1*2+y2) in * by lia.
    destruct y2 as [|[|]].
    3: lia.
    + inverts H0.
      unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
      1: lia.
      eexists; split.
      * applys_eq (v2_1 _ _ Hi'); flia.
      * lia.
    + inverts H0.
      eexists; split.
      * applys_eq (v2_0 (x0+y1+2)); flia.
      * lia.
Qed.

Lemma P_0 x:
  v2 x 0 ->
  P1 x 1.
Proof.
  intros Hx.
  inverts Hx.
  apply Step0.
Qed.

Lemma P_1 x:
  v2 x 1 ->
  P1 x 2.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 1 1).
  - apply P_0,H1.
  - inverts H1.
    applys_eq (P_0 _ (v2_0 (x+2))); flia.
Qed.

Lemma P_2 x:
  v2 x 2 ->
  P1 x 3.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 2 1).
  - apply P_1,H1.
  - inverts H1.
    applys_eq (P_0 _ (v2_0 (x+5))); flia.
Qed.

Lemma P_3 x:
  v2 x 3 ->
  P1 x 5.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 3 2).
  - apply P_2,H1.
  - inverts H1.
    inverts H2.
    apply P_1.
    applys_eq (v2_1 _ _ (v2_0 (x0+4))); flia.
Qed.

Lemma P_4 x:
  v2 x 4 ->
  P1 x 10.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 5 5).
  - apply P_3,H1.
  - inverts H1.
    inverts H2.
    inverts H1.
    inverts H2.
    apply P_3.
    assert (v2 ((1+((1+((1+((x0+1)*2+0))*2+1))*2+1))*2+1) 3) by repeat constructor.
    applys_eq H; flia.
Qed.

Lemma P_5 x:
  v2 x 5 ->
  P1 x 11.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 10 1).
  - apply P_4,H1.
  - inverts H1.
    apply P_0.
    applys_eq (v2_0 (x+17)); flia.
Qed.

Lemma P_6 x:
  v2 x 6 ->
  P1 x 13.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 11 2).
  - apply P_5,H1.
  - inverts H1.
    inverts H2.
    apply P_1.
    applys_eq (v2_1 _ _ (v2_0 (x0+10))); flia.
Qed.
    
Lemma P_i x i:
  v2 x i ->
  exists y, P1 x y /\ (i>=6 -> y*3+1<2^i).
Proof.
  gen x.
  induction i using lt_wf_ind.
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_0,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_1,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_2,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_3,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_4,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_5,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    1: apply P_6,Hx.
    lia.
  }
  { 
    intros x Hx.
    inverts Hx.
    unshelve epose proof (H _ _ _ H2) as [y [I1 I2]].
    1: lia.
    unshelve epose proof (v2_v2 _ _ (I2 _) _ H2) as [i' [E1 E2]].
    1: lia.
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_0; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_1; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_2; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_3; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_4; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_5; applys_eq E1; flia.
      - rw_pow; lia.
    }
    {
      unshelve epose proof (H _ _ _ E1) as [y0 [I3 I4]].
      1: lia.
      {
        eexists; split.
        - eapply Step1.
          + apply I1.
          + applys_eq I3; flia.
        - pose proof (Nat.pow_le_mono_r 2 i' i).
          rw_pow; lia.
      }
    }
  }
Qed.

Lemma v2_mod3 x:
  exists i,
  v2 (x*3) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/2) as x1.
  remember (x mod 2) as x2.
  replace x with (x1*2+x2) in * by lia.
  destruct x2 as [|[|]].
  3: lia.
  - exists O.
    applys_eq (v2_0 (x1*3)); flia.
  - unshelve epose proof (H x1 _) as [i I1].
    1: lia.
    eexists.
    applys_eq (v2_1 _ _ I1); flia.
Qed.

Definition S n := S1 0 (n*3) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros x.
  epose proof (v2_mod3 x) as [i I1].
  epose proof (P_i _ _ I1) as [y [I2 _]].
  unfold S1.
  specialize (I2 O O 0inf).
  unfold S1 in I2.
  cbn in *.
  repeat rewrite <-const_unfold in *.
  exists (x+y).
  follow10 I2.
  finish.
Qed.

End TM47.


Module TM22.
Definition tm := Eval compute in (TM_from_str "1RB0RC_1LC0LA_0LE1RD_0LF0RB_1RA1LE_---1LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{E}} [1]^^(1+b) *> [0] *> [1]^^(1+c) *> r.

Lemma Inc1 a b c r:
  S1 a (2+b) c r -->*
  S1 (1+a) b (1+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*2+b) c r -->*
  S1 (n+a) b (n+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d e r:
  S1 a 0 c ([0] *> [1]^^d *> [0] *> [1]^^e *> r) -->+
  S1 0 (3+a+c+d) (e) r.
Proof.
  es.
Qed.

Lemma Ov1 a c r:
  S1 (1+a) 1 c r -->+
  S1 0 a 1 ([0] *> [1]^^(1+c) *> r).
Proof.
  es.
Qed.

Lemma Ov1_0 c r:
  halts tm (S1 0 1 c r).
Proof.
  unfold S1.
  esx.
Qed.

Definition P2 x y :=
  forall c d e r,
  S1 0 x c ([0] *> [1]^^d *> [0] *> [1]^^e *> r) -->+
  S1 0 (x+y*3+c+d) e r.

Definition P1 x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*3+c) d r.

Lemma Step0 x:
  P2 (x*2+0) 1.
Proof.
  unfold P2; intros.
  follow Incs1.
  follow10 Ov0.
  finish.
Qed.

Lemma Step1 x y:
  P2 x y ->
  P1 ((1+x)*2+1) y.
Proof.
  unfold P1,P2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  finish.
Qed.

Lemma Step1' x y y0:
  P1 x y ->
  P1 (x+y*3+1) y0 ->
  P1 ((1+x)*2+1) (y+y0).
Proof.
  unfold P1,P2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step1'' x y y0:
  P1 x y ->
  P2 (x+y*3+1) y0 ->
  P2 ((1+x)*2+1) (y+y0).
Proof.
  unfold P1,P2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  follow100 H0.
  finish.
Qed.


Inductive v2: nat->nat->Prop :=
| v2_0 x: v2 (x*2+0) 0
| v2_1 x i: v2 x i -> v2 ((1+x)*2+1) (S i)
.

Lemma v2_v2 y i:
  y<2^i ->
  forall x,
  v2 x i ->
  exists i',
  v2 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/2) as y1.
    remember (y mod 2) as y2.
    replace y with (y1*2+y2) in * by lia.
    destruct y2 as [|[|]].
    3: lia.
    + inverts H0.
      unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
      1: lia.
      eexists; split.
      * applys_eq (v2_1 _ _ Hi'); flia.
      * lia.
    + inverts H0.
      eexists; split.
      * applys_eq (v2_0 (x0+y1+2)); flia.
      * lia.
Qed.

Lemma P_0 x:
  v2 x 0 ->
  P2 x 1.
Proof.
  intros Hx.
  inverts Hx.
  apply Step0.
Qed.

Lemma P_1 x:
  v2 x 1 ->
  P1 x 1.
Proof.
  intros Hx.
  inverts Hx.
  apply Step1,P_0,H1.
Qed.

Lemma P_2 x:
  v2 x 2 ->
  P1 x 2.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1' _ 1 1).
  1: apply P_1,H1.
  inverts H1.
  inverts H2.
  applys_eq (P_1 _ (v2_1 _ _ (v2_0 (x0+1)))); flia.
Qed.

Lemma P_3 x:
  v2 x 3 ->
  P2 x 3.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1'' _ 2 1).
  1: apply P_2,H1.
  inverts H1.
  applys_eq (P_0 _ (v2_0 (x+5))); flia.
Qed.

Lemma P_4 x:
  v2 x 4 ->
  P1 x 3.
Proof.
  intros Hx.
  inverts Hx.
  eapply Step1,P_3,H1.
Qed.

Lemma P_i x i:
  v2 x i ->
  exists y, (P1 x y \/ P2 x y) /\ (i>=4 -> y*3+1<2^i).
Proof.
  gen x.
  induction i using lt_wf_ind.
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - right; apply P_0,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - left; apply P_1,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - left; apply P_2,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - right; apply P_3,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - left; apply P_4,Hx.
    - lia.
  }
  { 
    intros x Hx.
    inverts Hx.
    unshelve epose proof (H _ _ _ H2) as [y [I1 I2]].
    1: lia.
    destruct I1 as [I1|I1].
    2: {
      eexists; split.
      * left; eapply Step1,I1.
      * rw_pow; lia.
    }
    unshelve epose proof (v2_v2 _ _ (I2 _) _ H2) as [i' [E1 E2]].
    1: lia.
    destruct i'.
    {
      eexists; split.
      - right; eapply Step1''.
        + apply I1.
        + apply P_0; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - left; eapply Step1'.
        + apply I1.
        + apply P_1; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - left; eapply Step1'.
        + apply I1.
        + apply P_2; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - right; eapply Step1''.
        + apply I1.
        + apply P_3; applys_eq E1; flia.
      - rw_pow; lia.
    }
    {
      unshelve epose proof (H _ _ _ E1) as [y0 [I3 I4]].
      1: lia.
      destruct I3 as [I3|I3].
      {
        eexists; split.
        - left; eapply Step1'.
          + apply I1.
          + applys_eq I3; flia.
        - pose proof (Nat.pow_le_mono_r 2 i' i).
          rw_pow; lia.
      }
      {
        eexists; split.
        - right; eapply Step1''.
          + apply I1.
          + applys_eq I3; flia.
        - pose proof (Nat.pow_le_mono_r 2 i' i).
          rw_pow; lia.
      }
    }
  }
Qed.

Lemma v2_mod3 x:
  exists i,
  v2 (x*3) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/2) as x1.
  remember (x mod 2) as x2.
  replace x with (x1*2+x2) in * by lia.
  destruct x2 as [|[|]].
  3: lia.
  - exists O.
    applys_eq (v2_0 (x1*3)); flia.
  - unshelve epose proof (H x1 _) as [i I1].
    1: lia.
    eexists.
    applys_eq (v2_1 _ _ I1); flia.
Qed.

Definition S n := S1 0 (n*3) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros x.
  epose proof (v2_mod3 x) as [i I1].
  epose proof (P_i _ _ I1) as [y [I2 _]].
  unfold S1.
  destruct I2.
  - specialize (H O O 0inf).
    unfold S1 in H.
    cbn in *.
    repeat rewrite <-const_unfold in *.
    exists (x+y).
    follow10 H.
    finish.
  - specialize (H O O O 0inf).
    unfold S1 in H.
    cbn in *.
    repeat rewrite <-const_unfold in *.
    exists (x+y).
    follow10 H.
    finish.
Qed.

End TM22.


Module TM49.
Definition tm := Eval compute in (TM_from_str "1RB0LD_1LC1RB_1LA1RC_---0LE_1RF1LE_1RA0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{E}} [1]^^(b) *> [0;0] *> [1]^^(1+c) *> r.

Lemma Inc1 a b c r:
  S1 a (2+b) c r -->*
  S1 (1+a) b (1+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*2+b) c r -->*
  S1 (n+a) b (n+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d e r:
  S1 a 0 c ([0] *> [1]^^d *> [0] *> [1]^^e *> r) -->+
  S1 0 (3+a+c+d) (e) r.
Proof.
  es.
Qed.

Lemma Ov1 a c r:
  S1 (1+a) 1 c r -->+
  S1 0 a 1 ([0] *> [1]^^(1+c) *> r).
Proof.
  es.
Qed.

Lemma Ov1_0 c r:
  halts tm (S1 0 1 c r).
Proof.
  unfold S1.
  esx.
Qed.

Definition P2 x y :=
  forall c d e r,
  S1 0 x c ([0] *> [1]^^d *> [0] *> [1]^^e *> r) -->+
  S1 0 (x+y*3+c+d) e r.

Definition P1 x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*3+c) d r.

Lemma Step0 x:
  P2 (x*2+0) 1.
Proof.
  unfold P2; intros.
  follow Incs1.
  follow10 Ov0.
  finish.
Qed.

Lemma Step1 x y:
  P2 x y ->
  P1 ((1+x)*2+1) y.
Proof.
  unfold P1,P2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  finish.
Qed.

Lemma Step1' x y y0:
  P1 x y ->
  P1 (x+y*3+1) y0 ->
  P1 ((1+x)*2+1) (y+y0).
Proof.
  unfold P1,P2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step1'' x y y0:
  P1 x y ->
  P2 (x+y*3+1) y0 ->
  P2 ((1+x)*2+1) (y+y0).
Proof.
  unfold P1,P2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  follow100 H0.
  finish.
Qed.


Inductive v2: nat->nat->Prop :=
| v2_0 x: v2 (x*2+0) 0
| v2_1 x i: v2 x i -> v2 ((1+x)*2+1) (S i)
.

Lemma v2_v2 y i:
  y<2^i ->
  forall x,
  v2 x i ->
  exists i',
  v2 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/2) as y1.
    remember (y mod 2) as y2.
    replace y with (y1*2+y2) in * by lia.
    destruct y2 as [|[|]].
    3: lia.
    + inverts H0.
      unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
      1: lia.
      eexists; split.
      * applys_eq (v2_1 _ _ Hi'); flia.
      * lia.
    + inverts H0.
      eexists; split.
      * applys_eq (v2_0 (x0+y1+2)); flia.
      * lia.
Qed.

Lemma P_0 x:
  v2 x 0 ->
  P2 x 1.
Proof.
  intros Hx.
  inverts Hx.
  apply Step0.
Qed.

Lemma P_1 x:
  v2 x 1 ->
  P1 x 1.
Proof.
  intros Hx.
  inverts Hx.
  apply Step1,P_0,H1.
Qed.

Lemma P_2 x:
  v2 x 2 ->
  P1 x 2.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1' _ 1 1).
  1: apply P_1,H1.
  inverts H1.
  inverts H2.
  applys_eq (P_1 _ (v2_1 _ _ (v2_0 (x0+1)))); flia.
Qed.

Lemma P_3 x:
  v2 x 3 ->
  P2 x 3.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1'' _ 2 1).
  1: apply P_2,H1.
  inverts H1.
  applys_eq (P_0 _ (v2_0 (x+5))); flia.
Qed.

Lemma P_4 x:
  v2 x 4 ->
  P1 x 3.
Proof.
  intros Hx.
  inverts Hx.
  eapply Step1,P_3,H1.
Qed.

Lemma P_i x i:
  v2 x i ->
  exists y, (P1 x y \/ P2 x y) /\ (i>=4 -> y*3+1<2^i).
Proof.
  gen x.
  induction i using lt_wf_ind.
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - right; apply P_0,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - left; apply P_1,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - left; apply P_2,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - right; apply P_3,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - left; apply P_4,Hx.
    - lia.
  }
  { 
    intros x Hx.
    inverts Hx.
    unshelve epose proof (H _ _ _ H2) as [y [I1 I2]].
    1: lia.
    destruct I1 as [I1|I1].
    2: {
      eexists; split.
      * left; eapply Step1,I1.
      * rw_pow; lia.
    }
    unshelve epose proof (v2_v2 _ _ (I2 _) _ H2) as [i' [E1 E2]].
    1: lia.
    destruct i'.
    {
      eexists; split.
      - right; eapply Step1''.
        + apply I1.
        + apply P_0; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - left; eapply Step1'.
        + apply I1.
        + apply P_1; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - left; eapply Step1'.
        + apply I1.
        + apply P_2; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - right; eapply Step1''.
        + apply I1.
        + apply P_3; applys_eq E1; flia.
      - rw_pow; lia.
    }
    {
      unshelve epose proof (H _ _ _ E1) as [y0 [I3 I4]].
      1: lia.
      destruct I3 as [I3|I3].
      {
        eexists; split.
        - left; eapply Step1'.
          + apply I1.
          + applys_eq I3; flia.
        - pose proof (Nat.pow_le_mono_r 2 i' i).
          rw_pow; lia.
      }
      {
        eexists; split.
        - right; eapply Step1''.
          + apply I1.
          + applys_eq I3; flia.
        - pose proof (Nat.pow_le_mono_r 2 i' i).
          rw_pow; lia.
      }
    }
  }
Qed.

Lemma v2_mod3 x:
  exists i,
  v2 (x*3) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/2) as x1.
  remember (x mod 2) as x2.
  replace x with (x1*2+x2) in * by lia.
  destruct x2 as [|[|]].
  3: lia.
  - exists O.
    applys_eq (v2_0 (x1*3)); flia.
  - unshelve epose proof (H x1 _) as [i I1].
    1: lia.
    eexists.
    applys_eq (v2_1 _ _ I1); flia.
Qed.

Definition S n := S1 0 (n*3) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros x.
  epose proof (v2_mod3 x) as [i I1].
  epose proof (P_i _ _ I1) as [y [I2 _]].
  unfold S1.
  destruct I2.
  - specialize (H O O 0inf).
    unfold S1 in H.
    cbn in *.
    repeat rewrite <-const_unfold in *.
    exists (x+y).
    follow10 H.
    finish.
  - specialize (H O O O 0inf).
    unfold S1 in H.
    cbn in *.
    repeat rewrite <-const_unfold in *.
    exists (x+y).
    follow10 H.
    finish.
Qed.

End TM49.


Module TM50.
Definition tm := Eval compute in (TM_from_str "1RB0LD_1LC1RB_1LA1RC_---0LE_1RF1LE_0RC0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{E}} [1]^^(b) *> [0;0] *> [1]^^(1+c) *> r.

Lemma Inc1 a b c r:
  S1 a (2+b) c r -->*
  S1 (1+a) b (1+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*2+b) c r -->*
  S1 (n+a) b (n+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d e r:
  S1 a 0 c ([0] *> [1]^^d *> [0] *> [1]^^e *> r) -->+
  S1 0 (3+a+c+d) (e) r.
Proof.
  es.
Qed.

Lemma Ov1 a c r:
  S1 (1+a) 1 c r -->+
  S1 0 a 1 ([0] *> [1]^^(1+c) *> r).
Proof.
  es.
Qed.

Lemma Ov1_0 c r:
  halts tm (S1 0 1 c r).
Proof.
  unfold S1.
  esx.
Qed.

Definition P2 x y :=
  forall c d e r,
  S1 0 x c ([0] *> [1]^^d *> [0] *> [1]^^e *> r) -->+
  S1 0 (x+y*3+c+d) e r.

Definition P1 x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*3+c) d r.

Lemma Step0 x:
  P2 (x*2+0) 1.
Proof.
  unfold P2; intros.
  follow Incs1.
  follow10 Ov0.
  finish.
Qed.

Lemma Step1 x y:
  P2 x y ->
  P1 ((1+x)*2+1) y.
Proof.
  unfold P1,P2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  finish.
Qed.

Lemma Step1' x y y0:
  P1 x y ->
  P1 (x+y*3+1) y0 ->
  P1 ((1+x)*2+1) (y+y0).
Proof.
  unfold P1,P2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step1'' x y y0:
  P1 x y ->
  P2 (x+y*3+1) y0 ->
  P2 ((1+x)*2+1) (y+y0).
Proof.
  unfold P1,P2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  follow100 H0.
  finish.
Qed.


Inductive v2: nat->nat->Prop :=
| v2_0 x: v2 (x*2+0) 0
| v2_1 x i: v2 x i -> v2 ((1+x)*2+1) (S i)
.

Lemma v2_v2 y i:
  y<2^i ->
  forall x,
  v2 x i ->
  exists i',
  v2 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/2) as y1.
    remember (y mod 2) as y2.
    replace y with (y1*2+y2) in * by lia.
    destruct y2 as [|[|]].
    3: lia.
    + inverts H0.
      unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
      1: lia.
      eexists; split.
      * applys_eq (v2_1 _ _ Hi'); flia.
      * lia.
    + inverts H0.
      eexists; split.
      * applys_eq (v2_0 (x0+y1+2)); flia.
      * lia.
Qed.

Lemma P_0 x:
  v2 x 0 ->
  P2 x 1.
Proof.
  intros Hx.
  inverts Hx.
  apply Step0.
Qed.

Lemma P_1 x:
  v2 x 1 ->
  P1 x 1.
Proof.
  intros Hx.
  inverts Hx.
  apply Step1,P_0,H1.
Qed.

Lemma P_2 x:
  v2 x 2 ->
  P1 x 2.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1' _ 1 1).
  1: apply P_1,H1.
  inverts H1.
  inverts H2.
  applys_eq (P_1 _ (v2_1 _ _ (v2_0 (x0+1)))); flia.
Qed.

Lemma P_3 x:
  v2 x 3 ->
  P2 x 3.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1'' _ 2 1).
  1: apply P_2,H1.
  inverts H1.
  applys_eq (P_0 _ (v2_0 (x+5))); flia.
Qed.

Lemma P_4 x:
  v2 x 4 ->
  P1 x 3.
Proof.
  intros Hx.
  inverts Hx.
  eapply Step1,P_3,H1.
Qed.

Lemma P_i x i:
  v2 x i ->
  exists y, (P1 x y \/ P2 x y) /\ (i>=4 -> y*3+1<2^i).
Proof.
  gen x.
  induction i using lt_wf_ind.
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - right; apply P_0,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - left; apply P_1,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - left; apply P_2,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - right; apply P_3,Hx.
    - lia.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    - left; apply P_4,Hx.
    - lia.
  }
  { 
    intros x Hx.
    inverts Hx.
    unshelve epose proof (H _ _ _ H2) as [y [I1 I2]].
    1: lia.
    destruct I1 as [I1|I1].
    2: {
      eexists; split.
      * left; eapply Step1,I1.
      * rw_pow; lia.
    }
    unshelve epose proof (v2_v2 _ _ (I2 _) _ H2) as [i' [E1 E2]].
    1: lia.
    destruct i'.
    {
      eexists; split.
      - right; eapply Step1''.
        + apply I1.
        + apply P_0; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - left; eapply Step1'.
        + apply I1.
        + apply P_1; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - left; eapply Step1'.
        + apply I1.
        + apply P_2; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - right; eapply Step1''.
        + apply I1.
        + apply P_3; applys_eq E1; flia.
      - rw_pow; lia.
    }
    {
      unshelve epose proof (H _ _ _ E1) as [y0 [I3 I4]].
      1: lia.
      destruct I3 as [I3|I3].
      {
        eexists; split.
        - left; eapply Step1'.
          + apply I1.
          + applys_eq I3; flia.
        - pose proof (Nat.pow_le_mono_r 2 i' i).
          rw_pow; lia.
      }
      {
        eexists; split.
        - right; eapply Step1''.
          + apply I1.
          + applys_eq I3; flia.
        - pose proof (Nat.pow_le_mono_r 2 i' i).
          rw_pow; lia.
      }
    }
  }
Qed.

Lemma v2_mod3 x:
  exists i,
  v2 (x*3) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/2) as x1.
  remember (x mod 2) as x2.
  replace x with (x1*2+x2) in * by lia.
  destruct x2 as [|[|]].
  3: lia.
  - exists O.
    applys_eq (v2_0 (x1*3)); flia.
  - unshelve epose proof (H x1 _) as [i I1].
    1: lia.
    eexists.
    applys_eq (v2_1 _ _ I1); flia.
Qed.

Definition S n := S1 0 (n*3) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros x.
  epose proof (v2_mod3 x) as [i I1].
  epose proof (P_i _ _ I1) as [y [I2 _]].
  unfold S1.
  destruct I2.
  - specialize (H O O 0inf).
    unfold S1 in H.
    cbn in *.
    repeat rewrite <-const_unfold in *.
    exists (x+y).
    follow10 H.
    finish.
  - specialize (H O O O 0inf).
    unfold S1 in H.
    cbn in *.
    repeat rewrite <-const_unfold in *.
    exists (x+y).
    follow10 H.
    finish.
Qed.

End TM50.


Module TM56.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1RC0RD_1LA1LC_1LE1RD_0LF0LA_---0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{A}} [1]^^(b) *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (2+b) c r -->*
  S1 (1+a) b (1+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*2+b) c r -->*
  S1 (n+a) b (n+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d r:
  S1 a 0 (1+c) ([0] *> [1]^^d *> r) -->+
  S1 0 (4+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov0_c0 a d e r:
  S1 a 0 0 ([0] *> [1]^^d *> [0] *> [1]^^e *> r) -->+
  S1 0 (3+a+d) e r.
Proof.
  es.
Qed.

Lemma Ov1 a c r:
  S1 (1+a) 1 c r -->+
  S1 0 a 1 ([0] *> [1]^^(1+c) *> r).
Proof.
  es.
Qed.

Lemma Ov1_0 c r:
  halts tm (S1 0 1 c r).
Proof.
  unfold S1.
  esx.
Qed.

Definition P1' x y :=
  forall c d r,
  S1 0 x (1+c) ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*3+c+1) d r.

Lemma Step0'1 x:
  P1' (x*2+0) 1.
Proof.
  unfold P1'; intros.
  follow Incs1.
  replace (x+(1+c)) with (1+(x+c)) by lia.
  follow10 Ov0.
  finish.
Qed.

Lemma Step1'1 x y y0:
  P1' x y ->
  P1' (x+y*3+1) y0 ->
  P1' ((1+x)*2+1) (y+y0).
Proof.
  unfold P1'; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  rewrite Nat.add_0_r.
  follow100 H0.
  finish.
Qed.

Lemma unfold_0inf:
  0inf = [0] *> [1]^^0 *> 0inf.
Proof.
  solve_const0_eq.
Qed.

Definition P0 x y :=
  S1 0 x 0 0inf -->+
  S1 0 (x+y*3) 0 0inf.

Lemma Step0'0 x:
  P0 (x*2+0) 1.
Proof.
  unfold P0.
  destruct x.
  - do 2 rewrite unfold_0inf.
    follow10 Ov0_c0.
    do 2 rewrite <-unfold_0inf.
    finish.
  - follow Incs1.
    rewrite Nat.add_0_r.
    rewrite unfold_0inf.
    follow10 Ov0.
    rewrite <-unfold_0inf.
    finish.
Qed.

Lemma Step1'0 x y y0:
  P1' x y ->
  P1' (x+y*3+1) y0 ->
  P0 ((1+x)*2+1) (y+y0).
Proof.
  unfold P0; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  rewrite Nat.add_0_r.
  rewrite unfold_0inf.
  follow100 H0.
  rewrite <-unfold_0inf.
  finish.
Qed.

Inductive P1: nat->nat->Prop :=
| Step0 x: P1 (x*2+0) 1
| Step1 x y y0:
  P1 x y ->
  P1 (x+y*3+1) y0 ->
  P1 ((1+x)*2+1) (y+y0).

Inductive v2: nat->nat->Prop :=
| v2_0 x: v2 (x*2+0) 0
| v2_1 x i: v2 x i -> v2 ((1+x)*2+1) (S i)
.

Lemma v2_v2 y i:
  y<2^i ->
  forall x,
  v2 x i ->
  exists i',
  v2 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/2) as y1.
    remember (y mod 2) as y2.
    replace y with (y1*2+y2) in * by lia.
    destruct y2 as [|[|]].
    3: lia.
    + inverts H0.
      unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
      1: lia.
      eexists; split.
      * applys_eq (v2_1 _ _ Hi'); flia.
      * lia.
    + inverts H0.
      eexists; split.
      * applys_eq (v2_0 (x0+y1+2)); flia.
      * lia.
Qed.

Lemma P_0 x:
  v2 x 0 ->
  P1 x 1.
Proof.
  intros Hx.
  inverts Hx.
  apply Step0.
Qed.

Lemma P_1 x:
  v2 x 1 ->
  P1 x 2.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 1 1).
  - apply P_0,H1.
  - inverts H1.
    applys_eq (P_0 _ (v2_0 (x+2))); flia.
Qed.

Lemma P_2 x:
  v2 x 2 ->
  P1 x 3.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 2 1).
  - apply P_1,H1.
  - inverts H1.
    applys_eq (P_0 _ (v2_0 (x+5))); flia.
Qed.

Lemma P_3 x:
  v2 x 3 ->
  P1 x 5.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 3 2).
  - apply P_2,H1.
  - inverts H1.
    inverts H2.
    apply P_1.
    applys_eq (v2_1 _ _ (v2_0 (x0+4))); flia.
Qed.

Lemma P_4 x:
  v2 x 4 ->
  P1 x 10.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 5 5).
  - apply P_3,H1.
  - inverts H1.
    inverts H2.
    inverts H1.
    inverts H2.
    apply P_3.
    assert (v2 ((1+((1+((1+((x0+1)*2+0))*2+1))*2+1))*2+1) 3) by repeat constructor.
    applys_eq H; flia.
Qed.

Lemma P_5 x:
  v2 x 5 ->
  P1 x 11.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 10 1).
  - apply P_4,H1.
  - inverts H1.
    apply P_0.
    applys_eq (v2_0 (x+17)); flia.
Qed.

Lemma P_6 x:
  v2 x 6 ->
  P1 x 13.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 11 2).
  - apply P_5,H1.
  - inverts H1.
    inverts H2.
    apply P_1.
    applys_eq (v2_1 _ _ (v2_0 (x0+10))); flia.
Qed.

Lemma P_i x i:
  v2 x i ->
  exists y, P1 x y /\ (i>=6 -> y*3+1<2^i).
Proof.
  gen x.
  induction i using lt_wf_ind.
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_0,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_1,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_2,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_3,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_4,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_5,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    1: apply P_6,Hx.
    lia.
  }
  { 
    intros x Hx.
    inverts Hx.
    unshelve epose proof (H _ _ _ H2) as [y [I1 I2]].
    1: lia.
    unshelve epose proof (v2_v2 _ _ (I2 _) _ H2) as [i' [E1 E2]].
    1: lia.
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_0; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_1; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_2; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_3; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_4; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_5; applys_eq E1; flia.
      - rw_pow; lia.
    }
    {
      unshelve epose proof (H _ _ _ E1) as [y0 [I3 I4]].
      1: lia.
      {
        eexists; split.
        - eapply Step1.
          + apply I1.
          + applys_eq I3; flia.
        - pose proof (Nat.pow_le_mono_r 2 i' i).
          rw_pow; lia.
      }
    }
  }
Qed.

Lemma P1'_i x i:
  P1 x i ->
  P1' x i.
Proof.
  intros HP.
  induction HP.
  - apply Step0'1.
  - apply Step1'1; assumption.
Qed.

Lemma P0_i x i:
  P1 x i ->
  P0 x i.
Proof.
  intros HP.
  inverts HP.
  - apply Step0'0.
  - apply Step1'0.
    + apply P1'_i,H.
    + apply P1'_i,H0.
Qed.

Lemma v2_mod3 x:
  exists i,
  v2 (x*3) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/2) as x1.
  remember (x mod 2) as x2.
  replace x with (x1*2+x2) in * by lia.
  destruct x2 as [|[|]].
  3: lia.
  - exists O.
    applys_eq (v2_0 (x1*3)); flia.
  - unshelve epose proof (H x1 _) as [i I1].
    1: lia.
    eexists.
    applys_eq (v2_1 _ _ I1); flia.
Qed.

Definition S n := S1 0 (n*3) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros x.
  epose proof (v2_mod3 x) as [i I1].
  epose proof (P_i _ _ I1) as [y [I2' _]].
  epose proof (P0_i _ _ I2') as I2.
  unfold P0 in I2.
  eexists (x+y).
  applys_eq I2; flia.
Qed.

End TM56.


Module TM57.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1RC0RD_1LA1LC_1LE1RD_0LF0LA_---1LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{A}} [1]^^(b) *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (2+b) c r -->*
  S1 (1+a) b (1+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*2+b) c r -->*
  S1 (n+a) b (n+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d r:
  S1 a 0 (1+c) ([0] *> [1]^^d *> r) -->+
  S1 0 (4+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov0_c0 a d e r:
  S1 a 0 0 ([0] *> [1]^^d *> [0] *> [1]^^e *> r) -->+
  S1 0 (3+a+d) e r.
Proof.
  es.
Qed.

Lemma Ov1 a c r:
  S1 (1+a) 1 c r -->+
  S1 0 a 1 ([0] *> [1]^^(1+c) *> r).
Proof.
  es.
Qed.

Lemma Ov1_0 c r:
  halts tm (S1 0 1 c r).
Proof.
  unfold S1.
  esx.
Qed.

Definition P1' x y :=
  forall c d r,
  S1 0 x (1+c) ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*3+c+1) d r.

Lemma Step0'1 x:
  P1' (x*2+0) 1.
Proof.
  unfold P1'; intros.
  follow Incs1.
  replace (x+(1+c)) with (1+(x+c)) by lia.
  follow10 Ov0.
  finish.
Qed.

Lemma Step1'1 x y y0:
  P1' x y ->
  P1' (x+y*3+1) y0 ->
  P1' ((1+x)*2+1) (y+y0).
Proof.
  unfold P1'; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  rewrite Nat.add_0_r.
  follow100 H0.
  finish.
Qed.

Lemma unfold_0inf:
  0inf = [0] *> [1]^^0 *> 0inf.
Proof.
  solve_const0_eq.
Qed.

Definition P0 x y :=
  S1 0 x 0 0inf -->+
  S1 0 (x+y*3) 0 0inf.

Lemma Step0'0 x:
  P0 (x*2+0) 1.
Proof.
  unfold P0.
  destruct x.
  - do 2 rewrite unfold_0inf.
    follow10 Ov0_c0.
    do 2 rewrite <-unfold_0inf.
    finish.
  - follow Incs1.
    rewrite Nat.add_0_r.
    rewrite unfold_0inf.
    follow10 Ov0.
    rewrite <-unfold_0inf.
    finish.
Qed.

Lemma Step1'0 x y y0:
  P1' x y ->
  P1' (x+y*3+1) y0 ->
  P0 ((1+x)*2+1) (y+y0).
Proof.
  unfold P0; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  rewrite Nat.add_0_r.
  rewrite unfold_0inf.
  follow100 H0.
  rewrite <-unfold_0inf.
  finish.
Qed.

Inductive P1: nat->nat->Prop :=
| Step0 x: P1 (x*2+0) 1
| Step1 x y y0:
  P1 x y ->
  P1 (x+y*3+1) y0 ->
  P1 ((1+x)*2+1) (y+y0).

Inductive v2: nat->nat->Prop :=
| v2_0 x: v2 (x*2+0) 0
| v2_1 x i: v2 x i -> v2 ((1+x)*2+1) (S i)
.

Lemma v2_v2 y i:
  y<2^i ->
  forall x,
  v2 x i ->
  exists i',
  v2 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/2) as y1.
    remember (y mod 2) as y2.
    replace y with (y1*2+y2) in * by lia.
    destruct y2 as [|[|]].
    3: lia.
    + inverts H0.
      unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
      1: lia.
      eexists; split.
      * applys_eq (v2_1 _ _ Hi'); flia.
      * lia.
    + inverts H0.
      eexists; split.
      * applys_eq (v2_0 (x0+y1+2)); flia.
      * lia.
Qed.

Lemma P_0 x:
  v2 x 0 ->
  P1 x 1.
Proof.
  intros Hx.
  inverts Hx.
  apply Step0.
Qed.

Lemma P_1 x:
  v2 x 1 ->
  P1 x 2.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 1 1).
  - apply P_0,H1.
  - inverts H1.
    applys_eq (P_0 _ (v2_0 (x+2))); flia.
Qed.

Lemma P_2 x:
  v2 x 2 ->
  P1 x 3.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 2 1).
  - apply P_1,H1.
  - inverts H1.
    applys_eq (P_0 _ (v2_0 (x+5))); flia.
Qed.

Lemma P_3 x:
  v2 x 3 ->
  P1 x 5.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 3 2).
  - apply P_2,H1.
  - inverts H1.
    inverts H2.
    apply P_1.
    applys_eq (v2_1 _ _ (v2_0 (x0+4))); flia.
Qed.

Lemma P_4 x:
  v2 x 4 ->
  P1 x 10.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 5 5).
  - apply P_3,H1.
  - inverts H1.
    inverts H2.
    inverts H1.
    inverts H2.
    apply P_3.
    assert (v2 ((1+((1+((1+((x0+1)*2+0))*2+1))*2+1))*2+1) 3) by repeat constructor.
    applys_eq H; flia.
Qed.

Lemma P_5 x:
  v2 x 5 ->
  P1 x 11.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 10 1).
  - apply P_4,H1.
  - inverts H1.
    apply P_0.
    applys_eq (v2_0 (x+17)); flia.
Qed.

Lemma P_6 x:
  v2 x 6 ->
  P1 x 13.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 11 2).
  - apply P_5,H1.
  - inverts H1.
    inverts H2.
    apply P_1.
    applys_eq (v2_1 _ _ (v2_0 (x0+10))); flia.
Qed.

Lemma P_i x i:
  v2 x i ->
  exists y, P1 x y /\ (i>=6 -> y*3+1<2^i).
Proof.
  gen x.
  induction i using lt_wf_ind.
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_0,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_1,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_2,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_3,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_4,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_5,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    1: apply P_6,Hx.
    lia.
  }
  { 
    intros x Hx.
    inverts Hx.
    unshelve epose proof (H _ _ _ H2) as [y [I1 I2]].
    1: lia.
    unshelve epose proof (v2_v2 _ _ (I2 _) _ H2) as [i' [E1 E2]].
    1: lia.
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_0; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_1; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_2; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_3; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_4; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_5; applys_eq E1; flia.
      - rw_pow; lia.
    }
    {
      unshelve epose proof (H _ _ _ E1) as [y0 [I3 I4]].
      1: lia.
      {
        eexists; split.
        - eapply Step1.
          + apply I1.
          + applys_eq I3; flia.
        - pose proof (Nat.pow_le_mono_r 2 i' i).
          rw_pow; lia.
      }
    }
  }
Qed.

Lemma P1'_i x i:
  P1 x i ->
  P1' x i.
Proof.
  intros HP.
  induction HP.
  - apply Step0'1.
  - apply Step1'1; assumption.
Qed.

Lemma P0_i x i:
  P1 x i ->
  P0 x i.
Proof.
  intros HP.
  inverts HP.
  - apply Step0'0.
  - apply Step1'0.
    + apply P1'_i,H.
    + apply P1'_i,H0.
Qed.

Lemma v2_mod3 x:
  exists i,
  v2 (x*3) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/2) as x1.
  remember (x mod 2) as x2.
  replace x with (x1*2+x2) in * by lia.
  destruct x2 as [|[|]].
  3: lia.
  - exists O.
    applys_eq (v2_0 (x1*3)); flia.
  - unshelve epose proof (H x1 _) as [i I1].
    1: lia.
    eexists.
    applys_eq (v2_1 _ _ I1); flia.
Qed.

Definition S n := S1 0 (n*3) 0 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros x.
  epose proof (v2_mod3 x) as [i I1].
  epose proof (P_i _ _ I1) as [y [I2' _]].
  epose proof (P0_i _ _ I2') as I2.
  unfold P0 in I2.
  eexists (x+y).
  applys_eq I2; flia.
Qed.

End TM57.


Module TM51.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RB_1LF0LD_1RE1LD_1LA0RB_---0LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{D}} [1]^^(b) *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (2+b) c r -->*
  S1 (1+a) b (1+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*2+b) c r -->*
  S1 (n+a) b (n+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d r:
  S1 a 0 c ([0] *> [1]^^d *> r) -->+
  S1 0 (2+a+c) (1+d) r.
Proof.
  es.
Qed.

Lemma Ov1 a c r:
  S1 (1+a) 1 c r -->+
  S1 0 a 0 ([0] *> [1]^^(2+c) *> r).
Proof.
  es.
Qed.

Lemma Ov1_0 c r:
  halts tm (S1 0 1 c r).
Proof.
  unfold S1.
  esx.
Qed.

Definition P1' x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*3+2+c) (1+d) r.

Lemma Step0'1 x:
  P1' (x*2+0) 0.
Proof.
  unfold P1'; intros.
  follow Incs1.
  follow10 Ov0.
  finish.
Qed.

Lemma Step1'1 x y y0:
  P1' x y ->
  P1' (x+y*3+2) y0 ->
  P1' ((1+x)*2+1) (y+y0+1).
Proof.
  unfold P1'; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  rewrite Nat.add_0_r.
  follow100 H0.
  finish.
Qed.

Lemma unfold_0inf:
  0inf = [0] *> [1]^^0 *> 0inf.
Proof.
  solve_const0_eq.
Qed.

Definition P0 x y :=
  S1 0 x 1 0inf -->+
  S1 0 (x+y*3+3) 1 0inf.

Lemma Step0'0 x:
  P0 (x*2+0) 0.
Proof.
  unfold P0.
  follow Incs1.
  rewrite unfold_0inf.
  follow10 Ov0.
  rewrite <-unfold_0inf.
  finish.
Qed.

Lemma Step1'0 x y y0:
  P1' x y ->
  P1' (x+y*3+2) y0 ->
  P0 ((1+x)*2+1) (y+y0+1).
Proof.
  unfold P0; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov1.
  follow100 H.
  rewrite Nat.add_0_r.
  rewrite unfold_0inf.
  follow100 H0.
  rewrite <-unfold_0inf.
  finish.
Qed.

Inductive P1: nat->nat->Prop :=
| Step0 x: P1 (x*2+0) 0
| Step1 x y y0:
  P1 x y ->
  P1 (x+y*3+2) y0 ->
  P1 ((1+x)*2+1) (y+y0+1).

Inductive v2: nat->nat->Prop :=
| v2_0 x: v2 (x*2+0) 0
| v2_1 x i: v2 x i -> v2 ((1+x)*2+1) (S i)
.

Lemma v2_v2 y i:
  y<2^i ->
  forall x,
  v2 x i ->
  exists i',
  v2 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/2) as y1.
    remember (y mod 2) as y2.
    replace y with (y1*2+y2) in * by lia.
    destruct y2 as [|[|]].
    3: lia.
    + inverts H0.
      unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
      1: lia.
      eexists; split.
      * applys_eq (v2_1 _ _ Hi'); flia.
      * lia.
    + inverts H0.
      eexists; split.
      * applys_eq (v2_0 (x0+y1+2)); flia.
      * lia.
Qed.

Lemma P_0 x:
  v2 x 0 ->
  P1 x 0.
Proof.
  intros Hx.
  inverts Hx.
  apply Step0.
Qed.

Lemma P_1 x:
  v2 x 1 ->
  P1 x 1.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 0 0).
  - apply P_0,H1.
  - inverts H1.
    applys_eq (P_0 _ (v2_0 (x+1))); flia.
Qed.

Lemma P_2 x:
  v2 x 2 ->
  P1 x 2.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 1 0).
  - apply P_1,H1.
  - inverts H1.
    applys_eq (P_0 _ (v2_0 (x+4))); flia.
Qed.

Lemma P_3 x:
  v2 x 3 ->
  P1 x 5.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 2 2).
  - apply P_2,H1.
  - inverts H1.
    inverts H2.
    inverts H1.
    apply P_2.
    applys_eq (v2_1 _ _ (v2_1 _ _ (v2_0 (x+1)))); flia.
Qed.

Lemma P_4 x:
  v2 x 4 ->
  P1 x 6.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 5 0).
  - apply P_3,H1.
  - inverts H1.
    applys_eq (P_0 _ (v2_0 (x+10))); flia.
Qed.

Lemma P_5 x:
  v2 x 5 ->
  P1 x 9.
Proof.
  intros Hx.
  inverts Hx.
  eapply (Step1 _ 6 2).
  - apply P_4,H1.
  - inverts H1.
    inverts H2.
    inverts H1.
    apply P_2.
    applys_eq (v2_1 _ _ (v2_1 _ _ (v2_0 (x+4)))); flia.
Qed.

Lemma P_i x i:
  v2 x i ->
  exists y, P1 x y /\ (i>=5 -> y*3+2<2^i).
Proof.
  gen x.
  induction i using lt_wf_ind.
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_0,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_1,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_2,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_3,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split. 2: lia.
    apply P_4,Hx.
  }
  destruct i.
  {
    intros x Hx.
    eexists; split.
    1: apply P_5,Hx.
    lia.
  }
  { 
    intros x Hx.
    inverts Hx.
    unshelve epose proof (H _ _ _ H2) as [y [I1 I2]].
    1: lia.
    unshelve epose proof (v2_v2 _ _ (I2 _) _ H2) as [i' [E1 E2]].
    1: lia.
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_0; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_1; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_2; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_3; applys_eq E1; flia.
      - rw_pow; lia.
    }
    destruct i'.
    {
      eexists; split.
      - eapply Step1.
        + apply I1.
        + apply P_4; applys_eq E1; flia.
      - rw_pow; lia.
    }
    {
      unshelve epose proof (H _ _ _ E1) as [y0 [I3 I4]].
      1: lia.
      {
        eexists; split.
        - eapply Step1.
          + apply I1.
          + applys_eq I3; flia.
        - pose proof (Nat.pow_le_mono_r 2 i' i).
          rw_pow; lia.
      }
    }
  }
Qed.

Lemma P1'_i x i:
  P1 x i ->
  P1' x i.
Proof.
  intros HP.
  induction HP.
  - apply Step0'1.
  - apply Step1'1; assumption.
Qed.

Lemma P0_i x i:
  P1 x i ->
  P0 x i.
Proof.
  intros HP.
  inverts HP.
  - apply Step0'0.
  - apply Step1'0.
    + apply P1'_i,H.
    + apply P1'_i,H0.
Qed.

Lemma v2_mod3 x:
  exists i,
  v2 (x*3) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/2) as x1.
  remember (x mod 2) as x2.
  replace x with (x1*2+x2) in * by lia.
  destruct x2 as [|[|]].
  3: lia.
  - exists O.
    applys_eq (v2_0 (x1*3)); flia.
  - unshelve epose proof (H x1 _) as [i I1].
    1: lia.
    eexists.
    applys_eq (v2_1 _ _ I1); flia.
Qed.

Definition S n := S1 0 (n*3) 1 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros x.
  epose proof (v2_mod3 x) as [i I1].
  epose proof (P_i _ _ I1) as [y [I2' _]].
  epose proof (P0_i _ _ I2') as I2.
  unfold P0 in I2.
  eexists (x+y+1).
  applys_eq I2; flia.
Qed.

End TM51.


Module TM4.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC0RC_1LD1RC_1LA1LE_1LF0LA_---0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{A}} [1]^^b *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (3+b) c r -->*
  S1 (1+a) b (2+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*3+b) c r -->*
  S1 (n+a) b (n*2+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d r:
  S1 a 0 c ([0] *> [1]^^d *> r) -->+
  S1 0 (a+c) (2+d) r.
Proof.
  es.
Qed.

Lemma Ov1 a c d r:
  S1 a 1 c ([0] *> [1]^^d *> r) -->+
  S1 0 (3+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov2 a c r:
  S1 (2+a) 2 c r -->+
  S1 0 a 1 ([0] *> [1]^^(3+c) *> r).
Proof.
  es.
Qed.

Lemma Ov2_1 c r:
  halts tm (S1 1 2 c r).
Proof.
  esx.
Qed.

Lemma Ov2_0 c r:
  S1 0 2 c r -->+
  S1 0 1 (3+c) r.
Proof.
  es.
Qed.

Definition P1_0 x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*2+c) d r.

Definition P1_2 x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*2+c) (2+d) r.

Lemma Step0' x:
  P1_2 (x*3+0) 0.
Proof.
  unfold P1_2; intros.
  follow Incs1.
  follow10 Ov0.
  finish.
Qed.

Lemma Step1' x:
  P1_0 (x*3+1) 1.
Proof.
  unfold P1_0; intros.
  follow Incs1.
  follow10 Ov1.
  finish.
Qed.

Lemma Step2' x y y0:
  P1_0 x y ->
  P1_0 (x+y*2+1) y0 ->
  P1_0 ((2+x)*3+2) (y+y0).
Proof.
  unfold P1_0; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov2.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step2a' x y y0:
  P1_0 x y ->
  P1_2 (x+y*2+1) y0 ->
  P1_2 ((2+x)*3+2) (y+y0).
Proof.
  unfold P1_0,P1_2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov2.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step2b' x y y0:
  P1_2 x y ->
  P1_0 (x+y*2+1) y0 ->
  P1_0 ((2+x)*3+2) (y+y0+1).
Proof.
  unfold P1_0,P1_2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov2.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step2c' x y y0:
  P1_2 x y ->
  P1_2 (x+y*2+1) y0 ->
  P1_2 ((2+x)*3+2) (y+y0+1).
Proof.
  unfold P1_0,P1_2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov2.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step2d':
  P1_0 2 2.
Proof.
  unfold P1_0; intros.
  follow10 Ov2_0.
  follow100 Ov1.
  finish.
Qed.

Inductive v3: nat->nat->Prop :=
| v3_0 x: v3 (x*3+0) 0
| v3_1 x: v3 (x*3+1) 0
| v3_2 x i:
  v3 x i ->
  v3 ((2+x)*3+2) (S i)
| v3_2_0:
  v3 2 1
.

Lemma v3_v3 y i:
  y<3^i ->
  forall x,
  v3 x i ->
  exists i',
  v3 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/3) as y1.
    remember (y mod 3) as y2.
    replace y with (y1*3+y2) in * by lia.
    destruct y2 as [|[|[|]]].
    4: lia.
    + inverts H0.
      {
        unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
        1: lia.
        eexists; split.
        * applys_eq (v3_2 _ _ Hi'); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_2_0).
        * lia.
      }
    + inverts H0.
      {
        eexists; split.
        * applys_eq (v3_0 (x0+y1+3)); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_0 1).
        * lia.
      }
    + inverts H0.
      {
        eexists; split.
        * applys_eq (v3_1 (x0+y1+3)); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_1 1).
        * lia.
      }
Qed.


Lemma P_0 x:
  v3 x 0 ->
  P1_0 x 1 \/ P1_2 x 0.
Proof.
  intros Hx.
  inverts Hx.
  - right.
    apply Step0'.
  - left.
    apply Step1'.
Qed.

Lemma P_1 x:
  v3 x 1 ->
  (P1_0 x 2 \/ P1_2 x 1).
Proof.
  intros Hx.
  inverts Hx.
  - inverts H1.
    + left.
      apply (Step2b' _ 0 1).
      * apply Step0'.
      * applys_eq (Step1' x); flia.
    + left.
      apply (Step2' _ 1 1).
      * apply Step1'.
      * applys_eq (Step1' (x+1)); flia.
  - left.
    apply Step2d'.
Qed.

Lemma P_2 x:
  v3 x 2 ->
  P1_0 x 3.
Proof.
  intros Hx.
  inverts Hx.
  inverts H1.
  - inverts H2.
    + eapply (Step2' _ 2 1).
      1: eapply (Step2b' _ 0 1).
      1: eapply Step0'.
      1: applys_eq (Step1' x0); flia.
      applys_eq (Step1' (x0*3+4)); flia.
    + eapply (Step2' _ 2 1).
      1: eapply (Step2' _ 1 1).
      1: eapply Step1'.
      1: applys_eq (Step1' (x0+1)); flia.
      applys_eq (Step1' (x0*3+5)); flia.
  - eapply (Step2' _ 2 1).
    1: apply Step2d'.
    apply (Step1' 2).
Qed.

Lemma P_i x i:
  v3 x i ->
  exists y, (P1_0 x y \/ P1_2 x y) /\ (i>=2 -> y*2+1<3^i).
Proof.
  gen x.
  induction i using lt_wf_ind.
  destruct i.
  {
    intros x Hx.
    epose proof (P_0 _ Hx) as [I|I].
    - eexists; split.
      1: left; apply I.
      lia.
    - eexists; split.
      1: right; apply I.
      lia.
  }
  destruct i.
  {
    intros x Hx.
    epose proof (P_1 _ Hx) as [I|I].
    - eexists; split.
      1: left; apply I.
      lia.
    - eexists; split.
      1: right; apply I.
      lia.
  }
  destruct i.
  {
    intros x Hx.
    epose proof (P_2 _ Hx) as I.
    - eexists; split.
      1: left; apply I.
      lia.
  }
  { 
    intros x Hx.
    inverts Hx.
    unshelve epose proof (H _ _ _ H2) as [y [I1 I2]].
    1: lia.
    destruct I1 as [I1|I1].
    {
      unshelve epose proof (v3_v3 _ _ (I2 _) _ H2) as [i' [E1 E2]].
      1: lia.
      destruct i'.
      {
        epose proof (P_0 _ E1) as [I|I].
        - eexists; split.
          1: left; apply Step2'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
        - eexists; split.
          1: right; apply Step2a'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
      }
      destruct i'.
      {
        epose proof (P_1 _ E1) as [I|I].
        - eexists; split.
          1: left; apply Step2'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
        - eexists; split.
          1: right; apply Step2a'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
      }
      {
        unshelve epose proof (H _ _ _ E1) as [y0 [I3 I4]].
        1: lia.
        destruct I3 as [I3|I3].
        {
          eexists; split.
          - left; eapply Step2'.
            + apply I1.
            + applys_eq I3; flia.
          - pose proof (Nat.pow_le_mono_r 3 i' i).
            rw_pow; lia.
        }
        {
          eexists; split.
          - right; eapply Step2a'.
            + apply I1.
            + applys_eq I3; flia.
          - pose proof (Nat.pow_le_mono_r 3 i' i).
            rw_pow; lia.
        }
      }
    }
    {
      unshelve epose proof (v3_v3 _ _ (I2 _) _ H2) as [i' [E1 E2]].
      1: lia.
      destruct i'.
      {
        epose proof (P_0 _ E1) as [I|I].
        - eexists; split.
          1: left; apply Step2b'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
        - eexists; split.
          1: right; apply Step2c'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
      }
      destruct i'.
      {
        epose proof (P_1 _ E1) as [I|I].
        - eexists; split.
          1: left; apply Step2b'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
        - eexists; split.
          1: right; apply Step2c'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
      }
      {
        unshelve epose proof (H _ _ _ E1) as [y0 [I3 I4]].
        1: lia.
        destruct I3 as [I3|I3].
        {
          eexists; split.
          - left; eapply Step2b'.
            + apply I1.
            + applys_eq I3; flia.
          - pose proof (Nat.pow_le_mono_r 3 i' i).
            rw_pow; lia.
        }
        {
          eexists; split.
          - right; eapply Step2c'.
            + apply I1.
            + applys_eq I3; flia.
          - pose proof (Nat.pow_le_mono_r 3 i' i).
            rw_pow; lia.
        }
      }
    }
  }
Qed.

Lemma v3_even x:
  exists i,
  v3 (x*2) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/3) as x1.
  remember (x mod 3) as x2.
  replace x with (x1*3+x2) in * by lia.
  destruct x2 as [|[|[|]]].
  4: lia.
  - exists O.
    applys_eq (v3_0 (x1*2)); flia.
  - destruct x1.
    + eexists.
      apply v3_2_0.
    + unshelve epose proof (H x1 _) as [i I1].
      1: lia.
      eexists.
      applys_eq (v3_2 _ _ I1); flia.
  - exists O.
    applys_eq (v3_1 (x1*2+1)); flia.
Qed.

Definition S '(n,i) := S1 0 (n*2) i 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S (O,O)).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_cond with (P:=fun '(n,i) => i=O\/i=2).
  2: lia.
  unfold S.
  intros [x tp].
  epose proof (v3_even (x)) as [i I1].
  epose proof (P_i _ _ I1) as [y [I2 _]].
  intros I3.
  destruct I2 as [I2|I2];
  destruct I3 as [I3|I3];
  epose proof (I2 _ O 0inf) as I2;
  cbn in I2;
  rewrite <-const_unfold in I2;
  unfold P1_0,P1_2 in *;
  subst.
  - eexists (x+y,_); split.
    + follow10 I2.
      finish.
    + lia.
  - eexists (x+y+1,_); split.
    + follow10 I2.
      finish.
    + lia.
  - eexists (x+y,_); split.
    + follow10 I2.
      finish.
    + lia.
  - eexists (x+y+1,_); split.
    + follow10 I2.
      finish.
    + lia.
Qed.

End TM4.


Module TM8.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1RC0RC_1LD1RC_1LA1LE_1LF0LA_---0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{A}} [1]^^b *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (3+b) c r -->*
  S1 (1+a) b (2+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*3+b) c r -->*
  S1 (n+a) b (n*2+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d r:
  S1 a 0 c ([0] *> [1]^^d *> r) -->+
  S1 0 (a+c) (2+d) r.
Proof.
  es.
Qed.

Lemma Ov1 a c d r:
  S1 a 1 c ([0] *> [1]^^d *> r) -->+
  S1 0 (3+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov2 a c r:
  S1 (2+a) 2 c r -->+
  S1 0 a 1 ([0] *> [1]^^(3+c) *> r).
Proof.
  es.
Qed.

Lemma Ov2_1 c r:
  halts tm (S1 1 2 c r).
Proof.
  esx.
Qed.

Lemma Ov2_0 c r:
  S1 0 2 c r -->+
  S1 0 1 (3+c) r.
Proof.
  es.
Qed.


Definition P1_0 x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*2+c) d r.

Definition P1_2 x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*2+c) (2+d) r.

Lemma Step0' x:
  P1_2 (x*3+0) 0.
Proof.
  unfold P1_2; intros.
  follow Incs1.
  follow10 Ov0.
  finish.
Qed.

Lemma Step1' x:
  P1_0 (x*3+1) 1.
Proof.
  unfold P1_0; intros.
  follow Incs1.
  follow10 Ov1.
  finish.
Qed.

Lemma Step2' x y y0:
  P1_0 x y ->
  P1_0 (x+y*2+1) y0 ->
  P1_0 ((2+x)*3+2) (y+y0).
Proof.
  unfold P1_0; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov2.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step2a' x y y0:
  P1_0 x y ->
  P1_2 (x+y*2+1) y0 ->
  P1_2 ((2+x)*3+2) (y+y0).
Proof.
  unfold P1_0,P1_2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov2.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step2b' x y y0:
  P1_2 x y ->
  P1_0 (x+y*2+1) y0 ->
  P1_0 ((2+x)*3+2) (y+y0+1).
Proof.
  unfold P1_0,P1_2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov2.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step2c' x y y0:
  P1_2 x y ->
  P1_2 (x+y*2+1) y0 ->
  P1_2 ((2+x)*3+2) (y+y0+1).
Proof.
  unfold P1_0,P1_2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov2.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step2d':
  P1_0 2 2.
Proof.
  unfold P1_0; intros.
  follow10 Ov2_0.
  follow100 Ov1.
  finish.
Qed.

Inductive v3: nat->nat->Prop :=
| v3_0 x: v3 (x*3+0) 0
| v3_1 x: v3 (x*3+1) 0
| v3_2 x i:
  v3 x i ->
  v3 ((2+x)*3+2) (S i)
| v3_2_0:
  v3 2 1
.

Lemma v3_v3 y i:
  y<3^i ->
  forall x,
  v3 x i ->
  exists i',
  v3 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/3) as y1.
    remember (y mod 3) as y2.
    replace y with (y1*3+y2) in * by lia.
    destruct y2 as [|[|[|]]].
    4: lia.
    + inverts H0.
      {
        unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
        1: lia.
        eexists; split.
        * applys_eq (v3_2 _ _ Hi'); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_2_0).
        * lia.
      }
    + inverts H0.
      {
        eexists; split.
        * applys_eq (v3_0 (x0+y1+3)); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_0 1).
        * lia.
      }
    + inverts H0.
      {
        eexists; split.
        * applys_eq (v3_1 (x0+y1+3)); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_1 1).
        * lia.
      }
Qed.


Lemma P_0 x:
  v3 x 0 ->
  P1_0 x 1 \/ P1_2 x 0.
Proof.
  intros Hx.
  inverts Hx.
  - right.
    apply Step0'.
  - left.
    apply Step1'.
Qed.

Lemma P_1 x:
  v3 x 1 ->
  (P1_0 x 2 \/ P1_2 x 1).
Proof.
  intros Hx.
  inverts Hx.
  - inverts H1.
    + left.
      apply (Step2b' _ 0 1).
      * apply Step0'.
      * applys_eq (Step1' x); flia.
    + left.
      apply (Step2' _ 1 1).
      * apply Step1'.
      * applys_eq (Step1' (x+1)); flia.
  - left.
    apply Step2d'.
Qed.

Lemma P_2 x:
  v3 x 2 ->
  P1_0 x 3.
Proof.
  intros Hx.
  inverts Hx.
  inverts H1.
  - inverts H2.
    + eapply (Step2' _ 2 1).
      1: eapply (Step2b' _ 0 1).
      1: eapply Step0'.
      1: applys_eq (Step1' x0); flia.
      applys_eq (Step1' (x0*3+4)); flia.
    + eapply (Step2' _ 2 1).
      1: eapply (Step2' _ 1 1).
      1: eapply Step1'.
      1: applys_eq (Step1' (x0+1)); flia.
      applys_eq (Step1' (x0*3+5)); flia.
  - eapply (Step2' _ 2 1).
    1: apply Step2d'.
    apply (Step1' 2).
Qed.

Lemma P_i x i:
  v3 x i ->
  exists y, (P1_0 x y \/ P1_2 x y) /\ (i>=2 -> y*2+1<3^i).
Proof.
  gen x.
  induction i using lt_wf_ind.
  destruct i.
  {
    intros x Hx.
    epose proof (P_0 _ Hx) as [I|I].
    - eexists; split.
      1: left; apply I.
      lia.
    - eexists; split.
      1: right; apply I.
      lia.
  }
  destruct i.
  {
    intros x Hx.
    epose proof (P_1 _ Hx) as [I|I].
    - eexists; split.
      1: left; apply I.
      lia.
    - eexists; split.
      1: right; apply I.
      lia.
  }
  destruct i.
  {
    intros x Hx.
    epose proof (P_2 _ Hx) as I.
    - eexists; split.
      1: left; apply I.
      lia.
  }
  { 
    intros x Hx.
    inverts Hx.
    unshelve epose proof (H _ _ _ H2) as [y [I1 I2]].
    1: lia.
    destruct I1 as [I1|I1].
    {
      unshelve epose proof (v3_v3 _ _ (I2 _) _ H2) as [i' [E1 E2]].
      1: lia.
      destruct i'.
      {
        epose proof (P_0 _ E1) as [I|I].
        - eexists; split.
          1: left; apply Step2'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
        - eexists; split.
          1: right; apply Step2a'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
      }
      destruct i'.
      {
        epose proof (P_1 _ E1) as [I|I].
        - eexists; split.
          1: left; apply Step2'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
        - eexists; split.
          1: right; apply Step2a'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
      }
      {
        unshelve epose proof (H _ _ _ E1) as [y0 [I3 I4]].
        1: lia.
        destruct I3 as [I3|I3].
        {
          eexists; split.
          - left; eapply Step2'.
            + apply I1.
            + applys_eq I3; flia.
          - pose proof (Nat.pow_le_mono_r 3 i' i).
            rw_pow; lia.
        }
        {
          eexists; split.
          - right; eapply Step2a'.
            + apply I1.
            + applys_eq I3; flia.
          - pose proof (Nat.pow_le_mono_r 3 i' i).
            rw_pow; lia.
        }
      }
    }
    {
      unshelve epose proof (v3_v3 _ _ (I2 _) _ H2) as [i' [E1 E2]].
      1: lia.
      destruct i'.
      {
        epose proof (P_0 _ E1) as [I|I].
        - eexists; split.
          1: left; apply Step2b'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
        - eexists; split.
          1: right; apply Step2c'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
      }
      destruct i'.
      {
        epose proof (P_1 _ E1) as [I|I].
        - eexists; split.
          1: left; apply Step2b'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
        - eexists; split.
          1: right; apply Step2c'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
      }
      {
        unshelve epose proof (H _ _ _ E1) as [y0 [I3 I4]].
        1: lia.
        destruct I3 as [I3|I3].
        {
          eexists; split.
          - left; eapply Step2b'.
            + apply I1.
            + applys_eq I3; flia.
          - pose proof (Nat.pow_le_mono_r 3 i' i).
            rw_pow; lia.
        }
        {
          eexists; split.
          - right; eapply Step2c'.
            + apply I1.
            + applys_eq I3; flia.
          - pose proof (Nat.pow_le_mono_r 3 i' i).
            rw_pow; lia.
        }
      }
    }
  }
Qed.

Lemma v3_even x:
  exists i,
  v3 (x*2) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/3) as x1.
  remember (x mod 3) as x2.
  replace x with (x1*3+x2) in * by lia.
  destruct x2 as [|[|[|]]].
  4: lia.
  - exists O.
    applys_eq (v3_0 (x1*2)); flia.
  - destruct x1.
    + eexists.
      apply v3_2_0.
    + unshelve epose proof (H x1 _) as [i I1].
      1: lia.
      eexists.
      applys_eq (v3_2 _ _ I1); flia.
  - exists O.
    applys_eq (v3_1 (x1*2+1)); flia.
Qed.

Definition S '(n,i) := S1 0 (n*2) i 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S (O,O)).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_cond with (P:=fun '(n,i) => i=O\/i=2).
  2: lia.
  unfold S.
  intros [x tp].
  epose proof (v3_even (x)) as [i I1].
  epose proof (P_i _ _ I1) as [y [I2 _]].
  intros I3.
  destruct I2 as [I2|I2];
  destruct I3 as [I3|I3];
  epose proof (I2 _ O 0inf) as I2;
  cbn in I2;
  rewrite <-const_unfold in I2;
  unfold P1_0,P1_2 in *;
  subst.
  - eexists (x+y,_); split.
    + follow10 I2.
      finish.
    + lia.
  - eexists (x+y+1,_); split.
    + follow10 I2.
      finish.
    + lia.
  - eexists (x+y,_); split.
    + follow10 I2.
      finish.
    + lia.
  - eexists (x+y+1,_); split.
    + follow10 I2.
      finish.
    + lia.
Qed.

End TM8.


Module TM9.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1RC0RC_1LD1RC_1RA1LE_1LF0LA_---0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{A}} [1]^^b *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (3+b) c r -->*
  S1 (1+a) b (2+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*3+b) c r -->*
  S1 (n+a) b (n*2+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d r:
  S1 a 0 c ([0] *> [1]^^d *> r) -->+
  S1 0 (a+c) (2+d) r.
Proof.
  es.
Qed.

Lemma Ov1 a c d r:
  S1 a 1 c ([0] *> [1]^^d *> r) -->+
  S1 0 (3+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov2 a c r:
  S1 (2+a) 2 c r -->+
  S1 0 a 1 ([0] *> [1]^^(3+c) *> r).
Proof.
  es.
Qed.

Lemma Ov2_1 c r:
  halts tm (S1 1 2 c r).
Proof.
  esx.
Qed.

Lemma Ov2_0 c d r:
  S1 0 2 c ([0] *> [1]^^d *> r) -->+
  S1 1 (3+c) d r.
Proof.
  es.
Qed.


Definition P1_0 x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*2+c) d r.

Definition P1_2 x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*2+c) (2+d) r.

Lemma Step0' x:
  P1_2 (x*3+0) 0.
Proof.
  unfold P1_2; intros.
  follow Incs1.
  follow10 Ov0.
  finish.
Qed.

Lemma Step1' x:
  P1_0 (x*3+1) 1.
Proof.
  unfold P1_0; intros.
  follow Incs1.
  follow10 Ov1.
  finish.
Qed.

Lemma Step2' x y y0:
  P1_0 x y ->
  P1_0 (x+y*2+1) y0 ->
  P1_0 ((2+x)*3+2) (y+y0).
Proof.
  unfold P1_0; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov2.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step2a' x y y0:
  P1_0 x y ->
  P1_2 (x+y*2+1) y0 ->
  P1_2 ((2+x)*3+2) (y+y0).
Proof.
  unfold P1_0,P1_2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov2.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step2b' x y y0:
  P1_2 x y ->
  P1_0 (x+y*2+1) y0 ->
  P1_0 ((2+x)*3+2) (y+y0+1).
Proof.
  unfold P1_0,P1_2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov2.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step2c' x y y0:
  P1_2 x y ->
  P1_2 (x+y*2+1) y0 ->
  P1_2 ((2+x)*3+2) (y+y0+1).
Proof.
  unfold P1_0,P1_2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov2.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step2d':
  P1_0 14 2.
Proof.
  unfold P1_0; intros.
  change 14 with ((2+2)*3+2).
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov2.
  follow100 Ov2_0.
  change (3+1) with (1*3+1).
  follow Incs1.
  follow100 Ov1.
  finish.
Qed.

Inductive v3: nat->nat->Prop :=
| v3_0 x: v3 (x*3+0) 0
| v3_1 x: v3 (x*3+1) 0
| v3_2 x i:
  v3 x i ->
  v3 ((2+x)*3+2) (S i)
| v3_2_0:
  v3 14 1
.

Lemma v3_v3 y i:
  y<3^i ->
  forall x,
  v3 x i ->
  exists i',
  v3 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/3) as y1.
    remember (y mod 3) as y2.
    replace y with (y1*3+y2) in * by lia.
    destruct y2 as [|[|[|]]].
    4: lia.
    + inverts H0.
      {
        unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
        1: lia.
        eexists; split.
        * applys_eq (v3_2 _ _ Hi'); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_2_0).
        * lia.
      }
    + inverts H0.
      {
        eexists; split.
        * applys_eq (v3_0 (x0+y1+3)); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_0 5).
        * lia.
      }
    + inverts H0.
      {
        eexists; split.
        * applys_eq (v3_1 (x0+y1+3)); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_1 5).
        * lia.
      }
Qed.


Lemma P_0 x:
  v3 x 0 ->
  P1_0 x 1 \/ P1_2 x 0.
Proof.
  intros Hx.
  inverts Hx.
  - right.
    apply Step0'.
  - left.
    apply Step1'.
Qed.

Lemma P_1 x:
  v3 x 1 ->
  (P1_0 x 2 \/ P1_2 x 1).
Proof.
  intros Hx.
  inverts Hx.
  - inverts H1.
    + left.
      apply (Step2b' _ 0 1).
      * apply Step0'.
      * applys_eq (Step1' x); flia.
    + left.
      apply (Step2' _ 1 1).
      * apply Step1'.
      * applys_eq (Step1' (x+1)); flia.
  - left.
    apply Step2d'.
Qed.

Lemma P_2 x:
  v3 x 2 ->
  P1_0 x 3.
Proof.
  intros Hx.
  inverts Hx.
  inverts H1.
  - inverts H2.
    + eapply (Step2' _ 2 1).
      1: eapply (Step2b' _ 0 1).
      1: eapply Step0'.
      1: applys_eq (Step1' x0); flia.
      applys_eq (Step1' (x0*3+4)); flia.
    + eapply (Step2' _ 2 1).
      1: eapply (Step2' _ 1 1).
      1: eapply Step1'.
      1: applys_eq (Step1' (x0+1)); flia.
      applys_eq (Step1' (x0*3+5)); flia.
  - eapply (Step2' _ 2 1).
    1: apply Step2d'.
    apply (Step1' 6).
Qed.

Lemma P_i x i:
  v3 x i ->
  exists y, (P1_0 x y \/ P1_2 x y) /\ (i>=2 -> y*2+1<3^i).
Proof.
  gen x.
  induction i using lt_wf_ind.
  destruct i.
  {
    intros x Hx.
    epose proof (P_0 _ Hx) as [I|I].
    - eexists; split.
      1: left; apply I.
      lia.
    - eexists; split.
      1: right; apply I.
      lia.
  }
  destruct i.
  {
    intros x Hx.
    epose proof (P_1 _ Hx) as [I|I].
    - eexists; split.
      1: left; apply I.
      lia.
    - eexists; split.
      1: right; apply I.
      lia.
  }
  destruct i.
  {
    intros x Hx.
    epose proof (P_2 _ Hx) as I.
    - eexists; split.
      1: left; apply I.
      lia.
  }
  { 
    intros x Hx.
    inverts Hx.
    unshelve epose proof (H _ _ _ H2) as [y [I1 I2]].
    1: lia.
    destruct I1 as [I1|I1].
    {
      unshelve epose proof (v3_v3 _ _ (I2 _) _ H2) as [i' [E1 E2]].
      1: lia.
      destruct i'.
      {
        epose proof (P_0 _ E1) as [I|I].
        - eexists; split.
          1: left; apply Step2'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
        - eexists; split.
          1: right; apply Step2a'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
      }
      destruct i'.
      {
        epose proof (P_1 _ E1) as [I|I].
        - eexists; split.
          1: left; apply Step2'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
        - eexists; split.
          1: right; apply Step2a'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
      }
      {
        unshelve epose proof (H _ _ _ E1) as [y0 [I3 I4]].
        1: lia.
        destruct I3 as [I3|I3].
        {
          eexists; split.
          - left; eapply Step2'.
            + apply I1.
            + applys_eq I3; flia.
          - pose proof (Nat.pow_le_mono_r 3 i' i).
            rw_pow; lia.
        }
        {
          eexists; split.
          - right; eapply Step2a'.
            + apply I1.
            + applys_eq I3; flia.
          - pose proof (Nat.pow_le_mono_r 3 i' i).
            rw_pow; lia.
        }
      }
    }
    {
      unshelve epose proof (v3_v3 _ _ (I2 _) _ H2) as [i' [E1 E2]].
      1: lia.
      destruct i'.
      {
        epose proof (P_0 _ E1) as [I|I].
        - eexists; split.
          1: left; apply Step2b'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
        - eexists; split.
          1: right; apply Step2c'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
      }
      destruct i'.
      {
        epose proof (P_1 _ E1) as [I|I].
        - eexists; split.
          1: left; apply Step2b'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
        - eexists; split.
          1: right; apply Step2c'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
      }
      {
        unshelve epose proof (H _ _ _ E1) as [y0 [I3 I4]].
        1: lia.
        destruct I3 as [I3|I3].
        {
          eexists; split.
          - left; eapply Step2b'.
            + apply I1.
            + applys_eq I3; flia.
          - pose proof (Nat.pow_le_mono_r 3 i' i).
            rw_pow; lia.
        }
        {
          eexists; split.
          - right; eapply Step2c'.
            + apply I1.
            + applys_eq I3; flia.
          - pose proof (Nat.pow_le_mono_r 3 i' i).
            rw_pow; lia.
        }
      }
    }
  }
Qed.

Lemma v3_even x:
  x<>1%nat ->
  exists i,
  v3 (x*2) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/3) as x1.
  remember (x mod 3) as x2.
  replace x with (x1*3+x2) in * by lia.
  destruct x2 as [|[|[|]]].
  4: lia.
  - exists O.
    applys_eq (v3_0 (x1*2)); flia.
  - destruct x1.
    1: lia.
    intros.
    destruct (Nat.eqb_spec x1 1).
    + subst.
      eexists.
      apply v3_2_0.
    + unshelve epose proof (H x1 _ _) as [i I1].
      1,2: lia.
      eexists.
      applys_eq (v3_2 _ _ I1); flia.
  - exists O.
    applys_eq (v3_1 (x1*2+1)); flia.
Qed.

Definition S '(n,i) := S1 0 ((n+2)*2) i 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S (3,0)%nat).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_cond with (P:=fun '(n,i) => i=O\/i=2).
  2: lia.
  unfold S.
  intros [x tp].
  epose proof (v3_even (x+2)) as [i I1].
  1: lia.
  epose proof (P_i _ _ I1) as [y [I2 _]].
  intros I3.
  destruct I2 as [I2|I2];
  destruct I3 as [I3|I3];
  epose proof (I2 _ O 0inf) as I2;
  cbn in I2;
  rewrite <-const_unfold in I2;
  unfold P1_0,P1_2 in *;
  subst.
  - eexists (x+y,_); split.
    + follow10 I2.
      finish.
    + lia.
  - eexists (x+y+1,_); split.
    + follow10 I2.
      finish.
    + lia.
  - eexists (x+y,_); split.
    + follow10 I2.
      finish.
    + lia.
  - eexists (x+y+1,_); split.
    + follow10 I2.
      finish.
    + lia.
Qed.

End TM9.


Module TM20.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC0RC_1LD1RC_1RA1LE_1LF0LA_---0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1]^^a <* [0] <{{A}} [1]^^b *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (3+b) c r -->*
  S1 (1+a) b (2+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*3+b) c r -->*
  S1 (n+a) b (n*2+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov0 a c d r:
  S1 a 0 c ([0] *> [1]^^d *> r) -->+
  S1 0 (a+c) (2+d) r.
Proof.
  es.
Qed.

Lemma Ov1 a c d r:
  S1 a 1 c ([0] *> [1]^^d *> r) -->+
  S1 0 (3+a+c) d r.
Proof.
  es.
Qed.

Lemma Ov2 a c r:
  S1 (2+a) 2 c r -->+
  S1 0 a 1 ([0] *> [1]^^(3+c) *> r).
Proof.
  es.
Qed.

Lemma Ov2_1 c r:
  halts tm (S1 1 2 c r).
Proof.
  esx.
Qed.

Lemma Ov2_0 c d r:
  S1 0 2 c ([0] *> [1]^^d *> r) -->+
  S1 1 (3+c) d r.
Proof.
  es.
Qed.


Definition P1_0 x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*2+c) d r.

Definition P1_2 x y :=
  forall c d r,
  S1 0 x c ([0] *> [1]^^d *> r) -->+
  S1 0 (x+y*2+c) (2+d) r.

Lemma Step0' x:
  P1_2 (x*3+0) 0.
Proof.
  unfold P1_2; intros.
  follow Incs1.
  follow10 Ov0.
  finish.
Qed.

Lemma Step1' x:
  P1_0 (x*3+1) 1.
Proof.
  unfold P1_0; intros.
  follow Incs1.
  follow10 Ov1.
  finish.
Qed.

Lemma Step2' x y y0:
  P1_0 x y ->
  P1_0 (x+y*2+1) y0 ->
  P1_0 ((2+x)*3+2) (y+y0).
Proof.
  unfold P1_0; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov2.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step2a' x y y0:
  P1_0 x y ->
  P1_2 (x+y*2+1) y0 ->
  P1_2 ((2+x)*3+2) (y+y0).
Proof.
  unfold P1_0,P1_2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov2.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step2b' x y y0:
  P1_2 x y ->
  P1_0 (x+y*2+1) y0 ->
  P1_0 ((2+x)*3+2) (y+y0+1).
Proof.
  unfold P1_0,P1_2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov2.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step2c' x y y0:
  P1_2 x y ->
  P1_2 (x+y*2+1) y0 ->
  P1_2 ((2+x)*3+2) (y+y0+1).
Proof.
  unfold P1_0,P1_2; intros.
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov2.
  follow100 H.
  follow100 H0.
  finish.
Qed.

Lemma Step2d':
  P1_0 14 2.
Proof.
  unfold P1_0; intros.
  change 14 with ((2+2)*3+2).
  follow Incs1.
  rewrite Nat.add_0_r.
  follow10 Ov2.
  follow100 Ov2_0.
  change (3+1) with (1*3+1).
  follow Incs1.
  follow100 Ov1.
  finish.
Qed.

Inductive v3: nat->nat->Prop :=
| v3_0 x: v3 (x*3+0) 0
| v3_1 x: v3 (x*3+1) 0
| v3_2 x i:
  v3 x i ->
  v3 ((2+x)*3+2) (S i)
| v3_2_0:
  v3 14 1
.

Lemma v3_v3 y i:
  y<3^i ->
  forall x,
  v3 x i ->
  exists i',
  v3 (x+y) i' /\
  i'<=i.
Proof.
  gen y.
  induction i.
  - intros.
    replace y with O by lia.
    exists O.
    split. 2: lia.
    intros.
    applys_eq H0; flia.
  - cbn[Nat.pow].
    intros.
    remember (y/3) as y1.
    remember (y mod 3) as y2.
    replace y with (y1*3+y2) in * by lia.
    destruct y2 as [|[|[|]]].
    4: lia.
    + inverts H0.
      {
        unshelve epose proof (IHi (y1) _ _ H3) as [i' [Hi' Hi0']].
        1: lia.
        eexists; split.
        * applys_eq (v3_2 _ _ Hi'); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_2_0).
        * lia.
      }
    + inverts H0.
      {
        eexists; split.
        * applys_eq (v3_0 (x0+y1+3)); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_0 5).
        * lia.
      }
    + inverts H0.
      {
        eexists; split.
        * applys_eq (v3_1 (x0+y1+3)); flia.
        * lia.
      }
      {
        replace y1 with O by lia.
        eexists; split.
        * apply (v3_1 5).
        * lia.
      }
Qed.


Lemma P_0 x:
  v3 x 0 ->
  P1_0 x 1 \/ P1_2 x 0.
Proof.
  intros Hx.
  inverts Hx.
  - right.
    apply Step0'.
  - left.
    apply Step1'.
Qed.

Lemma P_1 x:
  v3 x 1 ->
  (P1_0 x 2 \/ P1_2 x 1).
Proof.
  intros Hx.
  inverts Hx.
  - inverts H1.
    + left.
      apply (Step2b' _ 0 1).
      * apply Step0'.
      * applys_eq (Step1' x); flia.
    + left.
      apply (Step2' _ 1 1).
      * apply Step1'.
      * applys_eq (Step1' (x+1)); flia.
  - left.
    apply Step2d'.
Qed.

Lemma P_2 x:
  v3 x 2 ->
  P1_0 x 3.
Proof.
  intros Hx.
  inverts Hx.
  inverts H1.
  - inverts H2.
    + eapply (Step2' _ 2 1).
      1: eapply (Step2b' _ 0 1).
      1: eapply Step0'.
      1: applys_eq (Step1' x0); flia.
      applys_eq (Step1' (x0*3+4)); flia.
    + eapply (Step2' _ 2 1).
      1: eapply (Step2' _ 1 1).
      1: eapply Step1'.
      1: applys_eq (Step1' (x0+1)); flia.
      applys_eq (Step1' (x0*3+5)); flia.
  - eapply (Step2' _ 2 1).
    1: apply Step2d'.
    apply (Step1' 6).
Qed.

Lemma P_i x i:
  v3 x i ->
  exists y, (P1_0 x y \/ P1_2 x y) /\ (i>=2 -> y*2+1<3^i).
Proof.
  gen x.
  induction i using lt_wf_ind.
  destruct i.
  {
    intros x Hx.
    epose proof (P_0 _ Hx) as [I|I].
    - eexists; split.
      1: left; apply I.
      lia.
    - eexists; split.
      1: right; apply I.
      lia.
  }
  destruct i.
  {
    intros x Hx.
    epose proof (P_1 _ Hx) as [I|I].
    - eexists; split.
      1: left; apply I.
      lia.
    - eexists; split.
      1: right; apply I.
      lia.
  }
  destruct i.
  {
    intros x Hx.
    epose proof (P_2 _ Hx) as I.
    - eexists; split.
      1: left; apply I.
      lia.
  }
  { 
    intros x Hx.
    inverts Hx.
    unshelve epose proof (H _ _ _ H2) as [y [I1 I2]].
    1: lia.
    destruct I1 as [I1|I1].
    {
      unshelve epose proof (v3_v3 _ _ (I2 _) _ H2) as [i' [E1 E2]].
      1: lia.
      destruct i'.
      {
        epose proof (P_0 _ E1) as [I|I].
        - eexists; split.
          1: left; apply Step2'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
        - eexists; split.
          1: right; apply Step2a'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
      }
      destruct i'.
      {
        epose proof (P_1 _ E1) as [I|I].
        - eexists; split.
          1: left; apply Step2'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
        - eexists; split.
          1: right; apply Step2a'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
      }
      {
        unshelve epose proof (H _ _ _ E1) as [y0 [I3 I4]].
        1: lia.
        destruct I3 as [I3|I3].
        {
          eexists; split.
          - left; eapply Step2'.
            + apply I1.
            + applys_eq I3; flia.
          - pose proof (Nat.pow_le_mono_r 3 i' i).
            rw_pow; lia.
        }
        {
          eexists; split.
          - right; eapply Step2a'.
            + apply I1.
            + applys_eq I3; flia.
          - pose proof (Nat.pow_le_mono_r 3 i' i).
            rw_pow; lia.
        }
      }
    }
    {
      unshelve epose proof (v3_v3 _ _ (I2 _) _ H2) as [i' [E1 E2]].
      1: lia.
      destruct i'.
      {
        epose proof (P_0 _ E1) as [I|I].
        - eexists; split.
          1: left; apply Step2b'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
        - eexists; split.
          1: right; apply Step2c'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
      }
      destruct i'.
      {
        epose proof (P_1 _ E1) as [I|I].
        - eexists; split.
          1: left; apply Step2b'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
        - eexists; split.
          1: right; apply Step2c'.
          1: eassumption.
          1: applys_eq I; flia.
          rw_pow; lia.
      }
      {
        unshelve epose proof (H _ _ _ E1) as [y0 [I3 I4]].
        1: lia.
        destruct I3 as [I3|I3].
        {
          eexists; split.
          - left; eapply Step2b'.
            + apply I1.
            + applys_eq I3; flia.
          - pose proof (Nat.pow_le_mono_r 3 i' i).
            rw_pow; lia.
        }
        {
          eexists; split.
          - right; eapply Step2c'.
            + apply I1.
            + applys_eq I3; flia.
          - pose proof (Nat.pow_le_mono_r 3 i' i).
            rw_pow; lia.
        }
      }
    }
  }
Qed.

Lemma v3_even x:
  x<>1%nat ->
  exists i,
  v3 (x*2) i.
Proof.
  induction x using lt_wf_ind.
  remember (x/3) as x1.
  remember (x mod 3) as x2.
  replace x with (x1*3+x2) in * by lia.
  destruct x2 as [|[|[|]]].
  4: lia.
  - exists O.
    applys_eq (v3_0 (x1*2)); flia.
  - destruct x1.
    1: lia.
    intros.
    destruct (Nat.eqb_spec x1 1).
    + subst.
      eexists.
      apply v3_2_0.
    + unshelve epose proof (H x1 _ _) as [i I1].
      1,2: lia.
      eexists.
      applys_eq (v3_2 _ _ I1); flia.
  - exists O.
    applys_eq (v3_1 (x1*2+1)); flia.
Qed.

Definition S '(n,i) := S1 0 ((n+2)*2) i 0inf%sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S (3,0)%nat).
  1: unfold S,S1; esx.
  eapply progress_nonhalt_cond with (P:=fun '(n,i) => i=O\/i=2).
  2: lia.
  unfold S.
  intros [x tp].
  epose proof (v3_even (x+2)) as [i I1].
  1: lia.
  epose proof (P_i _ _ I1) as [y [I2 _]].
  intros I3.
  destruct I2 as [I2|I2];
  destruct I3 as [I3|I3];
  epose proof (I2 _ O 0inf) as I2;
  cbn in I2;
  rewrite <-const_unfold in I2;
  unfold P1_0,P1_2 in *;
  subst.
  - eexists (x+y,_); split.
    + follow10 I2.
      finish.
    + lia.
  - eexists (x+y+1,_); split.
    + follow10 I2.
      finish.
    + lia.
  - eexists (x+y,_); split.
    + follow10 I2.
      finish.
    + lia.
  - eexists (x+y+1,_); split.
    + follow10 I2.
      finish.
    + lia.
Qed.

End TM20.


Module TM21.
Definition tm := Eval compute in (TM_from_str "1RB0RB_1LB0LC_1RD1LC_1RE0RA_1RF0RB_---1LB").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1]^^a <* [0] <{{C}} [1]^^b *> [0;1] *> [1]^^c *> 0inf.

Definition S1_1 a b c :=
  S1 a (1+b*2) c.

Definition S1_0 a b c :=
  S1 a (2+b*2) c.

Lemma Inc1_0 a b c:
  S1_0 a (2+b) c -->*
  S1_0 (2+a) b (2+c).
Proof.
  unfold S1_0,S1.
  es.
Qed.

Lemma Incs1_0 n a b c:
  S1_0 a (n*2+b) c -->*
  S1_0 (n*2+a) b (n*2+c).
Proof.
  gen a b c.
  ind n Inc1_0.
Qed.

Lemma Inc1_1 a b c:
  S1_1 a (2+b) c -->*
  S1_1 (2+a) b (2+c).
Proof.
  unfold S1_1,S1.
  es.
Qed.

Lemma Incs1_1 n a b c:
  S1_1 a (n*2+b) c -->*
  S1_1 (n*2+a) b (n*2+c).
Proof.
  gen a b c.
  ind n Inc1_1.
Qed.

Lemma LL_2 n c:
  S1 0 (n*4+2) c -->*
  S1 0 (n*2) (3+n*2+c).
Proof.
  epose proof (Incs1_0 n 0 0 c) as I1.
  unfold S1_0 in I1.
  follow I1.
  es.
Qed.

Lemma LL_4 n c:
  S1 0 (n*4+4) c -->*
  S1 0 (6+n*4+c) 1.
Proof.
  epose proof (Incs1_0 n 0 1 c) as I1.
  unfold S1_0 in I1.
  follow I1.
  mid (S1 0 (6+n*2+n*2+c) 1).
  1: es.
  finish.
Qed.

Lemma LL_1 n c:
  S1 0 (n*4+1) c -->*
  S1 0 (3+n*4+c) 1.
Proof.
  epose proof (Incs1_1 n 0 0 c) as I1.
  unfold S1_1 in I1.
  follow I1.
  mid (S1 0 (3+n*2+n*2+c) 1).
  1: es.
  finish.
Qed.

Lemma LL_3 n c:
  S1 0 (n*4+3) c -->*
  S1 0 (1+n*2) (3+n*2+c).
Proof.
  epose proof (Incs1_1 n 0 1 c) as I1.
  unfold S1_1 in I1.
  follow I1.
  es.
Qed.

Lemma LL_0_1 c:
  halts tm (S1 0 0 (c*2+1)).
Proof.
  unfold S1.
  esx.
Qed.

Lemma LL_0_0 c:
  S1 0 0 (c*2) -->*
  S1 0 (1+c*2) 1.
Proof.
  es.
Qed.

Inductive v2: nat->nat->Prop :=
| v2_0 x: v2 (x*2+2) 0
| v2_1 x i: v2 x i -> v2 (x*2+1) (S i)
.

Lemma LLs_1 n i c:
  v2 n i ->
  S1 0 (n*2+1) c -->*
  S1 0 (2+i+c+(n*2+1)) 1.
Proof.
  gen n c.
  induction i; intros.
  - inverts H.
    follow (LL_1 (x+1) c).
    finish.
  - inverts H.
    follow (LL_3 x c).
    epose proof (IHi _ _ H2) as I1.
    follow I1. clear I1.
    finish.
Qed.

Lemma LLs_1' i c:
  S1 0 ((2^i-1)*2+1) c -->*
  S1 0 (2+i+c+((2^i-1)*2+1)) 1.
Proof.
  gen c.
  induction i; intros.
  - follow (LL_1 0 c).
    finish.
  - cbn[Nat.pow].
    follow (LL_3 (2^i-1) c).
    epose proof (IHi _) as I1.
    follow I1. clear I1.
    finish.
Qed.

Lemma LLs_0 n i c:
  v2 n i ->
  S1 0 (n*2) c -->*
  S1 0 (2+i+c+(n*2)) 1.
Proof.
  gen n c.
  induction i; intros.
  - inverts H.
    follow (LL_4 x c).
    finish.
  - inverts H.
    follow (LL_2 x c).
    epose proof (IHi _ _ H2) as I1.
    follow I1. clear I1.
    finish.
Qed.

Close Scope sym.

Ltac solve_v2 :=
match goal with
| |- v2 ?n (S ?i) => applys_eq (v2_1 (n/2) i); solve_v2
| |- v2 ?n O => applys_eq (v2_0 (n/2-1)); solve_v2
| _ => try lia
end.

Lemma v2_spec x i:
  v2 ((x*2+3)*2^i-1) i.
Proof.
  induction i; intros.
  1: solve_v2.
  cbn[Nat.pow].
  solve_v2.
  applys_eq IHi; flia.
Qed.

Lemma pow2_ge i:
  1+i<=2^i.
Proof.
  induction i; cbn[Nat.pow]; lia.
Qed.

Lemma P_n i n x:
  3<=i ->
  1<=n ->
  x<2^i ->
  x<>2^i-2 ->
  x<>2^i-3 ->
  x<>2^i-6 ->
  S1 0 (n*2^i+x) 1 -->*
  S1 0 (n*2^i+2^i-1) 1.
Proof.
  gen n x.
  induction i; intros.
  1: lia.
  destruct i as [|i].
  1: lia.
  destruct i as [|i].
  1: lia.
  destruct i as [|i].
  {
    cbn.
    intros.
    assert (I4:S1 0 (n*8+4) 1 -->* S1 0 (n*8+8-1) 1).
    {
      follow (LLs_0 (n*4+2) 0 1).
      1: solve_v2.
      finish.
    }
    assert (I3:S1 0 (n*8+3) 1 -->* S1 0 (n*8+8-1) 1).
    {
      follow (LLs_1 (n*4+1) 1 1).
      1: solve_v2.
      finish.
    }
    assert (I1:S1 0 (n*8+1) 1 -->* S1 0 (n*8+8-1) 1).
    {
      follow (LLs_1 (n*4) 0 1).
      1: solve_v2.
      follow I4.
      finish.
    }
    assert (I0:S1 0 (n*8+0) 1 -->* S1 0 (n*8+8-1) 1).
    {
      follow (LLs_0 (n*4) 0 1).
      1: solve_v2.
      follow I3.
      finish.
    }
    destruct x.
    1: follow I0; finish.
    destruct x.
    1: follow I1; finish.
    destruct x.
    1: lia.
    destruct x.
    1: follow I3; finish.
    destruct x.
    1: follow I4; finish.
    destruct x.
    1: lia.
    destruct x.
    1: lia.
    finish.
  }
  cbn[Nat.pow] in *.
  assert (I2:S1 0 (n*2^i*16+2^i*8-2) 1 -->* S1 0 (n*2^i*16+2^i*16-1) 1). {
    epose proof (LLs_0 _ _ 1 (v2_spec (n-1) (S(S i)))) as I.
    cbn[Nat.pow] in I.
    replace ((n-1)*2+3) with (n*2+1) in I by lia.
    follow I.
    pose proof (pow2_ge i).
    follow (IHi (n*2+1) (3+i)).
    1-6: lia.
    finish.
  }
  destruct (Nat.ltb_spec x (2^i*8)) as [E|E].
  {
    destruct (Nat.eqb_spec x (2^i*8-6)) as [E0|E0].
    {
      follow (LLs_0 (n*2^i*8+2^i*4-3) 1 1).
      1: solve_v2.
      follow I2.
      finish.
    }
    destruct (Nat.eqb_spec x (2^i*8-3)) as [E1|E1].
    {
      follow (LLs_1 (n*2^i*8+2^i*4-2) 0 1).
      1: solve_v2.
      follow (IHi (n*2+1) 0).
      1-6: lia.
      finish.
    }
    destruct (Nat.eqb_spec x (2^i*8-2)) as [E2|E2].
    1: follow I2; finish.
    follow (IHi (n*2) x).
    1-6: lia.
    epose proof (LLs_1 _ _ 1 (v2_spec (n-1) (S(S i)))) as I.
    cbn[Nat.pow] in I.
    replace ((n-1)*2+3) with (n*2+1) in I by lia.
    follow I.
    pose proof (pow2_ge i).
    follow (IHi (n*2+1) (4+i)).
    1-6: lia.
    finish.
  }
  {
    follow (IHi (n*2+1) (x-2^i*8)).
    1-6: lia.
    finish.
  }
Time Qed.

Definition S' i := S1 0 (2^i*8-1) 1.

Lemma BigStep' i:
  c0 -->* S' i.
Proof.
  induction i.
  1: unfold S',S1; esx.
  follow IHi.
  unfold S'.
  cbn[Nat.pow].
  epose proof (LLs_1' (S(S i)) 1) as I.
  cbn[Nat.pow] in I.
  follow I. clear I.
  epose proof (P_n (S(S(S i))) 1 (4+i)) as I.
  cbn[Nat.pow] in I.
  pose proof (pow2_ge i).
  follow I.
  1-5: lia.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_; split.
  1: apply (BigStep' n).
  split.
  1: unfold S',S1; solve_sigma_score.
  pose proof (pow2_ge n).
  lia.
Qed.

End TM21.


Module TM22.
Definition tm := Eval compute in (TM_from_str "1RB0RF_0RC0RF_1RD---_1LE0RB_0LB0LE_1LD1RA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <* <[1;0]^^a <{{B}} [0] *> [1;1]^^b *> [0] *> [1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (2+b) c r -->*
  S1 (1+a) b (2+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n a b c r:
  S1 a (n*2+b) c r -->*
  S1 (n+a) b (n*2+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma LL_0 n c r:
  S1 0 (n*2+0) c r -->*
  S1 0 n (1+n*2+c) r.
Proof.
  follow Incs1.
  es.
Qed.

Lemma LL_0' n c r:
  S1 1 (n*2+0) c r -->*
  S1 0 (n+1) (1+n*2+c) r.
Proof.
  follow Incs1.
  es.
Qed.

Definition S2 n r :=
  0inf <{{B}} [0] *> [1]^^n *> r.

Lemma LL_1 n c r:
  S1 0 (n*2+1) c r -->*
  S2 (4+n*2+n*2+c) r.
Proof.
  follow Incs1.
  es.
Qed.

Lemma LL_1' n c r:
  S1 1 (n*2+1) c r -->*
  S2 (6+n*2+n*2+c) r.
Proof.
  follow Incs1.
  es.
Qed.

Inductive v2: nat->nat->Prop :=
| v2_0 x: v2 (x*2+1) 0
| v2_1 x i: v2 x i -> v2 (x*2+0) (S i)
.

Lemma LLs n i c r:
  v2 n i ->
  S1 0 n c r -->*
  S2 (2+i+n*2+c) r.
Proof.
  intros.
  gen n c.
  induction i; intros.
  - inverts H.
    follow LL_1.
    finish.
  - inverts H.
    follow LL_0.
    follow IHi.
    finish.
Qed.

Lemma LLs_1 n i c r:
  v2 (n+2) i ->
  S1 1 n c r -->*
  S2 (4+i+n*2+c) r.
Proof.
  intros.
  inverts H.
  - replace n with ((x-1)*2+1) by lia.
    follow LL_1'.
    finish.
  - replace n with ((x-1)*2+0) by lia.
    follow LL_0'.
    eapply LLs in H1.
    follow H1.
    finish.
Qed.

Notation rh1 := (0>>1>>0inf).
Notation rh2 := (0>>1>>1>>0inf).
Notation rh3 := (0>>1>>1>>0>>1>>0inf).
Notation rh4 := (0>>rh2).

Inductive RH := RH0|RH1|RH2|RH3|RH4.
Inductive Tp := t0|t1.

Lemma Rst_4_0 n i:
  v2 (n+2) i ->
  S2 (n*2+4) 0inf -->+
  S2 (2+i+(n+2)*2) 0inf.
Proof.
  intros.
  mid10 (S1 1 n 2 0inf).
  1: es.
  follow LLs_1.
  finish.
Qed.

Lemma Rst_3_0 n i:
  v2 (n+2) i ->
  S2 (n*2+3) 0inf -->+
  S2 (2+i+(n+2)*2) rh1.
Proof.
  intros.
  mid10 (S1 1 n 2 rh1).
  1: es.
  follow LLs_1.
  finish.
Qed.

Lemma Rst_4_1 n i:
  v2 (n+2) i ->
  S2 (n*2+4) rh1 -->+
  S2 (3+i+(n+2)*2) 0inf.
Proof.
  intros.
  mid10 (S1 1 n 3 0inf).
  1: es.
  follow LLs_1.
  finish.
Qed.

Lemma Rst_3_1 n i:
  v2 (n+2) i ->
  S2 (n*2+3) rh1 -->+
  S2 (0+i+(n+2)*2) rh2.
Proof.
  intros.
  mid10 (S1 1 n 0 rh2).
  1: es.
  follow LLs_1.
  finish.
Qed.

Lemma Rst_4_2 n i:
  v2 (n+2) i ->
  S2 (n*2+4) rh2 -->+
  S2 (4+i+(n+2)*2) 0inf.
Proof.
  intros.
  mid10 (S1 1 n 4 0inf).
  1: es.
  follow LLs_1.
  finish.
Qed.

Lemma Rst_3_2 n i:
  v2 (n+2) i ->
  S2 (n*2+3) rh2 -->+
  S2 (2+i+(n+2)*2) rh3.
Proof.
  intros.
  mid10 (S1 1 n 2 rh3).
  1: es.
  follow LLs_1.
  finish.
Qed.

Lemma Rst_4_3 n i:
  v2 (n+2) i ->
  S2 (n*2+4) rh3 -->+
  S2 (4+i+(n+2)*2) rh1.
Proof.
  intros.
  mid10 (S1 1 n 4 rh1).
  1: es.
  follow LLs_1.
  finish.
Qed.

Lemma Rst_3_3 n i:
  v2 (n+2) i ->
  S2 (n*2+3) rh3 -->+
  S2 (2+i+(n+2)*2) rh4.
Proof.
  intros.
  mid10 (S1 1 n 2 rh4).
  1: es.
  follow LLs_1.
  finish.
Qed.

Lemma Rst_4_4 n i:
  v2 (n+2) i ->
  S2 (n*2+4) rh4 -->+
  S2 (2+i+(n+2)*2) rh2.
Proof.
  intros.
  mid10 (S1 1 n 2 rh2).
  1: es.
  follow LLs_1.
  finish.
Qed.

Lemma Rst_3_4 n:
  halts tm (S2 (n*2+3) rh4).
Proof.
  unfold S2.
  esx.
Qed.

Definition S3 n tp r :=
  S2 (n*2-
   match tp with
   | t0 => 0
   | t1 => 1
   end)
  (match r with
   | RH0 => 0inf
   | RH1 => rh1
   | RH2 => rh2
   | RH3 => rh3
   | RH4 => rh4
   end).

Close Scope sym.

From BusyCoq Require Import DivModCases.

Definition nxt i tp r :=
match mod2 i with
| mod2eq0 i =>
  match tp with
  | t0 =>
    match r with
    | RH0 => Some (i+1,t0,RH0)
    | RH1 => Some (i+2,t1,RH0)
    | RH2 => Some (i+2,t0,RH0)
    | RH3 => Some (i+2,t0,RH1)
    | RH4 => Some (i+1,t0,RH2)
    end
  | t1 =>
    match r with
    | RH0 => Some (i+1,t0,RH1)
    | RH1 => Some (i+0,t0,RH2)
    | RH2 => Some (i+1,t0,RH3)
    | RH3 => Some (i+1,t0,RH4)
    | RH4 => None
    end
  end
| mod2eq1 i =>
  match tp with
  | t0 =>
    match r with
    | RH0 => Some (i+2,t1,RH0)
    | RH1 => Some (i+2,t0,RH0)
    | RH2 => Some (i+3,t1,RH0)
    | RH3 => Some (i+3,t1,RH1)
    | RH4 => Some (i+2,t1,RH2)
    end
  | t1 =>
    match r with
    | RH0 => Some (i+2,t1,RH1)
    | RH1 => Some (i+1,t1,RH2)
    | RH2 => Some (i+2,t1,RH3)
    | RH3 => Some (i+2,t1,RH4)
    | RH4 => None
    end
  end
end.

Lemma nxt_spec n i tp r:
  n>=2 ->
  v2 n i ->
  match nxt i tp r with
  | Some (dn,tp',r') => S3 n tp r -->+ S3 (n+dn) tp' r'
  | None => halts tm (S3 n tp r)
  end.
Proof.
  intros.
  unfold nxt.
  remember (n-2) as n'.
  replace n with (n'+2) in * by lia.
  unfold S3.
  destruct (mod2 i); subst;
  destruct tp,r.
  - applys_eq (Rst_4_0 _ _ H0); flia.
  - applys_eq (Rst_4_1 _ _ H0); flia.
  - applys_eq (Rst_4_2 _ _ H0); flia.
  - applys_eq (Rst_4_3 _ _ H0); flia.
  - applys_eq (Rst_4_4 _ _ H0); flia.
  - applys_eq (Rst_3_0 _ _ H0); flia.
  - applys_eq (Rst_3_1 _ _ H0); flia.
  - applys_eq (Rst_3_2 _ _ H0); flia.
  - applys_eq (Rst_3_3 _ _ H0); flia.
  - applys_eq (Rst_3_4 n'); flia.
  - applys_eq (Rst_4_0 _ _ H0); flia.
  - applys_eq (Rst_4_1 _ _ H0); flia.
  - applys_eq (Rst_4_2 _ _ H0); flia.
  - applys_eq (Rst_4_3 _ _ H0); flia.
  - applys_eq (Rst_4_4 _ _ H0); flia.
  - applys_eq (Rst_3_0 _ _ H0); flia.
  - applys_eq (Rst_3_1 _ _ H0); flia.
  - applys_eq (Rst_3_2 _ _ H0); flia.
  - applys_eq (Rst_3_3 _ _ H0); flia.
  - applys_eq (Rst_3_4 n'); flia.
Qed.

Ltac solve_v2 :=
match goal with
| |- v2 ?n (S ?i) => applys_eq (v2_1 (n/2) i); solve_v2
| |- v2 ?n O => applys_eq (v2_0 (n/2)); solve_v2
| _ => try lia
end.

Fixpoint v2_c x :=
match x with
| xO x0 => S (v2_c x0)
| _ => O
end.

Lemma v2_c_spec x:
  v2 (Pos.to_nat x) (v2_c x).
Proof.
  induction x; cbn; solve_v2.
  applys_eq IHx; flia.
Qed.

Lemma v2_spec x i:
  v2 ((x*2+1)*2^i) i.
Proof.
  induction i; intros.
  1: solve_v2.
  cbn[Nat.pow].
  solve_v2.
  applys_eq IHi; flia.
Qed.

Lemma v2_inv x i:
  v2 x i ->
  exists x0, x=(x0*2+1)*2^i.
Proof.
  intros H.
  induction H.
  - exists x; lia.
  - destruct IHv2 as [x0 I].
    exists x0; cbn[Nat.pow]; lia.
Qed.

Lemma v2_eq n i x j:
  1<=x<2^i ->
  v2 x j ->
  v2 (n*2^i+x) j.
Proof.
  intros.
  apply v2_inv in H0.
  destruct H0 as [x0 I1].
  subst.
  epose proof (Nat.pow_lt_mono_r_iff 2 j i).
  replace i with (i-j-1+j+1) by lia.
  repeat rewrite Nat.pow_add_r.
  applys_eq (v2_spec (x0+n*2^(i-j-1)) j); lia.
Qed.

Fixpoint nxts x tp r m T :=
match T with
| O => None
| S T =>
  if Pos.ltb x m then
    match nxt (v2_c x) tp r with
    | Some (dn,tp',r') =>
      nxts ((N.of_nat dn) :+ x) tp' r' m T
    | None => Some false
    end
  else if Pos.eqb x m then
    match tp,r with
    | t0,RH1 => Some true
    | _,_ => None
    end
  else None
end.

Require Import ZifyN.

Lemma nxts_spec x tp r m T i n:
Pos.to_nat m = 2^i ->
1 <= Pos.to_nat x <= 2^i ->
1 <= n ->
match nxts x tp r m T with
| None => True
| Some true => S3 (n*2^i+(Pos.to_nat x)) tp r -->* S3 (n*2^i+2^i) t0 RH1
| Some false => halts tm (S3 (n*2^i+(Pos.to_nat x)) tp r)
end.
Proof.
  intros.
  gen x tp r.
  induction T; cbn[nxts]; intros; trivial.
  destruct (Pos.ltb_spec x m).
  - unshelve epose proof (nxt_spec (n*2^i+(Pos.to_nat x)) (v2_c x) tp r _ _).
    1: lia.
    1: apply v2_eq; [lia|apply v2_c_spec].
    destruct (nxt (v2_c x) tp r) as [[[dn tp'] r']|].
    2: assumption.
    destruct (nxts (N.of_nat dn :+ x) tp' r' m T) as [[]|] eqn:E; trivial.
    + unshelve (epose proof (IHT _ _ _ _) as I; rewrite E in I).
      1:{
        destruct T; cbn in E.
        1: congruence.
        destruct (Pos.ltb_spec (N.of_nat dn :+ x) m).
        1: lia.
        destruct (Pos.eqb_spec (N.of_nat dn :+ x) m).
        1: lia.
        congruence.
      }
      follow100 H3.
      follow I.
      finish.
    + unshelve (epose proof (IHT _ _ _ _) as I; rewrite E in I).
      1:{
        destruct T; cbn in E.
        1: congruence.
        destruct (Pos.ltb_spec (N.of_nat dn :+ x) m).
        1: lia.
        destruct (Pos.eqb_spec (N.of_nat dn :+ x) m).
        1: lia.
        congruence.
      }
      eapply halts_evstep.
      2: follow100 H3; finish.
      applys_eq I; flia.
  - destruct (Pos.eqb_spec x m); trivial.
    destruct tp,r; trivial.
    finish.
Qed.

Lemma nxts_spec' x tp r m T i n:
Pos.to_nat m = 2^i ->
2 <= Pos.to_nat x <= 2^i ->
match nxts x tp r m T with
| None => True
| Some true => S3 (n*2^i+(Pos.to_nat x)) tp r -->* S3 (n*2^i+2^i) t0 RH1
| Some false => halts tm (S3 (n*2^i+(Pos.to_nat x)) tp r)
end.
Proof.
  intros.
  gen x tp r.
  induction T; cbn[nxts]; intros; trivial.
  destruct (Pos.ltb_spec x m).
  - unshelve epose proof (nxt_spec (n*2^i+(Pos.to_nat x)) (v2_c x) tp r _ _).
    1: lia.
    1: apply v2_eq; [lia|apply v2_c_spec].
    destruct (nxt (v2_c x) tp r) as [[[dn tp'] r']|].
    2: assumption.
    destruct (nxts (N.of_nat dn :+ x) tp' r' m T) as [[]|] eqn:E; trivial.
    + unshelve (epose proof (IHT _ _ _ _) as I; rewrite E in I).
      1:{
        destruct T; cbn in E.
        1: congruence.
        destruct (Pos.ltb_spec (N.of_nat dn :+ x) m).
        1: lia.
        destruct (Pos.eqb_spec (N.of_nat dn :+ x) m).
        1: lia.
        congruence.
      }
      follow100 H2.
      follow I.
      finish.
    + unshelve (epose proof (IHT _ _ _ _) as I; rewrite E in I).
      1:{
        destruct T; cbn in E.
        1: congruence.
        destruct (Pos.ltb_spec (N.of_nat dn :+ x) m).
        1: lia.
        destruct (Pos.eqb_spec (N.of_nat dn :+ x) m).
        1: lia.
        congruence.
      }
      eapply halts_evstep.
      2: follow100 H2; finish.
      applys_eq I; flia.
  - destruct (Pos.eqb_spec x m); trivial.
    destruct tp,r; trivial.
    finish.
Qed.

Fixpoint nxtss tp r m T maxT :=
match T with
| O => true
| S T =>
  match nxts (Pos.of_succ_nat T) tp r m maxT with
  | Some true => nxtss tp r m T maxT
  | _ => false
  end
end.

Lemma nxtss_spec i tp r m T maxT:
  Pos.to_nat m = 2^i ->
  T < 2^i ->
  nxtss tp r m T maxT = true ->
  forall n x,
  1<=n ->
  1<=x<=T ->
  S3 (n*2^i+x) tp r -->* S3 (n*2^i+2^i) t0 RH1.
Proof.
  intro Hm.
  induction T; intros.
  1: lia.
  cbn[nxtss] in H0.
  destruct (nxts (Pos.of_succ_nat T) tp r m maxT) eqn:E.
  2: congruence.
  destruct b.
  2: congruence.
  assert (x<=T\/x=S T) as [E0|E0] by lia.
  - apply IHT; solve[assumption|lia].
  - unshelve (epose proof (nxts_spec _ _ _ _ _ _ n Hm _ _) as I; rewrite E in I).
    1,2: lia.
    follow I.
    finish.
Qed.

Lemma Step n x tp:
  1<=n ->
  1<=x<=501 ->
  S3 (n*2^10+x) tp RH0 -->* S3 (n*2^10+2^10) t0 RH1.
Proof.
  intros.
  apply nxtss_spec with (maxT:=1000) (m:=(2^10)%positive) (T:=501); try lia.
  destruct tp; native_check_eq.
Time Qed.

From BusyCoq Require Import BinaryCounter_v2.

Lemma v2_ex n:
  1<=n ->
  exists x i, v2 n i /\ n=(x*2+1)*2^i.
Proof.
  intros.
  lowbit_cases n.
  1: lia.
  exists x i; split.
  1: apply v2_spec.
  trivial.
Qed.

Lemma Step' n:
  1<=n ->
  n<2^990 ->
  S3 (n*2^10) t0 RH1 -->* S3 ((n+1)*2^10) t0 RH1.
Proof.
  intros.
  unshelve epose proof (v2_ex (n*2^10) _) as [x [i [I1 I2]]].
  1: lia.
  unshelve epose proof (nxt_spec (n*2^10) _ t0 RH1 _ I1) as I3.
  1: lia.
  assert (Hi:i<1000). {
    epose proof (Nat.pow_lt_mono_r_iff 2 i 1000).
    lia.
  }
  unfold nxt in I3.
  destruct (mod2 i); subst i.
  - follow100 I3.
    follow Step.
    1: lia.
    finish.
  - follow100 I3.
    follow Step.
    1: lia.
    finish.
Qed.

Lemma Halt n:
  n<2^990 ->
  halts tm (S3 ((2^990-n)*2^10) t0 RH1).
Proof.
  intros.
  induction n.
  - remember (2^1000) as v1.
    unshelve epose proof (nxt_spec v1 1000 t0 RH1 _ _).
    1: lia.
    1: applys_eq (v2_spec 0 1000); flia.
    unfold nxt in H0.
    destruct (mod2 1000).
    2: lia.
    replace a with 500 in * by lia.
    eapply halts_evstep.
    2:{
    replace ((2^990-0)*2^10) with v1 by lia.
    follow100 H0.
    finish.
    }
    unshelve epose proof (nxts_spec 502 t1 RH0 (2^10) 1000 10 (2^990) _ _ _) as I1.
    1-3: lia.
    replace (nxts 502 t1 RH0 (2 ^ 10) 1000) with (Some false) in I1 by (vm_compute; reflexivity).
    applys_eq I1; flia.
  - eapply halts_evstep.
    1: apply IHn; lia.
    follow (Step').
    1,2: lia.
    finish.
Qed.

Lemma init:
  c0 -->* S3 3 t1 RH0.
Proof.
  unfold S3,S2.
  esx.
Qed.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  1: apply (Halt (2^990-1)); lia.
  follow init.
  unshelve epose proof (nxts_spec' 3 t1 RH0 (2^10) 1000 10 0 _ _).
  1,2: lia.
  replace (nxts 3 t1 RH0 (2 ^ 10) 1000) with (Some true) in H by (vm_compute; reflexivity).
  remember (2^990) as v1.
  follow H.
  finish.
Qed.

End TM22.


