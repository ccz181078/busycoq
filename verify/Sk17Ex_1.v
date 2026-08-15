From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import SimplTape.
From BusyCoq Require Import ES_v3.

From BusyCoq Require Import DivModCases.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB1LC_1RC---_0LD1RE_0LA1LD_0RC1RF_0LF0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Fixpoint LC ls :=
match ls with
| [] => 0inf
| n::ls => LC ls <* <[1;0]^^n <* <[1]
end.


Notation Tp:=bool.
Notation tp0 := false.
Notation tp1 := true.

Inductive LInc: Tp->(list nat)->(list nat)->Prop :=
| LInc_tp0_2 a ls ls':
    LInc tp0 ls ls' ->
    LInc tp0 (2+a*2::ls) (2+a*2::ls')
| LInc_tp0_1 a ls ls':
    LInc tp1 ls ls' ->
    LInc tp0 (1+a*2::ls) (1+a*2::ls')
| LInc_tp1 a ls:
    LInc tp1 (a::ls) (1+a::ls)
| LInc_tp0_nil a:
    LInc tp0 [a*2] [1+a*2;O;O]
| LInc_tp0_00:
    LInc tp0 [O;O] [1;O;O;O]%nat
    .

Definition QL tp :=
match tp with
| tp0 => D
| tp1 => C
end.

Lemma LInc_spec tp ls ls':
  LInc tp ls ls' ->
  (forall r, LC ls <{{QL tp}} [1;0] *> r -->* LC ls' {{C}}> r).
Proof.
  intro H.
  induction H; cbn[QL LC] in *; intros.
  - es; er.
    follow IHLInc.
    es.
  - es; er.
    follow IHLInc.
    es.
  - es.
  - es.
  - es.
Qed.

Definition S1 ls n := LC ls {{C}}> [1;0]^^n *> 0inf.

Lemma Inc_00 a ls ls':
  LInc tp0 ls ls' ->
  S1 (a*2::ls) 0 -->*
  S1 ls' (a*2).
Proof.
  intro H.
  eapply LInc_spec in H.
  unfold S1.
  cbn[LC].
  es; er.
  follow H.
  finish.
Qed.

Lemma Inc_01 a ls ls':
  LInc tp1 ls ls' ->
  S1 (1+a*2::ls) 0 -->*
  S1 ls' (1+a*2).
Proof.
  intro H.
  eapply LInc_spec in H.
  unfold S1.
  cbn[LC].
  es; er.
  follow H.
  finish.
Qed.

Lemma Inc_1 n ls ls':
  LInc tp1 ls ls' ->
  S1 ls (1+n*2) -->*
  S1 ls' (n*2).
Proof.
  intro H.
  eapply LInc_spec in H.
  es; er.
  follow H.
  finish.
Qed.

Lemma Inc_2 n ls ls':
  LInc tp0 ls ls' ->
  S1 ls (2+n*2) -->*
  S1 ls' (1+n*2).
Proof.
  intro H.
  eapply LInc_spec in H.
  es; er.
  follow H.
  finish.
Qed.

Lemma init:
  c0 -->*
  S1 [3;O;O] 2.
Proof.
  unfold S1.
  esx.
Qed.

Close Scope sym.

Inductive WF: (list nat)->Prop :=
| WF_O n: WF ([0]^^n)
| WF_S a ls:
    a<>0 ->
    WF ls ->
    WF (a::ls)
.

Inductive WF': (list nat)->Prop :=
| WF'_O a: WF' [a]
| WF'_S a ls:
    a<>0 ->
    WF' ls ->
    WF' (a::ls).

Fixpoint ctzS_pos a :=
match a with
| xO a => S (ctzS_pos a)
| _ => O
end.

Definition ctzS(a:nat) :=
  ctzS_pos (Pos.of_succ_nat a).

Lemma ctzS_0':
  ctzS 0 = 0.
Proof. trivial. Qed.

Lemma ctzS_1':
  ctzS 1 = 1.
Proof. trivial. Qed.

Lemma ctzS_0 a:
  ctzS (a*2) = 0.
Proof.
  unfold ctzS.
  destruct a.
  - trivial.
  - replace (Pos.of_succ_nat (S a*2)) with (xI (Pos.of_succ_nat a)) by lia.
    trivial.
Qed.

Lemma ctzS_1 a:
  ctzS (1+a*2) = S (ctzS a).
Proof.
  unfold ctzS.
  replace (Pos.of_succ_nat (1+a*2)) with (xO (Pos.of_succ_nat a)) by lia.
  trivial.
Qed.

Lemma ctzS_spec_0 n0:
  forall n i,
  n < n0 ->
  ctzS n = i <-> n mod 2 ^ (i + 1) = 2 ^ i - 1.
Proof.
  induction n0.
  1: lia.
  intros n i Hn.
  assert (n < n0 \/ n = n0) as E by lia.
  destruct E as [E|E].
  1: apply IHn0; exact E.
  subst n. clear Hn.
  unfold ctzS.
  destruct (Pos.of_succ_nat n0) eqn:E; cbn[ctzS_pos].
  - assert (H:n0 = Pos.to_nat p * 2) by lia.
    destruct i as [|i].
    + change (2 ^ (0 + 1)) with 2.
      change (2 ^ 0 - 1) with 0.
      rewrite H, Nat.Div0.mod_mul.
      tauto.
    + cbn[Nat.add].
      cbn[Nat.pow]. rewrite H.
      rewrite Nat.mul_comm, Nat.Div0.mul_mod_distr_l.
      cbn[Nat.pow].
      lia.
  - destruct i as [|i].
    + split. 1: lia.
      change (2 ^ (0 + 1)) with 2.
      change (2 ^ 0 - 1) with 0.
      assert (H:n0 = (Pos.to_nat p - 1) * 2 + 1) by lia.
      rewrite H.
      rewrite Nat.Div0.add_mul_mod_distr_r with (b:=1); lia.
    + rewrite PeanoNat.Nat.succ_inj_wd.
      assert (H:n0 = (Pos.to_nat p - 1) * 2 + 1) by lia.
      assert (H0:n0 / 2 = Pos.to_nat p - 1).
      {
        rewrite H.
        rewrite Nat.div_add_l. 2: congruence.
        cbn. lia.
      }
      assert (H1:n0 / 2 < n0) by lia.
      specialize (IHn0 _ i H1).
      unfold ctzS in IHn0.
      rewrite H0 in IHn0.
      replace (Pos.of_succ_nat (Pos.to_nat p - 1)) with p in IHn0 by lia.
      rewrite <- H0 in IHn0, H.
      rewrite IHn0.
      remember (n0 / 2) as n1.
      rewrite H.
      cbn[Nat.add].
      cbn[Nat.pow].
      rewrite Nat.mul_comm.
      rewrite Nat.Div0.add_mul_mod_distr_l. 2: lia.
      lia.
  - assert (n0 = 0) by lia.
    subst n0.
    rewrite Nat.Div0.mod_0_l.
    destruct i as [|i].
    + cbn. tauto.
    + cbn[Nat.pow].
      lia.
Qed.

Lemma ctzS_spec n i:
  ctzS n = i <-> n mod 2 ^ (i + 1) = 2 ^ i - 1.
Proof.
  apply ctzS_spec_0 with (n0:=S n).
  lia.
Qed.

Lemma ctzS_pow_le n:
  match ctzS n with
  | 0 => True
  | S i => 2 ^ i <= n
  end.
Proof.
  remember (ctzS n) as r eqn:Hr.
  symmetry in Hr.
  destruct r as [|i]; [trivial|].
  apply ctzS_spec in Hr.
  pose proof (Nat.Div0.mod_le n (2 ^ (S i + 1))) as Hmod.
  rewrite Hr in Hmod.
  cbn[Nat.pow] in Hmod.
  lia.
Qed.

Lemma ctzS_lt_pow n l:
  n < 2 ^ l - 1 ->
  ctzS n < l.
Proof.
  intro Hn.
  remember (ctzS n) as r eqn:Hr.
  symmetry in Hr.
  apply ctzS_spec in Hr.
  pose proof (Nat.Div0.mod_le n (2 ^ (r + 1))) as Hmod.
  rewrite Hr in Hmod.
  assert (2 ^ r < 2 ^ l) by lia.
  apply (proj2 (PeanoNat.Nat.pow_lt_mono_r_iff 2 r l ltac:(lia))).
  exact H.
Qed.

Opaque ctzS.

Fixpoint ladd(a b:list nat){struct a}:list nat := 
match a with
| [] => b
| a0::a1 =>
  match b with
  | [] => a
  | b0::b1 => (a0+b0)::ladd a1 b1
  end
end.

Fixpoint tp(ls:list nat) :=
match ls with
| [] => tp0
| a::ls0 =>
  xorb (tp ls0) (Nat.odd a)
end.

Fixpoint gray(ls:list nat) :=
match ls with
| [] => 0
| a::ls0 => (if tp ls then 1 else 0)+(gray ls0)*2
end.

Lemma tp_all0 n:
  tp ([0]^^n) = tp0.
Proof.
  induction n; cbn; trivial.
  rewrite IHn; trivial.
Qed.

Lemma gray_all0 n:
  gray ([0]^^n) = 0.
Proof.
  induction n; cbn; trivial.
  rewrite tp_all0.
  rewrite IHn; trivial.
Qed.

Lemma length_all0 n:
  length ([0]^^n) = n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma ladd_nil_r a:
  ladd a [] = a.
Proof.
  destruct a; trivial.
Qed.

Ltac ec := econstructor.

Lemma odd_0 a:
  Nat.odd (a*2) = tp0.
Proof.
  applys_eq (Nat.odd_even a); flia.
Qed.

Lemma odd_1 a:
  Nat.odd (S (a*2)) = tp1.
Proof.
  rewrite Nat.odd_succ,Nat.mul_comm.
  apply Nat.even_even.
Qed.

Lemma mul2add1 a:
  a*2+1 = 1+a*2.
Proof.
  lia.
Qed.

Hint Rewrite
  tp_all0 gray_all0 length_all0
  ctzS_0' ctzS_0 ctzS_1
  ladd_nil_r
  Nat.add_0_l Nat.add_0_r mul2add1 Nat.sub_0_r
  odd_0 odd_1 Nat.odd_succ_succ: rw_v1.

Ltac rw_v1 :=
  repeat (
  autorewrite with rw_v1 in * ||
  cbn[tp gray xorb negb] in * ||
  trivial).

Lemma Inc_12 n ls ls':
  LInc (negb (Nat.odd n)) ls ls' ->
  S1 ls (1+n) -->*
  S1 ls' n.
Proof.
  destruct (mod2 n); subst; intros; rw_v1.
  - apply Inc_1,H.
  - apply Inc_2,H.
Qed.

Lemma Inc_0 n ls ls':
  LInc (Nat.odd n) ls ls' ->
  S1 (n::ls) 0 -->*
  S1 ls' n.
Proof.
  destruct (mod2 n); subst; intros; rw_v1.
  - apply Inc_00,H.
  - apply Inc_01,H.
Qed.

Lemma tp_S ls:
  tp (ladd ls ([0] ^^ ctzS (gray ls) ++ [1])) = 
  negb (tp ls).
Proof with rw_v1.
  induction ls.
  - cbn...
  - cbn.
    destruct (mod2 a); subst a;
    destruct (tp ls) eqn:E0...
    * cbn...
      rewrite IHls...
    * cbn...
      rewrite E0...
    * cbn...
      rewrite E0...
    * cbn...
      rewrite IHls...
Qed.

Lemma mul2sub1 a:
  a<>0 ->
  a*2-1 = 1+(a-1)*2.
Proof.
  lia.
Qed.

Lemma tp_pred ls:
  gray ls <> 0 ->
  tp (ladd ls ([0] ^^ ctzS (gray ls-1) ++ [1])) = 
  negb (tp ls).
Proof with rw_v1.
  induction ls; intros.
  - cbn...
  - cbn.
    destruct (mod2 a); subst a;
    destruct (tp ls) eqn:E0...
    * cbn...
      cbn...
      rewrite E0...
    * rewrite E0 in H...
      rewrite mul2sub1 by lia...
      cbn...
      rewrite IHls by lia...
    * rewrite E0 in H...
      rewrite mul2sub1 by lia...
      cbn...
      rewrite IHls by lia...
    * cbn...
      cbn...
      rewrite E0...
Qed.

Lemma gray_S ls:
  gray (ladd ls ([0] ^^ ctzS (gray ls) ++ [1])) = 
  1 + gray ls.
Proof with rw_v1.
  induction ls...
  destruct (mod2 a); subst a;
  destruct (tp ls) eqn:E0...
  * cbn; rewrite IHls,tp_S,E0...
  * cbn...
    rewrite E0...
  * cbn...
    rewrite E0...
  * cbn; rewrite IHls,tp_S,E0...
Qed.

Lemma gray_pred ls:
  gray ls <> 0 ->
  gray (ladd ls ([0] ^^ ctzS (gray ls - 1) ++ [1])) = 
  gray ls - 1.
Proof with rw_v1.
  induction ls; intros...
  1: lia.
  destruct (mod2 a); subst a;
  destruct (tp ls) eqn:E0...
  * cbn...
    cbn...
    rewrite E0...
  * cbn...
    rewrite mul2sub1 by lia...
    cbn...
    rewrite IHls,tp_pred,E0 by lia...
  * cbn...
    rewrite mul2sub1 by lia...
    cbn...
    rewrite IHls,tp_pred,E0 by lia...
  * cbn...
    cbn...
    rewrite E0...
Qed.

Inductive Inc: (list nat)->(list nat)->Prop :=
| Inc_intro ls ls'
    (Inc_a:ls' = ladd ls ([0]^^(ctzS (gray ls))++[1]))
    (Inc_b:LInc (negb (tp ls)) ls ls')
    (Inc_c:gray ls' = 1+gray ls)
    (Inc_d:tp ls' = negb (tp ls))
    (Inc_e:WF ls')
    (Inc_f:length ls' = length ls):
    Inc ls ls'.

Lemma Inc_spec ls:
  WF ls ->
  1+(gray ls)<2^(length ls) ->
  exists ls',
  Inc ls ls'.
Proof with rw_v1.
  induction ls; intros; cbn[length Nat.pow gray tp] in *.
  1: lia.
  inverts H.
  - destruct n; inverts H2...
    ec; ec.
    1: reflexivity.
    all: rw_v1.
    all: cbn; rw_v1; cbn.
    + ec.
    + ec.
      1: lia.
      ec.
  - specialize (IHls H4).
    destruct (sub a 1); [subst a|lia].
    destruct (mod2 c); subst c;
    destruct (tp ls) eqn:E0...
    + ec; ec.
      1: reflexivity.
      all: rw_v1.
      all: rewrite E0...
      all: cbn...
      * ec.
      * rewrite E0...
      * rewrite E0...
      * ec; eauto 1.
    + unshelve epose proof (IHls _) as [ls' I1].
      1: lia.
      inverts I1.
      rewrite E0 in *.
      ec; ec.
      1: reflexivity.
      all: rw_v1.
      all: rewrite E0...
      all: cbn...
      * ec; eauto 1.
      * rewrite tp_S,gray_S,E0...
      * rewrite tp_S,E0...
      * ec; eauto 1.
      * lia.
    + unshelve epose proof (IHls _) as [ls' I1].
      1: lia.
      inverts I1.
      rewrite E0 in *.
      ec; ec.
      1: reflexivity.
      all: rw_v1.
      all: rewrite E0...
      all: cbn...
      * ec; eauto 1.
      * rewrite tp_S,gray_S,E0...
      * rewrite tp_S,E0...
      * ec; eauto 1.
      * lia.
    + ec; ec.
      1: reflexivity.
      all: rw_v1.
      all: rewrite E0...
      all: cbn...
      * ec.
      * rewrite E0...
      * rewrite E0...
      * ec; eauto 1.
Qed.

Inductive Dec: (list nat)->(list nat)->Prop :=
| Dec_intro ls ls'
    (Dec_a:ls' = ladd ls ([0]^^(ctzS (gray ls-1))++[1]))
    (Dec_b:LInc (tp ls) ls ls')
    (Dec_c:gray ls' = gray ls-1)
    (Dec_d:tp ls' = negb (tp ls))
    (Dec_e:WF ls')
    (Dec_f:length ls' = length ls)
    (Dec_g:WF' ls -> WF' ls'):
    Dec ls ls'.

Lemma Dec_spec ls:
  WF ls ->
  gray ls <> 0 ->
  exists ls',
  Dec ls ls'.
Proof with rw_v1.
  induction ls; intros; cbn[length Nat.pow gray tp] in *.
  1: lia.
  inverts H.
  - destruct n; inverts H2...
    cbn in H0.
    lia.
  - specialize (IHls H4).
    destruct (sub a 1); [subst a|lia].
    destruct (mod2 c); subst c;
    destruct (tp ls) eqn:E0...
    + unshelve epose proof (IHls _) as [ls' I1].
      1: lia.
      inverts I1.
      rewrite E0 in *.
      ec; ec.
      1: reflexivity.
      all: rw_v1.
      all: rewrite E0...
      all: rewrite mul2sub1 by lia...
      all: cbn...
      * ec; eauto 1.
      * rewrite tp_pred,gray_pred,E0 by lia...
      * rewrite tp_pred,E0 by lia...
      * ec; eauto 1.
      * lia.
      * intro H.
        inverts H...
        1: lia.
        ec; eauto 2.
    + ec; ec.
      1: reflexivity.
      all: rw_v1.
      all: rewrite E0...
      all: cbn...
      all: cbn...
      * ec.
      * rewrite E0...
      * rewrite E0...
      * ec; eauto 1.
      * intro H.
        inverts H...
        -- ec.
        -- ec; eauto 1.
    + ec; ec.
      1: reflexivity.
      all: rw_v1.
      all: rewrite E0...
      all: cbn...
      all: cbn...
      * ec.
      * rewrite E0...
      * rewrite E0...
      * ec; eauto 1.
      * intro H.
        inverts H...
        -- ec.
        -- ec; eauto 1.
    + unshelve epose proof (IHls _) as [ls' I1].
      1: lia.
      inverts I1.
      rewrite E0 in *.
      ec; ec.
      1: reflexivity.
      all: rw_v1.
      all: rewrite E0...
      all: rewrite mul2sub1 by lia...
      all: cbn...
      * ec; eauto 1.
      * rewrite tp_pred,gray_pred,E0 by lia...
      * rewrite tp_pred,E0 by lia...
      * ec; eauto 1.
      * lia.
      * intro H.
        inverts H...
        1: lia.
        ec; eauto 2.
Qed.

Inductive Zero: (list nat)->(list nat)->Prop :=
| Zero_intro ls ls'
    (Zero_a:ls' = ladd ls ([0]^^(length ls-1)++[1;0;0]))
    (Zero_b:LInc (tp ls) ls ls')
    (Zero_c:gray ls' = 2^(length ls) - 1)
    (Zero_d:tp ls' = negb (tp ls))
    (Zero_e:WF ls')
    (Zero_f:length ls' = 2+length ls):
    Zero ls ls'.

Lemma tp_O ls:
  gray ls = 0 ->
  tp ls = tp0.
Proof with rw_v1.
  induction ls; intros...
  rewrite IHls in * by lia...
  destruct (Nat.odd a)...
  lia.
Qed.

Lemma WF'_length ls:
  WF' ls ->
  length ls <> 0.
Proof.
  intro H.
  induction H; cbn; lia.
Qed.

Lemma Zero_spec ls:
  WF' ls ->
  gray ls = 0 ->
  exists ls',
  Zero ls ls'.
Proof with rw_v1.
  intros H H0.
  epose proof (tp_O _ H0).
  epose proof (WF'_length _ H).
  gen H H0 H1 H2.
  induction ls; intros; cbn[length Nat.pow gray tp] in *.
  1: lia.
  rewrite H1 in H0.
  assert (I2:gray ls = 0) by lia.
  epose proof (tp_O _ I2) as I3.
  rewrite I3 in *.
  destruct (mod2 a); subst a...
  2: congruence.
  inverts H.
  - ec; ec.
    1: reflexivity.
    all: cbn...
    * ec.
    * ec; [lia|eapply (WF_O 2)].
  - assert (length ls<>0) as I4. { apply WF'_length; auto 1. }
    unshelve epose proof (IHls _ _ _) as [ls' I1]; eauto 1.
    inverts I1.
    destruct a0; [lia|].
    rewrite I3 in *.
    ec; ec.
    1: reflexivity.
    all: rw_v1.
    * rewrite I3...
      cbn[length Nat.sub]...
      replace (length ls) with (S(length ls-1)) by lia...
      cbn...
      ec; eauto 1.
    * cbn...
      replace (length ls) with (S(length ls-1)) by lia...
      cbn...
      rewrite Zero_c,Zero_d...
      remember (length ls-1) as v1.
      replace (length ls) with (S v1) by lia.
      cbn; lia.
    * cbn...
      replace (length ls) with (S(length ls-1)) by lia...
      cbn...
      rewrite Zero_d,I3...
    * cbn...
      replace (length ls) with (S(length ls-1)) by lia...
      cbn...
      ec; eauto 1.
    * cbn...
      replace (length ls) with (S(length ls-1)) by lia...
      cbn...
      lia.
Qed.

Inductive WF'': (list nat)->Prop :=
| WF''_O: WF'' []
| WF''_S a ls:
    a<>0 ->
    WF'' ls ->
    WF'' (a::ls).

Inductive Ov: (list nat)->Prop :=
| Ov_intro ls
    (Ov_b:LInc tp0 (ls++[0;0]) (ls++[1;0;0;0]))
    (Ov_c:gray (ls++[1;0;0;0]) = 2^(length ls)*2 - 1)
    (Ov_d:tp (ls++[1;0;0;0]) = tp1)
    (Ov_e:WF (ls++[1;0;0;0])):
    Ov ls.

Lemma Ov_spec ls:
  WF'' ls ->
  gray (ls++[0;0]) = 0 ->
  Ov ls.
Proof with rw_v1.
  intros H H0.
  epose proof (tp_O _ H0).
  gen H H0 H1.
  induction ls; intros; cbn in *.
  - eapply (Ov_intro []); cbn...
    + ec.
    + ec; eauto 1; eapply (WF_O 3).
  - destruct (tp (ls++[0;0])) eqn:E0,(Nat.odd a) eqn:E1...
    all: try congruence.
    + unshelve epose proof (tp_O (ls++[0;0]) _).
      1: lia.
      congruence.
    + inverts H.
      eapply IHls in H5.
      2: lia.
      2: trivial.
      destruct (sub a 1); [subst|lia].
      destruct (mod2 c); subst...
      1: congruence.
      inverts H5.
      ec...
      * cbn; ec; eauto 1.
      * cbn...
        rewrite Bool.xorb_comm...
        rewrite Ov_d.
        lia.
      * cbn...
        rewrite Bool.xorb_comm...
      * ec; eauto 1.
Qed.


Lemma ladd_comm a b:
  ladd a b = ladd b a.
Proof.
  gen b.
  induction a; intros.
  - rw_v1.
  - destruct b; cbn.
    + trivial.
    + rewrite IHa; flia.
Qed.

Lemma ladd_assoc a b c:
  ladd a (ladd b c) = ladd (ladd a b) c.
Proof.
  gen b c.
  induction a; intros.
  - trivial.
  - destruct b,c; cbn; trivial.
    rewrite IHa; flia.
Qed.

Fixpoint lsum a b :=
match b with
| O => []
| S b => ladd ([0]^^(ctzS a)++[1]) (lsum (S a) b)
end.

Lemma lsum_S' a b:
  lsum a (S b) = ladd ([0]^^(ctzS (a+b))++[1]) (lsum a b).
Proof.
  gen a.
  induction b; intros; cbn in *.
  - rw_v1.
  - rewrite IHb.
    do 2 rewrite ladd_assoc.
    f_equal.
    rewrite ladd_comm.
    flia.
Qed.

Lemma WF_WF' ls:
  WF ls ->
  2<=length ls ->
  2^(length ls-2) <= gray ls ->
  WF' ls.
Proof with rw_v1.
  induction ls; intros; cbn[length Nat.pow gray tp] in *.
  1: lia.
  inverts H.
  - destruct n; inverts H3...
    cbn in H1.
    lia.
  - destruct (length ls) eqn:E0.
    + destruct ls.
      2: inverts E0.
      ec.
    + destruct n.
      * destruct ls as [|a0 [|]]; inverts E0.
        ec; eauto 1; ec.
      * ec; eauto 1.
        eapply IHls; eauto 1.
        1: lia.
        cbn in *...
        destruct (xorb (tp ls) (Nat.odd a)); lia.
Qed.

Lemma odd_S n:
  Nat.odd (S n) = negb (Nat.odd n).
Proof.
  rewrite Nat.odd_succ.
  unfold Nat.odd.
  destruct (Nat.even n); trivial.
Qed.


Inductive Incs: nat->nat->(list nat)->(list nat)->Prop :=
| Incs_intro n n0 ls ls'
    (Incs_a:ls' = ladd ls (lsum (gray ls) n))
    (Incs_b:S1 ls (n+n0) -->* S1 ls' n0)
    (Incs_c:gray ls' = n+gray ls)
    (Incs_d:tp ls' = xorb (tp ls) (Nat.odd n))
    (Incs_e:WF ls')
    (Incs_f:length ls' = length ls):
    Incs n n0 ls ls'.

Lemma Incs_spec ls n n0:
  WF ls ->
  n + gray ls < 2^(length ls) ->
  Nat.odd (n+n0) = negb (tp ls) ->
  exists ls',
  Incs n n0 ls ls'.
Proof with rw_v1.
  gen ls n0.
  induction n; intros.
  - ec; ec.
    1: reflexivity.
    all: cbn...
    + rewrite Bool.xorb_comm...
  - eapply Inc_spec in H.
    2: lia.
    destruct H as [ls' I1].
    inverts I1.
    eapply IHn with (n0:=n0) in Inc_e.
    + destruct Inc_e as [ls' I1].
      inverts I1.
      remember ([0]^^ctzS (gray ls) ++ [1]) as v1.
      ec; ec.
      1: reflexivity.
      all: rewrite Inc_c in *.
      all: rewrite Inc_d in *.
      all:
        cbn[lsum Nat.add] in *;
        rewrite <-Heqv1;
        rewrite ladd_assoc.
      * eapply evstep_trans.
        2: eassumption.
        apply Inc_12.
        applys_eq Inc_b.
        rewrite odd_S in H1.
        apply H1.
      * rewrite Incs_c.
        lia.
      * rewrite Incs_d.
        rewrite Nat.odd_succ.
        unfold Nat.odd.
        apply Bool.xorb_negb_negb.
      * eauto 1.
      * lia.
    + rewrite Inc_f.
      lia.
    + rewrite Inc_d.
      cbn[Nat.add] in H1.
      rewrite Nat.odd_succ in H1.
      rewrite <-H1.
      trivial.
Qed.


Inductive Decs: nat->nat->(list nat)->(list nat)->Prop :=
| Decs_intro n n0 ls ls'
    (Decs_a:ls' = ladd ls (lsum (gray ls - n) n))
    (Decs_b:S1 ls (n+n0) -->* S1 ls' n0)
    (Decs_c:gray ls' = gray ls-n)
    (Decs_d:tp ls' = xorb (tp ls) (Nat.odd n))
    (Decs_e:WF ls')
    (Decs_f:length ls' = length ls)
    (Decs_g:WF' ls -> WF' ls'):
    Decs n n0 ls ls'.


Lemma Decs_spec ls n n0:
  WF ls ->
  n <= gray ls ->
  Nat.odd (n+n0) = (tp ls) ->
  exists ls',
  Decs n n0 ls ls'.
Proof with rw_v1.
  gen ls n0.
  induction n; intros.
  - ec; ec.
    1: reflexivity.
    all: cbn...
    + rewrite Bool.xorb_comm...
  - eapply Dec_spec in H.
    2: lia.
    destruct H as [ls' I1].
    inverts I1.
    eapply IHn with (n0:=n0) in Dec_e.
    + destruct Dec_e as [ls' I1].
      inverts I1.
      remember ([0]^^ctzS (gray ls-1) ++ [1]) as v1.
      ec; ec.
      1: reflexivity.
      all: rewrite Dec_c in *.
      all: rewrite Dec_d in *.
      all: replace (gray ls - 1 - n) with (gray ls - S n) in * by lia.
      all: rewrite lsum_S';
        replace (gray ls-S n+n) with (gray ls-1) by lia;
        rewrite <-Heqv1;
        rewrite ladd_assoc.
      * eapply evstep_trans.
        2: eassumption.
        cbn[Nat.add] in *.
        apply Inc_12.
        rewrite odd_S in H1.
        rewrite H1; eauto 1.
      * rewrite Decs_c.
        lia.
      * rewrite Decs_d.
        rewrite Nat.odd_succ.
        unfold Nat.odd.
        apply Bool.xorb_negb_negb.
      * eauto 1.
      * lia.
      * tauto.
    + lia.
    + rewrite Dec_d.
      cbn[Nat.add] in H1.
      rewrite Nat.odd_succ in H1.
      rewrite <-H1.
      trivial.
Qed.

Lemma WF'_WF ls:
  WF' ls ->
  WF ls.
Proof.
  intro H.
  induction H; intros.
  - destruct a.
    + eapply (WF_O 1).
    + ec; eauto 1; eapply (WF_O 0).
  - ec; eauto 1.
Qed.

Lemma WF_tl ls:
  WF ls ->
  WF (tl ls).
Proof.
  destruct ls; cbn.
  1: tauto.
  intro H.
  inverts H.
  - destruct n0; inverts H1.
    ec.
  - eauto 1.
Qed.

Inductive HDZD: (list nat)->(list nat)->Prop :=
| HDZD_intro a ls ls'
    (HDZD_a: ls' =
    (ladd
       (ladd
          (ladd (ladd ls ([0] ^^ ctzS (gray ls) ++ [1]))
             (lsum 0 (1 + gray ls)))
          ([0] ^^ (length ls - 1) ++ [1; 0; 0]))
       (lsum (2 ^ length ls - 1 - a) a)))
    (HDZD_b: S1 ((1+gray ls)+(1+a)::ls) 0 -->* S1 ls' 0)
    (HDZD_c:gray ls' = 2^(length ls) - 1 - a)
    (HDZD_c':a <= 2^(length ls) - 1)
    (HDZD_d:tp ls' = tp0)
    (HDZD_e:WF ls')
    (HDZD_f:length ls'=2+length ls):
    HDZD ((1+gray ls)+(1+a)::ls) ls'.

Lemma HDZD_spec a ls:
  WF ls ->
  2<=length ls ->
  2^(length ls - 2) <= 1+gray ls < 2^(length ls) ->
  a < 2^(length ls) ->
  tp ((1+gray ls)+(1+a)::ls) = tp1 ->
  exists ls',
  HDZD ((1+gray ls)+(1+a)::ls) ls'.
Proof.
  intros HWF Hlen Hlt Ha Htp.
  eapply Inc_spec in HWF.
  2: lia.
  destruct HWF as [ls' I1].
  inverts I1.
  rw_v1.
  eassert (I2:_). {
    eapply (Inc_0 ((1+gray ls)+(1+a))).
    applys_eq Inc_b.
    destruct (Nat.odd ((1+gray ls)+(1+a))),(tp ls); rw_v1; congruence.
  }
  epose proof Inc_e as I1.
  eapply Decs_spec with (n:=1+gray ls) (n0:=1+a) in I1.
  2: lia.
  2:{
    rewrite Inc_d in *.
    destruct (Nat.odd ((1+gray ls)+(1+a))),(tp ls); rw_v1; congruence.
  }
  destruct I1 as [ls' I1].
  inverts I1.
  rewrite Inc_c in *.
  rewrite Inc_d in *.
  rewrite Inc_f in *.
  eassert (I3:_). {
    eapply Decs_g.
    eapply WF_WF'; eauto 1.
    - lia.
    - rewrite Inc_f.
      lia.
  }
  clear Decs_g.
  eapply Zero_spec in I3.
  2: lia.
  destruct I3 as [ls'0 I1].
  inverts I1.
  rewrite Decs_d in *.
  rewrite Decs_f in *.
  rewrite Nat.odd_add in Htp.
  repeat rewrite odd_S in *.
  eassert (I4:_). {
    eapply (Inc_12 a).
    applys_eq (Zero_b).
    destruct (Nat.odd a),(tp ls),(Nat.odd (gray ls)); rw_v1; congruence.
  }
  rewrite Nat.sub_diag in *.
  eapply Decs_spec with (n:=a) (n0:=0) in Zero_e.
  all: try rewrite Zero_c in *.
  all: try rewrite Zero_d in *.
  2: lia.
  2:{
    rewrite Nat.add_0_r.
    destruct (Nat.odd a),(tp ls),(Nat.odd (gray ls)); rw_v1; congruence.
  }
  destruct Zero_e as [ls'1 I1].
  inverts I1.
  rewrite Zero_c in *.
  rewrite Zero_d in *.
  rewrite Zero_f in *.
  ec; ec.
  1: reflexivity.
  - follow I2.
    follow Decs_b.
    follow I4.
    follow Decs_b0.
    finish.
  - lia.
  - lia.
  - rewrite Decs_d0.
    destruct (Nat.odd a),(tp ls),(Nat.odd (gray ls)); rw_v1; congruence.
  - eauto 1.
  - eauto 1.
Qed.

Lemma HDZD_spec' ls:
  WF ls ->
  2<=length (tl ls) ->
  2^(length (tl ls) - 2) <= 1+gray (tl ls) < 2^(length (tl ls)) ->
  gray (tl ls) + 2 <= hd 0 ls < 2^(length (tl ls)) + gray (tl ls) + 2 ->
  tp ls = tp1 ->
  exists ls',
  HDZD ls ls'.
Proof.
  intros.
  destruct ls as [|a ls].
  1: cbn in *; lia.
  apply WF_tl in H.
  cbn in *.
  replace a with (1+gray ls+(1+(a-2-gray ls))) by lia.
  eapply HDZD_spec; eauto 1.
  - lia.
  - cbn.
    applys_eq H3; flia.
Qed.

Inductive HI: (list nat)->(list nat)->Prop :=
| HI_intro a ls ls'
    (HI_a:ls' = (ladd (ladd ls ([0] ^^ ctzS (gray ls - 1) ++ [1])) (lsum (gray ls - 1) a)))
    (HI_b:S1 (a::ls) 0 -->* S1 ls' 0)
    (HI_c:gray ls' = a + (gray ls - 1))
    (HI_d:tp ls' = tp1)
    (HI_e:WF ls')
    (HI_f:length ls' = length ls):
    HI (a::ls) ls'.

Lemma HI_spec a ls:
  WF ls ->
  gray ls <> 0 ->
  a + (gray ls - 1) < 2 ^ length ls ->
  tp (a::ls) = tp0 ->
  exists ls',
  HI (a::ls) ls'.
Proof.
  intros HWF Hnz Hlt Htp.
  eapply Dec_spec in HWF.
  2: lia.
  destruct HWF as [ls' I1].
  inverts I1.
  rw_v1.
  eassert (I2:_). {
    eapply (Inc_0 a).
    applys_eq Dec_b.
    destruct (tp ls),(Nat.odd a); rw_v1; congruence.
  }
  eapply Incs_spec with (n:=a) (n0:=0) in Dec_e.
  all: try rewrite Dec_c.
  all: try rewrite Dec_d.
  all: try rewrite Dec_f.
  2: lia.
  2:{
    rw_v1.
    destruct (tp ls),(Nat.odd a); rw_v1; congruence.
  }
  destruct (Dec_e) as [ls'0 I1].
  inverts I1.
  rewrite Dec_c in *.
  rewrite Dec_d in *.
  rewrite Dec_f in *.
  ec; ec.
  1: reflexivity.
  - follow I2.
    follow Incs_b.
    finish.
  - lia.
  - rewrite Incs_d.
    destruct (tp ls),(Nat.odd a); rw_v1; congruence.
  - eauto 1.
  - cbn; lia.
Qed.

Lemma HI_spec' ls:
  WF ls ->
  gray (tl ls) <> 0 ->
  hd 0 ls + (gray (tl ls) - 1) < 2 ^ length (tl ls) ->
  tp ls = tp0 ->
  exists ls',
  HI ls ls'.
Proof.
  intros.
  destruct ls as [|a ls].
  1: cbn in *; lia.
  apply WF_tl in H.
  cbn in *.
  eapply HI_spec; eauto 1.
Qed.

Inductive HD: (list nat)->(list nat)->Prop :=
| HD_intro a ls ls'
    (HD_a:ls' = ladd (ladd ls ([0] ^^ ctzS (gray ls) ++ [1])) (lsum (1 + gray ls - a) a))
    (HD_b:S1 (a::ls) 0 -->* S1 ls' 0)
    (HD_c:gray ls' = 1 + gray ls - a)
    (HD_d:tp ls' = tp0)
    (HD_e:WF ls')
    (HD_f:length ls' = length ls):
    HD (a::ls) ls'.

Lemma HD_spec a ls:
  WF ls ->
  a <= 1 + gray ls < 2^(length ls) ->
  tp (a::ls) = tp1 ->
  exists ls',
  HD (a::ls) ls'.
Proof.
  intros HWF Hlt Htp.
  eapply Inc_spec in HWF.
  2: lia.
  destruct HWF as [ls' I1].
  inverts I1.
  rw_v1.
  eassert (I2:_). {
    eapply (Inc_0 a).
    applys_eq Inc_b.
    destruct (tp ls),(Nat.odd a); rw_v1; congruence.
  }
  eapply Decs_spec with (n:=a) (n0:=0) in Inc_e.
  all: try rewrite Inc_c.
  all: try rewrite Inc_d.
  all: try rewrite Inc_f.
  2: lia.
  2:{
    rw_v1.
    destruct (tp ls),(Nat.odd a); rw_v1; congruence.
  }
  destruct (Inc_e) as [ls'0 I1].
  inverts I1.
  rewrite Inc_c in *.
  rewrite Inc_d in *.
  rewrite Inc_f in *.
  ec; ec.
  1: reflexivity.
  - follow I2.
    follow Decs_b.
    finish.
  - lia.
  - rewrite Decs_d.
    destruct (tp ls),(Nat.odd a); rw_v1; congruence.
  - eauto 1.
  - eauto 1.
Qed.

Inductive HZI: (list nat)->(list nat)->Prop :=
| HZI_intro a ls ls'
    (HZI_a: ls' =
    ladd (ladd ls ([0] ^^ (Datatypes.length ls - 1) ++ [1; 0; 0]))
       (lsum (2 ^ Datatypes.length ls - 1) (a * 2)))
    (HZI_b: S1 (a*2::ls) 0 -->* S1 ls' 0)
    (HZI_c:gray ls' = a*2 + 2^(length ls) - 1)
    (HZI_d:tp ls' = tp1)
    (HZI_e:WF ls')
    (HZI_f:length ls'=2+length ls):
    HZI (a*2::ls) ls'.

Lemma HZI_spec a ls:
  WF' ls ->
  gray ls = 0 ->
  a * 2 <= 2 ^ (Datatypes.length ls) * 3 ->
  exists ls',
  HZI (a*2::ls) ls'.
Proof.
  intros HWF Hgr Hlt.
  eapply Zero_spec in HWF.
  2: lia.
  pose proof (tp_O _ Hgr) as Htp.
  destruct HWF as [ls' I1].
  inverts I1.
  eassert (I4:_). {
    eapply (Inc_0 (a*2)).
    applys_eq (Zero_b).
    rw_v1.
    congruence.
  }
  eapply Incs_spec with (n:=a*2) (n0:=0) in Zero_e.
  all: try rewrite Zero_c in *.
  all: try rewrite Zero_d in *.
  all: try rewrite Zero_f in *.
  2: cbn; lia.
  2: rewrite Htp; rw_v1.
  destruct Zero_e as [ls'1 I1].
  inverts I1.
  rewrite Zero_c in *.
  rewrite Zero_d in *.
  rewrite Zero_f in *.
  ec; ec.
  1: reflexivity.
  - follow I4.
    follow Incs_b.
    finish.
  - lia.
  - rewrite Incs_d.
    rewrite Htp; rw_v1.
  - eauto 1.
  - eauto 1.
Qed.

Inductive HOI: (list nat)->(list nat)->Prop :=
| HOI_intro a ls ls'
    (HOI_a: ls' = (ladd (ls ++ [1; 0; 0; 0])
       (lsum (2 ^ Datatypes.length ls * 2 - 1) (a * 2))))
    (HOI_b: S1 (a*2::ls++[0;0]) 0 -->* S1 ls' 0)
    (HOI_c:gray ls' = a*2 + 2^(length ls)*2 - 1)
    (HOI_d:tp ls' = tp1)
    (HOI_e:WF ls')
    (HOI_f:length ls'=4+length ls):
    HOI (a*2::ls++[0;0]) ls'.

Lemma HOI_spec a ls:
  WF'' ls ->
  gray (ls++[0;0]) = 0 ->
  a*2 <= 2^(length ls)*14 ->
  exists ls',
  HOI (a*2::ls++[0;0]) ls'.
Proof.
  intros HWF Hgr Hlt.
  eapply Ov_spec in HWF.
  2: lia.
  pose proof (tp_O _ Hgr) as Htp.
  inverts HWF.
  eassert (I4:_). {
    eapply (Inc_0 (a*2)).
    applys_eq (Ov_b).
    rw_v1.
  }
  eapply Incs_spec with (n:=a*2) (n0:=0) in Ov_e.
  all: try rewrite Ov_c in *.
  all: try rewrite Ov_d in *.
  2: rewrite length_app,Nat.pow_add_r; cbn; try lia.
  2: rw_v1.
  destruct Ov_e as [ls'1 I1].
  inverts I1.
  rewrite Ov_c in *.
  rewrite Ov_d in *.
  ec; ec.
  1: reflexivity.
  - follow I4.
    follow Incs_b.
    finish.
  - lia.
  - rewrite Incs_d.
    rw_v1.
  - eauto 1.
  - rewrite Incs_f.
    rewrite length_app; cbn; lia.
Qed.

Notation len := length.
Notation "a '+l' b" := (ladd a b) (at level 50, left associativity).

Fixpoint L1 n :=
match n with
| O => [1]
| S n => 0 :: L1 n
end.

Lemma L1_fold n:
  [0]^^n++[1] = L1 n.
Proof.
  induction n; cbn; congruence.
Qed.

Lemma tp_L1_2 ls i:
  tp (ls +l (L1 i +l L1 i)) = tp ls.
Proof with rw_v1.
  gen ls.
  induction i; cbn; intros...
  - destruct ls...
    cbn...
    rewrite (Nat.add_comm _ 2)...
  - destruct ls; cbn.
    + epose proof (IHi []) as I1.
      cbn in I1.
      rewrite I1...
    + rewrite IHi...
Qed.

Lemma gray_L1_2 ls i:
  gray (ls +l (L1 i +l L1 i)) =
  gray ls.
Proof with rw_v1.
  gen ls.
  induction i; cbn; intros...
  - destruct ls; cbn...
    rewrite (Nat.add_comm _ 2)...
  - destruct ls; cbn.
    + epose proof (tp_L1_2 []) as I1.
      epose proof (IHi []) as I2.
      cbn in *.
      rewrite I1,I2...
    + rewrite tp_L1_2...
      rewrite IHi...
Qed.

Ltac rws H :=
  progress (repeat rewrite H in *).

Lemma ladd_swap a b c:
  a +l b +l c = a +l c +l b.
Proof.
  do 2 rewrite <-ladd_assoc.
  rewrite (ladd_comm b).
  trivial.
Qed.

Lemma lsum_add a b c:
  lsum a (b+c) = lsum a b +l lsum (a+b) c.
Proof.
  gen a.
  induction b; intros.
  - cbn.
    flia.
  - cbn.
    rewrite IHb,ladd_assoc.
    flia.
Qed.

Ltac ladd_swaps a :=
  repeat rewrite (ladd_swap _ (a) _).

Lemma gray_pred2 a ls:
  2 <= gray (a::ls) ->
  (a :: ls) +l lsum (gray (a :: ls) - 2) 2 =
  1+a :: (ls +l lsum (gray ls - 1) 1).
Proof with rw_v1.
  intros...
  destruct (xorb (tp ls) (Nat.odd a)).
  - cbn[lsum].
    replace (S(1+gray ls*2-2)) with ((gray ls)*2) by lia.
    replace (1+gray ls*2-2) with (1+(gray ls-1)*2) by lia...
    cbn...
    flia.
  - cbn[lsum].
    replace (S(0+gray ls*2-2)) with (1+(gray ls-1)*2) by lia.
    replace (0+gray ls*2-2) with ((gray ls-1)*2) by lia...
    cbn...
    flia.
Qed.

Lemma gray_succ2 a ls:
  (a :: ls) +l lsum (gray (a :: ls)) 2 =
  1+a :: (ls +l lsum (gray ls) 1).
Proof with rw_v1.
  intros...
  destruct (xorb (tp ls) (Nat.odd a)).
  - cbn[lsum]...
    replace (S(1+gray ls*2)) with ((1+gray ls)*2) by lia...
    cbn...
    flia.
  - cbn[lsum]...
    cbn...
    flia.
Qed.

Lemma gray_decs ls k:
  k <= gray ls ->
  gray (ls +l (lsum (gray ls - k) k)) =
  gray ls - k.
Proof with rw_v1.
  gen ls.
  induction k; intros.
  - cbn...
  - cbn...
    replace (S(gray ls-S k)) with (gray ls-k) by lia.
    rewrite ladd_assoc.
    rewrite ladd_swap.
    replace (gray ls-S k) with (gray ls-k-1) by lia.
    unshelve epose proof (IHk ls _) as I1.
    1: lia.
    rewrite <-I1.
    eapply eq_trans.
    2: rewrite <-gray_pred by lia.
    2: reflexivity.
    rewrite I1.
    trivial.
Qed.

Lemma gray_incs ls k:
  gray (ls +l (lsum (gray ls) k)) =
  gray ls + k.
Proof with rw_v1.
  gen ls.
  induction k; intros.
  - cbn...
  - rewrite lsum_S'.
    rewrite ladd_assoc.
    rewrite ladd_swap.
    replace (gray ls+S k) with (S(gray ls+k)) by lia.
    rewrite <-IHk.
    rewrite <-gray_S.
    trivial.
Qed.

Lemma lsum_1 a:
  lsum a 1 = L1 (ctzS a).
Proof.
  cbn.
  rw_v1.
  apply L1_fold.
Qed.

Lemma len_gray_S ls:
  gray ls + 1 < 2^(len ls) ->
  len (ls +l lsum (gray ls) 1) =
  len ls.
Proof with rw_v1.
  cbn[lsum]...
  induction ls; intros.
  1: cbn in H; lia.
  cbn in *...
  destruct (xorb (tp ls) (Nat.odd a)); rw_v1; cbn...
  f_equal.
  apply IHls; lia.
Qed.

Local Opaque lsum.

Inductive Box{T} :=
| box(x:T): Box.

Lemma gray_lt ls:
  gray ls < 2^(len ls).
Proof.
  induction ls; cbn.
  1: lia.
  destruct (xorb (tp ls) (Nat.odd a)); lia.
Qed.

Definition lmul2 ls := ls +l ls.

Lemma Case1 ls ls0 ls1 ls2 i:
  HDZD ls ls0 ->
  HI ls0 ls1 ->
  HDZD ls1 ls2 ->
  ls1 = ls +l (lmul2 (L1 (S i))) ->
  ls2 = ls0 +l (lmul2 (L1 i)).
Proof.
  unfold lmul2.
  intros.
  inverts H.
  inverts H0.
  inverts H1.
  rws L1_fold.
  rws gray_L1_2.
  replace a1 with a in * by lia.
  rws ladd_assoc.
  cbn in *.
  rewrite <-H3 in HDZD_f.
  cbn in *.
  replace (len (ls3 +l L1 i +l L1 i)) with (len ls3) in * by lia.
  ladd_swaps (L1 i).
  trivial.
Qed.

Lemma Case2 ls ls0 ls1 ls2 i:
  HI ls ls0 ->
  HDZD ls0 ls1 ->
  HI ls1 ls2 ->
  ls1 = ls +l (lmul2 (L1 (S i))) ->
  ls2 = ls0 +l (lmul2 (L1 i)).
Proof.
  unfold lmul2.
  intros.
  inverts H.
  inverts H0.
  inverts H1.
  rws gray_L1_2.

  rws ladd_assoc.
  rws H3.
  ladd_swaps (L1 i).
  flia.
Qed.

Lemma Case3 ls ls0 ls1 ls2:
  HDZD ls ls0 ->
  HI ls0 ls1 ->
  HDZD ls1 ls2 ->
  ls1 = ls +l (lmul2 (L1 0)) ->
  ls2 = ls0 +l (lsum (gray ls0 - 2) 2).
Proof.
  unfold lmul2.
  intros.
  inverts H.
  inverts H0.
  inverts H1.
  rws L1_fold.

  rws ladd_nil_r.
  replace a1 with (2+a) in * by lia.
  rewrite (lsum_add _ 2 a).
  rws ladd_assoc.
  rewrite HDZD_c.
  ladd_swaps (lsum (2 ^ len ls3 - 1 - (2 + a)) 2).
  flia.
Qed.

Lemma Case4 ls ls0 ls1 ls2:
  HI ls ls0 ->
  HDZD ls0 ls1 ->
  HI ls1 ls2 ->
  ls1 = ls +l (lmul2 (L1 0)) ->
  ls2 = ls0 +l (lsum (gray ls0) 2).
Proof.
  unfold lmul2.
  intros.
  inverts H.
  inverts H0.
  inverts H1.
  rws L1_fold.

  rws H3.
  rws ladd_nil_r.

  rewrite lsum_add.
  rws ladd_assoc.
  rewrite HI_c.
  ladd_swaps (lsum (gray ls3 - 1) a).
  flia.
Qed.

Lemma gray_tl ls:
  gray (tl ls) = gray ls / 2.
Proof with rw_v1.
  destruct ls...
  cbn[tl].
  destruct (xorb (tp ls) (Nat.odd n))...
  all: lia.
Qed.

Local Opaque gray tp ladd.

Lemma Case5 ls ls0 ls1 ls2:
  HDZD ls ls0 ->
  HI ls0 ls1 ->
  HDZD ls1 ls2 ->
  ls1 = ls +l (lsum (gray ls) 2) ->
  gray (tl ls1) < 2 ^ len (tl ls) ->
  ls2 = ls0 +l (lmul2 (lsum (gray (tl ls1)) 1)).
Proof.
  unfold lmul2.
  intros.
  replace (gray (tl ls1)) with (gray (tl ls) + 1) in *.
  2:{
    subst ls1.
    rws gray_tl.
    rws gray_incs.
    lia.
  }
  inverts H.
  inverts H0.
  inverts H1.

  rws L1_fold.
  rewrite gray_succ2 in H0.
  inverts H0.
  rws gray_incs.
  replace a1 with a in * by lia.
  repeat rewrite <-lsum_1.
  cbn[tl] in *.
  rewrite (Nat.add_comm 1 (_ + 1)).
  rewrite (lsum_add 0 (gray ls3 + 1) 1).
  rewrite len_gray_S by lia.
  rws ladd_assoc.
  ladd_swaps (lsum (gray ls3 + 1) 1).
  flia.
Qed.

Lemma Case6 ls ls0 ls1 ls2:
  HI ls ls0 ->
  HDZD ls0 ls1 ->
  HI ls1 ls2 ->
  ls1 = ls +l (lsum (gray ls - 2) 2) ->
  2 <= gray ls ->
  1 <= gray (tl ls1) ->
  ls2 = ls0 +l (lmul2 (lsum (gray (tl ls1) - 1) 1)).
Proof.
  unfold lmul2.
  intros.
  replace (gray (tl ls1)) with (gray (tl ls) - 1) in *.
  2:{
    subst ls1.
    rws gray_tl.
    rewrite gray_decs by lia.
    lia.
  }
  inverts H.
  inverts H0.
  inverts H1.

  rws L1_fold.
  rewrite gray_pred2 in H0 by lia.
  inverts H0.
  rws H5.
  cbn[tl] in *.
  rewrite gray_decs by lia.
  repeat rewrite <-lsum_1.
  replace (S a) with (1+a) by lia.
  rewrite lsum_add.
  rws ladd_assoc.
  ladd_swaps (lsum (gray ls3 - 1 - 1) 1).
  flia.
Qed.

Definition HI_ready ls :=
  WF ls /\
  tp ls = tp0 /\
  gray (tl ls) <> 0 /\
  hd 0 ls + (gray (tl ls) - 1) < 2 ^ len (tl ls).

Definition HDZD_ready ls :=
  WF ls /\
  tp ls = tp1 /\
  2 <= len (tl ls) /\
  2 ^ (len (tl ls) - 2) <= 1 + gray (tl ls) < 2 ^ len (tl ls) /\
  gray (tl ls) + 2 <= hd 0 ls <
    2 ^ len (tl ls) + gray (tl ls) + 2.

Fixpoint Add2sDelta i :=
match i with
| 0 => lmul2 (L1 0)
| 1 => lmul2 (L1 1)
| S (S j) => lmul2 (L1 (S (S j))) +l Add2sDelta j
end.

Lemma HI_run x y:
  HI x y -> S1 x 0 -->* S1 y 0.
Proof.
  intro H. inversion H. exact HI_b.
Qed.

Lemma HDZD_run x y:
  HDZD x y -> S1 x 0 -->* S1 y 0.
Proof.
  intro H. inversion H. exact HDZD_b.
Qed.


Lemma HDZD_length ls ls0:
  HDZD ls ls0 ->
  len ls0 = S (len ls).
Proof.
  intro H.
  inversion H; subst.
  cbn[len] in *.
  lia.
Qed.

Lemma HI_length ls ls0:
  HI ls ls0 ->
  S (len ls0) = len ls.
Proof.
  intro H.
  inversion H; subst.
  cbn[len] in *.
  lia.
Qed.

Lemma HDZD_HI_tl_length ls ls0 ls1:
  HDZD ls ls0 ->
  HI ls0 ls1 ->
  len (tl ls) = len (tl ls1).
Proof.
  intros Hhd Hhi.
  pose proof (HDZD_length ls ls0 Hhd) as Hlen0.
  pose proof (HI_length ls0 ls1 Hhi) as Hlen1.
  assert (Hlen: len ls = len ls1) by lia.
  destruct ls as [|a t].
  - inversion Hhd.
  - destruct ls1 as [|a1 t1].
    + cbn[len] in Hlen. lia.
    + cbn[tl len] in Hlen |- *. lia.
Qed.

Lemma HDZD_HI_gray_bound ls ls0 ls1:
  HDZD ls ls0 ->
  HI ls0 ls1 ->
  gray (tl ls1) < 2 ^ len (tl ls).
Proof.
  intros Hhd Hhi.
  rewrite (HDZD_HI_tl_length ls ls0 ls1 Hhd Hhi).
  apply gray_lt.
Qed.

Inductive St :=
| mk_St(ls ls0:list nat)(g g0 l:nat)(inc:Tp)(o:option nat).

Definition St_of (ls ls0:list nat) (inc:Tp) (o:option nat) :=
  mk_St ls ls0 (gray (tl ls)) (gray (tl ls0))
    (if inc then 1 + len ls else len ls) inc o.

Definition St_cur x :=
match x with
| mk_St ls _ _ _ _ _ _ => ls
end.

Definition St_prev x :=
match x with
| mk_St _ ls0 _ _ _ _ _ => ls0
end.

Inductive St_WF: St -> Prop :=
| St_WF_1 ls ls0 ls1 g1 g0 l n:
  HI ls ls0 ->
  HDZD ls0 ls1 ->
  ls1 = ls +l ((L1 n) +l (L1 n)) ->
  g1 = gray (tl ls1) ->
  g0 = gray (tl ls0) ->
  l = 1 + len ls1 ->
  St_WF (mk_St ls1 ls0 g1 g0 l tp1 (Some n))
| St_WF_2 ls ls0 ls1 g1 g0 l n:
  HDZD ls ls0 ->
  HI ls0 ls1 ->
  ls1 = ls +l ((L1 n) +l (L1 n)) ->
  g1 = gray (tl ls1) ->
  g0 = gray (tl ls0) ->
  l = len ls1 ->
  St_WF (mk_St ls1 ls0 g1 g0 l tp0 (Some n))
| St_WF_3 ls ls0 ls1 g1 g0 l:
  HI ls ls0 ->
  HDZD ls0 ls1 ->
  ls1 = ls +l (lsum (gray ls - 2) 2) ->
  2 <= gray ls ->
  g1 = gray (tl ls1) ->
  g0 = gray (tl ls0) ->
  l = 1 + len ls1 ->
  St_WF (mk_St ls1 ls0 g1 g0 l tp1 None)
| St_WF_4 ls ls0 ls1 g1 g0 l:
  HDZD ls ls0 ->
  HI ls0 ls1 ->
  ls1 = ls +l (lsum (gray ls) 2) ->
  g1 = gray (tl ls1) ->
  g0 = gray (tl ls0) ->
  l = len ls1 ->
  St_WF (mk_St ls1 ls0 g1 g0 l tp0 None)
.

Definition S2 (x:St) :=
match x with
| mk_St ls _ _ _ _ _ _ => S1 ls 0
end.

Definition St_Ready x :=
match x with
| mk_St ls _ _ _ _ inc _ =>
    if inc then HI_ready ls else HDZD_ready ls
end.

Definition St_PrevReady x :=
match x with
| mk_St _ ls0 _ _ _ inc _ =>
    St_Ready (St_of ls0 [] (negb inc) None)
end.

Definition TGray (p:Tp) (g:nat) :=
  (if p then 1 else 0) + g * 2.

Lemma gray_tgray_tl ls:
  gray ls = TGray (tp ls) (gray (tl ls)).
Proof.
  destruct ls; cbn[gray tp tl TGray]; reflexivity.
Qed.

Lemma St_Ready_tp ls ls0 inc o:
  St_Ready (St_of ls ls0 inc o) ->
  tp ls = negb inc.
Proof.
  destruct inc; cbn[St_of St_Ready HI_ready HDZD_ready];
    intros [_ [Htp _]]; exact Htp.
Qed.

Lemma St_Ready_gray ls ls0 inc o:
  St_Ready (St_of ls ls0 inc o) ->
  gray ls = TGray (negb inc) (gray (tl ls)).
Proof.
  intro Hready.
  rewrite gray_tgray_tl, (St_Ready_tp _ _ _ _ Hready).
  reflexivity.
Qed.

Inductive St_valid_step: St -> St -> Prop :=
| St_valid_step_1 ls ls0 ls1 ls2 i:
    HDZD ls ls0 ->
    HI ls0 ls1 ->
    HDZD ls1 ls2 ->
    ls1 = ls +l lmul2 (L1 (S i)) ->
    St_valid_step
      (St_of ls1 ls0 tp0 (Some (S i)))
      (St_of ls2 ls1 tp1 (Some i))
| St_valid_step_2 ls ls0 ls1 ls2 i:
    HI ls ls0 ->
    HDZD ls0 ls1 ->
    HI ls1 ls2 ->
    ls1 = ls +l lmul2 (L1 (S i)) ->
    St_valid_step
      (St_of ls1 ls0 tp1 (Some (S i)))
      (St_of ls2 ls1 tp0 (Some i))
| St_valid_step_3 ls ls0 ls1 ls2:
    HDZD ls ls0 ->
    HI ls0 ls1 ->
    HDZD ls1 ls2 ->
    ls1 = ls +l lmul2 (L1 0) ->
    2 <= gray ls0 ->
    St_valid_step
      (St_of ls1 ls0 tp0 (Some 0))
      (St_of ls2 ls1 tp1 None)
| St_valid_step_4 ls ls0 ls1 ls2:
    HI ls ls0 ->
    HDZD ls0 ls1 ->
    HI ls1 ls2 ->
    ls1 = ls +l lmul2 (L1 0) ->
    St_valid_step
      (St_of ls1 ls0 tp1 (Some 0))
      (St_of ls2 ls1 tp0 None)
| St_valid_step_5 ls ls0 ls1 ls2:
    HDZD ls ls0 ->
    HI ls0 ls1 ->
    HDZD ls1 ls2 ->
    ls1 = ls +l lsum (gray ls) 2 ->
    gray (tl ls1) < 2 ^ len (tl ls) ->
    St_valid_step
      (St_of ls1 ls0 tp0 None)
      (St_of ls2 ls1 tp1 (Some (ctzS (gray (tl ls1)))))
| St_valid_step_6 ls ls0 ls1 ls2:
    HI ls ls0 ->
    HDZD ls0 ls1 ->
    HI ls1 ls2 ->
    ls1 = ls +l lsum (gray ls - 2) 2 ->
    2 <= gray ls ->
    1 <= gray (tl ls1) ->
    St_valid_step
      (St_of ls1 ls0 tp1 None)
      (St_of ls2 ls1 tp0 (Some (ctzS (gray (tl ls1) - 1)))).

Definition St_next x :=
match x with
| mk_St ls ls0 _ _ _ inc (Some (S i)) =>
    St_of (ls0 +l lmul2 (L1 i)) ls (negb inc) (Some i)
| mk_St ls ls0 _ _ _ inc (Some 0) =>
    St_of
      (ls0 +l lsum (if inc then gray ls0 else gray ls0 - 2) 2)
      ls (negb inc) None
| mk_St ls ls0 _ _ _ inc None =>
    let k := ctzS (if inc then gray (tl ls) - 1 else gray (tl ls)) in
    St_of (ls0 +l lmul2 (L1 k)) ls (negb inc) (Some k)
end.

Definition St_NextSafe x :=
match x with
| mk_St _ ls0 _ _ _ tp0 (Some 0) => 2 <= gray ls0
| _ => True
end.

Lemma St_next_valid x:
  St_WF x ->
  St_Ready x ->
  St_NextSafe x ->
  St_valid_step x (St_next x).
Proof.
  intros Hwf Hready Hsafe.
  destruct Hwf as
    [ls ls0 ls1 g1 g0 l n Hhi Hhd Heq Hg1 Hg0 Hl
    |ls ls0 ls1 g1 g0 l n Hhd Hhi Heq Hg1 Hg0 Hl
    |ls ls0 ls1 g1 g0 l Hhi Hhd Heq Hgray Hg1 Hg0 Hl
    |ls ls0 ls1 g1 g0 l Hhd Hhi Heq Hg1 Hg0 Hl].
  - cbn[St_Ready HI_ready] in Hready.
    destruct Hready as [Hcur_wf [Htp [Hnz Hroom]]].
    destruct (HI_spec' ls1 Hcur_wf Hnz Hroom Htp) as [ls2 Hnext].
    subst g1 g0 l.
    destruct n as [|n]; cbn[St_next].
    + assert (Heq2: ls2 = ls0 +l lsum (gray ls0) 2)
        by (eapply Case4; eauto 1).
      rewrite <- Heq2.
      econstructor; eauto 1.
    + assert (Heq2: ls2 = ls0 +l lmul2 (L1 n))
        by (eapply Case2; eauto 1).
      rewrite <- Heq2.
      econstructor; eauto 1.
  - cbn[St_Ready HDZD_ready] in Hready.
    destruct Hready as [Hcur_wf [Htp [Hlen [Hrange Hhead]]]].
    destruct (HDZD_spec' ls1 Hcur_wf Hlen Hrange Hhead Htp)
      as [ls2 Hnext].
    subst g1 g0 l.
    destruct n as [|n]; cbn[St_next St_NextSafe] in Hsafe |- *.
    + assert (Heq2: ls2 = ls0 +l lsum (gray ls0 - 2) 2)
        by (eapply Case3; eauto 1).
      rewrite <- Heq2.
      econstructor; eauto 1.
    + assert (Heq2: ls2 = ls0 +l lmul2 (L1 n))
        by (eapply Case1; eauto 1).
      rewrite <- Heq2.
      econstructor; eauto 1.
  - cbn[St_Ready HI_ready] in Hready.
    destruct Hready as [Hcur_wf [Htp [Hnz Hroom]]].
    destruct (HI_spec' ls1 Hcur_wf Hnz Hroom Htp) as [ls2 Hnext].
    subst g1 g0 l.
    cbn[St_next].
    assert (Heq2:
      ls2 = ls0 +l lmul2 (L1 (ctzS (gray (tl ls1) - 1)))).
    {
      rewrite <- lsum_1.
      eapply Case6; eauto 1.
      lia.
    }
    rewrite <- Heq2.
    econstructor; eauto 1; lia.
  - cbn[St_Ready HDZD_ready] in Hready.
    destruct Hready as [Hcur_wf [Htp [Hlen [Hrange Hhead]]]].
    destruct (HDZD_spec' ls1 Hcur_wf Hlen Hrange Hhead Htp)
      as [ls2 Hnext].
    subst g1 g0 l.
    cbn[St_next].
    assert (Hbound: gray (tl ls1) < 2 ^ len (tl ls)).
    {
      apply HDZD_HI_gray_bound with (ls0:=ls0); assumption.
    }
    assert (Heq2:
      ls2 = ls0 +l lmul2 (L1 (ctzS (gray (tl ls1))))).
    {
      rewrite <- lsum_1.
      eapply Case5; eauto 1.
    }
    rewrite <- Heq2.
    econstructor; eauto 1.
  all: unfold lmul2 in *; eauto 1.
Qed.

Lemma St_valid_step_next x y:
  St_valid_step x y ->
  y = St_next x.
Proof.
  intro H.
  destruct H; cbn[St_next].
  - rewrite (Case1 ls ls0 ls1 ls2 i); eauto 1.
  - rewrite (Case2 ls ls0 ls1 ls2 i); eauto 1.
  - rewrite (Case3 ls ls0 ls1 ls2); eauto 1.
  - rewrite (Case4 ls ls0 ls1 ls2); eauto 1.
  - assert (Heq2:
      ls2 = ls0 +l lmul2 (L1 (ctzS (gray (tl ls1))))).
    {
      rewrite <- lsum_1.
      eapply Case5; eauto 1.
    }
    rewrite Heq2. reflexivity.
  - assert (Heq2:
      ls2 = ls0 +l lmul2 (L1 (ctzS (gray (tl ls1) - 1)))).
    {
      rewrite <- lsum_1.
      eapply Case6; eauto 1.
    }
    rewrite Heq2. reflexivity.
Qed.

Lemma St_valid_step_source_WF x y:
  St_valid_step x y -> St_WF x.
Proof.
  intro H.
  destruct H; cbn[St_of]; econstructor; eauto 1;
    unfold lmul2 in *; eauto 1.
Qed.

Lemma St_valid_step_target_WF x y:
  St_valid_step x y -> St_WF y.
Proof.
  intro H.
  destruct H.
  - assert (Heq: ls2 = ls0 +l lmul2 (L1 i))
      by (eapply Case1; eauto 1).
    cbn[St_of].
    econstructor; eauto 1; unfold lmul2 in *; eauto 1.
  - assert (Heq: ls2 = ls0 +l lmul2 (L1 i))
      by (eapply Case2; eauto 1).
    cbn[St_of].
    econstructor; eauto 1; unfold lmul2 in *; eauto 1.
  - assert (Heq: ls2 = ls0 +l lsum (gray ls0 - 2) 2)
      by (eapply Case3; eauto 1).
    cbn[St_of].
    econstructor; eauto 1.
  - assert (Heq: ls2 = ls0 +l lsum (gray ls0) 2)
      by (eapply Case4; eauto 1).
    cbn[St_of].
    econstructor; eauto 1.
  - assert (Heq:
      ls2 = ls0 +l lmul2 (L1 (ctzS (gray (tl ls1))))).
    {
      rewrite <- lsum_1.
      eapply Case5; eauto 1.
    }
    cbn[St_of].
    econstructor; eauto 1; unfold lmul2 in *; eauto 1.
  - assert (Heq:
      ls2 = ls0 +l lmul2 (L1 (ctzS (gray (tl ls1) - 1)))).
    {
      rewrite <- lsum_1.
      eapply Case6; eauto 1.
    }
    cbn[St_of].
    econstructor; eauto 1; unfold lmul2 in *; eauto 1.
Qed.


Lemma St_valid_step_run x y:
  St_valid_step x y ->
  S2 x -->* S2 y.
Proof.
  intro H.
  destruct H; cbn[S2 St_of].
  all: try (eapply HDZD_run; eassumption).
  all: try (eapply HI_run; eassumption).
Qed.



Definition embanked := St_valid_step.

Definition St_mark x :=
match x with
| mk_St _ _ _ _ _ _ o => o
end.

Fixpoint St_nextn n x :=
match n with
| 0 => x
| S i => St_nextn i (St_next x)
end.


Lemma nat_ind2 (P:nat -> Prop):
  P 0 ->
  P 1 ->
  (forall n, P n -> P (S (S n))) ->
  forall n, P n.
Proof.
  intros H0 H1 HSS.
  fix IH 1.
  intro n.
  destruct n as [|[|n]].
  - exact H0.
  - exact H1.
  - apply HSS, IH.
Qed.

Fixpoint carry_cur r ls :=
match r with
| 0 => ls
| 1 => ls
| S (S i) => carry_cur i (ls +l lmul2 (L1 i))
end.

Fixpoint carry_prev r ls :=
match r with
| 0 => ls
| 1 => ls +l lmul2 (L1 0)
| S (S i) => carry_prev i (ls +l lmul2 (L1 (S i)))
end.

Lemma carry_cur_delta i:
  forall ls,
  carry_cur (S (S i)) ls = ls +l Add2sDelta i.
Proof.
  induction i as [| |i IH] using nat_ind2; intro ls.
  - reflexivity.
  - reflexivity.
  - change
      (carry_cur (S (S i))
        (ls +l lmul2 (L1 (S (S i)))) =
       ls +l (lmul2 (L1 (S (S i))) +l Add2sDelta i)).
    rewrite IH, ladd_assoc. reflexivity.
Qed.

Lemma carry_prev_delta i:
  forall ls,
  carry_prev (S i) ls = ls +l Add2sDelta i.
Proof.
  induction i as [| |i IH] using nat_ind2; intro ls.
  - reflexivity.
  - reflexivity.
  - change
      (carry_prev (S i)
        (ls +l lmul2 (L1 (S (S i)))) =
       ls +l (lmul2 (L1 (S (S i))) +l Add2sDelta i)).
    rewrite IH, ladd_assoc. reflexivity.
Qed.

Definition carry_target r ls ls0 inc :=
if Nat.even r then
  St_of (carry_cur r ls) (carry_prev r ls0) inc (Some 0)
else
  St_of (carry_prev r ls0) (carry_cur r ls) (negb inc) (Some 0).

Lemma St_nextn_carry r ls ls0 inc:
  St_nextn r (St_of ls ls0 inc (Some r)) =
  carry_target r ls ls0 inc.
Proof.
  revert ls ls0 inc.
  induction r as [| |r IH] using nat_ind2; intros ls ls0 inc.
  - reflexivity.
  - destruct inc; reflexivity.
  - cbn[St_nextn St_next St_of].
    rewrite IH.
    unfold carry_target.
    rewrite Nat.even_succ_succ.
    cbn[carry_cur carry_prev].
    destruct (Nat.even r), inc; reflexivity.
Qed.

Lemma St_nextn_add a b x:
  St_nextn (a + b) x = St_nextn b (St_nextn a x).
Proof.
  revert x.
  induction a as [|a IH]; intro x.
  - reflexivity.
  - cbn[St_nextn]. apply IH.
Qed.

Definition batch_next_rank (r:nat) (ls ls0:list nat) (inc:Tp) :=
  let cur := carry_cur r ls in
  let prev := carry_prev r ls0 in
  if Nat.even r then
    let prev' :=
      prev +l lsum (if inc then gray prev else gray prev - 2) 2 in
    ctzS (if negb inc
      then gray (List.tl prev') - 1 else gray (List.tl prev'))
  else
    let cur' :=
      cur +l lsum (if negb inc then gray cur else gray cur - 2) 2 in
    ctzS (if inc then gray (List.tl cur') - 1 else gray (List.tl cur')).

Definition batch_target (r:nat) (ls ls0:list nat) (inc:Tp) :=
  let cur := carry_cur r ls in
  let prev := carry_prev r ls0 in
  let k := batch_next_rank r ls ls0 inc in
  if Nat.even r then
    let prev' :=
      prev +l lsum (if inc then gray prev else gray prev - 2) 2 in
    St_of (cur +l lmul2 (L1 k)) prev' inc (Some k)
  else
    let cur' :=
      cur +l lsum (if negb inc then gray cur else gray cur - 2) 2 in
    St_of (prev +l lmul2 (L1 k)) cur' (negb inc) (Some k).

Lemma St_nextn_batch_target r ls ls0 inc:
  St_nextn (r + 2) (St_of ls ls0 inc (Some r)) =
  batch_target r ls ls0 inc.
Proof.
  rewrite St_nextn_add, St_nextn_carry.
  unfold carry_target, batch_target, batch_next_rank.
  destruct (Nat.even r), inc; reflexivity.
Qed.

Inductive embanked_batch: nat -> St -> St -> Prop :=
| embanked_batch_0 x y z:
    St_mark x = Some 0 ->
    embanked x y ->
    embanked y z ->
    embanked_batch 0 x z
| embanked_batch_1 x y z w:
    St_mark x = Some 1 ->
    embanked x y ->
    embanked y z ->
    embanked z w ->
    embanked_batch 1 x w
| embanked_batch_SS i x y z w:
    St_mark x = Some (S (S i)) ->
    embanked x y ->
    embanked y z ->
    embanked_batch i z w ->
    embanked_batch (S (S i)) x w.

Lemma embanked_run x y:
  embanked x y -> S2 x -->* S2 y.
Proof. apply St_valid_step_run. Qed.

Lemma embanked_batch_run n x y:
  embanked_batch n x y -> S2 x -->* S2 y.
Proof.
  intro H.
  induction H.
  - eapply evstep_trans; [apply embanked_run, H0|].
    apply embanked_run, H1.
  - eapply evstep_trans; [apply embanked_run, H0|].
    eapply evstep_trans; [apply embanked_run, H1|].
    apply embanked_run, H2.
  - eapply evstep_trans; [apply embanked_run, H0|].
    eapply evstep_trans; [apply embanked_run, H1|exact IHembanked_batch].
Qed.

Lemma embanked_batch_target_WF n x y:
  embanked_batch n x y -> St_WF y.
Proof.
  intro H; induction H.
  - eapply St_valid_step_target_WF; eassumption.
  - eapply St_valid_step_target_WF; eassumption.
  - exact IHembanked_batch.
Qed.

Lemma embanked_next x y:
  embanked x y -> y = St_next x.
Proof. apply St_valid_step_next. Qed.

Lemma mark_next_S n x:
  St_mark x = Some (S n) ->
  St_mark (St_next x) = Some n.
Proof.
  destruct x as [ls ls0 g g0 l inc [[|i]|]];
    cbn[St_mark St_next St_of]; intro H; try discriminate.
  inversion H. reflexivity.
Qed.

Lemma embanked_batch_target_nextn n x y:
  embanked_batch n x y -> y = St_nextn (n + 2) x.
Proof.
  intro H; induction H.
  - rewrite (embanked_next x y H0) in H1.
    rewrite (embanked_next (St_next x) z H1).
    reflexivity.
  - rewrite (embanked_next x y H0) in H1.
    rewrite (embanked_next (St_next x) z H1) in H2.
    rewrite (embanked_next (St_next (St_next x)) w H2).
    reflexivity.
  - rewrite (embanked_next x y H0) in H1.
    rewrite (embanked_next (St_next x) z H1) in IHembanked_batch.
    cbn[St_nextn] in IHembanked_batch |- *.
    exact IHembanked_batch.
Qed.

Lemma embanked_batch_target n ls ls0 inc y:
  embanked_batch n (St_of ls ls0 inc (Some n)) y ->
  y = batch_target n ls ls0 inc.
Proof.
  intro H.
  rewrite (embanked_batch_target_nextn _ _ _ H).
  apply St_nextn_batch_target.
Qed.

Fixpoint BatchReady n x :=
match n with
| 0 =>
    St_Ready x /\ St_NextSafe x /\
    St_Ready (St_next x) /\ St_NextSafe (St_next x)
| 1 =>
    St_Ready x /\ St_NextSafe x /\
    St_Ready (St_next x) /\ St_NextSafe (St_next x) /\
    St_Ready (St_next (St_next x)) /\
      St_NextSafe (St_next (St_next x))
| S (S i) =>
    St_Ready x /\ St_NextSafe x /\
    St_Ready (St_next x) /\ St_NextSafe (St_next x) /\
    BatchReady i (St_next (St_next x))
end.

Lemma BatchReady_embanked_batch n x:
  St_WF x ->
  St_mark x = Some n ->
  BatchReady n x ->
  exists y, embanked_batch n x y.
Proof.
  revert x.
  induction n as [| |n IH] using nat_ind2;
    intros x Hwf Hmark Hready.
  - cbn[BatchReady] in Hready.
    destruct Hready as [Hr0 [Hs0 [Hr1 Hs1]]].
    pose proof (St_next_valid x Hwf Hr0 Hs0) as Hstep0.
    pose proof (St_valid_step_target_WF x (St_next x) Hstep0) as Hwf1.
    pose proof (St_next_valid (St_next x) Hwf1 Hr1 Hs1) as Hstep1.
    exists (St_next (St_next x)).
    econstructor; eassumption.
  - cbn[BatchReady] in Hready.
    destruct Hready as [Hr0 [Hs0 [Hr1 [Hs1 [Hr2 Hs2]]]]].
    pose proof (St_next_valid x Hwf Hr0 Hs0) as Hstep0.
    pose proof (St_valid_step_target_WF x (St_next x) Hstep0) as Hwf1.
    pose proof (St_next_valid (St_next x) Hwf1 Hr1 Hs1) as Hstep1.
    pose proof
      (St_valid_step_target_WF
        (St_next x) (St_next (St_next x)) Hstep1) as Hwf2.
    pose proof
      (St_next_valid (St_next (St_next x)) Hwf2 Hr2 Hs2) as Hstep2.
    exists (St_next (St_next (St_next x))).
    econstructor; eassumption.
  - cbn[BatchReady] in Hready.
    destruct Hready as [Hr0 [Hs0 [Hr1 [Hs1 Htail]]]].
    pose proof (St_next_valid x Hwf Hr0 Hs0) as Hstep0.
    pose proof (St_valid_step_target_WF x (St_next x) Hstep0) as Hwf1.
    pose proof (St_next_valid (St_next x) Hwf1 Hr1 Hs1) as Hstep1.
    pose proof
      (St_valid_step_target_WF
        (St_next x) (St_next (St_next x)) Hstep1) as Hwf2.
    pose proof (mark_next_S (S n) x Hmark) as Hmark1.
    pose proof (mark_next_S n (St_next x) Hmark1) as Hmark2.
    destruct (IH (St_next (St_next x)) Hwf2 Hmark2 Htail)
      as [y Hbatch].
    exists y. econstructor; eassumption.
Qed.

Definition carry_cur_add r :=
match r with
| 0 | 1 => []
| S (S i) => Add2sDelta i
end.

Definition carry_prev_add r :=
match r with
| 0 => []
| S i => Add2sDelta i
end.

Lemma carry_cur_add_eq r ls:
  carry_cur r ls = ls +l carry_cur_add r.
Proof.
  destruct r as [|[|r]].
  - cbn[carry_cur carry_cur_add]. rewrite ladd_nil_r. reflexivity.
  - cbn[carry_cur carry_cur_add]. rewrite ladd_nil_r. reflexivity.
  - apply carry_cur_delta.
Qed.

Lemma carry_prev_add_eq r ls:
  carry_prev r ls = ls +l carry_prev_add r.
Proof.
  destruct r as [|r].
  - cbn[carry_prev carry_prev_add]. rewrite ladd_nil_r. reflexivity.
  - apply carry_prev_delta.
Qed.

Definition batch_swap r := negb (Nat.even r).

Definition batch_cur_add (r:nat) (ls ls0:list nat) (inc:Tp) :=
  let cur := carry_cur r ls in
  let prev := carry_prev r ls0 in
  let k := batch_next_rank r ls ls0 inc in
  if Nat.even r then
    carry_cur_add r +l lmul2 (L1 k)
  else
    carry_prev_add r +l lmul2 (L1 k).

Definition batch_prev_add (r:nat) (ls ls0:list nat) (inc:Tp) :=
  let cur := carry_cur r ls in
  let prev := carry_prev r ls0 in
  if Nat.even r then
    carry_prev_add r +l
      lsum (if inc then gray prev else gray prev - 2) 2
  else
    carry_cur_add r +l
      lsum (if negb inc then gray cur else gray cur - 2) 2.

Definition PairLadd (swap:bool) (dcur dprev:list nat) (x y:St) :=
  if swap then
    St_cur y = St_prev x +l dcur /\
    St_prev y = St_cur x +l dprev
  else
    St_cur y = St_cur x +l dcur /\
    St_prev y = St_prev x +l dprev.

Lemma embanked_batch_effect r ls ls0 inc y:
  embanked_batch r (St_of ls ls0 inc (Some r)) y ->
  PairLadd (batch_swap r)
    (batch_cur_add r ls ls0 inc)
    (batch_prev_add r ls ls0 inc)
    (St_of ls ls0 inc (Some r)) y.
Proof.
  intro H.
  rewrite (embanked_batch_target r ls ls0 inc y H).
  unfold PairLadd, batch_swap, batch_cur_add, batch_prev_add,
    batch_target.
  rewrite carry_cur_add_eq, carry_prev_add_eq.
  destruct (Nat.even r), inc;
    cbn[negb St_cur St_prev St_of];
    split; rewrite ladd_assoc; reflexivity.
Qed.

Definition compose_swap (s1 s2:bool) := xorb s1 s2.

Definition compose_cur_add (s2:bool)
    (dcur1 dprev1 dcur2:list nat) :=
  (if s2 then dprev1 else dcur1) +l dcur2.

Definition compose_prev_add (s2:bool)
    (dcur1 dprev1 dprev2:list nat) :=
  (if s2 then dcur1 else dprev1) +l dprev2.

Lemma PairLadd_refl x:
  PairLadd false [] [] x x.
Proof. cbn[PairLadd]. rewrite !ladd_nil_r. tauto. Qed.

Lemma PairLadd_trans s1 dc1 dp1 s2 dc2 dp2 x y z:
  PairLadd s1 dc1 dp1 x y ->
  PairLadd s2 dc2 dp2 y z ->
  PairLadd (compose_swap s1 s2)
    (compose_cur_add s2 dc1 dp1 dc2)
    (compose_prev_add s2 dc1 dp1 dp2) x z.
Proof.
  destruct s1, s2;
    cbn[PairLadd compose_swap];
    intros [Hc1 Hp1] [Hc2 Hp2].
  all: unfold compose_cur_add, compose_prev_add; cbn.
  - split.
    + rewrite Hc2, Hp1. rewrite ?ladd_assoc. reflexivity.
    + rewrite Hp2, Hc1. rewrite ?ladd_assoc. reflexivity.
  - split.
    + rewrite Hc2, Hc1. rewrite ?ladd_assoc. reflexivity.
    + rewrite Hp2, Hp1. rewrite ?ladd_assoc. reflexivity.
  - split.
    + rewrite Hc2, Hp1. rewrite ?ladd_assoc. reflexivity.
    + rewrite Hp2, Hc1. rewrite ?ladd_assoc. reflexivity.
  - split.
    + rewrite Hc2, Hc1. rewrite ?ladd_assoc. reflexivity.
    + rewrite Hp2, Hp1. rewrite ?ladd_assoc. reflexivity.
Qed.

Import ListNotations.

Ltac flia := repeat (lia || f_equal).

Lemma ladd_lmul2_0 a ls:
  (a :: ls) +l lmul2 (L1 0) = a + 2 :: ls.
Proof.
  unfold lmul2. cbn[L1 ladd].
  rewrite ladd_nil_r. reflexivity.
Qed.

Lemma ladd_lmul2_S a ls i:
  (a :: ls) +l lmul2 (L1 (S i)) =
  a :: (ls +l lmul2 (L1 i)).
Proof. unfold lmul2. cbn[L1 ladd]. flia. Qed.

Lemma gray_lmul2 ls i:
  gray (ls +l lmul2 (L1 i)) = gray ls.
Proof. unfold lmul2. apply gray_L1_2. Qed.

Lemma tp_lmul2 ls i:
  tp (ls +l lmul2 (L1 i)) = tp ls.
Proof. unfold lmul2. apply tp_L1_2. Qed.

Lemma gray_Add2sDelta i:
  forall ls, gray (ls +l Add2sDelta i) = gray ls.
Proof.
  induction i as [| |i IH] using nat_ind2; intro ls.
  - apply gray_lmul2.
  - apply gray_lmul2.
  - cbn[Add2sDelta].
    rewrite ladd_assoc, IH, gray_lmul2. reflexivity.
Qed.

Lemma tp_Add2sDelta i:
  forall ls, tp (ls +l Add2sDelta i) = tp ls.
Proof.
  induction i as [| |i IH] using nat_ind2; intro ls.
  - apply tp_lmul2.
  - apply tp_lmul2.
  - cbn[Add2sDelta].
    rewrite ladd_assoc, IH, tp_lmul2. reflexivity.
Qed.

Lemma ladd_nonempty_l ls ds:
  ls <> [] -> ls +l ds <> [].
Proof.
  destruct ls as [|a ls]; [contradiction|].
  destruct ds; cbn[ladd]; discriminate.
Qed.

Lemma gray_tl_same_of_gray_tp xs ys:
  xs <> [] -> ys <> [] ->
  gray xs = gray ys -> tp xs = tp ys ->
  gray (List.tl xs) = gray (List.tl ys).
Proof.
  destruct xs as [|a xs], ys as [|b ys];
    try contradiction.
  cbn[List.tl gray] in *.
  destruct (tp (a :: xs)), (tp (b :: ys)); lia.
Qed.

Lemma gray_tl_lmul2 ls i:
  ls <> [] ->
  gray (List.tl (ls +l lmul2 (L1 i))) = gray (List.tl ls).
Proof.
  intro Hne.
  eapply gray_tl_same_of_gray_tp.
  - apply ladd_nonempty_l, Hne.
  - exact Hne.
  - apply gray_lmul2.
  - apply tp_lmul2.
Qed.

Lemma gray_tl_Add2sDelta ls i:
  ls <> [] ->
  gray (List.tl (ls +l Add2sDelta i)) = gray (List.tl ls).
Proof.
  intro Hne.
  eapply gray_tl_same_of_gray_tp.
  - apply ladd_nonempty_l, Hne.
  - exact Hne.
  - apply gray_Add2sDelta.
  - apply tp_Add2sDelta.
Qed.

Lemma carry_cur_nonempty r ls:
  ls <> [] -> carry_cur r ls <> [].
Proof. rewrite carry_cur_add_eq. apply ladd_nonempty_l. Qed.

Lemma carry_prev_nonempty r ls:
  ls <> [] -> carry_prev r ls <> [].
Proof. rewrite carry_prev_add_eq. apply ladd_nonempty_l. Qed.

Lemma carry_cur_gray r ls:
  gray (carry_cur r ls) = gray ls.
Proof.
  rewrite carry_cur_add_eq.
  destruct r as [|[|r]]; cbn[carry_cur_add];
    rewrite ?ladd_nil_r, ?gray_Add2sDelta; reflexivity.
Qed.

Lemma carry_prev_gray r ls:
  gray (carry_prev r ls) = gray ls.
Proof.
  rewrite carry_prev_add_eq.
  destruct r as [|r]; cbn[carry_prev_add];
    rewrite ?ladd_nil_r, ?gray_Add2sDelta; reflexivity.
Qed.

Lemma carry_cur_tl_gray r ls:
  ls <> [] ->
  gray (List.tl (carry_cur r ls)) = gray (List.tl ls).
Proof.
  intro Hne. rewrite carry_cur_add_eq.
  destruct r as [|[|r]]; cbn[carry_cur_add];
    rewrite ?ladd_nil_r; try reflexivity.
  apply gray_tl_Add2sDelta, Hne.
Qed.

Lemma carry_prev_tl_gray r ls:
  ls <> [] ->
  gray (List.tl (carry_prev r ls)) = gray (List.tl ls).
Proof.
  intro Hne. rewrite carry_prev_add_eq.
  destruct r as [|r]; cbn[carry_prev_add];
    rewrite ?ladd_nil_r; try reflexivity.
  apply gray_tl_Add2sDelta, Hne.
Qed.

Lemma gray_tl_lsum_succ2 ls:
  ls <> [] ->
  gray (List.tl (ls +l lsum (gray ls) 2)) =
    gray (List.tl ls) + 1.
Proof.
  destruct ls as [|a ls]; [contradiction|].
  intro Hne. rewrite gray_succ2. cbn[List.tl].
  rewrite gray_incs. reflexivity.
Qed.

Lemma gray_tl_lsum_pred2 ls:
  ls <> [] -> 2 <= gray ls ->
  gray (List.tl (ls +l lsum (gray ls - 2) 2)) =
    gray (List.tl ls) - 1.
Proof.
  destruct ls as [|a ls]; [contradiction|].
  intros _ Hgray.
  rewrite gray_pred2 by exact Hgray.
  cbn[List.tl].
  assert (1 <= gray ls).
  {
    pose proof (gray_tl (a :: ls)) as Htl.
    cbn[List.tl] in Htl. lia.
  }
  rewrite gray_decs by assumption. reflexivity.
Qed.

Definition batch_rank (inc:Tp) (g:nat) :=
  ctzS (if inc then g else g - 1).

Definition next_inc (r:nat) (inc:Tp) :=
  if Nat.even r then inc else negb inc.

Definition next_cur_gray (r:nat) (inc:Tp) (gcur gprev:nat) :=
  if Nat.even r then gcur else gprev.

Definition next_prev_gray (r:nat) (inc:Tp) (gcur gprev:nat) :=
  if Nat.even r then
    if inc then S gprev else gprev - 1
  else
    if inc then gcur - 1 else S gcur.

Definition BoundarySafe (inc:Tp) (gcur gprev:nat) :=
  if inc then 1 <= gcur else 1 <= gprev.

Lemma prev_full_gray r ls ls0 inc:
  St_PrevReady (St_of ls ls0 inc (Some r)) ->
  gray ls0 = TGray inc (gray (List.tl ls0)).
Proof.
  intro Hready.
  cbn[St_PrevReady] in Hready.
  pose proof (St_Ready_gray ls0 [] (negb inc) None Hready) as H.
  replace (negb (negb inc)) with inc in H by
    (destruct inc; reflexivity).
  exact H.
Qed.

Lemma cur_full_gray r ls ls0 inc:
  St_Ready (St_of ls ls0 inc (Some r)) ->
  gray ls = TGray (negb inc) (gray (List.tl ls)).
Proof. apply St_Ready_gray. Qed.

Lemma batch_next_rank_numeric r ls ls0 inc:
  ls <> [] -> ls0 <> [] ->
  St_Ready (St_of ls ls0 inc (Some r)) ->
  St_PrevReady (St_of ls ls0 inc (Some r)) ->
  BoundarySafe inc (gray (List.tl ls)) (gray (List.tl ls0)) ->
  batch_next_rank r ls ls0 inc =
    batch_rank (next_inc r inc)
      (next_prev_gray r inc
        (gray (List.tl ls)) (gray (List.tl ls0))).
Proof.
  intros Hne Hne0 Hcur Hprev Hsafe.
  pose proof (cur_full_gray r ls ls0 inc Hcur) as Hgcur.
  pose proof (prev_full_gray r ls ls0 inc Hprev) as Hgprev.
  unfold batch_next_rank, batch_rank, next_inc, next_prev_gray,
    BoundarySafe in *.
  destruct (Nat.even r) eqn:Heven, inc;
    cbn[negb TGray] in *.
  - rewrite gray_tl_lsum_succ2.
    + rewrite carry_prev_tl_gray by exact Hne0. f_equal; lia.
    + apply carry_prev_nonempty, Hne0.
  - rewrite gray_tl_lsum_pred2.
    + rewrite carry_prev_tl_gray by exact Hne0. f_equal; lia.
    + apply carry_prev_nonempty, Hne0.
    + rewrite carry_prev_gray, Hgprev. unfold TGray. lia.
  - rewrite gray_tl_lsum_pred2.
    + rewrite carry_cur_tl_gray by exact Hne. f_equal; lia.
    + apply carry_cur_nonempty, Hne.
    + rewrite carry_cur_gray, Hgcur. unfold TGray. lia.
  - rewrite gray_tl_lsum_succ2.
    + rewrite carry_cur_tl_gray by exact Hne. f_equal; lia.
    + apply carry_cur_nonempty, Hne.
Qed.

Import ListNotations.

Record Shape (ls:list nat) (p:Tp) (g h l:nat) := {
  shape_WF : WF ls;
  shape_tp : tp ls = p;
  shape_gray : gray (List.tl ls) = g;
  shape_hd : hd 0 ls = h;
  shape_len : length (List.tl ls) = l
}.

Lemma shape_nonempty ls p g h l:
  Shape ls p g h l -> h <> 0 -> ls <> [].
Proof.
  intros Hshape Hh ->.
  inversion Hshape. cbn in *. lia.
Qed.

Lemma nonempty_tl_length_eq (xs ys:list nat):
  xs <> [] -> ys <> [] ->
  length xs = length ys ->
  length (List.tl xs) = length (List.tl ys).
Proof.
  destruct xs, ys; cbn; intros; try contradiction; lia.
Qed.

Lemma length_lmul2 ls i:
  i < length ls ->
  length (ls +l lmul2 (L1 i)) = length ls.
Proof.
  revert i.
  induction ls as [|a ls IH]; intros i Hi.
  - cbn in Hi. lia.
  - destruct i.
    + rewrite ladd_lmul2_0. reflexivity.
    + rewrite ladd_lmul2_S. cbn in *.
      f_equal. apply IH. lia.
Qed.

Lemma WF_lmul2_0 ls:
  WF ls -> WF (ls +l lmul2 (L1 0)).
Proof.
  intro Hwf.
  destruct ls as [|a ls].
  - cbn[L1 lmul2 ladd]. apply WF_S; [lia|apply (WF_O 0)].
  - rewrite ladd_lmul2_0.
    constructor; [lia|exact (WF_tl _ Hwf)].
Qed.

Lemma nth_all0 n i:
  nth i (Helper.lpow [0] n) 0 = 0.
Proof.
  revert i. induction n as [|n IH]; intros [|i]; cbn; auto.
Qed.

Lemma WF_0_nth ls i:
  WF (0 :: ls) -> nth i (0 :: ls) 0 = 0.
Proof.
  intro Hwf.
  remember (0 :: ls) as xs eqn:Hxs.
  induction Hwf as [n|a xs Ha Hwf IH].
  - apply nth_all0.
  - inversion Hxs; subst. contradiction.
Qed.

Lemma WF_0_gray ls:
  WF (0 :: ls) -> gray (0 :: ls) = 0.
Proof.
  intro Hwf.
  remember (0 :: ls) as xs eqn:Hxs.
  induction Hwf.
  - subst. apply gray_all0.
  - inversion Hxs; subst. contradiction.
Qed.

Lemma WF_nth_zero_gray_lt ls i:
  WF ls -> nth i ls 0 = 0 -> gray ls < 2 ^ i.
Proof.
  revert ls.
  induction i as [|i IH]; intros ls Hwf Hnth.
  - destruct ls as [|a ls].
    + cbn[gray Nat.pow]. lia.
    + cbn[nth] in Hnth. subst a.
      rewrite (WF_0_gray ls Hwf). cbn[Nat.pow]. lia.
  - destruct ls as [|a ls].
    + cbn[gray Nat.pow]. lia.
    + cbn[nth] in Hnth.
      pose proof (IH ls (WF_tl _ Hwf) Hnth) as Hlt.
      cbn[gray].
      destruct (tp (a :: ls)); cbn[Nat.pow]; lia.
Qed.

Lemma WF_lmul2_nth ls i:
  WF ls ->
  i < length ls ->
  nth i ls 0 <> 0 ->
  WF (ls +l lmul2 (L1 i)).
Proof.
  revert ls.
  induction i as [|i IH]; intros ls Hwf Hi Hnth.
  - destruct ls as [|a ls]; [cbn in Hi; lia|].
    rewrite ladd_lmul2_0.
    constructor.
    + cbn[nth] in Hnth. lia.
    + exact (WF_tl _ Hwf).
  - destruct ls as [|a ls]; [cbn in Hi; lia|].
    rewrite ladd_lmul2_S.
    constructor.
    + destruct a as [|a].
      * exfalso.
        pose proof (WF_0_nth ls (S i) Hwf) as Hzero.
        cbn[nth] in Hzero. contradiction.
      * lia.
    + apply IH.
      * exact (WF_tl _ Hwf).
      * cbn in Hi. lia.
      * cbn[nth] in Hnth. exact Hnth.
Qed.

Definition head_add i := if i =? 0 then 2 else 0.

Lemma Shape_lmul2 ls p g h l i:
  Shape ls p g h l ->
  ls <> [] ->
  i <= l ->
  (match i with 0 => True | S j => 2 ^ j <= g end) ->
  Shape (ls +l lmul2 (L1 i)) p g (h + head_add i) l.
Proof.
  intros Hshape Hne Hi Hgray.
  destruct Hshape as [Hwf Htp Hg Hhd Hlen].
  destruct ls as [|a ls]; [contradiction|].
  cbn[List.tl hd] in Hg, Hhd, Hlen.
  destruct i as [|i].
  - constructor.
    + apply WF_lmul2_0, Hwf.
    + rewrite tp_lmul2. exact Htp.
    + rewrite gray_tl_lmul2 by discriminate. exact Hg.
    + rewrite ladd_lmul2_0. cbn[hd head_add Nat.eqb]. lia.
    + rewrite ladd_lmul2_0. cbn[List.tl]. exact Hlen.
  - assert (Hil: i < length ls) by lia.
    assert (Hnth: nth i ls 0 <> 0).
    {
      intro Hz.
      pose proof (WF_nth_zero_gray_lt ls i (WF_tl _ Hwf) Hz).
      lia.
    }
    constructor.
    + apply WF_lmul2_nth.
      * exact Hwf.
      * cbn. lia.
      * cbn[nth]. exact Hnth.
    + rewrite tp_lmul2. exact Htp.
    + rewrite gray_tl_lmul2 by discriminate. exact Hg.
    + rewrite ladd_lmul2_S. cbn[hd head_add Nat.eqb]. lia.
    + rewrite ladd_lmul2_S. cbn[List.tl].
      rewrite length_lmul2 by exact Hil. exact Hlen.
Qed.

Lemma Shape_succ2 ls g h l:
  Shape ls tp1 g h l ->
  ls <> [] ->
  gray ls + 2 < 2 ^ length ls ->
  Shape (ls +l lsum (gray ls) 2) tp1 (S g) (S h) l.
Proof.
  intros Hshape Hne Hroom.
  destruct Hshape as [Hwf Htp Hg Hhd Hlen].
  destruct (Incs_spec ls 2 0 Hwf ltac:(lia)) as [dst Hinc].
  1:{ rewrite Htp. reflexivity. }
  inversion Hinc as [n n0 src dst' Heq Hrun Hgray Htp' Hwf' Hlen'].
  cbn in Htp'.
  replace (ls +l lsum (gray ls) 2) with dst by exact Heq.
  constructor.
  - exact Hwf'.
  - rewrite Htp', Htp. reflexivity.
  - rewrite Heq, gray_tl_lsum_succ2 by exact Hne.
    rewrite Hg. f_equal; lia.
  - destruct ls as [|a ls]; [contradiction|].
    rewrite Heq, gray_succ2. cbn[hd] in *. lia.
  - rewrite <-Hlen. apply nonempty_tl_length_eq.
    + rewrite Heq. apply ladd_nonempty_l, Hne.
    + exact Hne.
    + exact Hlen'.
Qed.

Lemma Shape_pred2 ls g h l:
  Shape ls tp0 g h l ->
  ls <> [] ->
  2 <= gray ls ->
  Shape (ls +l lsum (gray ls - 2) 2) tp0 (g - 1) (S h) l.
Proof.
  intros Hshape Hne Hbound.
  destruct Hshape as [Hwf Htp Hg Hhd Hlen].
  destruct (Decs_spec ls 2 0 Hwf Hbound) as [dst Hdec].
  1:{ rewrite Htp. reflexivity. }
  inversion Hdec as
    [n n0 src dst' Heq Hrun Hgray Htp' Hwf' Hlen' Hwf'_strong].
  cbn in Htp'.
  replace (ls +l lsum (gray ls - 2) 2) with dst by exact Heq.
  constructor.
  - exact Hwf'.
  - rewrite Htp', Htp. reflexivity.
  - rewrite Heq, gray_tl_lsum_pred2 by assumption.
    rewrite Hg. reflexivity.
  - destruct ls as [|a ls]; [contradiction|].
    rewrite Heq, gray_pred2 by exact Hbound. cbn[hd] in *. lia.
  - rewrite <-Hlen. apply nonempty_tl_length_eq.
    + rewrite Heq. apply ladd_nonempty_l, Hne.
    + exact Hne.
    + exact Hlen'.
Qed.

Lemma Shape_HI_ready ls g h l:
  Shape ls tp0 g h l ->
  g <> 0 -> h + (g - 1) < 2 ^ l ->
  HI_ready ls.
Proof.
  intros Hshape Hnz Hroom.
  destruct Hshape as [Hwf Htp Hg Hhd Hlen].
  unfold HI_ready. repeat split.
  - exact Hwf.
  - exact Htp.
  - rewrite Hg. exact Hnz.
  - rewrite Hg, Hhd, Hlen. exact Hroom.
Qed.

Lemma Shape_HDZD_ready ls g h l:
  Shape ls tp1 g h l ->
  2 <= l ->
  2 ^ (l - 2) <= 1 + g < 2 ^ l ->
  g + 2 <= h < 2 ^ l + g + 2 ->
  HDZD_ready ls.
Proof.
  intros Hshape Hlen Hrange Hhead.
  destruct Hshape as [Hwf Htp Hg Hhd Hlength].
  unfold HDZD_ready. repeat split; try assumption;
    rewrite ?Hg, ?Hhd, ?Hlength; lia.
Qed.


Definition NumState := (Tp * nat * nat)%type.

Definition num_rank (x:NumState) :=
  let '(inc, _, gprev) := x in batch_rank inc gprev.

Definition num_step (x:NumState) : NumState :=
  let '(inc, gcur, gprev) := x in
  let r := batch_rank inc gprev in
  (next_inc r inc,
   next_cur_gray r inc gcur gprev,
   next_prev_gray r inc gcur gprev).


Lemma even_add2 n:
  Nat.even (2 + n) = Nat.even n.
Proof.
  replace (2 + n) with (n + 2 * 1) by lia.
  apply Nat.even_add_mul_2.
Qed.


Import ListNotations.

Definition ReadySlack (p:Tp) (d g h l:nat) :=
  if p then
    2 <= l /\
    2 ^ (l - 2) <= 1 + g < 2 ^ l /\
    g + 2 <= h /\ h + d < 2 ^ l + g + 2
  else
    g <> 0 /\ h + d + (g - 1) < 2 ^ l.

Definition Addable (r g l:nat) :=
  r <= l /\
  match r with
  | 0 => True
  | S i => 2 ^ i <= g
  end.

Definition Window ls p g h l d r :=
  Shape ls p g h l /\ ReadySlack p d g h l /\ Addable r g l.

Definition BoundaryReady (p:Tp) (g l:nat) :=
  if p then g + 2 < 2 ^ l else 2 <= g.

Definition CurNeed r :=
match r with
| S (S i) => if Nat.even i then 2 else 0
| _ => 0
end.

Definition PrevNeed r :=
match r with
| S i => if Nat.even i then 2 else 0
| 0 => 0
end.

Lemma CurNeed_SS r:
  CurNeed (S (S r)) = CurNeed r + head_add r.
Proof.
  destruct r as [|[|r]]; cbn[CurNeed head_add Nat.eqb].
  - reflexivity.
  - reflexivity.
  - rewrite Nat.even_succ_succ, Nat.add_0_r. reflexivity.
Qed.

Lemma PrevNeed_SS r:
  PrevNeed (S (S r)) = PrevNeed r.
Proof.
  destruct r; cbn[PrevNeed].
  - reflexivity.
  - rewrite Nat.even_succ_succ. reflexivity.
Qed.

Lemma Shape_full_gray ls p g h l:
  Shape ls p g h l -> gray ls = TGray p g.
Proof.
  intros [_ Htp Hg _ _].
  rewrite gray_tgray_tl, Htp, Hg. reflexivity.
Qed.

Lemma Shape_nonempty ls p g h l:
  Shape ls p g h l ->
  g <> 0 \/ h <> 0 -> ls <> [].
Proof.
  intros Hshape [Hg|Hh].
  - intro Heq; subst ls.
    destruct Hshape as [_ _ Hgray _ _]. cbn in Hgray. subst g. contradiction.
  - eapply shape_nonempty; eassumption.
Qed.

Lemma Window_nonempty ls p g h l d r:
  Window ls p g h l d r -> ls <> [].
Proof.
  intros [Hshape [Hready _]].
  apply Shape_nonempty with (p:=p) (g:=g) (h:=h) (l:=l); [exact Hshape|].
  destruct p; cbn[ReadySlack] in Hready.
  - right. lia.
  - left. tauto.
Qed.

Lemma Window_ready ls p g h l d r:
  Window ls p g h l d r ->
  if p then HDZD_ready ls else HI_ready ls.
Proof.
  intros [Hshape [Hready _]].
  destruct p; cbn[ReadySlack] in Hready |- *.
  - destruct Hready as [Hl [Hrange [Hlow Hhigh]]].
    apply Shape_HDZD_ready with (g:=g) (h:=h) (l:=l); try assumption.
    lia.
  - destruct Hready as [Hnz Hroom].
    apply Shape_HI_ready with (g:=g) (h:=h) (l:=l); try assumption.
    lia.
Qed.

Lemma Window_St_Ready ls ls0 inc o g h l d r:
  Window ls (negb inc) g h l d r ->
  St_Ready (St_of ls ls0 inc o).
Proof.
  intro Hwindow.
  destruct inc; cbn[St_Ready St_of negb];
    apply Window_ready in Hwindow; exact Hwindow.
Qed.

Lemma Addable_weaken r r' g l:
  r' <= r -> Addable r g l -> Addable r' g l.
Proof.
  intros Hle [Hlen Hgray]. split; [lia|].
  destruct r' as [|i]; [trivial|].
  destruct r as [|j]; [lia|].
  cbn in Hgray |- *.
  pose proof (Nat.pow_le_mono_r 2 i j ltac:(lia)). lia.
Qed.

Lemma Window_reindex ls p g h l d r r':
  r' <= r ->
  Window ls p g h l d r ->
  Window ls p g h l d r'.
Proof.
  intros Hle [Hshape [Hready Hadd]].
  refine (conj Hshape (conj Hready _)).
  eapply Addable_weaken; eassumption.
Qed.

Lemma Window_weaken ls p g h l d d' r:
  d <= d' ->
  Window ls p g h l d' r ->
  Window ls p g h l d r.
Proof.
  intros Hle [Hshape [Hready Hadd]].
  refine (conj Hshape (conj _ Hadd)).
  destruct p; cbn[ReadySlack] in *; lia.
Qed.

Lemma Window_set_addable ls p g h l d r r':
  Window ls p g h l d r ->
  Addable r' g l ->
  Window ls p g h l d r'.
Proof.
  intros [Hshape [Hready _]] Hadd.
  exact (conj Hshape (conj Hready Hadd)).
Qed.

Lemma Window_lmul2 ls p g h l d r i:
  ls <> [] -> i <= r ->
  Window ls p g h l (d + head_add i) r ->
  Window (ls +l lmul2 (L1 i)) p g (h + head_add i) l d r.
Proof.
  intros Hne Hir [Hshape [Hready Hadd]].
  destruct Hadd as [Hrlen Hrgray].
  assert (Hil: i <= l) by lia.
  assert (Hig:
    match i with 0 => True | S j => 2 ^ j <= g end).
  {
    destruct i as [|j]; [trivial|].
    destruct r as [|k]; [lia|].
    cbn in Hrgray |- *.
    pose proof (Nat.pow_le_mono_r 2 j k ltac:(lia)). lia.
  }
  refine (conj _ (conj _ _)).
  - eapply Shape_lmul2; eassumption.
  - destruct p, i; cbn[ReadySlack head_add Nat.eqb] in *; lia.
  - split; assumption.
Qed.

Lemma full_gray_succ_bound g l:
  g + 2 < 2 ^ l ->
  1 + g * 2 + 2 < 2 ^ S l.
Proof. cbn[Nat.pow]. lia. Qed.

Lemma full_gray_pred_bound g:
  2 <= g -> 2 <= g * 2.
Proof. lia. Qed.

Lemma Boundary_full_safe ls p g h l d r:
  Window ls p g h l d r ->
  BoundaryReady p g l ->
  if p then gray ls + 2 < 2 ^ length ls else 2 <= gray ls.
Proof.
  intros Hwindow Hbound.
  pose proof (Window_nonempty _ _ _ _ _ _ _ Hwindow) as Hne.
  destruct Hwindow as [Hshape _].
  pose proof (Shape_full_gray _ _ _ _ _ Hshape) as Hgray.
  destruct Hshape as [_ _ _ _ Hlen].
  destruct ls as [|a ls]; [contradiction|].
  cbn[List.tl length] in Hlen.
  destruct p; cbn[BoundaryReady TGray] in *.
  - rewrite Hgray. cbn[TGray length]. rewrite Hlen.
    apply full_gray_succ_bound, Hbound.
  - rewrite Hgray. cbn[TGray]. apply full_gray_pred_bound, Hbound.
Qed.

Lemma ReadySlack_boundary p g h l:
  ReadySlack p 0 g h l ->
  BoundaryReady p g l ->
  ReadySlack p 0
    (if p then S g else g - 1) (S h) l.
Proof.
  destruct p; cbn[ReadySlack BoundaryReady]; lia.
Qed.

Lemma Window_boundary ls p g h l r:
  Window ls p g h l 0 r ->
  BoundaryReady p g l ->
  Shape
    (ls +l lsum (if p then gray ls else gray ls - 2) 2)
    p (if p then S g else g - 1) (S h) l.
Proof.
  intros Hwindow Hbound.
  pose proof (Window_nonempty _ _ _ _ _ _ _ Hwindow) as Hne.
  pose proof (Boundary_full_safe _ _ _ _ _ _ _ Hwindow Hbound) as Hsafe.
  destruct Hwindow as [Hshape _].
  destruct p; cbn in *.
  - eapply Shape_succ2; eassumption.
  - eapply Shape_pred2; eassumption.
Qed.

Lemma Window_boundary_ready ls p g h l r:
  Window ls p g h l 0 r ->
  BoundaryReady p g l ->
  if p then
    HDZD_ready (ls +l lsum (gray ls) 2)
  else
    HI_ready (ls +l lsum (gray ls - 2) 2).
Proof.
  intros Hwindow Hbound.
  pose proof (Window_boundary _ _ _ _ _ _ Hwindow Hbound) as Hshape.
  pose proof (ReadySlack_boundary p g h l (proj1 (proj2 Hwindow)) Hbound)
    as Hready.
  destruct p; cbn in *.
  - destruct Hready as [Hl [Hrange [Hlow Hhigh]]].
    eapply Shape_HDZD_ready; eauto 1; lia.
  - destruct Hready as [Hnz Hroom].
    eapply Shape_HI_ready; eauto 1; lia.
Qed.

Lemma rank0_safe ls ls0 inc g h l d r:
  Window ls0 inc g h l d r ->
  BoundaryReady inc g l ->
  St_NextSafe (St_of ls ls0 inc (Some 0)).
Proof.
  intros Hwindow Hbound.
  destruct inc; cbn[St_NextSafe St_of]; [trivial|].
  pose proof (Boundary_full_safe _ _ _ _ _ _ _ Hwindow Hbound).
  exact H.
Qed.

Lemma BatchReady_window_0
    ls ls0 inc gc hc lc gp hp lp:
  Window ls (negb inc) gc hc lc 0 0 ->
  Window ls0 inc gp hp lp 0 0 ->
  BoundaryReady inc gp lp ->
  BatchReady 0 (St_of ls ls0 inc (Some 0)).
Proof.
  intros Hcur Hprev Hbound.
  pose proof
    (Window_St_Ready ls ls0 inc (Some 0) gc hc lc 0 0 Hcur)
    as Hready.
  pose proof
    (rank0_safe ls ls0 inc gp hp lp 0 0 Hprev Hbound)
    as Hsafe.
  pose proof
    (Window_boundary_ready ls0 inc gp hp lp 0 Hprev Hbound)
    as Hnext.
  destruct inc;
    cbn[BatchReady St_next St_of St_NextSafe negb] in *;
    tauto.
Qed.

Lemma BatchReady_window r:
  forall ls ls0 inc gc hc lc gp hp lp,
  Window ls (negb inc) gc hc lc (CurNeed r) r ->
  Window ls0 inc gp hp lp (PrevNeed r) r ->
  BoundaryReady (negb inc) gc lc ->
  BoundaryReady inc gp lp ->
  BatchReady r (St_of ls ls0 inc (Some r)).
Proof.
  induction r as [| |r IH] using nat_ind2;
    intros ls ls0 inc gc hc lc gp hp lp
      Hcur Hprev Hbound_cur Hbound_prev.
  - eapply BatchReady_window_0; eassumption.
  - assert (Hsource:
      St_Ready (St_of ls ls0 inc (Some 1))).
    { eapply Window_St_Ready, Hcur. }
    assert (Hsource_safe:
      St_NextSafe (St_of ls ls0 inc (Some 1))).
    { destruct inc; cbn[St_NextSafe St_of]; exact I. }
    assert (Hprev_add:
      Window (ls0 +l lmul2 (L1 0)) inc gp (hp + 2) lp 0 0).
    {
      eapply Window_reindex with (r:=1); [lia|].
      eapply Window_lmul2 with (r:=1) (i:=0).
      - eapply Window_nonempty, Hprev.
      - lia.
      - exact Hprev.
    }
    assert (Hcur0:
      Window ls (negb inc) gc hc lc 0 0).
    { eapply Window_reindex with (r:=1); [lia|exact Hcur]. }
    change
      (St_Ready (St_of ls ls0 inc (Some 1)) /\
       St_NextSafe (St_of ls ls0 inc (Some 1)) /\
       BatchReady 0 (St_next (St_of ls ls0 inc (Some 1)))).
    split; [exact Hsource|]. split; [exact Hsource_safe|].
    cbn[St_next St_of].
    eapply BatchReady_window_0.
    + replace (negb (negb inc)) with inc by
        (destruct inc; reflexivity).
      exact Hprev_add.
    + exact Hcur0.
    + exact Hbound_cur.
  - assert (Hsource:
      St_Ready (St_of ls ls0 inc (Some (S (S r))))).
    { eapply Window_St_Ready, Hcur. }
    assert (Hprev_add:
      Window (ls0 +l lmul2 (L1 (S r)))
        inc gp (hp + head_add (S r)) lp (PrevNeed r) r).
    {
      eapply Window_reindex with (r:=S (S r)); [lia|].
      eapply Window_lmul2 with (r:=S (S r)) (i:=S r).
      - eapply Window_nonempty, Hprev.
      - lia.
      - rewrite PrevNeed_SS in Hprev.
        cbn[head_add Nat.eqb]. rewrite Nat.add_0_r. exact Hprev.
    }
    assert (Hcur_add:
      Window (ls +l lmul2 (L1 r))
        (negb inc) gc (hc + head_add r) lc (CurNeed r) r).
    {
      eapply Window_reindex with (r:=S (S r)); [lia|].
      eapply Window_lmul2 with (r:=S (S r)) (i:=r).
      - eapply Window_nonempty, Hcur.
      - lia.
      - rewrite CurNeed_SS in Hcur. exact Hcur.
    }
    cbn[BatchReady].
    refine (conj Hsource (conj _ (conj _ (conj _ _)))).
    + destruct inc; cbn[St_NextSafe St_of]; exact I.
    + cbn[St_next St_of].
      eapply Window_St_Ready.
      replace (negb (negb inc)) with inc by
        (destruct inc; reflexivity).
      exact Hprev_add.
    + destruct inc; cbn[St_NextSafe St_of St_next]; exact I.
    + cbn[St_next St_of].
      replace (negb (negb inc)) with inc by
        (destruct inc; reflexivity).
      eapply IH; eassumption.
Qed.

Lemma embanked_batch_window r ls ls0 inc gc hc lc gp hp lp:
  St_WF (St_of ls ls0 inc (Some r)) ->
  Window ls (negb inc) gc hc lc (CurNeed r) r ->
  Window ls0 inc gp hp lp (PrevNeed r) r ->
  BoundaryReady (negb inc) gc lc ->
  BoundaryReady inc gp lp ->
  exists y, embanked_batch r (St_of ls ls0 inc (Some r)) y.
Proof.
  intros Hwf Hcur Hprev Hbound_cur Hbound_prev.
  apply BatchReady_embanked_batch; [exact Hwf|reflexivity|].
  eapply BatchReady_window; eassumption.
Qed.

Lemma Shape_carry_cur r:
  forall ls p g h l d,
  Window ls p g h l (d + CurNeed r) r ->
  Shape (carry_cur r ls) p g (h + CurNeed r) l.
Proof.
  induction r as [| |r IH] using nat_ind2;
    intros ls p g h l d Hwindow.
  - cbn[carry_cur CurNeed].
    replace (h + 0) with h by lia. exact (proj1 Hwindow).
  - cbn[carry_cur CurNeed].
    replace (h + 0) with h by lia. exact (proj1 Hwindow).
  - assert (Hstep:
      Window (ls +l lmul2 (L1 r)) p g (h + head_add r) l
        (d + CurNeed r) r).
    {
      eapply Window_reindex with (r:=S (S r)); [lia|].
      eapply Window_lmul2 with (r:=S (S r)) (i:=r).
      - eapply Window_nonempty, Hwindow.
      - lia.
      - rewrite CurNeed_SS in Hwindow.
        replace (d + (CurNeed r + head_add r))
          with ((d + CurNeed r) + head_add r) in Hwindow by lia.
        exact Hwindow.
    }
    change
      (Shape (carry_cur r (ls +l lmul2 (L1 r)))
        p g (h + CurNeed (S (S r))) l).
    replace (h + CurNeed (S (S r)))
      with ((h + head_add r) + CurNeed r).
    + eapply IH, Hstep.
    + rewrite CurNeed_SS. lia.
Qed.

Lemma Shape_carry_prev r:
  forall ls p g h l d,
  Window ls p g h l (d + PrevNeed r) r ->
  Shape (carry_prev r ls) p g (h + PrevNeed r) l.
Proof.
  induction r as [| |r IH] using nat_ind2;
    intros ls p g h l d Hwindow.
  - cbn[carry_prev PrevNeed].
    replace (h + 0) with h by lia. exact (proj1 Hwindow).
  - cbn[carry_prev PrevNeed].
    eapply Shape_lmul2.
    + exact (proj1 Hwindow).
    + eapply Window_nonempty, Hwindow.
    + destruct Hwindow as [_ [_ [Hlen _]]]. cbn in Hlen. lia.
    + trivial.
  - assert (Hstep:
      Window (ls +l lmul2 (L1 (S r))) p g
        (h + head_add (S r)) l (d + PrevNeed r) r).
    {
      eapply Window_reindex with (r:=S (S r)); [lia|].
      eapply Window_lmul2 with (r:=S (S r)) (i:=S r).
      - eapply Window_nonempty, Hwindow.
      - lia.
      - rewrite PrevNeed_SS in Hwindow.
        cbn[head_add Nat.eqb].
        rewrite !Nat.add_0_r. exact Hwindow.
    }
    change
      (Shape (carry_prev r (ls +l lmul2 (L1 (S r))))
        p g (h + PrevNeed (S (S r))) l).
    rewrite PrevNeed_SS.
    cbn[head_add Nat.eqb] in Hstep.
    rewrite Nat.add_0_r in Hstep.
    eapply IH, Hstep.
Qed.

Lemma Window_carry_cur r ls p g h l d:
  Window ls p g h l (d + CurNeed r) r ->
  Window (carry_cur r ls) p g (h + CurNeed r) l d r.
Proof.
  intro Hwindow.
  pose proof (Shape_carry_cur r ls p g h l d Hwindow) as Hshape.
  destruct Hwindow as [_ [Hready Hadd]].
  refine (conj Hshape (conj _ Hadd)).
  destruct p; cbn[ReadySlack] in *; lia.
Qed.

Lemma Window_carry_prev r ls p g h l d:
  Window ls p g h l (d + PrevNeed r) r ->
  Window (carry_prev r ls) p g (h + PrevNeed r) l d r.
Proof.
  intro Hwindow.
  pose proof (Shape_carry_prev r ls p g h l d Hwindow) as Hshape.
  destruct Hwindow as [_ [Hready Hadd]].
  refine (conj Hshape (conj _ Hadd)).
  destruct p; cbn[ReadySlack] in *; lia.
Qed.

Lemma Shape_lmul2_addable ls p g h l i:
  Shape ls p g h l ->
  ls <> [] ->
  Addable i g l ->
  Shape (ls +l lmul2 (L1 i)) p g (h + head_add i) l.
Proof.
  intros Hshape Hne [Hlen Hgray].
  eapply Shape_lmul2; eassumption.
Qed.

Lemma Window_prev_ready ls ls0 inc o gp hp lp d r:
  Window ls0 inc gp hp lp d r ->
  St_PrevReady (St_of ls ls0 inc o).
Proof.
  intro Hprev.
  unfold St_PrevReady.
  eapply Window_St_Ready.
  replace (negb (negb inc)) with inc by
    (destruct inc; reflexivity).
  exact Hprev.
Qed.

Lemma Window_gray ls p g h l d r:
  Window ls p g h l d r -> gray (List.tl ls) = g.
Proof. intros [Hshape _]. exact (shape_gray _ _ _ _ _ Hshape). Qed.

Lemma Window_boundary_safe inc gc lc gp lp:
  BoundaryReady (negb inc) gc lc ->
  BoundaryReady inc gp lp ->
  BoundarySafe inc gc gp.
Proof.
  destruct inc; cbn[BoundaryReady BoundarySafe negb]; lia.
Qed.

Lemma batch_next_rank_window r ls ls0 inc gc hc lc gp hp lp:
  Window ls (negb inc) gc hc lc (CurNeed r) r ->
  Window ls0 inc gp hp lp (PrevNeed r) r ->
  BoundaryReady (negb inc) gc lc ->
  BoundaryReady inc gp lp ->
  batch_next_rank r ls ls0 inc =
    batch_rank (next_inc r inc) (next_prev_gray r inc gc gp).
Proof.
  intros Hcur Hprev Hbound_cur Hbound_prev.
  assert (Hsafe:
    BoundarySafe inc (gray (List.tl ls)) (gray (List.tl ls0))).
  {
    rewrite (Window_gray _ _ _ _ _ _ _ Hcur),
      (Window_gray _ _ _ _ _ _ _ Hprev).
    eapply Window_boundary_safe; eassumption.
  }
  pose proof
    (batch_next_rank_numeric r ls ls0 inc
      (Window_nonempty _ _ _ _ _ _ _ Hcur)
      (Window_nonempty _ _ _ _ _ _ _ Hprev)
      (Window_St_Ready _ _ _ _ _ _ _ _ _ Hcur)
      (Window_prev_ready _ _ _ _ _ _ _ _ _ Hprev)
      Hsafe)
    as Hrank.
  rewrite (Window_gray _ _ _ _ _ _ _ Hcur),
    (Window_gray _ _ _ _ _ _ _ Hprev) in Hrank.
  exact Hrank.
Qed.

Definition next_cur_head r k hc hp :=
  if Nat.even r
  then hc + CurNeed r + head_add k
  else hp + PrevNeed r + head_add k.

Definition next_prev_head r hc hp :=
  if Nat.even r
  then hp + PrevNeed r + 1
  else hc + CurNeed r + 1.

Definition next_cur_len (r lc lp:nat) :=
  if Nat.even r then lc else lp.

Definition next_prev_len (r lc lp:nat) :=
  if Nat.even r then lp else lc.

Lemma batch_target_shape r ls ls0 inc gc hc lc gp hp lp:
  Window ls (negb inc) gc hc lc (CurNeed r) r ->
  Window ls0 inc gp hp lp (PrevNeed r) r ->
  BoundaryReady (negb inc) gc lc ->
  BoundaryReady inc gp lp ->
  let k := batch_rank (next_inc r inc)
    (next_prev_gray r inc gc gp) in
  Addable k (next_cur_gray r inc gc gp) (next_cur_len r lc lp) ->
  let y := batch_target r ls ls0 inc in
  Shape (St_cur y) (negb (next_inc r inc))
    (next_cur_gray r inc gc gp) (next_cur_head r k hc hp)
    (next_cur_len r lc lp) /\
  Shape (St_prev y) (next_inc r inc)
    (next_prev_gray r inc gc gp) (next_prev_head r hc hp)
    (next_prev_len r lc lp).
Proof.
  intros Hcur Hprev Hbound_cur Hbound_prev.
  cbn zeta. intro Hadd.
  pose proof
    (Window_carry_cur r ls (negb inc) gc hc lc 0 Hcur) as Hcur_carry.
  pose proof
    (Window_carry_prev r ls0 inc gp hp lp 0 Hprev) as Hprev_carry.
  pose proof
    (batch_next_rank_window r ls ls0 inc gc hc lc gp hp lp
      Hcur Hprev Hbound_cur Hbound_prev) as Hrank.
  cbn zeta.
  unfold batch_target.
  rewrite Hrank.
  unfold next_cur_head, next_prev_head, next_cur_len, next_prev_len,
    next_cur_gray, next_prev_gray, next_inc, batch_rank in *.
  destruct (Nat.even r) eqn:Heven, inc;
    cbn[St_cur St_prev St_of negb] in *; split.
  - eapply Shape_lmul2_addable.
    + exact (proj1 Hcur_carry).
    + eapply Window_nonempty, Hcur_carry.
    + exact Hadd.
  - replace (hp + PrevNeed r + 1) with (S (hp + PrevNeed r)) by lia.
    exact (Window_boundary _ tp1 gp (hp + PrevNeed r) lp r
      Hprev_carry Hbound_prev).
  - eapply Shape_lmul2_addable.
    + exact (proj1 Hcur_carry).
    + eapply Window_nonempty, Hcur_carry.
    + exact Hadd.
  - replace (hp + PrevNeed r + 1) with (S (hp + PrevNeed r)) by lia.
    exact (Window_boundary _ tp0 gp (hp + PrevNeed r) lp r
      Hprev_carry Hbound_prev).
  - eapply Shape_lmul2_addable.
    + exact (proj1 Hprev_carry).
    + eapply Window_nonempty, Hprev_carry.
    + exact Hadd.
  - replace (hc + CurNeed r + 1) with (S (hc + CurNeed r)) by lia.
    exact (Window_boundary _ tp0 gc (hc + CurNeed r) lc r
      Hcur_carry Hbound_cur).
  - eapply Shape_lmul2_addable.
    + exact (proj1 Hprev_carry).
    + eapply Window_nonempty, Hprev_carry.
    + exact Hadd.
  - replace (hc + CurNeed r + 1) with (S (hc + CurNeed r)) by lia.
    exact (Window_boundary _ tp1 gc (hc + CurNeed r) lc r
      Hcur_carry Hbound_cur).
Qed.

Lemma batch_step r ls ls0 inc gc hc lc gp hp lp:
  St_WF (St_of ls ls0 inc (Some r)) ->
  Shape ls (negb inc) gc hc lc ->
  Shape ls0 inc gp hp lp ->
  ReadySlack (negb inc) (CurNeed r) gc hc lc ->
  ReadySlack inc (PrevNeed r) gp hp lp ->
  Addable r gc lc -> Addable r gp lp ->
  BoundaryReady (negb inc) gc lc ->
  BoundaryReady inc gp lp ->
  let k := batch_rank (next_inc r inc)
    (next_prev_gray r inc gc gp) in
  Addable k (next_cur_gray r inc gc gp) (next_cur_len r lc lp) ->
  exists y,
    embanked_batch r (St_of ls ls0 inc (Some r)) y /\
    y = batch_target r ls ls0 inc /\
    St_WF y /\
    Shape (St_cur y) (negb (next_inc r inc))
      (next_cur_gray r inc gc gp) (next_cur_head r k hc hp)
      (next_cur_len r lc lp) /\
    Shape (St_prev y) (next_inc r inc)
      (next_prev_gray r inc gc gp) (next_prev_head r hc hp)
      (next_prev_len r lc lp).
Proof.
  intros Hwf Hcur_shape Hprev_shape Hcur_ready Hprev_ready
    Hcur_add Hprev_add Hbound_cur Hbound_prev.
  cbn zeta. intro Hnext_add.
  assert (Hcur:
    Window ls (negb inc) gc hc lc (CurNeed r) r)
    by exact (conj Hcur_shape (conj Hcur_ready Hcur_add)).
  assert (Hprev:
    Window ls0 inc gp hp lp (PrevNeed r) r)
    by exact (conj Hprev_shape (conj Hprev_ready Hprev_add)).
  destruct (embanked_batch_window r ls ls0 inc gc hc lc gp hp lp
    Hwf Hcur Hprev Hbound_cur Hbound_prev) as [y Hbatch].
  exists y. split; [exact Hbatch|].
  assert (Hy: y = batch_target r ls ls0 inc)
    by (eapply embanked_batch_target, Hbatch).
  split; [exact Hy|].
  split.
  - eapply embanked_batch_target_WF, Hbatch.
  - rewrite Hy.
    eapply batch_target_shape; eassumption.
Qed.

Lemma batch_target_ready r ls ls0 inc gc hc lc gp hp lp:
  let k := batch_rank (next_inc r inc)
    (next_prev_gray r inc gc gp) in
  Window ls (negb inc) gc hc lc (head_add k + CurNeed r) r ->
  Window ls0 inc gp hp lp (head_add k + PrevNeed r) r ->
  Addable k gc lc -> Addable k gp lp ->
  BoundaryReady (negb inc) gc lc ->
  BoundaryReady inc gp lp ->
  let y := batch_target r ls ls0 inc in
  St_Ready y /\ St_PrevReady y.
Proof.
  cbn zeta.
  set (k := batch_rank (next_inc r inc)
    (next_prev_gray r inc gc gp)).
  intros Hcur Hprev Hkcur Hkprev Hbound_cur Hbound_prev.
  assert (Hcur0:
    Window ls (negb inc) gc hc lc (CurNeed r) r).
  {
    eapply Window_weaken with (d':=head_add k + CurNeed r);
      [lia|exact Hcur].
  }
  assert (Hprev0:
    Window ls0 inc gp hp lp (PrevNeed r) r).
  {
    eapply Window_weaken with (d':=head_add k + PrevNeed r);
      [lia|exact Hprev].
  }
  assert (Hcur_carry0:
    Window (carry_cur r ls) (negb inc) gc (hc + CurNeed r) lc 0 r).
  {
    eapply Window_carry_cur.
    replace (0 + CurNeed r) with (CurNeed r) by lia.
    exact Hcur0.
  }
  assert (Hprev_carry0:
    Window (carry_prev r ls0) inc gp (hp + PrevNeed r) lp 0 r).
  {
    eapply Window_carry_prev.
    replace (0 + PrevNeed r) with (PrevNeed r) by lia.
    exact Hprev0.
  }
  assert (Hcur_carryk:
    Window (carry_cur r ls) (negb inc) gc (hc + CurNeed r) lc
      (head_add (batch_rank (next_inc r inc)
        (next_prev_gray r inc gc gp)))
      (batch_rank (next_inc r inc) (next_prev_gray r inc gc gp))).
  {
    eapply Window_set_addable; [|exact Hkcur].
    eapply Window_carry_cur.
    exact Hcur.
  }
  assert (Hprev_carryk:
    Window (carry_prev r ls0) inc gp (hp + PrevNeed r) lp
      (head_add (batch_rank (next_inc r inc)
        (next_prev_gray r inc gc gp)))
      (batch_rank (next_inc r inc) (next_prev_gray r inc gc gp))).
  {
    eapply Window_set_addable; [|exact Hkprev].
    eapply Window_carry_prev.
    exact Hprev.
  }
  assert (Hcur_final:
    Window (carry_cur r ls +l lmul2 (L1 k))
      (negb inc) gc (hc + CurNeed r + head_add k) lc 0 k).
  {
    eapply Window_lmul2.
    - eapply Window_nonempty, Hcur_carryk.
    - lia.
    - replace (0 + head_add k) with (head_add k) by lia.
      exact Hcur_carryk.
  }
  assert (Hprev_final:
    Window (carry_prev r ls0 +l lmul2 (L1 k))
      inc gp (hp + PrevNeed r + head_add k) lp 0 k).
  {
    eapply Window_lmul2.
    - eapply Window_nonempty, Hprev_carryk.
    - lia.
    - replace (0 + head_add k) with (head_add k) by lia.
      exact Hprev_carryk.
  }
  pose proof (Window_ready _ _ _ _ _ _ _ Hcur_final) as Hcur_ready.
  pose proof (Window_ready _ _ _ _ _ _ _ Hprev_final) as Hprev_ready.
  pose proof
    (Window_boundary_ready _ _ _ _ _ _ Hcur_carry0 Hbound_cur)
    as Hcur_boundary.
  pose proof
    (Window_boundary_ready _ _ _ _ _ _ Hprev_carry0 Hbound_prev)
    as Hprev_boundary.
  assert (Hrank: batch_next_rank r ls ls0 inc = k).
  {
    subst k.
    eapply batch_next_rank_window; eassumption.
  }
  cbn zeta. unfold batch_target. rewrite Hrank.
  destruct (Nat.even r), inc;
    cbn[St_Ready St_PrevReady St_of negb] in *; tauto.
Qed.

Import ListNotations.

Definition HeadSlack (p:Tp) (d g h l:nat) :=
  if p then h + d < 2 ^ l + g + 2
  else h + d + (g - 1) < 2 ^ l.

Lemma HI_source_head_slack d src dst:
  HI src dst ->
  gray dst + d < 2 ^ length (List.tl src) ->
  HeadSlack tp0 d (gray (List.tl src)) (List.hd 0 src)
    (length (List.tl src)).
Proof.
  intros Hhi Hroom.
  inversion Hhi; subst; clear Hhi.
  rewrite HI_c in Hroom.
  cbn[HeadSlack List.tl List.hd] in *. lia.
Qed.

Lemma HDZD_source_head_slack d src dst:
  HDZD src dst ->
  d <= gray dst ->
  HeadSlack tp1 d (gray (List.tl src)) (List.hd 0 src)
    (length (List.tl src)).
Proof.
  intros Hhd Hgray.
  inversion Hhd; subst; clear Hhd.
  rewrite HDZD_c in Hgray.
  cbn[HeadSlack List.tl List.hd] in *. lia.
Qed.

Lemma HeadSlack_lmul2 p d ls i:
  ls <> [] ->
  i <= length (List.tl ls) ->
  HeadSlack p (d + head_add i)
    (gray (List.tl ls)) (List.hd 0 ls) (length (List.tl ls)) ->
  HeadSlack p d
    (gray (List.tl (ls +l lmul2 (L1 i))))
    (List.hd 0 (ls +l lmul2 (L1 i)))
    (length (List.tl (ls +l lmul2 (L1 i)))).
Proof.
  destruct ls as [|a ls]; [contradiction|].
  intros _ Hi Hslack.
  destruct i as [|i].
  - rewrite ladd_lmul2_0.
    cbn[HeadSlack head_add Nat.eqb List.tl List.hd] in *.
    destruct p; cbn[HeadSlack] in *.
    + replace (a + 2 + d) with (a + (d + 2)) by lia.
      exact Hslack.
    + replace (a + 2 + d + (gray ls - 1))
        with (a + (d + 2) + (gray ls - 1)) by lia.
      exact Hslack.
  - rewrite ladd_lmul2_S.
    cbn[HeadSlack head_add Nat.eqb List.tl List.hd] in *.
    rewrite gray_lmul2, length_lmul2 by lia.
    replace (d + 0) with d in Hslack by lia.
    exact Hslack.
Qed.

Lemma St_WF_cur_head_slack n cur prev inc d:
  St_WF (St_of cur prev inc (Some n)) ->
  n <= length (List.tl cur) ->
  (if inc
   then gray prev + (d + head_add n) < 2 ^ length (List.tl cur)
   else d + head_add n <= gray prev) ->
  HeadSlack (negb inc) d
    (gray (List.tl cur)) (List.hd 0 cur) (length (List.tl cur)).
Proof.
  destruct inc; cbn[negb]; intros Hwf Hrank Hbound.
  - inversion Hwf; subst; try discriminate.
    assert (Hsrc_ne: ls <> []).
    { inversion H5; discriminate. }
    assert (Hcur_ne: ls +l lmul2 (L1 n) <> []).
    { eapply ladd_nonempty_l, Hsrc_ne. }
    assert (Hlen: length ls = length (ls +l lmul2 (L1 n))).
    {
      pose proof (HI_length ls prev H5).
      change (HDZD prev (ls +l lmul2 (L1 n))) in H6.
      pose proof (HDZD_length prev (ls +l lmul2 (L1 n)) H6).
      lia.
    }
    assert (Htlen:
      length (List.tl ls) =
      length (List.tl (ls +l lmul2 (L1 n)))).
    { apply nonempty_tl_length_eq; assumption. }
    eapply HeadSlack_lmul2.
    + exact Hsrc_ne.
    + rewrite Htlen. exact Hrank.
    + eapply HI_source_head_slack; [exact H5|].
      rewrite Htlen. exact Hbound.
  - inversion Hwf; subst; try discriminate.
    assert (Hsrc_ne: ls <> []).
    { inversion H5; discriminate. }
    assert (Hcur_ne: ls +l lmul2 (L1 n) <> []).
    { eapply ladd_nonempty_l, Hsrc_ne. }
    assert (Hlen: length ls = length (ls +l lmul2 (L1 n))).
    {
      pose proof (HDZD_length ls prev H5).
      change (HI prev (ls +l lmul2 (L1 n))) in H6.
      pose proof (HI_length prev (ls +l lmul2 (L1 n)) H6).
      lia.
    }
    assert (Htlen:
      length (List.tl ls) =
      length (List.tl (ls +l lmul2 (L1 n)))).
    { apply nonempty_tl_length_eq; assumption. }
    eapply HeadSlack_lmul2.
    + exact Hsrc_ne.
    + rewrite Htlen. exact Hrank.
    + eapply HDZD_source_head_slack; [exact H5|exact Hbound].
Qed.

Lemma St_WF_prev_head_slack n cur prev inc d:
  St_WF (St_of cur prev inc (Some n)) ->
  (if inc then d <= gray cur
   else gray cur + d < 2 ^ length (List.tl prev)) ->
  HeadSlack inc d
    (gray (List.tl prev)) (List.hd 0 prev) (length (List.tl prev)).
Proof.
  destruct inc; cbn; intros Hwf Hbound.
  - inversion Hwf; subst; try discriminate.
    eapply HDZD_source_head_slack; eassumption.
  - inversion Hwf; subst; try discriminate.
    eapply HI_source_head_slack; eassumption.
Qed.

Lemma ReadySlack_of_shape_ready ls p g h l d:
  Shape ls p g h l ->
  (if p then HDZD_ready ls else HI_ready ls) ->
  HeadSlack p d g h l ->
  ReadySlack p d g h l.
Proof.
  intros Hshape Hready Hslack.
  destruct p; cbn[ReadySlack HeadSlack] in *.
  - destruct Hready as [_ [_ [Hlen [Hrange Hhead]]]].
    destruct Hshape as [_ _ Hg Hh Hl].
    rewrite Hg, Hh, Hl in *. lia.
  - destruct Hready as [_ [_ [Hnz Hroom]]].
    destruct Hshape as [_ _ Hg Hh Hl].
    rewrite Hg, Hh, Hl in *. lia.
Qed.

Lemma current_shape cur prev inc o gc lc:
  St_Ready (St_of cur prev inc o) ->
  gray (List.tl cur) = gc ->
  length (List.tl cur) = lc ->
  Shape cur (negb inc) gc (List.hd 0 cur) lc.
Proof.
  intros Hready Hg Hl. constructor.
  - destruct inc; cbn[St_Ready St_of HI_ready HDZD_ready] in Hready |- *;
      exact (proj1 Hready).
  - eapply St_Ready_tp, Hready.
  - exact Hg.
  - reflexivity.
  - exact Hl.
Qed.

Lemma prev_shape cur prev inc o gp lp:
  St_PrevReady (St_of cur prev inc o) ->
  gray (List.tl prev) = gp ->
  length (List.tl prev) = lp ->
  Shape prev inc gp (List.hd 0 prev) lp.
Proof.
  intros Hready Hg Hl.
  unfold St_PrevReady in Hready.
  pose proof
    (current_shape prev [] (negb inc) None gp lp Hready Hg Hl) as Hshape.
  replace (negb (negb inc)) with inc in Hshape by
    (destruct inc; reflexivity).
  exact Hshape.
Qed.

Record ClosedFeature := mkClosed {
  c_inc : Tp;
  c_cur_gray : nat;
  c_cur_len : nat;
  c_prev_gray : nat;
  c_prev_len : nat
}.

Definition c_rank c := batch_rank (c_inc c) (c_prev_gray c).

Definition c_step c :=
  let r := c_rank c in
  mkClosed
    (next_inc r (c_inc c))
    (next_cur_gray r (c_inc c) (c_cur_gray c) (c_prev_gray c))
    (next_cur_len r (c_cur_len c) (c_prev_len c))
    (next_prev_gray r (c_inc c) (c_cur_gray c) (c_prev_gray c))
    (next_prev_len r (c_cur_len c) (c_prev_len c)).

Definition ClosedNumeric c :=
  let r := c_rank c in
  let k := c_rank (c_step c) in
  let inc := c_inc c in
  let gc := c_cur_gray c in
  let gp := c_prev_gray c in
  let lc := c_cur_len c in
  let lp := c_prev_len c in
  Addable r gc lc /\ Addable r gp lp /\
  Addable k gc lc /\ Addable k gp lp /\
  BoundaryReady (negb inc) gc lc /\ BoundaryReady inc gp lp /\
  (if inc then
     TGray inc gp + (head_add k + CurNeed r + head_add r) < 2 ^ lc
   else
     head_add k + CurNeed r + head_add r <= TGray inc gp) /\
  (if inc then
     head_add k + PrevNeed r <= TGray (negb inc) gc
   else
     TGray (negb inc) gc + (head_add k + PrevNeed r) < 2 ^ lp).

Definition ClosedRep (x:St) c :=
  exists cur prev,
    x = St_of cur prev (c_inc c) (Some (c_rank c)) /\
    St_WF x /\ St_Ready x /\ St_PrevReady x /\
    gray (List.tl cur) = c_cur_gray c /\
    length (List.tl cur) = c_cur_len c /\
    gray (List.tl prev) = c_prev_gray c /\
    length (List.tl prev) = c_prev_len c.

Lemma closed_windows r cur prev inc gc lc gp lp:
  St_WF (St_of cur prev inc (Some r)) ->
  St_Ready (St_of cur prev inc (Some r)) ->
  St_PrevReady (St_of cur prev inc (Some r)) ->
  gray (List.tl cur) = gc -> length (List.tl cur) = lc ->
  gray (List.tl prev) = gp -> length (List.tl prev) = lp ->
  let k := batch_rank (next_inc r inc) (next_prev_gray r inc gc gp) in
  Addable r gc lc -> Addable r gp lp ->
  (if inc then
     TGray inc gp + (head_add k + CurNeed r + head_add r) < 2 ^ lc
   else
     head_add k + CurNeed r + head_add r <= TGray inc gp) ->
  (if inc then
     head_add k + PrevNeed r <= TGray (negb inc) gc
   else
     TGray (negb inc) gc + (head_add k + PrevNeed r) < 2 ^ lp) ->
  Window cur (negb inc) gc (List.hd 0 cur) lc
    (head_add k + CurNeed r) r /\
  Window prev inc gp (List.hd 0 prev) lp
    (head_add k + PrevNeed r) r.
Proof.
  intros Hwf Hready Hprev Hg Hl Hgp Hlp.
  cbn zeta. intros Hr_cur Hr_prev Hcur_bound Hprev_bound.
  pose proof (current_shape cur prev inc (Some r) gc lc Hready Hg Hl)
    as Hcur_shape.
  pose proof (prev_shape cur prev inc (Some r) gp lp Hprev Hgp Hlp)
    as Hprev_shape.
  pose proof (St_Ready_gray cur prev inc (Some r) Hready) as Hfull_cur.
  pose proof (St_Ready_gray prev [] (negb inc) None Hprev) as Hfull_prev.
  replace (negb (negb inc)) with inc in Hfull_prev by
    (destruct inc; reflexivity).
  assert (Hcur_head:
    HeadSlack (negb inc) (head_add
      (batch_rank (next_inc r inc) (next_prev_gray r inc gc gp)) +
      CurNeed r) gc (List.hd 0 cur) lc).
  {
    assert (Hrank: r <= length (List.tl cur)).
    { rewrite Hl. exact (proj1 Hr_cur). }
    assert (Hbound:
      if inc then
        gray prev + (head_add
          (batch_rank (next_inc r inc) (next_prev_gray r inc gc gp)) +
          CurNeed r + head_add r) < 2 ^ length (List.tl cur)
      else
        head_add
          (batch_rank (next_inc r inc) (next_prev_gray r inc gc gp)) +
          CurNeed r + head_add r <= gray prev).
    {
      rewrite Hfull_prev, Hgp, Hl.
      exact Hcur_bound.
    }
    pose proof (St_WF_cur_head_slack r cur prev inc
      (head_add
        (batch_rank (next_inc r inc) (next_prev_gray r inc gc gp)) +
       CurNeed r) Hwf Hrank Hbound) as Hhead.
    rewrite Hg, Hl in Hhead. exact Hhead.
  }
  assert (Hprev_head:
    HeadSlack inc (head_add
      (batch_rank (next_inc r inc) (next_prev_gray r inc gc gp)) +
      PrevNeed r) gp (List.hd 0 prev) lp).
  {
    assert (Hbound:
      if inc then
        head_add
          (batch_rank (next_inc r inc) (next_prev_gray r inc gc gp)) +
          PrevNeed r <= gray cur
      else
        gray cur +
          (head_add
            (batch_rank (next_inc r inc) (next_prev_gray r inc gc gp)) +
           PrevNeed r) < 2 ^ length (List.tl prev)).
    {
      rewrite Hfull_cur, Hg, Hlp.
      exact Hprev_bound.
    }
    pose proof (St_WF_prev_head_slack r cur prev inc
      (head_add
        (batch_rank (next_inc r inc) (next_prev_gray r inc gc gp)) +
       PrevNeed r) Hwf Hbound) as Hhead.
    rewrite Hgp, Hlp in Hhead. exact Hhead.
  }
  split.
  - refine (conj Hcur_shape (conj _ Hr_cur)).
    eapply ReadySlack_of_shape_ready; [exact Hcur_shape| |exact Hcur_head].
    destruct inc; cbn[St_Ready St_of] in Hready |- *; exact Hready.
  - refine (conj Hprev_shape (conj _ Hr_prev)).
    eapply ReadySlack_of_shape_ready; [exact Hprev_shape| |exact Hprev_head].
    unfold St_PrevReady in Hprev.
    destruct inc; cbn[St_Ready St_of negb] in Hprev |- *; exact Hprev.
Qed.

Lemma batch_target_closed_canonical r cur prev inc gc gp:
  batch_next_rank r cur prev inc =
    batch_rank (next_inc r inc) (next_prev_gray r inc gc gp) ->
  let y := batch_target r cur prev inc in
  y = St_of (St_cur y) (St_prev y) (next_inc r inc)
    (Some (batch_rank (next_inc r inc)
      (next_prev_gray r inc gc gp))).
Proof.
  intro Hrank. cbn zeta.
  unfold batch_target. rewrite Hrank.
  unfold next_inc.
  destruct (Nat.even r), inc; reflexivity.
Qed.

Lemma ClosedRep_step x c:
  ClosedRep x c ->
  ClosedNumeric c ->
  exists y,
    embanked_batch (c_rank c) x y /\
    ClosedRep y (c_step c).
Proof.
  destruct c as [inc gc lc gp lp].
  cbn[ClosedRep ClosedNumeric c_rank c_step c_inc c_cur_gray c_cur_len
    c_prev_gray c_prev_len] in *.
  intros [cur [prev [Hx [Hwf [Hready [Hprev [Hg [Hl [Hgp Hlp]]]]]]]]]
    Hnumeric.
  subst x.
  destruct Hnumeric as
    [Hr_cur [Hr_prev [Hk_cur [Hk_prev
      [Hbound_cur [Hbound_prev [Hcur_bound Hprev_bound]]]]]]].
  set (r := batch_rank inc gp) in *.
  set (k := batch_rank (next_inc r inc)
    (next_prev_gray r inc gc gp)) in *.
  destruct (closed_windows r cur prev inc gc lc gp lp
    Hwf Hready Hprev Hg Hl Hgp Hlp
    Hr_cur Hr_prev Hcur_bound Hprev_bound) as [Hcur Hprev_window].
  assert (Hcur0:
    Window cur (negb inc) gc (List.hd 0 cur) lc (CurNeed r) r).
  {
    eapply Window_weaken with (d':=head_add k + CurNeed r);
      [lia|exact Hcur].
  }
  assert (Hprev0:
    Window prev inc gp (List.hd 0 prev) lp (PrevNeed r) r).
  {
    eapply Window_weaken with (d':=head_add k + PrevNeed r);
      [lia|exact Hprev_window].
  }
  assert (Hnext_add:
    Addable k (next_cur_gray r inc gc gp) (next_cur_len r lc lp)).
  {
    unfold next_cur_gray, next_cur_len.
    destruct (Nat.even r); assumption.
  }
  destruct (batch_step r cur prev inc gc (List.hd 0 cur) lc
    gp (List.hd 0 prev) lp Hwf
    (proj1 Hcur) (proj1 Hprev_window)
    (proj1 (proj2 Hcur0)) (proj1 (proj2 Hprev0))
    Hr_cur Hr_prev Hbound_cur Hbound_prev Hnext_add)
    as [y [Hbatch [Hy [Hywf [Hycur Hyprev]]]]].
  pose proof (batch_target_ready r cur prev inc gc (List.hd 0 cur) lc
    gp (List.hd 0 prev) lp Hcur Hprev_window Hk_cur Hk_prev
    Hbound_cur Hbound_prev) as Hyready.
  destruct Hyready as [Hyready Hyprevready].
  rewrite <-Hy in Hyready, Hyprevready.
  exists y. split; [exact Hbatch|].
  exists (St_cur y), (St_prev y).
  refine (conj _ (conj Hywf (conj Hyready (conj Hyprevready _)))).
  - rewrite Hy.
    eapply batch_target_closed_canonical.
    subst k.
    eapply batch_next_rank_window; eassumption.
  - refine (conj _ (conj _ (conj _ _))).
    + exact (shape_gray _ _ _ _ _ Hycur).
    + exact (shape_len _ _ _ _ _ Hycur).
    + exact (shape_gray _ _ _ _ _ Hyprev).
    + exact (shape_len _ _ _ _ _ Hyprev).
Qed.

Inductive ClosedPath: nat -> St -> ClosedFeature -> St -> Prop :=
| ClosedPath_0 x c:
    ClosedPath 0 x c x
| ClosedPath_S n x c y z:
    embanked_batch (c_rank c) x y ->
    ClosedPath n y (c_step c) z ->
    ClosedPath (S n) x c z.

Lemma ClosedPath_run n x c y:
  ClosedPath n x c y -> S2 x -->* S2 y.
Proof.
  intro Hpath. induction Hpath.
  - constructor.
  - eapply evstep_trans.
    + eapply embanked_batch_run, H.
    + exact IHHpath.
Qed.

Definition closed_num c : NumState :=
  (c_inc c, c_cur_gray c, c_prev_gray c).

Lemma closed_num_step c:
  closed_num (c_step c) = num_step (closed_num c).
Proof. destruct c; reflexivity. Qed.


Lemma head_add_le2 r: head_add r <= 2.
Proof. destruct r; cbn[head_add Nat.eqb]; lia. Qed.

Lemma CurNeed_head_bound r:
  CurNeed r + head_add r <= 2.
Proof.
  destruct r as [|[|r]]; cbn[CurNeed head_add Nat.eqb].
  - lia.
  - lia.
  - destruct (Nat.even r); lia.
Qed.

Lemma PrevNeed_bound r: PrevNeed r <= 2.
Proof.
  destruct r; cbn[PrevNeed].
  - lia.
  - destruct (Nat.even r); lia.
Qed.

Lemma cur_total_bound r k:
  head_add k + CurNeed r + head_add r <= 4.
Proof.
  pose proof (head_add_le2 k).
  pose proof (CurNeed_head_bound r). lia.
Qed.

Lemma prev_total_bound r k:
  head_add k + PrevNeed r <= 4.
Proof.
  pose proof (head_add_le2 k).
  pose proof (PrevNeed_bound r). lia.
Qed.

Lemma pow_succ_double l:
  2 ^ S l = 2 * 2 ^ l.
Proof. cbn[Nat.pow]. lia. Qed.

Lemma ClosedNumeric_I low high lhi llo:
  lhi = S llo ->
  2 <= low ->
  high + 2 < 2 ^ llo ->
  let c := mkClosed tp1 low lhi high llo in
  Addable (c_rank c) low lhi ->
  Addable (c_rank c) high llo ->
  Addable (c_rank (c_step c)) low lhi ->
  Addable (c_rank (c_step c)) high llo ->
  ClosedNumeric c.
Proof.
  intros Hl Hlow Hhigh. cbn zeta.
  intros Hr_cur Hr_prev Hk_cur Hk_prev.
  unfold ClosedNumeric.
  cbn[c_rank c_step c_inc c_cur_gray c_cur_len c_prev_gray c_prev_len].
  set (r := ctzS high) in *.
  set (k := batch_rank (next_inc r tp1)
    (next_prev_gray r tp1 low high)) in *.
  refine (conj Hr_cur (conj Hr_prev (conj Hk_cur (conj Hk_prev _)))).
  repeat split.
  - cbn[BoundaryReady]. exact Hlow.
  - cbn[BoundaryReady]. exact Hhigh.
  - rewrite Hl, pow_succ_double.
    change (1 + high * 2 +
      (head_add k + CurNeed r + head_add r) < 2 * 2 ^ llo).
    pose proof (cur_total_bound r k). lia.
  - change (head_add k + PrevNeed r <= low * 2).
    pose proof (prev_total_bound r k). lia.
Qed.

Lemma ClosedNumeric_D high low llo lhi:
  lhi = S llo ->
  2 <= low ->
  high + 2 < 2 ^ llo ->
  let c := mkClosed tp0 high llo low lhi in
  Addable (c_rank c) high llo ->
  Addable (c_rank c) low lhi ->
  Addable (c_rank (c_step c)) high llo ->
  Addable (c_rank (c_step c)) low lhi ->
  ClosedNumeric c.
Proof.
  intros Hl Hlow Hhigh. cbn zeta.
  intros Hr_cur Hr_prev Hk_cur Hk_prev.
  unfold ClosedNumeric.
  cbn[c_rank c_step c_inc c_cur_gray c_cur_len c_prev_gray c_prev_len].
  set (r := ctzS (low - 1)) in *.
  set (k := batch_rank (next_inc r tp0)
    (next_prev_gray r tp0 high low)) in *.
  refine (conj Hr_cur (conj Hr_prev (conj Hk_cur (conj Hk_prev _)))).
  repeat split.
  - cbn[BoundaryReady]. exact Hhigh.
  - cbn[BoundaryReady]. exact Hlow.
  - change (head_add k + CurNeed r + head_add r <= low * 2).
    pose proof (cur_total_bound r k). lia.
  - rewrite Hl, pow_succ_double.
    change (1 + high * 2 + (head_add k + PrevNeed r) < 2 * 2 ^ llo).
    pose proof (prev_total_bound r k). lia.
Qed.

Lemma Addable_0 g l: Addable 0 g l.
Proof. cbn[Addable]. split; [lia|trivial]. Qed.

Lemma Addable_1 g l:
  1 <= g -> 1 <= l -> Addable 1 g l.
Proof.
  intros Hg Hl. unfold Addable. split; [exact Hl|].
  change (1 <= g). exact Hg.
Qed.

Lemma Addable_2r r g l:
  2 + r <= l ->
  2 ^ (1 + r) <= g ->
  Addable (2 + r) g l.
Proof.
  unfold Addable. split; [assumption|].
  change (2 ^ (1 + r) <= g). assumption.
Qed.

Lemma c_step_I_even low high lhi llo r:
  ctzS high = r -> Nat.even r = true ->
  c_step (mkClosed tp1 low lhi high llo) =
    mkClosed tp1 low lhi (S high) llo.
Proof.
  intros Hr Heven.
  unfold c_step, c_rank, batch_rank, next_inc,
    next_cur_gray, next_prev_gray, next_cur_len, next_prev_len.
  cbn[c_inc c_cur_gray c_cur_len c_prev_gray c_prev_len].
  rewrite Hr, Heven. reflexivity.
Qed.

Lemma c_step_I_odd low high lhi llo r:
  ctzS high = r -> Nat.even r = false ->
  c_step (mkClosed tp1 low lhi high llo) =
    mkClosed tp0 high llo (low - 1) lhi.
Proof.
  intros Hr Heven.
  unfold c_step, c_rank, batch_rank, next_inc,
    next_cur_gray, next_prev_gray, next_cur_len, next_prev_len.
  cbn[c_inc c_cur_gray c_cur_len c_prev_gray c_prev_len].
  rewrite Hr, Heven. reflexivity.
Qed.

Lemma c_step_D_even high low llo lhi r:
  ctzS (low - 1) = r -> Nat.even r = true ->
  c_step (mkClosed tp0 high llo low lhi) =
    mkClosed tp0 high llo (low - 1) lhi.
Proof.
  intros Hr Heven.
  unfold c_step, c_rank, batch_rank, next_inc,
    next_cur_gray, next_prev_gray, next_cur_len, next_prev_len.
  cbn[c_inc c_cur_gray c_cur_len c_prev_gray c_prev_len].
  rewrite Hr, Heven. reflexivity.
Qed.

Lemma c_step_D_odd high low llo lhi r:
  ctzS (low - 1) = r -> Nat.even r = false ->
  c_step (mkClosed tp0 high llo low lhi) =
    mkClosed tp1 low lhi (S high) llo.
Proof.
  intros Hr Heven.
  unfold c_step, c_rank, batch_rank, next_inc,
    next_cur_gray, next_prev_gray, next_cur_len, next_prev_len.
  cbn[c_inc c_cur_gray c_cur_len c_prev_gray c_prev_len].
  rewrite Hr, Heven. reflexivity.
Qed.

Definition CycleRank q r := r = 0 \/ r = 1 \/ r = 2 + q.

Lemma CycleRank_addable q r g l:
  CycleRank q r ->
  2 + q <= l ->
  2 ^ (1 + q) <= g ->
  Addable r g l.
Proof.
  intros Hrank Hlen Hgray.
  destruct Hrank as [Hrank|[Hrank|Hrank]]; subst r.
  - apply Addable_0.
  - apply Addable_1; lia.
  - apply Addable_2r; assumption.
Qed.

Lemma ClosedNumeric_I_cycle q low high lhi llo:
  lhi = S llo ->
  2 <= low -> high + 2 < 2 ^ llo ->
  CycleRank q (c_rank (mkClosed tp1 low lhi high llo)) ->
  CycleRank q (c_rank (c_step (mkClosed tp1 low lhi high llo))) ->
  2 + q <= llo ->
  2 ^ (1 + q) <= low ->
  2 ^ (1 + q) <= high ->
  ClosedNumeric (mkClosed tp1 low lhi high llo).
Proof.
  intros Hl Hlow Hhigh Hr Hk Hlen Hglow Hghigh.
  eapply ClosedNumeric_I.
  - exact Hl.
  - exact Hlow.
  - exact Hhigh.
  - eapply CycleRank_addable; [exact Hr|lia|exact Hglow].
  - eapply CycleRank_addable; [exact Hr|exact Hlen|exact Hghigh].
  - eapply CycleRank_addable; [exact Hk|lia|exact Hglow].
  - eapply CycleRank_addable; [exact Hk|exact Hlen|exact Hghigh].
Qed.

Lemma ClosedNumeric_D_cycle q high low llo lhi:
  lhi = S llo ->
  2 <= low -> high + 2 < 2 ^ llo ->
  CycleRank q (c_rank (mkClosed tp0 high llo low lhi)) ->
  CycleRank q (c_rank (c_step (mkClosed tp0 high llo low lhi))) ->
  2 + q <= llo ->
  2 ^ (1 + q) <= low ->
  2 ^ (1 + q) <= high ->
  ClosedNumeric (mkClosed tp0 high llo low lhi).
Proof.
  intros Hl Hlow Hhigh Hr Hk Hlen Hglow Hghigh.
  eapply ClosedNumeric_D.
  - exact Hl.
  - exact Hlow.
  - exact Hhigh.
  - eapply CycleRank_addable; [exact Hr|exact Hlen|exact Hghigh].
  - eapply CycleRank_addable; [exact Hr|lia|exact Hglow].
  - eapply CycleRank_addable; [exact Hk|exact Hlen|exact Hghigh].
  - eapply CycleRank_addable; [exact Hk|lia|exact Hglow].
Qed.

Inductive NumericPath: nat -> ClosedFeature -> ClosedFeature -> Prop :=
| NumericPath_0 c: NumericPath 0 c c
| NumericPath_S n c d:
    ClosedNumeric c ->
    NumericPath n (c_step c) d ->
    NumericPath (S n) c d.

Lemma cycle_numeric_path h v r llo:
  4 <= v -> v <= h -> h + 6 < 2 ^ llo ->
  2 + r <= llo -> 2 ^ (1 + r) <= v - 2 ->
  ctzS h = 1 -> ctzS (S h) = 0 ->
  ctzS (S (S h)) = 2 + r -> ctzS (S (S (S h))) = 0 ->
  ctzS (S (S (S (S h)))) = 1 ->
  ctzS v = 0 -> ctzS (v - 1) = 2 + r ->
  ctzS (v - 2) = 0 -> ctzS (v - 3) = 1 ->
  NumericPath 8 (mkClosed tp1 (v + 2) (S llo) h llo)
    (mkClosed tp1 (v - 2) (S llo) (h + 4) llo).
Proof.
  intros Hv Hvh Hroom Hrlen Hrpow Hh0 Hh1 Hh2 Hh3 Hh4
    Hv0 Hv1 Hv2 Hv3.
  Ltac normalize_gray v :=
    repeat match goal with
    | |- context [v + 2 - 1] => replace (v + 2 - 1) with (v + 1) by lia
    | |- context [v + 1 - 1] => replace (v + 1 - 1) with v by lia
    | |- context [v - 1 - 1] => replace (v - 1 - 1) with (v - 2) by lia
    | |- context [v - 2 - 1] => replace (v - 2 - 1) with (v - 3) by lia
    end.
  Ltac solve_rank v :=
    unfold CycleRank;
    unfold c_step, c_rank;
    repeat progress (
      try unfold batch_rank, next_inc, next_prev_gray;
      cbn[c_rank c_inc c_cur_gray c_prev_gray Nat.even negb];
      normalize_gray v;
      rewrite ?even_add2;
      repeat match goal with
      | H: ctzS ?x = ?y |- context [ctzS ?x] => rewrite H
      | H: Nat.even ?x = ?y |- context [Nat.even ?x] => rewrite H
      end);
    tauto.
  Ltac solve_numeric v r :=
    first [eapply ClosedNumeric_I_cycle with (q:=r)
          | eapply ClosedNumeric_D_cycle with (q:=r)];
    [reflexivity | lia | lia | solve_rank v | solve_rank v |
     assumption | lia | lia].
  econstructor; [solve_numeric v r|].
  rewrite (c_step_I_odd (v + 2) h (S llo) llo 1 Hh0 eq_refl).
  normalize_gray v.
  econstructor; [solve_numeric v r|].
  rewrite (c_step_D_even h (v + 1) llo (S llo) 0
    ltac:(normalize_gray v; exact Hv0) eq_refl).
  normalize_gray v.
  destruct (Nat.even r) eqn:Hpar.
  - econstructor; [solve_numeric v r|].
    rewrite (c_step_D_even h v llo (S llo) (2 + r) Hv1
      ltac:(rewrite even_add2, Hpar; reflexivity)).
    econstructor; [solve_numeric v r|].
    rewrite (c_step_D_even h (v - 1) llo (S llo) 0
      ltac:(normalize_gray v; exact Hv2) eq_refl).
    normalize_gray v.
    econstructor; [solve_numeric v r|].
    rewrite (c_step_D_odd h (v - 2) llo (S llo) 1
      ltac:(normalize_gray v; exact Hv3) eq_refl).
    econstructor; [solve_numeric v r|].
    rewrite (c_step_I_even (v - 2) (S h) (S llo) llo 0 Hh1 eq_refl).
    econstructor; [solve_numeric v r|].
    rewrite (c_step_I_even (v - 2) (S (S h)) (S llo) llo (2 + r) Hh2
      ltac:(rewrite even_add2, Hpar; reflexivity)).
    econstructor; [solve_numeric v r|].
    rewrite (c_step_I_even (v - 2) (S (S (S h))) (S llo) llo 0
      Hh3 eq_refl).
    replace (S (S (S (S h)))) with (h + 4) by lia.
    constructor.
  - econstructor; [solve_numeric v r|].
    rewrite (c_step_D_odd h v llo (S llo) (2 + r) Hv1
      ltac:(rewrite even_add2, Hpar; reflexivity)).
    econstructor; [solve_numeric v r|].
    rewrite (c_step_I_even v (S h) (S llo) llo 0 Hh1 eq_refl).
    econstructor; [solve_numeric v r|].
    rewrite (c_step_I_odd v (S (S h)) (S llo) llo (2 + r) Hh2
      ltac:(rewrite even_add2, Hpar; reflexivity)).
    econstructor; [solve_numeric v r|].
    rewrite (c_step_D_even (S (S h)) (v - 1) llo (S llo) 0
      ltac:(normalize_gray v; exact Hv2) eq_refl).
    normalize_gray v.
    econstructor; [solve_numeric v r|].
    rewrite (c_step_D_odd (S (S h)) (v - 2) llo (S llo) 1
      ltac:(normalize_gray v; exact Hv3) eq_refl).
    econstructor; [solve_numeric v r|].
    rewrite (c_step_I_even (v - 2) (S (S (S h))) (S llo) llo 0
      Hh3 eq_refl).
    replace (S (S (S (S h)))) with (h + 4) by lia.
    constructor.
Qed.


Ltac pow_lia :=
  repeat first [rewrite Nat.pow_add_r in * | cbn[Nat.pow] in *];
  lia.

Definition cap m := 2 ^ (2 * m + 6) - 1.
Definition last_q m := 2 ^ (2 * m + 3) - 2.
Definition high m q := cap m - 2 - 4 * q.

Definition q_feature m q :=
  mkClosed tp1 (4 * q + 2) (S (2 * m + 6))
    (high m q) (2 * m + 6).

Lemma high_ctz m q:
  q <= last_q m -> ctzS (high m (S q)) = 1.
Proof.
  intro Hq. unfold high, cap, last_q in *.
  remember (2 ^ (2 * m + 3)) as p.
  replace (2 ^ (2 * m + 6)) with (8 * p) by (subst p; pow_lia).
  replace (8 * p - 1 - 2 - 4 * S q)
    with (1 + (2 * (2 * p - q - 2)) * 2) by pow_lia.
  rewrite ctzS_1.
  replace (2 * (2 * p - q - 2))
    with ((2 * p - q - 2) * 2) by lia.
  rewrite ctzS_0. reflexivity.
Qed.

Lemma ctzS_pow_sub_q n q:
  q + 1 < 2 ^ n -> ctzS (2 ^ n - q - 2) = ctzS q.
Proof.
  revert q. induction n; intros q Hq.
  - cbn[Nat.pow] in Hq. lia.
  - destruct (mod2 q); subst q.
    + replace (2 ^ S n - a * 2 - 2) with ((2 ^ n - a - 1) * 2)
        by (cbn[Nat.pow] in *; lia).
      rewrite !ctzS_0. reflexivity.
    + replace (2 ^ S n - (1 + a * 2) - 2)
        with (1 + (2 ^ n - a - 2) * 2)
        by (cbn[Nat.pow] in *; lia).
      rewrite !ctzS_1. f_equal. apply IHn.
      cbn[Nat.pow] in Hq. lia.
Qed.

Lemma high_succ1_ctz m q:
  q <= last_q m -> ctzS (S (high m (S q))) = 0.
Proof.
  intro Hq. unfold high, cap, last_q in *.
  remember (2 ^ (2 * m + 3)) as p.
  replace (2 ^ (2 * m + 6)) with (8 * p) by (subst p; pow_lia).
  replace (S (8 * p - 1 - 2 - 4 * S q))
    with ((4 * p - 2 * q - 3) * 2) by pow_lia.
  rewrite ctzS_0. reflexivity.
Qed.

Lemma high_succ2_ctz m q:
  q <= last_q m -> ctzS (S (S (high m (S q)))) = 2 + ctzS q.
Proof.
  intro Hq. unfold high, cap, last_q in *.
  remember (2 ^ (2 * m + 3)) as p.
  replace (2 ^ (2 * m + 6)) with (8 * p) by (subst p; pow_lia).
  replace (S (S (8 * p - 1 - 2 - 4 * S q)))
    with (1 + (4 * p - 2 * q - 3) * 2) by pow_lia.
  rewrite ctzS_1.
  replace (4 * p - 2 * q - 3)
    with (1 + (2 * p - q - 2) * 2) by lia.
  rewrite ctzS_1.
  replace (2 * p) with (2 ^ (2 * m + 4)) by (subst p; pow_lia).
  rewrite ctzS_pow_sub_q; [reflexivity|subst p; pow_lia].
Qed.

Lemma high_succ3_ctz m q:
  q <= last_q m -> ctzS (S (S (S (high m (S q))))) = 0.
Proof.
  intro Hq. unfold high, cap, last_q in *.
  remember (2 ^ (2 * m + 3)) as p.
  replace (2 ^ (2 * m + 6)) with (8 * p) by (subst p; pow_lia).
  replace (S (S (S (8 * p - 1 - 2 - 4 * S q))))
    with ((4 * p - 2 * q - 2) * 2) by pow_lia.
  rewrite ctzS_0. reflexivity.
Qed.

Lemma high_succ4_ctz m q:
  q <= last_q m -> ctzS (S (S (S (S (high m (S q)))))) = 1.
Proof.
  intro Hq. destruct q as [|q].
  - replace (S (S (S (S (high m 1))))) with (cap m - 2)
      by (unfold high, cap; pow_lia).
    unfold cap.
    replace (2 * m + 6) with (S (S (2 * m + 4))) by lia.
    replace (2 ^ S (S (2 * m + 4)) - 1 - 2)
      with (1 + (2 ^ S (2 * m + 4) - 2) * 2) by pow_lia.
    rewrite ctzS_1.
    replace (2 ^ S (2 * m + 4) - 2)
      with ((2 ^ (2 * m + 4) - 1) * 2) by pow_lia.
    rewrite ctzS_0. reflexivity.
  - replace (S (S (S (S (high m (S (S q)))))))
      with (high m (S q)) by (unfold high, cap, last_q in *; pow_lia).
    apply high_ctz. lia.
Qed.

Lemma low_ctz0 q: ctzS (4 * S q) = 0.
Proof.
  replace (4 * S q) with ((2 * S q) * 2) by lia.
  rewrite ctzS_0. reflexivity.
Qed.

Lemma low_ctz_plus1 q: ctzS (4 * S q + 1) = 1.
Proof.
  replace (4 * S q + 1) with (1 + (2 * S q) * 2) by lia.
  rewrite ctzS_1.
  replace (2 * S q) with (S q * 2) by lia.
  rewrite ctzS_0. reflexivity.
Qed.

Lemma low_ctz1 q: ctzS (4 * S q - 1) = 2 + ctzS q.
Proof.
  replace (4 * S q - 1) with (1 + (2 * S q - 1) * 2) by lia.
  rewrite ctzS_1.
  replace (2 * S q - 1) with (1 + q * 2) by lia.
  rewrite ctzS_1. reflexivity.
Qed.

Lemma low_ctz2 q: ctzS (4 * S q - 2) = 0.
Proof.
  replace (4 * S q - 2) with ((2 * S q - 1) * 2) by lia.
  rewrite ctzS_0. reflexivity.
Qed.

Lemma low_ctz3 q: ctzS (4 * S q - 3) = 1.
Proof.
  replace (4 * S q - 3) with (1 + (2 * q) * 2) by lia.
  rewrite ctzS_1.
  replace (2 * q) with (q * 2) by lia.
  rewrite ctzS_0. reflexivity.
Qed.

Lemma pow_ctzS_le_S q: 2 ^ ctzS q <= S q.
Proof.
  pattern q. apply lt_wf_ind. clear q.
  intros q IH. destruct (mod2 q); subst q.
  - rewrite ctzS_0. lia.
  - rewrite ctzS_1. cbn[Nat.pow].
    specialize (IH a ltac:(lia)). lia.
Qed.

Lemma q_bounds m q:
  q <= last_q m ->
  4 <= 4 * S q /\
  4 * S q <= high m (S q) /\
  high m (S q) + 6 < 2 ^ (2 * m + 6) /\
  2 + ctzS q <= 2 * m + 6 /\
  2 ^ (1 + ctzS q) <= 4 * S q - 2.
Proof.
  intro Hq.
  assert (Hctz: ctzS q < 2 * m + 3).
  {
    apply ctzS_lt_pow. unfold last_q in Hq. pow_lia.
  }
  pose proof (pow_ctzS_le_S q).
  unfold high, cap, last_q in *. repeat split; pow_lia.
Qed.

Lemma q_numeric_path m q:
  q <= last_q m ->
  NumericPath 8 (q_feature m (S q)) (q_feature m q).
Proof.
  intro Hq. unfold q_feature.
  destruct (q_bounds m q Hq) as [Hv [Hvh [Hroom [Hrlen Hrpow]]]].
  replace (4 * q + 2) with (4 * S q - 2) by lia.
  replace (high m q) with (high m (S q) + 4)
    by (unfold high, cap, last_q in *; pow_lia).
  eapply cycle_numeric_path; eauto using high_ctz, high_succ1_ctz,
    high_succ2_ctz, high_succ3_ctz, high_succ4_ctz,
    low_ctz0, low_ctz1, low_ctz2, low_ctz3.
Qed.


Definition mid_pow m := 2 ^ (2 * m + 5).

Definition start_feature m :=
  mkClosed tp0 (mid_pow m - 1) (2 * m + 6)
    (mid_pow m - 1) (S (2 * m + 6)).

Definition first_q m := S (last_q m).


Lemma mid_ctz m: ctzS (mid_pow m) = 0.
Proof.
  unfold mid_pow.
  replace (2 * m + 5) with (S (2 * m + 4)) by lia.
  replace (2 ^ S (2 * m + 4)) with (2 ^ (2 * m + 4) * 2)
    by (cbn[Nat.pow]; lia).
  rewrite ctzS_0. reflexivity.
Qed.

Lemma mid_sub2_ctz m: ctzS (mid_pow m - 2) = 0.
Proof.
  unfold mid_pow.
  replace (2 * m + 5) with (S (2 * m + 4)) by lia.
  replace (2 ^ S (2 * m + 4) - 2)
    with ((2 ^ (2 * m + 4) - 1) * 2) by pow_lia.
  rewrite ctzS_0. reflexivity.
Qed.

Lemma mid_sub3_ctz m: ctzS (mid_pow m - 3) = 1.
Proof.
  unfold mid_pow.
  replace (2 * m + 5) with (S (S (2 * m + 3))) by lia.
  replace (2 ^ S (S (2 * m + 3)) - 3)
    with (1 + (2 ^ S (2 * m + 3) - 2) * 2) by pow_lia.
  rewrite ctzS_1.
  replace (2 ^ S (2 * m + 3) - 2)
    with ((2 ^ (2 * m + 3) - 1) * 2) by pow_lia.
  rewrite ctzS_0. reflexivity.
Qed.

Lemma mid_succ_ctz m: ctzS (S (mid_pow m)) = 1.
Proof.
  unfold mid_pow.
  replace (2 * m + 5) with (S (2 * m + 4)) by lia.
  replace (S (2 ^ S (2 * m + 4)))
    with (1 + 2 ^ (2 * m + 4) * 2) by pow_lia.
  rewrite ctzS_1.
  replace (2 * m + 4) with (S (2 * m + 3)) by lia.
  replace (2 ^ S (2 * m + 3)) with (2 ^ (2 * m + 3) * 2)
    by (cbn[Nat.pow]; lia).
  rewrite ctzS_0. reflexivity.
Qed.

Lemma prefix_step0 m:
  c_step (start_feature m) =
    mkClosed tp0 (mid_pow m - 1) (2 * m + 6)
      (mid_pow m - 2) (S (2 * m + 6)).
Proof.
  unfold start_feature.
  rewrite (c_step_D_even (mid_pow m - 1) (mid_pow m - 1)
    (2 * m + 6) (S (2 * m + 6)) 0
    ltac:(replace (mid_pow m - 1 - 1) with (mid_pow m - 2)
      by (unfold mid_pow; pow_lia); apply mid_sub2_ctz) eq_refl).
  f_equal; unfold mid_pow; pow_lia.
Qed.

Lemma prefix_step1 m:
  c_step (mkClosed tp0 (mid_pow m - 1) (2 * m + 6)
    (mid_pow m - 2) (S (2 * m + 6))) =
  mkClosed tp1 (mid_pow m - 2) (S (2 * m + 6))
    (mid_pow m) (2 * m + 6).
Proof.
  rewrite (c_step_D_odd (mid_pow m - 1) (mid_pow m - 2)
    (2 * m + 6) (S (2 * m + 6)) 1
    ltac:(replace (mid_pow m - 2 - 1) with (mid_pow m - 3)
      by (unfold mid_pow; pow_lia); apply mid_sub3_ctz) eq_refl).
  f_equal; unfold mid_pow; pow_lia.
Qed.

Lemma prefix_step2 m:
  c_step (mkClosed tp1 (mid_pow m - 2) (S (2 * m + 6))
    (mid_pow m) (2 * m + 6)) =
  mkClosed tp1 (mid_pow m - 2) (S (2 * m + 6))
    (S (mid_pow m)) (2 * m + 6).
Proof. eapply c_step_I_even; [apply mid_ctz|reflexivity]. Qed.

Lemma prefix_target m:
  mkClosed tp1 (mid_pow m - 2) (S (2 * m + 6))
    (S (mid_pow m)) (2 * m + 6) = q_feature m (first_q m).
Proof.
  unfold q_feature, first_q, last_q, high, cap, mid_pow.
  f_equal; pow_lia.
Qed.

Lemma start_rank m: c_rank (start_feature m) = 0.
Proof.
  unfold start_feature, c_rank, batch_rank.
  cbn[c_inc c_prev_gray].
  replace (mid_pow m - 1 - 1) with (mid_pow m - 2)
    by (unfold mid_pow; pow_lia).
  apply mid_sub2_ctz.
Qed.

Lemma prefix_rank1 m:
  c_rank (mkClosed tp0 (mid_pow m - 1) (2 * m + 6)
    (mid_pow m - 2) (S (2 * m + 6))) = 1.
Proof.
  unfold c_rank, batch_rank. cbn[c_inc c_prev_gray].
  replace (mid_pow m - 2 - 1) with (mid_pow m - 3)
    by (unfold mid_pow; pow_lia).
  apply mid_sub3_ctz.
Qed.

Lemma prefix_rank2 m:
  c_rank (mkClosed tp1 (mid_pow m - 2) (S (2 * m + 6))
    (mid_pow m) (2 * m + 6)) = 0.
Proof. unfold c_rank, batch_rank; cbn[c_inc c_prev_gray]; apply mid_ctz. Qed.

Lemma prefix_rank3 m:
  c_rank (mkClosed tp1 (mid_pow m - 2) (S (2 * m + 6))
    (S (mid_pow m)) (2 * m + 6)) = 1.
Proof. unfold c_rank, batch_rank; cbn[c_inc c_prev_gray]; apply mid_succ_ctz. Qed.

Lemma prefix_numeric0 m: ClosedNumeric (start_feature m).
Proof.
  eapply ClosedNumeric_D.
  - reflexivity.
  - unfold mid_pow. pow_lia.
  - unfold mid_pow. pow_lia.
  - unfold c_rank, batch_rank. cbn[c_inc c_prev_gray].
    replace (mid_pow m - 1 - 1) with (mid_pow m - 2)
      by (unfold mid_pow; pow_lia).
    rewrite mid_sub2_ctz. apply Addable_0.
  - unfold c_rank, batch_rank. cbn[c_inc c_prev_gray].
    replace (mid_pow m - 1 - 1) with (mid_pow m - 2)
      by (unfold mid_pow; pow_lia).
    rewrite mid_sub2_ctz. apply Addable_0.
  - change (Addable (c_rank (c_step (start_feature m)))
      (mid_pow m - 1) (2 * m + 6)).
    rewrite prefix_step0, prefix_rank1. apply Addable_1; unfold mid_pow; pow_lia.
  - change (Addable (c_rank (c_step (start_feature m)))
      (mid_pow m - 1) (S (2 * m + 6))).
    rewrite prefix_step0, prefix_rank1. apply Addable_1; unfold mid_pow; pow_lia.
Qed.

Lemma prefix_numeric1 m:
  ClosedNumeric (mkClosed tp0 (mid_pow m - 1) (2 * m + 6)
    (mid_pow m - 2) (S (2 * m + 6))).
Proof.
  eapply ClosedNumeric_D.
  - reflexivity.
  - unfold mid_pow. pow_lia.
  - unfold mid_pow. pow_lia.
  - rewrite prefix_rank1. apply Addable_1; unfold mid_pow; pow_lia.
  - rewrite prefix_rank1. apply Addable_1; unfold mid_pow; pow_lia.
  - rewrite prefix_step1, prefix_rank2. apply Addable_0.
  - rewrite prefix_step1, prefix_rank2. apply Addable_0.
Qed.

Lemma prefix_numeric2 m:
  ClosedNumeric (mkClosed tp1 (mid_pow m - 2) (S (2 * m + 6))
    (mid_pow m) (2 * m + 6)).
Proof.
  eapply ClosedNumeric_I.
  - reflexivity.
  - unfold mid_pow. pow_lia.
  - unfold mid_pow. pow_lia.
  - rewrite prefix_rank2. apply Addable_0.
  - rewrite prefix_rank2. apply Addable_0.
  - rewrite prefix_step2, prefix_rank3. apply Addable_1; unfold mid_pow; pow_lia.
  - rewrite prefix_step2, prefix_rank3. apply Addable_1; unfold mid_pow; pow_lia.
Qed.

Lemma prefix_numeric_path m:
  NumericPath 3 (start_feature m) (q_feature m (first_q m)).
Proof.
  econstructor; [apply prefix_numeric0|]. rewrite prefix_step0.
  econstructor; [apply prefix_numeric1|]. rewrite prefix_step1.
  econstructor; [apply prefix_numeric2|]. rewrite prefix_step2, prefix_target.
  constructor.
Qed.

Definition pre_feature m :=
  mkClosed tp0 (cap m - 2) (2 * m + 6) 1 (S (2 * m + 6)).

Lemma cap_sub2_ctz m: ctzS (cap m - 2) = 1.
Proof.
  unfold cap.
  replace (2 * m + 6) with (S (S (2 * m + 4))) by lia.
  replace (2 ^ S (S (2 * m + 4)) - 1 - 2)
    with (1 + (2 ^ S (2 * m + 4) - 2) * 2) by pow_lia.
  rewrite ctzS_1.
  replace (2 ^ S (2 * m + 4) - 2)
    with ((2 ^ (2 * m + 4) - 1) * 2) by pow_lia.
  rewrite ctzS_0. reflexivity.
Qed.

Lemma q0_rank m: c_rank (q_feature m 0) = 1.
Proof.
  unfold q_feature, c_rank, batch_rank, high.
  cbn[c_inc c_prev_gray Nat.mul Nat.add].
  rewrite Nat.sub_0_r. apply cap_sub2_ctz.
Qed.

Lemma q0_step_raw m:
  c_step (mkClosed tp1 2 (S (2 * m + 6))
    (cap m - 2) (2 * m + 6)) = pre_feature m.
Proof.
  unfold pre_feature.
  rewrite (c_step_I_odd 2 (cap m - 2) (S (2 * m + 6))
    (2 * m + 6) 1 (cap_sub2_ctz m) eq_refl).
  reflexivity.
Qed.

Lemma q0_step m: c_step (q_feature m 0) = pre_feature m.
Proof.
  unfold q_feature, high. cbn[Nat.mul Nat.add]. rewrite Nat.sub_0_r.
  change (c_step (mkClosed tp1 2 (S (2 * m + 6))
    (cap m - 2) (2 * m + 6)) =
    pre_feature m).
  apply q0_step_raw.
Qed.

Lemma pre_rank m: c_rank (pre_feature m) = 0.
Proof. unfold pre_feature, c_rank, batch_rank; reflexivity. Qed.

Lemma q0_numeric m: ClosedNumeric (q_feature m 0).
Proof.
  unfold q_feature, high. cbn[Nat.mul Nat.add]. rewrite Nat.sub_0_r.
  eapply ClosedNumeric_I.
  - reflexivity.
  - lia.
  - unfold cap.
    replace (m + (m + 0) + 6) with (2 * m + 6) by lia. pow_lia.
  - unfold c_rank, batch_rank. cbn[c_inc c_prev_gray].
    rewrite cap_sub2_ctz. apply Addable_1; lia.
  - unfold c_rank, batch_rank. cbn[c_inc c_prev_gray].
    rewrite cap_sub2_ctz. apply Addable_1; [unfold cap; pow_lia|lia].
  - replace (m + (m + 0) + 6) with (2 * m + 6) by lia.
    rewrite q0_step_raw, pre_rank. apply Addable_0.
  - replace (m + (m + 0) + 6) with (2 * m + 6) by lia.
    rewrite q0_step_raw, pre_rank. apply Addable_0.
Qed.

Lemma q0_to_pre x m:
  ClosedRep x (q_feature m 0) ->
  exists y,
    embanked_batch 1 x y /\
    ClosedRep y (pre_feature m).
Proof.
  intro Hrep.
  destruct (ClosedRep_step x (q_feature m 0) Hrep (q0_numeric m))
    as [y [Hbatch Hy]].
  exists y. split.
  - rewrite <- (q0_rank m). exact Hbatch.
  - rewrite q0_step in Hy. exact Hy.
Qed.

Definition OpenRep x inc gc lc gp lp :=
  exists cur prev hc hp,
    x = St_of cur prev inc None /\
    St_WF x /\
    Shape cur (negb inc) gc hc lc /\
    Shape prev inc gp hp lp.

Definition source_open m x :=
  OpenRep x tp1 0 (S (2 * m + 6)) (cap m - 2) (2 * m + 6).

Lemma pre_to_source_open x m:
  ClosedRep x (pre_feature m) ->
  exists y,
    embanked x y /\
    source_open m y /\
    PairLadd true [1; 1] [] x y.
Proof.
  unfold pre_feature, ClosedRep.
  intros [cur [prev [Hx [Hwf [Hready [Hprev [Hg [Hl [Hgp Hlp]]]]]]]]].
  subst x.
  assert (Hrank:
    c_rank (mkClosed tp0 (cap m - 2) (2 * m + 6)
      1 (S (2 * m + 6))) = 0).
  { apply pre_rank. }
  rewrite Hrank in Hwf, Hready, Hprev.
  cbn[c_inc c_cur_gray c_cur_len c_prev_gray c_prev_len]
    in Hwf, Hready, Hprev, Hg, Hl, Hgp, Hlp.
  assert (Hsafe:
    St_NextSafe (St_of cur prev tp0 (Some (c_rank
      (mkClosed tp0 (cap m - 2) (2 * m + 6) 1 (S (2 * m + 6))))))).
  {
    rewrite Hrank.
    change (2 <= gray prev).
    pose proof (prev_full_gray 0 cur prev tp0 Hprev) as Hfull.
    rewrite Hgp in Hfull. cbn[c_prev_gray TGray] in Hfull.
    rewrite Hfull. cbv[TGray]. lia.
  }
  pose proof (St_next_valid _ Hwf Hready Hsafe) as Hstep.
  exists (St_next (St_of cur prev tp0 (Some (c_rank
    (mkClosed tp0 (cap m - 2) (2 * m + 6) 1 (S (2 * m + 6))))))).
  split; [exact Hstep|]. split.
  rewrite Hrank. cbn[St_next St_of].
  assert (Hprev_shape:
    Shape prev tp0 1 (List.hd 0 prev) (S (2 * m + 6))).
  { eapply prev_shape; eassumption. }
  assert (Hcur_shape:
    Shape cur tp1 (cap m - 2) (List.hd 0 cur) (2 * m + 6)).
  { exact (current_shape cur prev tp0 (Some 0)
      (cap m - 2) (2 * m + 6) Hready Hg Hl). }
  unfold source_open, OpenRep.
  exists (prev +l lsum (gray prev - 2) 2), cur.
  exists (S (List.hd 0 prev)), (List.hd 0 cur).
  split; [reflexivity|].
  split.
  - eapply St_valid_step_target_WF, Hstep.
  - split.
    + change (Shape (prev +l lsum (gray prev - 2) 2)
        tp0 (1 - 1) (S (List.hd 0 prev)) (S (2 * m + 6))).
      eapply Shape_pred2.
      * exact Hprev_shape.
      * eapply Shape_nonempty; [exact Hprev_shape|].
        left. discriminate.
      * pose proof (prev_full_gray 0 cur prev tp0 Hprev) as Hfull.
        rewrite Hgp in Hfull. cbv[c_prev_gray TGray] in Hfull.
        rewrite Hfull. lia.
    + exact Hcur_shape.
  - unfold PairLadd. rewrite Hrank. cbn[St_next St_of St_cur St_prev].
    pose proof (prev_full_gray 0 cur prev tp0 Hprev) as Hfull.
    rewrite Hgp in Hfull. cbn[c_prev_gray TGray] in Hfull.
    rewrite Hfull. replace (TGray tp0 1) with 2 by reflexivity.
    cbn[lsum]. replace (2 - 2) with 0 by lia.
    replace (ctzS 0) with 0 by reflexivity.
    replace (ctzS 1) with 1 by reflexivity.
    cbn[Helper.lpow app ladd]. rewrite ladd_nil_r. tauto.
Qed.

Import ListNotations.


Definition coeff (xs : list nat) i := nth i xs 0.

Lemma coeff_ladd xs ys i:
  coeff (xs +l ys) i = coeff xs i + coeff ys i.
Proof.
  revert ys i. induction xs as [|x xs IH]; intros ys i.
  - cbn[coeff ladd]. destruct ys; destruct i; reflexivity.
  - destruct ys as [|y ys], i as [|i]; cbn[coeff ladd nth]; try lia.
    apply IH.
Qed.

Lemma coeff_L1 k i:
  coeff (L1 k) i = if Nat.eqb i k then 1 else 0.
Proof.
  revert i. induction k as [|k IH]; intros [|i]; cbn[coeff L1 nth Nat.eqb].
  - reflexivity.
  - destruct i; reflexivity.
  - reflexivity.
  - apply IH.
Qed.

Lemma coeff_lmul2 xs k i:
  coeff (xs +l lmul2 (L1 k)) i =
    coeff xs i + 2 * (if Nat.eqb i k then 1 else 0).
Proof.
  unfold lmul2. rewrite !coeff_ladd, !coeff_L1.
  destruct (Nat.eqb i k); lia.
Qed.

Definition Add2At k xs ys :=
  length xs = length ys /\
  forall i,
    coeff ys i = coeff xs i + 2 * (if Nat.eqb i k then 1 else 0).

Lemma Add2At_lmul2 xs k:
  k < length xs -> Add2At k xs (xs +l lmul2 (L1 k)).
Proof.
  intro Hk. split.
  - symmetry. apply length_lmul2. exact Hk.
  - intro i. apply coeff_lmul2.
Qed.

Lemma Add2At_index_lt k xs ys:
  Add2At k xs ys -> k < length xs.
Proof.
  intros [Hlen Hcoeff].
  destruct (lt_dec k (length xs)); [assumption|].
  specialize (Hcoeff k). rewrite Nat.eqb_refl in Hcoeff.
  unfold coeff in Hcoeff.
  rewrite !nth_overflow in Hcoeff by lia. lia.
Qed.

Lemma coeff_ext xs ys:
  length xs = length ys ->
  (forall i, coeff xs i = coeff ys i) ->
  xs = ys.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys] Hlen Hcoeff;
    cbn[length] in Hlen; try lia; [reflexivity|].
  f_equal.
  - exact (Hcoeff 0).
  - apply IH; [lia|]. intro i. exact (Hcoeff (S i)).
Qed.

Lemma Add2At_eq k xs ys:
  Add2At k xs ys -> ys = xs +l lmul2 (L1 k).
Proof.
  intros [Hlen Hcoeff]. apply coeff_ext.
  - rewrite <-Hlen. symmetry. apply length_lmul2.
    eapply Add2At_index_lt. split; eassumption.
  - intro i. rewrite coeff_lmul2. apply Hcoeff.
Qed.

Fixpoint pow_counts n :=
match n with
| 0 => [1]
| S n => 2 ^ S n :: pow_counts n
end.

Fixpoint pow_counts_dup n :=
match n with
| 0 => [1; 1]
| S n => 2 ^ S n :: pow_counts_dup n
end.

Lemma ctzS_pow_sub1 n: ctzS (2 ^ n - 1) = n.
Proof.
  induction n.
  - reflexivity.
  - replace (2 ^ S n - 1) with (1 + (2 ^ n - 1) * 2)
      by (cbn[Nat.pow]; lia).
    rewrite ctzS_1, IHn. reflexivity.
Qed.


Lemma ladd_all0_S_one n:
  (Helper.lpow [0] (S n) ++ [1]) +l [1] = 1 :: L1 n.
Proof.
  induction n.
  - reflexivity.
  - cbn[L1 ladd]. rewrite L1_fold. reflexivity.
Qed.

Lemma lsum_even_pair b:
  lsum (b * 2) 2 = 1 :: L1 (ctzS b).
Proof.
  rewrite lsum_S', lsum_1.
  replace (b * 2 + 1) with (1 + b * 2) by lia.
  rewrite ctzS_1, ctzS_0. apply ladd_all0_S_one.
Qed.

Lemma lsum_odd_pair b:
  lsum (1 + b * 2) 2 = 1 :: L1 (ctzS b).
Proof.
  rewrite lsum_S', lsum_1.
  replace (1 + b * 2 + 1) with (S b * 2) by lia.
  rewrite ctzS_0, ctzS_1.
  repeat rewrite L1_fold.
  change (L1 0 +l L1 (S (ctzS b)) = 1 :: L1 (ctzS b)).
  cbn[L1 ladd]. reflexivity.
Qed.

Lemma lsum_even_pairs a b:
  lsum (a * 2) (2 * S b) = S b :: lsum a (S b).
Proof.
  revert a. induction b; intro a.
  - replace (2 * S 0) with 2 by lia.
    rewrite lsum_even_pair, lsum_1. reflexivity.
  - replace (2 * S (S b)) with (2 + 2 * S b) by lia.
    rewrite lsum_add, lsum_even_pair.
    replace (a * 2 + 2) with (S a * 2) by lia.
    rewrite IHb. cbn[ladd lsum]. repeat rewrite L1_fold. flia.
Qed.

Lemma lsum_odd_pairs a b:
  lsum (1 + a * 2) (2 * S b) = S b :: lsum a (S b).
Proof.
  revert a. induction b; intro a.
  - replace (2 * S 0) with 2 by lia.
    rewrite lsum_odd_pair, lsum_1. reflexivity.
  - replace (2 * S (S b)) with (2 + 2 * S b) by lia.
    rewrite lsum_add.
    rewrite lsum_odd_pair.
    replace (1 + a * 2 + 2) with (1 + S a * 2) by lia.
    rewrite IHb. cbn[ladd lsum]. repeat rewrite L1_fold. flia.
Qed.

Lemma lsum_pow_pred_cycle n:
  lsum (2 ^ n - 1) (2 ^ n) = lsum 0 (2 ^ n).
Proof.
  induction n.
  - reflexivity.
  - cbn[Nat.pow].
    replace (2 * 2 ^ n - 1) with (1 + (2 ^ n - 1) * 2)
      by lia.
    replace (2 * 2 ^ n) with (2 * S (2 ^ n - 1))
      by lia.
    rewrite lsum_odd_pairs.
    replace (S (2 ^ n - 1)) with (2 ^ n)
      by lia.
    rewrite IHn.
    replace (2 * 2 ^ n) with (2 * S (2 ^ n - 1))
      by lia.
    change (2 ^ n :: lsum 0 (2 ^ n) = lsum (0 * 2) (2 * S (2 ^ n - 1))).
    rewrite lsum_even_pairs. flia.
Qed.

Lemma lsum_0_double_pos b:
  b <> 0 -> lsum 0 (b * 2) = b :: lsum 0 b.
Proof.
  destruct b.
  - congruence.
  - intro Hnz. replace (S b * 2) with (2 * S b) by lia.
    change (lsum (0 * 2) (2 * S b) = S b :: lsum 0 (S b)).
    apply lsum_even_pairs.
Qed.

Lemma lsum_0_pow_succ_sub1 n:
  lsum 0 (2 ^ S n - 1) = pow_counts n.
Proof.
  induction n.
  - reflexivity.
  - replace (2 ^ S (S n) - 1) with ((2 ^ S n - 1) * 2 + 1)
      by (repeat rewrite Nat.pow_succ_r; lia).
    rewrite lsum_add, lsum_0_double_pos by (cbn[Nat.pow]; lia).
    rewrite IHn.
    replace (0 + (2 ^ S n - 1) * 2) with ((2 ^ S n - 1) * 2) by lia.
    rewrite lsum_1, ctzS_0. cbn[pow_counts L1 ladd].
    rewrite ladd_nil_r. f_equal. lia.
Qed.

Lemma pow_counts_dup_eq n:
  pow_counts n +l L1 (S n) = pow_counts_dup n.
Proof.
  induction n.
  - reflexivity.
  - cbn[pow_counts pow_counts_dup L1 ladd]. f_equal; [lia|exact IHn].
Qed.

Lemma lsum_0_pow_succ n:
  lsum 0 (2 ^ S n) = pow_counts_dup n.
Proof.
  replace (2 ^ S n) with (2 ^ S n - 1 + 1) at 1
    by lia.
  rewrite lsum_add, lsum_0_pow_succ_sub1.
  replace (0 + (2 ^ S n - 1)) with (2 ^ S n - 1) by lia.
  rewrite lsum_1, ctzS_pow_sub1. apply pow_counts_dup_eq.
Qed.

Lemma lsum_pow_full n:
  lsum (2 ^ S n - 1) (2 ^ S n) = pow_counts_dup n.
Proof. rewrite lsum_pow_pred_cycle. apply lsum_0_pow_succ. Qed.


Lemma HD_Add2_shift src dst src' dst' i:
  HD src dst ->
  HD src' dst' ->
  Add2At (S i) src src' ->
  Add2At i dst dst'.
Proof.
  intros Hhd Hhd' Hadd.
  pose proof (Add2At_index_lt _ _ _ Hadd) as Hindex.
  pose proof (Add2At_eq _ _ _ Hadd) as Heq.
  destruct Hhd as [a xs dst Hdst Hrun Hg Htp Hwf Hlen].
  destruct Hhd' as [a' xs' dst' Hdst' Hrun' Hg' Htp' Hwf' Hlen'].
  unfold lmul2 in Heq.
  cbn[L1 ladd] in Heq.
  inversion Heq; subst xs'.
  replace a' with a in * by lia.
  repeat rewrite gray_L1_2 in *.
  subst dst dst'.
  repeat rewrite Nat.add_0_r in *.
  match goal with
  | |- Add2At i ?before ?after =>
      assert (Hafter: after = before +l lmul2 (L1 i))
  end.
  {
    unfold lmul2. repeat rewrite ladd_assoc.
    ladd_swaps (L1 i). reflexivity.
  }
  rewrite Hafter.
  apply Add2At_lmul2.
  cbn[length] in Hindex. lia.
Qed.

Lemma HZI_Add2_shift src dst src' dst' i:
  HZI src dst ->
  HZI src' dst' ->
  Add2At (S i) src src' ->
  Add2At i dst dst'.
Proof.
  intros Hzi Hzi' Hadd.
  pose proof (Add2At_index_lt _ _ _ Hadd) as Hindex.
  pose proof (Add2At_eq _ _ _ Hadd) as Heq.
  destruct Hzi as [a xs dst Hdst Hrun Hg Htp Hwf Hlen].
  destruct Hzi' as [a' xs' dst' Hdst' Hrun' Hg' Htp' Hwf' Hlen'].
  unfold lmul2 in Heq.
  cbn[L1 ladd] in Heq.
  inversion Heq; subst xs'.
  replace a' with a in * by lia.
  assert (Hitail: i < length xs) by (cbn[length] in Hindex; lia).
  pose proof (length_lmul2 xs i Hitail) as Hsame.
  unfold lmul2 in Hsame.
  rewrite Hsame in *.
  subst dst dst'.
  repeat rewrite Nat.add_0_r in *.
  match goal with
  | |- Add2At i ?before ?after =>
      assert (Hafter: after = before +l lmul2 (L1 i))
  end.
  {
    unfold lmul2. repeat rewrite ladd_assoc.
    ladd_swaps (L1 i). reflexivity.
  }
  rewrite Hafter. apply Add2At_lmul2.
  cbn[length] in Hindex. lia.
Qed.

Lemma WF'_lmul2 xs i:
  WF' xs ->
  i < length xs ->
  WF' (xs +l lmul2 (L1 i)).
Proof.
  intros Hwf. revert i.
  induction Hwf as [a|a xs Ha Hwf IH]; intros [|i] Hi.
  - rewrite ladd_lmul2_0. constructor.
  - cbn[length] in Hi. lia.
  - rewrite ladd_lmul2_0.
    constructor; [lia|exact Hwf].
  - rewrite ladd_lmul2_S.
    constructor; [exact Ha|]. apply IH. cbn[length] in Hi. lia.
Qed.

Definition HDReady xs :=
  exists a tail,
    xs = a :: tail /\
    WF' xs /\
    a <= 1 + gray tail < 2 ^ length tail /\
    tp xs = tp1.

Definition HZIReady xs :=
  exists a tail,
    xs = a * 2 :: tail /\
    WF' xs /\ WF' tail /\
    gray tail = 0 /\
    a * 2 <= 2 ^ length tail * 3.

Lemma HDReady_spec xs:
  HDReady xs -> exists ys, HD xs ys.
Proof.
  intros [a [tail [-> [Hwf [Hbound Htp]]]]].
  destruct tail as [|b tail].
  - cbn[gray length Nat.pow] in Hbound. lia.
  - inversion Hwf; subst.
    eapply HD_spec; [apply WF'_WF; eassumption|exact Hbound|exact Htp].
Qed.

Lemma HZIReady_spec xs:
  HZIReady xs -> exists ys, HZI xs ys.
Proof.
  intros [a [tail [-> [_ [Hwf [Hgray Hbound]]]]]].
  eapply HZI_spec; eassumption.
Qed.

Lemma HD_exact a tail dst:
  WF tail ->
  a <= 1 + gray tail < 2 ^ length tail ->
  tp (a :: tail) = tp1 ->
  dst = tail +l L1 (ctzS (gray tail)) +l
    lsum (1 + gray tail - a) a ->
  HD (a :: tail) dst.
Proof.
  intros Hwf Hbound Htp ->.
  destruct (HD_spec a tail Hwf Hbound Htp) as [ys Hhd].
  replace (tail +l L1 (ctzS (gray tail)) +l
    lsum (1 + gray tail - a) a) with ys.
  - exact Hhd.
  - inversion Hhd; subst. rewrite <-L1_fold. reflexivity.
Qed.

Lemma HZI_exact a tail dst:
  WF' tail ->
  gray tail = 0 ->
  a * 2 <= 2 ^ length tail * 3 ->
  dst = tail +l (Helper.lpow [0] (length tail - 1) ++ [1; 0; 0]) +l
    lsum (2 ^ length tail - 1) (a * 2) ->
  HZI (a * 2 :: tail) dst.
Proof.
  intros Hwf Hgray Hbound ->.
  destruct (HZI_spec a tail Hwf Hgray Hbound) as [ys Hhzi].
  replace (tail +l (Helper.lpow [0] (length tail - 1) ++ [1; 0; 0]) +l
    lsum (2 ^ length tail - 1) (a * 2)) with ys.
  - exact Hhzi.
  - inversion Hhzi; subst. reflexivity.
Qed.

Lemma HDReady_shift xs ys i:
  HDReady xs ->
  Add2At (S i) xs ys ->
  HDReady ys.
Proof.
  intros [a [tail [-> [Hwf [Hbound Htp]]]]] Hadd.
  pose proof (Add2At_index_lt _ _ _ Hadd) as Hi.
  assert (Hparts: a <> 0 /\ WF' tail).
  {
    inversion Hwf; subst.
    - cbn[length] in Hi. lia.
    - split; assumption.
  }
  destruct Hparts as [Ha Htail].
  pose proof (Add2At_eq _ _ _ Hadd) as ->.
  rewrite ladd_lmul2_S.
  exists a, (tail +l lmul2 (L1 i)). split; [reflexivity|].
  split.
  - constructor; [exact Ha|]. apply WF'_lmul2; [exact Htail|].
    cbn[length] in Hi. lia.
  - split.
    + rewrite gray_lmul2, length_lmul2
        by (cbn[length] in Hi; lia).
      exact Hbound.
    + rewrite <-ladd_lmul2_S.
      rewrite tp_lmul2. exact Htp.
Qed.

Lemma HZIReady_shift xs ys i:
  HZIReady xs ->
  Add2At (S i) xs ys ->
  HZIReady ys.
Proof.
  intros [a [tail [-> [Hfull [Hwf [Hgray Hbound]]]]]] Hadd.
  pose proof (Add2At_index_lt _ _ _ Hadd) as Hi.
  assert (Ha: a * 2 <> 0).
  {
    inversion Hfull; subst.
    - cbn[length] in Hi. lia.
    - assumption.
  }
  pose proof (Add2At_eq _ _ _ Hadd) as ->.
  rewrite ladd_lmul2_S.
  exists a, (tail +l lmul2 (L1 i)). split; [reflexivity|].
  split.
  - constructor; [exact Ha|].
    apply WF'_lmul2; [exact Hwf|]. cbn[length] in Hi. lia.
  - split.
    + apply WF'_lmul2; [exact Hwf|]. cbn[length] in Hi. lia.
    + split.
      * rewrite gray_lmul2. exact Hgray.
      * rewrite length_lmul2 by (cbn[length] in Hi; lia). exact Hbound.
Qed.

Inductive HZKind := HZNextHD | HZNextHZI.

Record HZSt := mkHZSt {
  hz_cur : list nat;
  hz_prev : list nat;
  hz_kind : HZKind;
  hz_rank : nat
}.

Definition HZS x := S1 (hz_cur x) 0.

Inductive HZ_WF : HZSt -> Prop :=
| HZ_WF_HZI a b c i:
    HD a b ->
    HZI b c ->
    Add2At i a c ->
    HZ_WF (mkHZSt c b HZNextHD i)
| HZ_WF_HD a b c i:
    HZI a b ->
    HD b c ->
    Add2At i a c ->
    HZ_WF (mkHZSt c b HZNextHZI i).

Inductive HZ_valid_step : HZSt -> HZSt -> Prop :=
| HZ_valid_HD a b c d i:
    HD a b ->
    HZI b c ->
    Add2At (S i) a c ->
    HD c d ->
    HZ_valid_step
      (mkHZSt c b HZNextHD (S i))
      (mkHZSt d c HZNextHZI i)
| HZ_valid_HZI a b c d i:
    HZI a b ->
    HD b c ->
    Add2At (S i) a c ->
    HZI c d ->
    HZ_valid_step
      (mkHZSt c b HZNextHZI (S i))
      (mkHZSt d c HZNextHD i).

Lemma HZ_valid_source_WF x y:
  HZ_valid_step x y -> HZ_WF x.
Proof.
  intros Hstep. destruct Hstep.
  - eapply HZ_WF_HZI; eassumption.
  - eapply HZ_WF_HD; eassumption.
Qed.

Lemma HZ_valid_target_WF x y:
  HZ_valid_step x y -> HZ_WF y.
Proof.
  intros Hstep. destruct Hstep.
  - eapply HZ_WF_HD; [exact H0|exact H2|].
    eapply HD_Add2_shift; eassumption.
  - eapply HZ_WF_HZI; [exact H0|exact H2|].
    eapply HZI_Add2_shift; eassumption.
Qed.

Definition HZReady x :=
  match hz_kind x with
  | HZNextHD => exists y, HD (hz_cur x) y
  | HZNextHZI => exists y, HZI (hz_cur x) y
  end.

Definition HZSafe x :=
  match hz_kind x with
  | HZNextHD => HDReady (hz_cur x) /\ HZIReady (hz_prev x)
  | HZNextHZI => HZIReady (hz_cur x) /\ HDReady (hz_prev x)
  end.

Lemma HZSafe_ready x:
  HZSafe x -> HZReady x.
Proof.
  destruct x as [cur prev [|] rank]; cbn[HZSafe HZReady hz_kind hz_cur hz_prev].
  - intros [Hready _]. apply HDReady_spec, Hready.
  - intros [Hready _]. apply HZIReady_spec, Hready.
Qed.

Lemma HZSafe_step x y i:
  HZSafe x ->
  hz_rank y = S i ->
  HZ_valid_step x y ->
  HZSafe y.
Proof.
  intros Hsafe Hrank Hstep. destruct Hstep.
  - cbn[HZSafe hz_kind hz_cur hz_prev hz_rank] in Hsafe, Hrank |- *.
    subst i0. destruct Hsafe as [Hcur Hprev]. split; [|exact Hcur].
    eapply HZIReady_shift; [exact Hprev|].
    eapply HD_Add2_shift; eassumption.
  - cbn[HZSafe hz_kind hz_cur hz_prev hz_rank] in Hsafe, Hrank |- *.
    subst i0. destruct Hsafe as [Hcur Hprev]. split; [|exact Hcur].
    eapply HDReady_shift; [exact Hprev|].
    eapply HZI_Add2_shift; eassumption.
Qed.

Lemma HZ_WF_ready_step x i:
  HZ_WF x ->
  hz_rank x = S i ->
  HZReady x ->
  exists y, HZ_valid_step x y.
Proof.
  intros Hwf Hrank Hready. destruct Hwf.
  - cbn[hz_rank hz_kind hz_cur HZReady] in Hrank, Hready.
    subst i0. destruct Hready as [d Hnext].
    exists (mkHZSt d c HZNextHZI i).
    econstructor; eassumption.
  - cbn[hz_rank hz_kind hz_cur HZReady] in Hrank, Hready.
    subst i0. destruct Hready as [d Hnext].
    exists (mkHZSt d c HZNextHD i).
    econstructor; eassumption.
Qed.

Lemma HZ_valid_run x y:
  HZ_valid_step x y -> HZS x -->* HZS y.
Proof.
  intros Hstep. destruct Hstep; cbn[HZS hz_cur].
  - inversion H2; assumption.
  - inversion H2; assumption.
Qed.

Lemma HZ_valid_pair x y z i:
  hz_rank x = S (S i) ->
  HZ_valid_step x y ->
  HZ_valid_step y z ->
  hz_rank z = i /\
  hz_kind z = hz_kind x /\
  Add2At i (hz_cur x) (hz_cur z).
Proof.
  intros Hrank Hxy Hyz. destruct Hxy.
  - cbn[hz_rank] in Hrank. inversion Hrank; subst i0.
    inversion Hyz; subst; try congruence.
    split; [reflexivity|]. split; [reflexivity|].
    eapply HZI_Add2_shift; eassumption.
  - cbn[hz_rank] in Hrank. inversion Hrank; subst i0.
    inversion Hyz; subst; try congruence.
    split; [reflexivity|]. split; [reflexivity|].
    eapply HD_Add2_shift; eassumption.
Qed.

Inductive HZPath : nat -> HZSt -> HZSt -> Prop :=
| HZPath_0 x: HZPath 0 x x
| HZPath_S n x y z:
    HZ_valid_step x y ->
    HZPath n y z ->
    HZPath (S n) x z.

Fixpoint HZReadies n x :=
  match n with
  | 0 => True
  | S n => HZReady x /\
      forall y, HZ_valid_step x y -> HZReadies n y
  end.

Lemma HZReadies_of_safe n x:
  hz_rank x = n ->
  HZ_WF x ->
  HZSafe x ->
  HZReadies n x.
Proof.
  revert x. induction n as [|n IH]; intros x Hrank Hwf Hsafe.
  - exact I.
  - cbn[HZReadies]. split; [apply HZSafe_ready; exact Hsafe|].
    intros y Hstep.
    assert (Hyrank: hz_rank y = n).
    { destruct Hstep; cbn[hz_rank] in *; lia. }
    destruct n as [|n].
    + exact I.
    + eapply IH.
      * exact Hyrank.
      * eapply HZ_valid_target_WF, Hstep.
      * eapply HZSafe_step; eassumption.
Qed.

Inductive EvenAdds : nat -> list nat -> list nat -> Prop :=
| EvenAdds_0 xs: EvenAdds 0 xs xs
| EvenAdds_S k xs mid ys:
    Add2At (2 * k) xs mid ->
    EvenAdds k mid ys ->
    EvenAdds (S k) xs ys.

Definition even_hit k i := andb (Nat.even i) (Nat.ltb i (2 * k)).

Lemma EvenAdds_length k xs ys:
  EvenAdds k xs ys -> length xs = length ys.
Proof.
  intro H. induction H; [reflexivity|].
  destruct H as [Hlen _]. lia.
Qed.

Lemma EvenAdds_coeff k xs ys:
  EvenAdds k xs ys ->
  forall i,
    coeff ys i = coeff xs i + 2 * (if even_hit k i then 1 else 0).
Proof.
  intro Hadds. induction Hadds as [xs|k xs mid ys Hadd Htail IH]; intro i.
  - assert (even_hit 0 i = tp0).
    { unfold even_hit. cbn[Nat.mul]. destruct (Nat.even i); reflexivity. }
    rewrite H. lia.
  - destruct Hadd as [_ Hadd]. rewrite IH, Hadd.
    unfold even_hit.
    destruct (Nat.eqb_spec i (2 * k));
      destruct (Nat.even i) eqn:Heven;
      destruct (Nat.ltb i (2 * k)) eqn:Hlt;
      destruct (Nat.ltb i (2 * S k)) eqn:HltS;
      cbn; try rewrite Nat.eqb_refl;
      try rewrite Nat.eqb_neq by assumption; try lia.
    all: apply Nat.ltb_lt in Hlt || apply Nat.ltb_ge in Hlt.
    all: apply Nat.ltb_lt in HltS || apply Nat.ltb_ge in HltS.
    all: try lia.
    all: try (apply Nat.even_spec in Heven; destruct Heven as [j ->]; lia).
    all: subst i; rewrite Nat.even_even in Heven; discriminate.
Qed.

Lemma HZPath_even_adds k x y:
  hz_rank x = 2 * k ->
  HZPath (2 * k) x y ->
  EvenAdds k (hz_cur x) (hz_cur y).
Proof.
  revert x y. induction k as [|k IH]; intros x y Hrank Hpath.
  - cbn in Hpath. inversion Hpath; subst. constructor.
  - replace (2 * S k) with (S (S (2 * k))) in Hrank, Hpath by lia.
    inversion Hpath as [|n0 x0 x1 y0 H01 Htail]; subst.
    inversion Htail as [|n1 x1' x2 y1 H12 Hrest]; subst.
    pose proof (HZ_valid_pair x x1 x2 (2 * k) Hrank H01 H12)
      as [Hrank2 [Hkind2 Hadd]].
    econstructor; [exact Hadd|].
    eapply IH; eassumption.
Qed.

Lemma HZReadies_path n x:
  hz_rank x = n ->
  HZ_WF x ->
  HZReadies n x ->
  exists y, HZPath n x y.
Proof.
  revert x. induction n as [|n IH]; intros x Hrank Hwf Hready.
  - exists x. constructor.
  - cbn[HZReadies] in Hready. destruct Hready as [Hfirst Htail].
    destruct (HZ_WF_ready_step x n Hwf Hrank Hfirst) as [y Hstep].
    assert (Hyrank: hz_rank y = n).
    { destruct Hstep; cbn[hz_rank] in *; lia. }
    destruct (IH y Hyrank (HZ_valid_target_WF _ _ Hstep)
      (Htail y Hstep)) as [z Hpath].
    exists z. econstructor; eassumption.
Qed.

Lemma HZPath_run n x y:
  HZPath n x y -> HZS x -->* HZS y.
Proof.
  intro Hpath. induction Hpath.
  - constructor.
  - eapply evstep_trans; [eapply HZ_valid_run, H|exact IHHpath].
Qed.


Lemma HD_run xs ys: HD xs ys -> S1 xs 0 -->* S1 ys 0.
Proof. intro H; inversion H; assumption. Qed.

Lemma HZI_run xs ys: HZI xs ys -> S1 xs 0 -->* S1 ys 0.
Proof. intro H; inversion H; assumption. Qed.

Inductive HZBridge (r:nat) : list nat -> list nat -> Prop :=
| HZBridge_intro src first start out dst:
    HD src first ->
    HZI first start ->
    Add2At r src start ->
    HZPath r (mkHZSt start first HZNextHD r) out ->
    hz_cur out = dst ->
    HZBridge r src dst.

Lemma HZBridge_run r src dst:
  HZBridge r src dst -> S1 src 0 -->* S1 dst 0.
Proof.
  intros [src0 first start out dst0 Hhd Hhzi Hadd Hpath Hdst].
  eapply evstep_trans; [eapply HD_run, Hhd|].
  eapply evstep_trans; [eapply HZI_run, Hhzi|].
  pose proof (HZPath_run _ _ _ Hpath) as Hrun.
  destruct out as [cur prev kind rank].
  cbn[hz_cur] in Hdst. subst cur.
  exact Hrun.
Qed.

Import ListNotations.

Record CEffect := mkEffect {
  e_swap : bool;
  e_cur : list nat;
  e_prev : list nat
}.

Definition step_effect c :=
  let r := c_rank c in
  let k := c_rank (c_step c) in
  let inc := c_inc c in
  let gc := c_cur_gray c in
  let gp := c_prev_gray c in
  mkEffect (batch_swap r)
    ((if Nat.even r then carry_cur_add r else carry_prev_add r) +l
      lmul2 (L1 k))
    (if Nat.even r then
       carry_prev_add r +l
         lsum (if inc then TGray inc gp else TGray inc gp - 2) 2
     else
       carry_cur_add r +l
         lsum (if negb inc then TGray (negb inc) gc
               else TGray (negb inc) gc - 2) 2).

Definition effect_id := mkEffect false [] [].

Definition effect_compose a b :=
  mkEffect (compose_swap (e_swap a) (e_swap b))
    (compose_cur_add (e_swap b) (e_cur a) (e_prev a) (e_cur b))
    (compose_prev_add (e_swap b) (e_cur a) (e_prev a) (e_prev b)).

Lemma effect_compose_id_l e: effect_compose effect_id e = e.
Proof.
  destruct e as [s dc dp], s;
    cbn[effect_compose effect_id compose_swap compose_cur_add
      compose_prev_add e_swap e_cur e_prev xorb];
    rewrite ?ladd_nil_l; reflexivity.
Qed.

Lemma effect_compose_id_r e: effect_compose e effect_id = e.
Proof.
  destruct e as [s dc dp], s;
    unfold effect_compose, effect_id, compose_swap,
      compose_cur_add, compose_prev_add;
    cbn[e_swap e_cur e_prev xorb];
    rewrite !ladd_nil_r; reflexivity.
Qed.

Lemma effect_compose_assoc a b c:
  effect_compose (effect_compose a b) c =
  effect_compose a (effect_compose b c).
Proof.
  destruct a as [sa ac ap], b as [sb bc bp], c as [sc cc cp].
  destruct sa, sb, sc;
    repeat progress (
      unfold effect_compose, compose_swap, compose_cur_add, compose_prev_add;
      cbn[e_swap e_cur e_prev xorb]);
    f_equal; rewrite ?ladd_assoc; reflexivity.
Qed.

Fixpoint steps_effect n c :=
match n with
| 0 => effect_id
| S n => effect_compose (step_effect c) (steps_effect n (c_step c))
end.

Lemma steps_effect_S n c:
  steps_effect (S n) c =
    effect_compose (step_effect c) (steps_effect n (c_step c)).
Proof. reflexivity. Qed.

Definition num_closed (x : NumState) :=
  let '(inc, gc, gp) := x in mkClosed inc gc 0 gp 0.

Definition num_effect x := step_effect (num_closed x).

Fixpoint num_effects n x :=
match n with
| 0 => effect_id
| S n => effect_compose (num_effect x) (num_effects n (num_step x))
end.

Fixpoint num_effects_acc n x acc :=
match n with
| 0 => acc
| S n => num_effects_acc n (num_step x)
    (effect_compose acc (num_effect x))
end.

Lemma num_effects_acc_S n x acc:
  num_effects_acc (S n) x acc =
    num_effects_acc n (num_step x) (effect_compose acc (num_effect x)).
Proof. reflexivity. Qed.

Lemma num_effects_acc_spec n x acc:
  num_effects_acc n x acc = effect_compose acc (num_effects n x).
Proof.
  revert x acc. induction n as [|n IH]; intros x acc.
  - cbn[num_effects_acc num_effects]. symmetry. apply effect_compose_id_r.
  - cbn[num_effects_acc num_effects]. rewrite IH, effect_compose_assoc.
    reflexivity.
Qed.

Lemma num_effects_acc_id n x:
  num_effects_acc n x effect_id = num_effects n x.
Proof. rewrite num_effects_acc_spec, effect_compose_id_l. reflexivity. Qed.

Lemma step_effect_ranks c r k:
  c_rank c = r -> c_rank (c_step c) = k ->
  step_effect c =
  mkEffect (batch_swap r)
    ((if Nat.even r then carry_cur_add r else carry_prev_add r) +l
      lmul2 (L1 k))
    (if Nat.even r then
       carry_prev_add r +l
         lsum (if c_inc c then TGray (c_inc c) (c_prev_gray c)
               else TGray (c_inc c) (c_prev_gray c) - 2) 2
     else
       carry_cur_add r +l
         lsum (if negb (c_inc c)
               then TGray (negb (c_inc c)) (c_cur_gray c)
               else TGray (negb (c_inc c)) (c_cur_gray c) - 2) 2).
Proof.
  intros Hr Hk. unfold step_effect. rewrite Hr, Hk. reflexivity.
Qed.

Lemma num_effect_ranks inc gc gp r k:
  num_rank (inc, gc, gp) = r ->
  num_rank (num_step (inc, gc, gp)) = k ->
  num_effect (inc, gc, gp) =
  mkEffect (batch_swap r)
    ((if Nat.even r then carry_cur_add r else carry_prev_add r) +l
      lmul2 (L1 k))
    (if Nat.even r then
       carry_prev_add r +l
         lsum (if inc then TGray inc gp else TGray inc gp - 2) 2
     else
       carry_cur_add r +l
         lsum (if negb inc then TGray (negb inc) gc
               else TGray (negb inc) gc - 2) 2).
Proof.
  intros Hr Hk. unfold num_effect, num_closed.
  eapply step_effect_ranks.
  - exact Hr.
  - change (num_rank (num_step (inc, gc, gp)) = k). exact Hk.
Qed.

Lemma step_effect_num c:
  step_effect c = num_effect (closed_num c).
Proof. destruct c; reflexivity. Qed.

Lemma steps_effect_num n c:
  steps_effect n c = num_effects n (closed_num c).
Proof.
  revert c. induction n as [|n IH]; intro c; [reflexivity|].
  cbn[steps_effect num_effects]. rewrite step_effect_num, IH, closed_num_step.
  reflexivity.
Qed.

Definition PairEffect e x y :=
  PairLadd (e_swap e) (e_cur e) (e_prev e) x y.

Lemma closed_batch_effect x c y:
  ClosedRep x c ->
  ClosedNumeric c ->
  embanked_batch (c_rank c) x y ->
  PairEffect (step_effect c) x y.
Proof.
  destruct c as [inc gc lc gp lp].
  cbn[ClosedRep ClosedNumeric c_rank c_step c_inc c_cur_gray c_cur_len
    c_prev_gray c_prev_len] in *.
  intros [cur [prev [Hx [Hwf [Hready [Hprev [Hg [Hl [Hgp Hlp]]]]]]]]]
    Hnumeric Hbatch.
  subst x.
  destruct Hnumeric as
    [Hr_cur [Hr_prev [Hk_cur [Hk_prev
      [Hbound_cur [Hbound_prev [Hcur_bound Hprev_bound]]]]]]].
  set (r := batch_rank inc gp) in *.
  set (k := batch_rank (next_inc r inc)
    (next_prev_gray r inc gc gp)) in *.
  destruct (closed_windows r cur prev inc gc lc gp lp
    Hwf Hready Hprev Hg Hl Hgp Hlp
    Hr_cur Hr_prev Hcur_bound Hprev_bound) as [Hcur Hprev_window].
  assert (Hcur0:
    Window cur (negb inc) gc (List.hd 0 cur) lc (CurNeed r) r).
  {
    eapply Window_weaken with (d':=head_add k + CurNeed r);
      [lia|exact Hcur].
  }
  assert (Hprev0:
    Window prev inc gp (List.hd 0 prev) lp (PrevNeed r) r).
  {
    eapply Window_weaken with (d':=head_add k + PrevNeed r);
      [lia|exact Hprev_window].
  }
  assert (Hrank: batch_next_rank r cur prev inc = k).
  {
    subst k. eapply batch_next_rank_window; eassumption.
  }
  pose proof (cur_full_gray r cur prev inc Hready) as Hfull_cur.
  pose proof (prev_full_gray r cur prev inc Hprev) as Hfull_prev.
  rewrite Hg in Hfull_cur. rewrite Hgp in Hfull_prev.
  pose proof (embanked_batch_effect r cur prev inc y Hbatch) as Heffect.
  change (PairLadd (batch_swap r)
    ((if Nat.even r then carry_cur_add r else carry_prev_add r) +l
      lmul2 (L1 k))
    (if Nat.even r then
       carry_prev_add r +l
         lsum (if inc then TGray inc gp else TGray inc gp - 2) 2
     else
       carry_cur_add r +l
         lsum (if negb inc then TGray (negb inc) gc
               else TGray (negb inc) gc - 2) 2)
    (St_of cur prev inc (Some r)) y).
  unfold batch_cur_add, batch_prev_add in Heffect.
  fold k in Heffect. rewrite Hrank in Heffect.
  destruct (Nat.even r), inc;
    cbn[negb] in Heffect |- *;
    rewrite ?carry_cur_gray, ?carry_prev_gray,
      ?Hfull_cur, ?Hfull_prev in Heffect;
    exact Heffect.
Qed.

Lemma PairEffect_id x: PairEffect effect_id x x.
Proof. apply PairLadd_refl. Qed.

Lemma PairEffect_compose a b x y z:
  PairEffect a x y -> PairEffect b y z ->
  PairEffect (effect_compose a b) x z.
Proof.
  intros Ha Hb. unfold PairEffect, effect_compose.
  cbn[e_swap e_cur e_prev]. eapply PairLadd_trans; eassumption.
Qed.

Lemma ClosedRep_numeric_path n x c d:
  NumericPath n c d ->
  ClosedRep x c ->
  exists y,
    ClosedPath n x c y /\
    ClosedRep y d /\
    PairEffect (steps_effect n c) x y.
Proof.
  intro Hpath. revert x.
  induction Hpath as [c|n c d Hnumeric Hpath IH]; intros x Hrep.
  - exists x. split; [constructor|]. split; [exact Hrep|apply PairEffect_id].
  - destruct (ClosedRep_step x c Hrep Hnumeric) as [y [Hbatch Hy]].
    destruct (IH y Hy) as [z [Htail [Hz Heffect]]].
    exists z. repeat split.
    + econstructor; eassumption.
    + exact Hz.
    + cbn[steps_effect]. eapply PairEffect_compose.
      * eapply closed_batch_effect; eassumption.
      * exact Heffect.
Qed.

Import ListNotations.


Fixpoint source_tail m :=
match m with
| 0 => [6; 4; 0; 0]
| S m =>
    (2 ^ (2 * m + 5) - 2) :: 2 ^ (2 * m + 4) :: source_tail m
end.

Fixpoint source_body_tail m :=
match m with
| 0 => [6; 4]
| S m =>
    (2 ^ (2 * m + 5) - 2) :: 2 ^ (2 * m + 4) :: source_body_tail m
end.

Definition source_body m := 2 ^ (2 * m + 4) :: source_body_tail m.

Definition source m :=
  (2 ^ (2 * m + 5) - 4) :: 2 ^ (2 * m + 4) :: source_tail m.

Fixpoint reentry_tail m :=
match m with
| 0 => [10; 4; 4; 1; 0]
| S m =>
    (2 ^ (2 * m + 5) + 2) :: 2 ^ (2 * m + 4) :: reentry_tail m
end.

Definition reentry m :=
  (2 ^ (2 * m + 5) + 4) :: 2 ^ (2 * m + 4) :: reentry_tail m.

Definition pre_reentry m :=
  (2 ^ (2 * m + 5) + 2) :: 2 ^ (2 * m + 4) :: reentry_tail m.

Fixpoint reentry_prev_tail m :=
match m with
| 0 => [8; 6; 2; 3; 0; 0]
| S m =>
    2 ^ (2 * m + 5) :: (2 ^ (2 * m + 4) + 2) ::
      reentry_prev_tail m
end.

Definition reentry_prev m :=
  (2 ^ (2 * m + 5) + 1) :: (2 ^ (2 * m + 4) + 2) ::
    reentry_prev_tail m.

Definition start_state m :=
  St_of (reentry m) (reentry_prev m) tp0 (Some 0).

Definition overflow_source m := source (S m).

Lemma source_tail_length m:
  length (source_tail m) = 2 * m + 4.
Proof.
  induction m; cbn[source_tail length]; lia.
Qed.

Lemma source_body_tail_length m:
  length (source_body_tail m) = 2 * m + 2.
Proof.
  induction m; cbn[source_body_tail length]; lia.
Qed.

Lemma source_body_length m:
  length (source_body m) = 2 * m + 3.
Proof.
  unfold source_body. cbn[length]. rewrite source_body_tail_length. lia.
Qed.

Lemma source_body_tail_app m:
  source_body_tail m ++ [0; 0] = source_tail m.
Proof.
  induction m; cbn[source_body_tail source_tail app]; congruence.
Qed.

Lemma odd_pow_S n: Nat.odd (2 ^ S n) = tp0.
Proof. cbn[Nat.pow]. rewrite Nat.mul_comm. apply odd_0. Qed.

Lemma odd_pow_SS_sub2 n: Nat.odd (2 ^ S (S n) - 2) = tp0.
Proof.
  cbn[Nat.pow].
  replace (2 * (2 * 2 ^ n) - 2) with ((2 * 2 ^ n - 1) * 2) by lia.
  apply odd_0.
Qed.

Lemma gray_even_cons a xs:
  Nat.odd a = tp0 -> gray xs = 0 -> gray (a :: xs) = 0.
Proof.
  intros Ha Hg. cbn[gray tp]. rewrite Ha, (tp_O _ Hg), Hg. reflexivity.
Qed.

Lemma source_body_tail_WF m: WF'' (source_body_tail m).
Proof.
  induction m.
  - repeat constructor; lia.
  - cbn[source_body_tail]. repeat constructor; try exact IHm; pow_lia.
Qed.

Lemma source_body_WF m: WF'' (source_body m).
Proof.
  unfold source_body. constructor; [pow_lia|apply source_body_tail_WF].
Qed.

Lemma source_body_tail_gray0 m:
  gray (source_body_tail m ++ [0; 0]) = 0.
Proof.
  induction m.
  - reflexivity.
  - cbn[source_body_tail app].
    apply gray_even_cons.
    + replace (2 * m + 5) with (S (S (2 * m + 3))) by lia.
      apply odd_pow_SS_sub2.
    + apply gray_even_cons.
      * replace (2 * m + 4) with (S (2 * m + 3)) by lia.
        apply odd_pow_S.
      * exact IHm.
Qed.

Lemma source_body_gray0 m:
  gray (source_body m ++ [0; 0]) = 0.
Proof.
  unfold source_body. cbn[app]. apply gray_even_cons.
  - replace (2 * m + 4) with (S (2 * m + 3)) by lia.
    apply odd_pow_S.
  - apply source_body_tail_gray0.
Qed.

Lemma source_as_HOI m:
  source m =
    ((2 ^ (2 * m + 4) - 2) * 2) :: source_body m ++ [0; 0].
Proof.
  unfold source, source_body. cbn[app].
  rewrite source_body_tail_app. f_equal. pow_lia.
Qed.

Definition source_after_hoi m :=
  (source_body m ++ [1; 0; 0; 0]) +l
  lsum (2 ^ length (source_body m) * 2 - 1)
    ((2 ^ (2 * m + 4) - 2) * 2).

Lemma HOI_exact a xs:
  WF'' xs ->
  gray (xs ++ [0; 0]) = 0 ->
  a * 2 <= 2 ^ length xs * 14 ->
  HOI (a * 2 :: xs ++ [0; 0])
    ((xs ++ [1; 0; 0; 0]) +l
      lsum (2 ^ length xs * 2 - 1) (a * 2)).
Proof.
  intros Hwf Hg Hbound.
  destruct (HOI_spec a xs Hwf Hg Hbound) as [ys Hhoi].
  replace
    ((xs ++ [1; 0; 0; 0]) +l lsum (2 ^ length xs * 2 - 1) (a * 2))
    with ys.
  - exact Hhoi.
  - inversion Hhoi; subst.
    match goal with
    | H : ?a0 * 2 = a * 2 |- _ => replace a0 with a in * by lia
    end.
    match goal with
    | H : ?xs0 ++ [0; 0] = xs ++ [0; 0] |- _ =>
        apply app_inv_tail in H; subst
    end.
    reflexivity.
Qed.

Lemma source_HOI m: HOI (source m) (source_after_hoi m).
Proof.
  rewrite source_as_HOI. unfold source_after_hoi.
  apply HOI_exact.
  - apply source_body_WF.
  - apply source_body_gray0.
  - rewrite source_body_length. pow_lia.
Qed.


Lemma source_length m:
  length (source m) = 2 * m + 6.
Proof. unfold source; cbn[length]; rewrite source_tail_length; lia. Qed.

Lemma reentry_tail_length m:
  length (reentry_tail m) = 2 * m + 5.
Proof.
  induction m; cbn[reentry_tail length]; lia.
Qed.

Lemma reentry_length m:
  length (reentry m) = 2 * m + 7.
Proof. unfold reentry; cbn[length]; rewrite reentry_tail_length; lia. Qed.

Lemma reentry_prev_tail_length m:
  length (reentry_prev_tail m) = 2 * m + 6.
Proof.
  induction m; cbn[reentry_prev_tail length]; lia.
Qed.

Fixpoint hz_low_odd k :=
match k with
| 0 => [8; 4; 4; 1; 0]
| S k => 2 ^ (2 * k + 5) :: 2 ^ (2 * k + 4) :: hz_low_odd k
end.

Fixpoint hz_low_pre0 k :=
match k with
| 0 => [10; 4; 4; 1; 0]
| S k => 2 ^ (2 * k + 5) :: 2 ^ (2 * k + 4) :: hz_low_pre0 k
end.

Fixpoint hz_low_hd k :=
match k with
| 0 => [8; 6; 2; 2]
| S k => 2 ^ (2 * k + 5) :: 2 ^ (2 * k + 4) :: hz_low_hd k
end.

Lemma hz_low_odd_length k: length (hz_low_odd k) = 2 * k + 5.
Proof. induction k; cbn[hz_low_odd length]; lia. Qed.

Lemma hz_low_pre0_length k: length (hz_low_pre0 k) = 2 * k + 5.
Proof. induction k; cbn[hz_low_pre0 length]; lia. Qed.

Lemma hz_low_hd_length k: length (hz_low_hd k) = 2 * k + 4.
Proof. induction k; cbn[hz_low_hd length]; lia. Qed.

Lemma hz_low_odd_WF' k: WF' (hz_low_odd k).
Proof.
  induction k.
  - cbn[hz_low_odd]. repeat constructor; lia.
  - cbn[hz_low_odd]. repeat constructor; try exact IHk; pow_lia.
Qed.

Lemma hz_low_odd_WF k: WF (hz_low_odd k).
Proof. apply WF'_WF, hz_low_odd_WF'. Qed.

Lemma hz_low_odd_tp k: tp (hz_low_odd k) = tp1.
Proof.
  induction k.
  - reflexivity.
  - cbn[hz_low_odd tp]. rewrite IHk.
    replace (2 * k + 5) with (S (2 * k + 4)) by lia.
    rewrite odd_pow_S.
    replace (2 * k + 4) with (S (2 * k + 3)) by lia.
    rewrite odd_pow_S. reflexivity.
Qed.

Lemma hz_low_odd_gray k:
  gray (hz_low_odd k) = 2 ^ (2 * k + 4) - 1.
Proof.
  induction k.
  - reflexivity.
  - cbn[hz_low_odd gray tp]. rewrite hz_low_odd_tp.
    replace (2 * k + 5) with (S (2 * k + 4)) by lia.
    rewrite odd_pow_S.
    replace (2 * k + 4) with (S (2 * k + 3)) by lia.
    rewrite odd_pow_S, IHk. cbn. pow_lia.
Qed.

Lemma hz_low_cons_gray k:
  gray (2 ^ (2 * k + 4) :: hz_low_odd k) =
    2 ^ (2 * k + 5) - 1.
Proof.
  cbn[gray tp]. rewrite hz_low_odd_tp.
  replace (2 * k + 4) with (S (2 * k + 3)) by lia.
  rewrite odd_pow_S, hz_low_odd_gray. cbn. pow_lia.
Qed.

Lemma hz_low_hd_WF' k: WF' (hz_low_hd k).
Proof.
  induction k.
  - cbn[hz_low_hd]. repeat constructor; lia.
  - cbn[hz_low_hd]. repeat constructor; try exact IHk; pow_lia.
Qed.

Lemma hz_low_hd_gray0 k: gray (hz_low_hd k) = 0.
Proof.
  induction k.
  - reflexivity.
  - cbn[hz_low_hd]. apply gray_even_cons.
    + replace (2 * k + 5) with (S (2 * k + 4)) by lia.
      apply odd_pow_S.
    + apply gray_even_cons.
      * replace (2 * k + 4) with (S (2 * k + 3)) by lia.
        apply odd_pow_S.
      * exact IHk.
Qed.

Lemma hz_low_carry k:
  hz_low_odd k +l L1 (2 * k + 4) +l pow_counts_dup (2 * k + 3) =
  2 ^ (2 * k + 4) :: hz_low_hd k.
Proof.
  induction k.
  - reflexivity.
  - cbn[hz_low_odd hz_low_hd].
    replace (L1 (2 * S k + 4)) with (0 :: 0 :: L1 (2 * k + 4))
      by (replace (2 * S k + 4) with (S (S (2 * k + 4))) by lia;
          reflexivity).
    replace (pow_counts_dup (2 * S k + 3)) with
      (2 ^ (2 * k + 5) :: 2 ^ (2 * k + 4) ::
        pow_counts_dup (2 * k + 3)).
    2:{ replace (2 * S k + 3) with (S (S (2 * k + 3))) by lia.
        replace (2 * k + 5) with (S (S (2 * k + 3))) by lia.
        replace (2 * k + 4) with (S (2 * k + 3)) by lia. reflexivity. }
    cbn[ladd]. f_equal.
    + replace (2 * S k + 4) with (S (2 * k + 5)) by lia.
      cbn[Nat.pow]. lia.
    + f_equal.
      * replace (2 * k + 5) with (S (2 * k + 4)) by lia.
        cbn[Nat.pow]. lia.
      * exact IHk.
Qed.

Lemma hz_low_HD_carry k:
  (2 ^ (2 * k + 4) :: hz_low_odd k) +l L1 (2 * k + 5) +l
    pow_counts_dup (2 * k + 4) = hz_low_hd (S k).
Proof.
  cbn[hz_low_hd].
  replace (L1 (2 * k + 5)) with (0 :: L1 (2 * k + 4))
    by (replace (2 * k + 5) with (S (2 * k + 4)) by lia; reflexivity).
  replace (pow_counts_dup (2 * k + 4)) with
    (2 ^ (2 * k + 4) :: pow_counts_dup (2 * k + 3))
    by (replace (2 * k + 4) with (S (2 * k + 3)) by lia; reflexivity).
  cbn[ladd]. f_equal; [pow_lia|apply hz_low_carry].
Qed.

Lemma hz_low_HD k: HD (hz_low_odd k) (hz_low_hd k).
Proof.
  destruct k as [|k].
  - apply (HD_exact 8 [4; 4; 1; 0]).
    + do 3 (constructor; [lia|]).
      change (WF (Helper.lpow [0] 1)). apply WF_O.
    + cbv[gray tp length Nat.odd Nat.even xorb negb]. lia.
    + reflexivity.
    + reflexivity.
  - cbn[hz_low_odd]. apply HD_exact.
    + constructor; [pow_lia|apply hz_low_odd_WF].
    + rewrite hz_low_cons_gray. cbn[length]. rewrite hz_low_odd_length. pow_lia.
    + change (tp (hz_low_odd (S k)) = tp1). apply hz_low_odd_tp.
    + rewrite hz_low_cons_gray, ctzS_pow_sub1.
      replace (1 + (2 ^ (2 * k + 5) - 1) - 2 ^ (2 * k + 5)) with 0
        by pow_lia.
      replace (2 * k + 5) with (S (2 * k + 4)) by lia.
      rewrite lsum_0_pow_succ. symmetry.
      replace (S (2 * k + 4)) with (2 * k + 5) by lia.
      apply hz_low_HD_carry.
Qed.

Lemma hz_low_HZI_carry k:
  hz_low_hd k +l (Helper.lpow [0] (2 * k + 3) ++ [1; 0; 0]) +l
    pow_counts_dup (2 * k + 3) =
  2 ^ (2 * k + 4) :: hz_low_pre0 k.
Proof.
  induction k.
  - reflexivity.
  - cbn[hz_low_hd hz_low_pre0].
    replace (Helper.lpow [0] (2 * S k + 3) ++ [1; 0; 0]) with
      (0 :: 0 :: (Helper.lpow [0] (2 * k + 3) ++ [1; 0; 0]))
      by (replace (2 * S k + 3) with (S (S (2 * k + 3))) by lia;
          reflexivity).
    replace (pow_counts_dup (2 * S k + 3)) with
      (2 ^ (2 * k + 5) :: 2 ^ (2 * k + 4) ::
        pow_counts_dup (2 * k + 3)).
    2:{ replace (2 * S k + 3) with (S (S (2 * k + 3))) by lia.
        replace (2 * k + 5) with (S (S (2 * k + 3))) by lia.
        replace (2 * k + 4) with (S (2 * k + 3)) by lia. reflexivity. }
    cbn[ladd]. f_equal.
    + replace (2 * S k + 4) with (S (2 * k + 5)) by lia.
      cbn[Nat.pow]. lia.
    + f_equal.
      * replace (2 * k + 5) with (S (2 * k + 4)) by lia.
        cbn[Nat.pow]. lia.
      * exact IHk.
Qed.

Lemma hz_low_HZI k: HZI (hz_low_hd k) (hz_low_pre0 k).
Proof.
  destruct k as [|k].
  - apply (HZI_exact 4 [6; 2; 2]).
    + repeat constructor; lia.
    + reflexivity.
    + cbn; lia.
    + reflexivity.
  - cbn[hz_low_hd].
    replace (2 ^ (2 * k + 5)) with (2 ^ (2 * k + 4) * 2) by pow_lia.
    apply HZI_exact.
    + constructor; [pow_lia|apply hz_low_hd_WF'].
    + apply gray_even_cons.
      * replace (2 * k + 4) with (S (2 * k + 3)) by lia.
        apply odd_pow_S.
      * apply hz_low_hd_gray0.
    + cbn[length]. rewrite hz_low_hd_length. pow_lia.
    + cbn[length]. rewrite hz_low_hd_length.
      replace (S (2 * k + 4) - 1) with (2 * k + 4) by lia.
      replace (2 ^ (2 * k + 4) * 2) with (2 ^ S (2 * k + 4))
        by (cbn[Nat.pow]; lia).
      rewrite lsum_pow_full.
      symmetry.
      change
        ((2 ^ (2 * k + 4) :: hz_low_hd k) +l
          (Helper.lpow [0] (2 * k + 4) ++ [1; 0; 0]) +l
          pow_counts_dup (2 * k + 4) = hz_low_pre0 (S k)).
      cbn[hz_low_pre0].
      replace (Helper.lpow [0] (2 * k + 4) ++ [1; 0; 0]) with
        (0 :: (Helper.lpow [0] (2 * k + 3) ++ [1; 0; 0]))
        by (replace (2 * k + 4) with (S (2 * k + 3)) by lia; reflexivity).
      replace (pow_counts_dup (2 * k + 4)) with
        (2 ^ (2 * k + 4) :: pow_counts_dup (2 * k + 3))
        by (replace (2 * k + 4) with (S (2 * k + 3)) by lia; reflexivity).
      cbn[ladd]. f_equal; [pow_lia|apply hz_low_HZI_carry].
Qed.

Lemma hz_low_pair k:
  HD (hz_low_odd k) (hz_low_hd k) /\
  HZI (hz_low_hd k) (hz_low_pre0 k).
Proof. split; [apply hz_low_HD|apply hz_low_HZI]. Qed.

Lemma hz_low_odd_HDReady k: HDReady (hz_low_odd k).
Proof.
  destruct k as [|k].
  - exists 8, [4; 4; 1; 0]. split; [reflexivity|].
    split; [apply hz_low_odd_WF'|]. split.
    + cbv[gray tp length Nat.odd Nat.even xorb negb]. lia.
    + reflexivity.
  - exists (2 ^ (2 * k + 5)),
      (2 ^ (2 * k + 4) :: hz_low_odd k).
    split; [reflexivity|]. split; [apply hz_low_odd_WF'|]. split.
    + rewrite hz_low_cons_gray. cbn[length]. rewrite hz_low_odd_length. pow_lia.
    + apply hz_low_odd_tp.
Qed.

Lemma hz_low_hd_HZIReady k: HZIReady (hz_low_hd k).
Proof.
  destruct k as [|k].
  - exists 4, [6; 2; 2]. split; [reflexivity|].
    split; [apply hz_low_hd_WF'|]. split.
    + repeat constructor; lia.
    + split; [reflexivity|cbn; lia].
  - exists (2 ^ (2 * k + 4)),
      (2 ^ (2 * k + 4) :: hz_low_hd k).
    split.
    + cbn[hz_low_hd]. f_equal. pow_lia.
    + split; [apply hz_low_hd_WF'|]. split.
      * constructor; [pow_lia|apply hz_low_hd_WF'].
      * split.
        -- apply gray_even_cons.
           ++ replace (2 * k + 4) with (S (2 * k + 3)) by lia.
              apply odd_pow_S.
           ++ apply hz_low_hd_gray0.
        -- cbn[length]. rewrite hz_low_hd_length. pow_lia.
Qed.

Lemma hz_low_pre0_add k:
  hz_low_pre0 k = hz_low_odd k +l lmul2 (L1 (2 * k)).
Proof.
  induction k.
  - reflexivity.
  - cbn[hz_low_pre0 hz_low_odd].
    replace (2 * S k) with (S (S (2 * k))) by lia.
    unfold lmul2 in IHk |- *.
    cbn[L1 ladd]. f_equal; [lia|]. f_equal; [lia|exact IHk].
Qed.

Lemma hz_low_first_add k: Add2At (2 * k) (hz_low_odd k) (hz_low_pre0 k).
Proof.
  rewrite hz_low_pre0_add. apply Add2At_lmul2.
  rewrite hz_low_odd_length. lia.
Qed.

Lemma even_hit_0 i: even_hit 0 i = tp0.
Proof.
  unfold even_hit. cbn[Nat.mul]. destruct (Nat.even i); reflexivity.
Qed.

Lemma even_hit_SS k i:
  even_hit (S k) (S (S i)) = even_hit k i.
Proof.
  unfold even_hit.
  replace (2 * S k) with (S (S (2 * k))) by lia.
  reflexivity.
Qed.

Lemma hz_endpoint_coeff k i:
  coeff (reentry_tail k) i =
  coeff (hz_low_pre0 k) i +
    2 * (if even_hit k i then 1 else 0).
Proof.
  revert i. induction k as [|k IH]; intro i.
  - rewrite even_hit_0. cbn. lia.
  - destruct i as [|[|i]].
    + assert (even_hit (S k) 0 = tp1).
      { unfold even_hit. replace (2 * S k) with (S (S (2 * k))) by lia.
        reflexivity. }
      cbn[reentry_tail hz_low_pre0 coeff nth]. rewrite H. lia.
    + assert (even_hit (S k) 1 = tp0) by
        (unfold even_hit; reflexivity).
      cbn[reentry_tail hz_low_pre0 coeff nth]. rewrite H. lia.
    + change
        (coeff (reentry_tail k) i = coeff (hz_low_pre0 k) i +
          2 * (if even_hit (S k) (S (S i)) then 1 else 0)).
      rewrite even_hit_SS, IH. reflexivity.
Qed.

Lemma hz_endpoint_unique k ys:
  EvenAdds k (hz_low_pre0 k) ys -> ys = reentry_tail k.
Proof.
  intro Hadds. apply coeff_ext.
  - pose proof (EvenAdds_length _ _ _ Hadds) as Hlen.
    rewrite <-Hlen, hz_low_pre0_length, reentry_tail_length. reflexivity.
  - intro i. rewrite (EvenAdds_coeff _ _ _ Hadds), hz_endpoint_coeff.
    reflexivity.
Qed.

Lemma hz_bridge m:
  HZBridge (2 * S m) (hz_low_odd (S m)) (reentry_tail (S m)).
Proof.
  destruct (hz_low_pair (S m)) as [Hhd Hhzi].
  pose proof (hz_low_first_add (S m)) as Hadd.
  set (x := mkHZSt (hz_low_pre0 (S m)) (hz_low_hd (S m))
    HZNextHD (2 * S m)).
  assert (Hwf: HZ_WF x).
  { unfold x. eapply HZ_WF_HZI; eassumption. }
  assert (Hsafe: HZSafe x).
  {
    unfold x. cbn[HZSafe hz_kind hz_cur hz_prev]. split.
    - replace (2 * S m) with (S (S (2 * m))) in Hadd by lia.
      eapply HDReady_shift; [apply hz_low_odd_HDReady|exact Hadd].
    - apply hz_low_hd_HZIReady.
  }
  assert (Hrank: hz_rank x = 2 * S m) by reflexivity.
  pose proof (HZReadies_of_safe _ _ Hrank Hwf Hsafe) as Hreadies.
  destruct (HZReadies_path _ _ Hrank Hwf Hreadies) as [out Hpath].
  eapply HZBridge_intro with
    (first:=hz_low_hd (S m)) (start:=hz_low_pre0 (S m)) (out:=out).
  - exact Hhd.
  - exact Hhzi.
  - exact Hadd.
  - exact Hpath.
  - apply hz_endpoint_unique.
    pose proof (HZPath_even_adds (S m) x out Hrank Hpath) as Heven.
    unfold x in Heven. cbn[hz_cur] in Heven. exact Heven.
Qed.

Import ListNotations.


Lemma ctzS_pow_S_sub2 n: ctzS (2 ^ S n - 2) = 0.
Proof.
  replace (2 ^ S n - 2) with ((2 ^ n - 1) * 2) by
    (cbn[Nat.pow]; lia).
  apply ctzS_0.
Qed.

Fixpoint pow_down n :=
match n with
| 0 => [1; 0]
| S n => 2 ^ S n :: pow_down n
end.

Fixpoint pow_down_ge2 n :=
match n with
| 0 => [2; 0]
| S n => 2 ^ S (S n) :: pow_down_ge2 n
end.

Fixpoint hz_low_from n :=
match n with
| 0 => [4; 4; 1; 0]
| S n => 2 ^ S (S (S n)) :: hz_low_from n
end.

Lemma pow_down_length n: length (pow_down n) = n + 2.
Proof. induction n; cbn[pow_down length]; lia. Qed.

Lemma pow_down_WF n: WF (pow_down n).
Proof.
  induction n.
  - constructor; [lia|]. change (WF (Helper.lpow [0] 1)). apply WF_O.
  - cbn[pow_down]. constructor; [pow_lia|exact IHn].
Qed.

Lemma pow_down_tp_gray n:
  tp (pow_down n) = tp1 /\ gray (pow_down n) = 2 ^ S n - 1.
Proof.
  induction n as [|n [Htp Hgray]].
  - split; reflexivity.
  - cbn[pow_down tp gray]. rewrite Htp, odd_pow_S, Hgray.
    split; [reflexivity|].
    cbn[Nat.pow]. remember (2 ^ n) as p.
    assert (0 < p) by (subst p; lia). destruct p; cbn in *; lia.
Qed.

Lemma pow_down_pred_cons_data n:
  tp ((2 ^ S n - 1) :: pow_down n) = tp0 /\
  gray ((2 ^ S n - 1) :: pow_down n) = 2 ^ S (S n) - 2.
Proof.
  pose proof (pow_down_tp_gray n) as [Htp Hgray].
  assert (Hodd: Nat.odd (2 ^ S n - 1) = tp1).
  { replace (2 ^ S n - 1) with (1 + (2 ^ n - 1) * 2) by
      (cbn[Nat.pow]; lia).
    apply odd_1. }
  split.
  - cbn[tp]. rewrite Htp, Hodd. reflexivity.
  - cbn[gray tp]. rewrite Htp, Hodd, Hgray.
    cbn[Nat.pow]. remember (2 ^ n) as p.
    assert (0 < p) by (subst p; lia). destruct p; cbn in *; lia.
Qed.

Lemma pow_down_ge2_length n: length (pow_down_ge2 n) = n + 2.
Proof. induction n; cbn[pow_down_ge2 length]; lia. Qed.

Lemma pow_down_ge2_WF' n: WF' (pow_down_ge2 n).
Proof.
  induction n.
  - repeat constructor; lia.
  - cbn[pow_down_ge2]. constructor; [pow_lia|exact IHn].
Qed.

Lemma pow_down_ge2_gray0 n: gray (pow_down_ge2 n) = 0.
Proof.
  induction n.
  - reflexivity.
  - cbn[pow_down_ge2]. apply gray_even_cons.
    + cbn[Nat.pow]. rewrite Nat.mul_comm. apply odd_0.
    + exact IHn.
Qed.

Lemma pow_down_add_counts n:
  pow_down n +l pow_counts n = pow_down_ge2 n.
Proof.
  induction n.
  - reflexivity.
  - cbn[pow_down pow_counts pow_down_ge2 ladd].
    f_equal; [pow_lia|exact IHn].
Qed.

Lemma pow_down_pred_cons_add_counts n:
  ((2 ^ S n - 1) :: pow_down n) +l L1 0 +l pow_counts (S n) =
  pow_down_ge2 (S n).
Proof.
  cbn[pow_counts L1 ladd pow_down_ge2]. f_equal.
  - cbn[Nat.pow]. remember (2 ^ n) as p.
    assert (0 < p) by (subst p; lia). destruct p; cbn in *; lia.
  - rewrite ladd_nil_r. apply pow_down_add_counts.
Qed.

Lemma pow_down_add_counts_dup n:
  pow_down n +l L1 (S n) +l pow_counts_dup n =
  pow_down_ge2 n +l lmul2 (L1 (S n)).
Proof.
  induction n.
  - reflexivity.
  - cbn[pow_down pow_down_ge2 pow_counts_dup L1 lmul2 ladd].
    f_equal; [pow_lia|exact IHn].
Qed.

Lemma pow_down_ge2_last2_data n:
  length (pow_down_ge2 n +l lmul2 (L1 (S n))) = n + 2 /\
  WF' (pow_down_ge2 n +l lmul2 (L1 (S n))) /\
  gray (pow_down_ge2 n +l lmul2 (L1 (S n))) = 0.
Proof.
  induction n as [|n [Hlen [Hwf Hgray]]].
  - cbn[pow_down_ge2 L1 lmul2 ladd length]. repeat split.
    + repeat constructor; lia.
  - cbn[pow_down_ge2 L1 lmul2 ladd length].
    repeat split.
    + change (S (length (pow_down_ge2 n +l lmul2 (L1 (S n)))) =
        S n + 2).
      rewrite Hlen. lia.
    + constructor; [pow_lia|exact Hwf].
    + apply gray_even_cons.
      * cbn[Nat.pow].
        replace (2 * (2 * 2 ^ n) + (0 + 0)) with ((2 * 2 ^ n) * 2) by lia.
        apply odd_0.
      * exact Hgray.
Qed.

Lemma hzi_tail_combine_strong n:
  pow_down_ge2 n +l (0 :: Helper.lpow [0] n ++ [1; 0; 0]) +l
    (2 ^ S n :: pow_counts_dup n) =
  2 ^ S (S n) :: pow_down (S n).
Proof.
  induction n.
  - reflexivity.
  - cbn[pow_down_ge2 pow_counts_dup pow_down Helper.lpow app ladd].
    f_equal; [pow_lia|exact IHn].
Qed.

Lemma hzi_tail_combine n:
  pow_down_ge2 n +l (Helper.lpow [0] (S n) ++ [1; 0; 0]) +l
    ((2 ^ S n - 1) :: pow_counts_dup n) =
  (2 ^ S (S n) - 1) :: pow_down (S n).
Proof.
  destruct n.
  - reflexivity.
  - cbn[pow_down_ge2 pow_counts_dup pow_down Helper.lpow app ladd].
    f_equal.
    + cbn[Nat.pow]. remember (2 ^ n) as p.
      assert (0 < p) by (subst p; lia). destruct p; cbn in *; lia.
    + apply hzi_tail_combine_strong.
Qed.

Lemma hzi_tail_combine_low n:
  (pow_down_ge2 n +l lmul2 (L1 (S n))) +l
    (Helper.lpow [0] (S n) ++ [1; 0; 0]) +l pow_counts_dup (S n) =
  hz_low_from n.
Proof.
  induction n.
  - reflexivity.
  - cbn[pow_down_ge2 L1 lmul2 Helper.lpow app ladd
      pow_counts_dup hz_low_from].
    f_equal; [pow_lia|exact IHn].
Qed.

Lemma lsum_0_pow_SS_sub2 n:
  lsum 0 (2 ^ S (S n) - 2) = (2 ^ S n - 1) :: pow_counts n.
Proof.
  replace (2 ^ S (S n) - 2) with ((2 ^ S n - 1) * 2) by
    (cbn[Nat.pow]; lia).
  rewrite lsum_0_double_pos by (destruct n; pow_lia).
  rewrite lsum_0_pow_succ_sub1. reflexivity.
Qed.

Lemma lsum_pow_shift_sub1 n:
  lsum (2 ^ S n) (2 ^ S n - 1) = pow_counts n.
Proof.
  induction n.
  - reflexivity.
  - replace (2 ^ S (S n) - 1) with
      (2 * S (2 ^ S n - 2) + 1) by (cbn[Nat.pow]; lia).
    rewrite lsum_add.
    replace (2 ^ S (S n)) with (2 ^ S n * 2) by (cbn[Nat.pow]; lia).
    rewrite lsum_even_pairs.
    replace (S (2 ^ S n - 2)) with (2 ^ S n - 1) by pow_lia.
    rewrite IHn.
    replace (2 ^ S n * 2 + 2 * (2 ^ S n - 1))
      with (2 ^ S (S n) + (2 ^ S (S n) - 2)) by pow_lia.
    rewrite lsum_1.
    replace (ctzS (2 ^ S (S n) + (2 ^ S (S n) - 2))) with 0.
    2:{ replace (2 ^ S (S n) + (2 ^ S (S n) - 2))
          with (2 ^ S (S (S n)) - 2) by pow_lia.
        symmetry. apply ctzS_pow_S_sub2. }
    cbn[pow_counts L1 ladd]. rewrite ladd_nil_r. f_equal; pow_lia.
Qed.

Lemma lsum_pow_pred_full n:
  lsum (2 ^ S (S n) - 1) (2 ^ S (S n) - 1) =
  (2 ^ S n - 1) :: pow_counts_dup n.
Proof.
  replace (2 ^ S (S n) - 1) with
    (1 + (2 ^ S (S n) - 2)) by pow_lia.
  rewrite lsum_add, lsum_1.
  replace (ctzS (1 + (2 ^ S (S n) - 2))) with (S (S n)).
  2:{ replace (1 + (2 ^ S (S n) - 2)) with (2 ^ S (S n) - 1)
        by pow_lia.
      symmetry. apply ctzS_pow_sub1. }
  replace (2 ^ S (S n) - 1 + 1) with (2 ^ S (S n)) by pow_lia.
  replace (2 ^ S (S n) - 2) with (2 * S (2 ^ S n - 2)) by pow_lia.
  replace
    (lsum (1 + 2 * S (2 ^ S n - 2) + 1) (2 * S (2 ^ S n - 2)))
    with (S (2 ^ S n - 2) :: lsum (2 ^ S n) (S (2 ^ S n - 2))).
  2:{ replace (1 + 2 * S (2 ^ S n - 2) + 1) with (2 ^ S n * 2)
        by pow_lia.
      rewrite lsum_even_pairs. reflexivity. }
  replace (S (2 ^ S n - 2)) with (2 ^ S n - 1) by pow_lia.
  replace (lsum (2 ^ S n) (2 ^ S n - 1)) with (pow_counts n).
  2:{ symmetry. apply lsum_pow_shift_sub1. }
  change ((2 ^ S n - 1) :: (L1 (S n) +l pow_counts n) =
    (2 ^ S n - 1) :: pow_counts_dup n).
  f_equal. rewrite ladd_comm. apply pow_counts_dup_eq.
Qed.

Lemma lsum_pow_high_sub2 n:
  lsum (2 ^ S (S (S n)) - 1) (2 ^ S (S (S n)) - 2) =
  (2 ^ S (S n) - 1) :: (2 ^ S n - 1) :: pow_counts_dup n.
Proof.
  replace (2 ^ S (S (S n)) - 1)
    with (1 + (2 ^ S (S n) - 1) * 2) by pow_lia.
  replace (2 ^ S (S (S n)) - 2)
    with (2 * S (2 ^ S (S n) - 2)) by pow_lia.
  rewrite lsum_odd_pairs.
  replace (S (2 ^ S (S n) - 2)) with (2 ^ S (S n) - 1) by pow_lia.
  rewrite lsum_pow_pred_full. reflexivity.
Qed.

Lemma lsum_pow_high_full n:
  lsum (2 ^ S (S (S n)) - 1) (2 ^ S (S (S n))) =
  2 ^ S (S n) :: 2 ^ S n :: pow_counts_dup n.
Proof. rewrite lsum_pow_full. reflexivity. Qed.

Lemma hz_low_from_odd k: hz_low_from (2 * k + 1) = hz_low_odd k.
Proof.
  induction k.
  - reflexivity.
  - replace (2 * S k + 1) with (S (S (2 * k + 1))) by lia.
    cbn[hz_low_from hz_low_odd]. rewrite IHk. repeat f_equal; lia.
Qed.

Import ListNotations.


Definition di_tail m :=
  (2 ^ (2 * m + 4) - 1) ::
  (2 ^ (2 * m + 3) - 1) :: pow_down (2 * m + 2).

Definition di_mid m := (2 ^ (2 * m + 5) - 2) :: di_tail m.

Definition hz_hd0 m :=
  (2 ^ (2 * m + 5) - 2) :: pow_down_ge2 (2 * m + 3).

Definition hz_mid1 m :=
  (2 ^ (2 * m + 5) - 1) ::
  (2 ^ (2 * m + 4) - 1) :: pow_down (2 * m + 3).

Definition hz_hd1 m := pow_down_ge2 (2 * m + 4).
Definition hz_mid2 m := pow_down (2 * m + 5).

Definition hz_hd2 m :=
  2 ^ (2 * m + 5) ::
  (pow_down_ge2 (2 * m + 3) +l lmul2 (L1 (2 * m + 4))).

Definition hz_low m := hz_low_from (2 * m + 3).

Lemma odd_pow_S_sub1 n: Nat.odd (2 ^ S n - 1) = tp1.
Proof.
  cbn[Nat.pow].
  replace (2 * 2 ^ n - 1) with (S ((2 ^ n - 1) * 2)) by lia.
  apply odd_1.
Qed.

Lemma ctzS_pow_SS_sub3 n: ctzS (2 ^ S (S n) - 3) = 1.
Proof.
  replace (2 ^ S (S n) - 3) with
    (1 + (2 ^ S n - 2) * 2) by pow_lia.
  rewrite ctzS_1, ctzS_pow_S_sub2. reflexivity.
Qed.

Lemma di_tail_data m:
  length (di_tail m) = 2 * m + 6 /\
  WF (di_tail m) /\
  tp (di_tail m) = tp1 /\
  gray (di_tail m) = 2 ^ (2 * m + 5) - 3.
Proof.
  pose proof (pow_down_length (2 * m + 2)) as Hlen.
  pose proof (pow_down_WF (2 * m + 2)) as Hwf.
  pose proof (pow_down_tp_gray (2 * m + 2)) as [Htp Hgray].
  unfold di_tail. repeat split.
  - cbn[length]. lia.
  - repeat constructor; try exact Hwf; pow_lia.
  - cbn[tp]. rewrite Htp.
    replace (2 * m + 3) with (S (2 * m + 2)) by lia.
    rewrite odd_pow_S_sub1.
    replace (2 * m + 4) with (S (2 * m + 3)) by lia.
    rewrite odd_pow_S_sub1. reflexivity.
  - cbn[gray tp]. rewrite Htp.
    replace (2 * m + 3) with (S (2 * m + 2)) by lia.
    rewrite odd_pow_S_sub1, Hgray.
    replace (2 * m + 4) with (S (2 * m + 3)) by lia.
    rewrite odd_pow_S_sub1.
    replace (2 * m + 5) with (S (S (S (2 * m + 2)))) by lia.
    cbn[Nat.pow]. remember (2 ^ (2 * m + 2)) as p.
    assert (0 < p) by (subst p; lia). destruct p; cbn in *; lia.
Qed.

Lemma di_mid_HD_target m:
  di_tail m +l L1 (ctzS (gray (di_tail m))) +l
    lsum (1 + gray (di_tail m) - (2 ^ (2 * m + 5) - 2))
      (2 ^ (2 * m + 5) - 2) = hz_hd0 m.
Proof.
  pose proof (di_tail_data m) as [_ [_ [_ Hgray]]]. rewrite Hgray.
  replace (2 * m + 5) with (S (S (2 * m + 3))) by lia.
  rewrite ctzS_pow_SS_sub3.
  replace (1 + (2 ^ S (S (2 * m + 3)) - 3) -
    (2 ^ S (S (2 * m + 3)) - 2)) with 0 by pow_lia.
  rewrite lsum_0_pow_SS_sub2.
  unfold di_tail, hz_hd0.
  replace (2 * m + 4) with (S (2 * m + 3)) by lia.
  replace (2 * m + 3) with (S (2 * m + 2)) by lia.
  cbn[L1 ladd]. f_equal.
  - pow_lia.
  - change (((2 ^ S (2 * m + 2) - 1) :: pow_down (2 * m + 2)) +l
      L1 0 +l pow_counts (S (2 * m + 2)) =
      pow_down_ge2 (S (2 * m + 2))).
    apply pow_down_pred_cons_add_counts.
Qed.

Lemma di_mid_HD m: HD (di_mid m) (hz_hd0 m).
Proof.
  pose proof (di_tail_data m) as [Hlen [Hwf [Htp Hgray]]].
  unfold di_mid. eapply HD_exact.
  - exact Hwf.
  - rewrite Hgray, Hlen. pow_lia.
  - cbn[tp]. rewrite Htp.
    replace (2 * m + 5) with (S (S (2 * m + 3))) by lia.
    rewrite odd_pow_SS_sub2. reflexivity.
  - symmetry. apply di_mid_HD_target.
Qed.

Lemma hz_hd0_HZI_target m:
  pow_down_ge2 (2 * m + 3) +l
    (Helper.lpow [0] (length (pow_down_ge2 (2 * m + 3)) - 1) ++
      [1; 0; 0]) +l
    lsum (2 ^ length (pow_down_ge2 (2 * m + 3)) - 1)
      ((2 ^ (2 * m + 4) - 1) * 2) = hz_mid1 m.
Proof.
  replace (2 * m + 3) with (S (2 * m + 2)) by lia.
  rewrite pow_down_ge2_length.
  replace (S (2 * m + 2) + 2 - 1) with (S (S (2 * m + 2))) by lia.
  replace (S (2 * m + 2) + 2) with (S (S (S (2 * m + 2)))) by lia.
  replace ((2 ^ (2 * m + 4) - 1) * 2)
    with (2 ^ S (S (S (2 * m + 2))) - 2) by pow_lia.
  rewrite lsum_pow_high_sub2.
  unfold hz_mid1.
  replace (2 * m + 5) with (S (S (S (2 * m + 2)))) by lia.
  replace (2 * m + 4) with (S (S (2 * m + 2))) by lia.
  cbn[pow_down_ge2 pow_down Helper.lpow app ladd]. f_equal.
  - pow_lia.
  - replace (2 * m + 3) with (S (2 * m + 2)) by lia.
    apply hzi_tail_combine.
Qed.

Lemma hz_hd0_HZI m: HZI (hz_hd0 m) (hz_mid1 m).
Proof.
  unfold hz_hd0. replace (2 ^ (2 * m + 5) - 2) with
    ((2 ^ (2 * m + 4) - 1) * 2) by pow_lia.
  eapply HZI_exact.
  - apply pow_down_ge2_WF'.
  - apply pow_down_ge2_gray0.
  - rewrite pow_down_ge2_length. pow_lia.
  - symmetry. apply hz_hd0_HZI_target.
Qed.

Lemma hz_mid1_tail_data m:
  let tail := (2 ^ (2 * m + 4) - 1) :: pow_down (2 * m + 3) in
  length tail = 2 * m + 6 /\ WF tail /\ tp tail = tp0 /\
  gray tail = 2 ^ (2 * m + 5) - 2.
Proof.
  pose proof (pow_down_length (2 * m + 3)) as Hlen.
  pose proof (pow_down_WF (2 * m + 3)) as Hwf.
  pose proof (pow_down_pred_cons_data (2 * m + 3)) as [Htp Hgray].
  cbn zeta. repeat split.
  - cbn[length]. lia.
  - constructor; [pow_lia|exact Hwf].
  - replace (2 * m + 4) with (S (2 * m + 3)) by lia. exact Htp.
  - replace (2 * m + 4) with (S (2 * m + 3)) by lia.
    replace (2 * m + 5) with (S (S (2 * m + 3))) by lia. exact Hgray.
Qed.

Lemma hz_mid1_HD_target m:
  let tail := (2 ^ (2 * m + 4) - 1) :: pow_down (2 * m + 3) in
  tail +l L1 (ctzS (gray tail)) +l
    lsum (1 + gray tail - (2 ^ (2 * m + 5) - 1))
      (2 ^ (2 * m + 5) - 1) = hz_hd1 m.
Proof.
  pose proof (hz_mid1_tail_data m) as [_ [_ [_ Hgray]]].
  cbn zeta in *. rewrite Hgray.
  replace (2 * m + 5) with (S (2 * m + 4)) by lia.
  rewrite ctzS_pow_S_sub2.
  replace (1 + (2 ^ S (2 * m + 4) - 2) -
    (2 ^ S (2 * m + 4) - 1)) with 0 by pow_lia.
  rewrite lsum_0_pow_succ_sub1.
  unfold hz_hd1.
  replace (2 * m + 4) with (S (2 * m + 3)) by lia.
  apply pow_down_pred_cons_add_counts.
Qed.

Lemma hz_mid1_HD m: HD (hz_mid1 m) (hz_hd1 m).
Proof.
  pose proof (hz_mid1_tail_data m) as [Hlen [Hwf [Htp Hgray]]].
  unfold hz_mid1. eapply HD_exact.
  - exact Hwf.
  - rewrite Hgray, Hlen. pow_lia.
  - change (xorb
      (tp ((2 ^ (2 * m + 4) - 1) :: pow_down (2 * m + 3)))
      (Nat.odd (2 ^ (2 * m + 5) - 1)) = tp1).
    rewrite Htp.
    replace (2 * m + 5) with (S (2 * m + 4)) by lia.
    rewrite odd_pow_S_sub1. reflexivity.
  - symmetry. apply hz_mid1_HD_target.
Qed.

Lemma hz_hd1_HZI_target m:
  pow_down_ge2 (2 * m + 3) +l
    (Helper.lpow [0] (length (pow_down_ge2 (2 * m + 3)) - 1) ++
      [1; 0; 0]) +l
    lsum (2 ^ length (pow_down_ge2 (2 * m + 3)) - 1)
      (2 ^ (2 * m + 5)) = hz_mid2 m.
Proof.
  rewrite pow_down_ge2_length.
  replace (2 * m + 3 + 2 - 1) with (S (S (2 * m + 2))) by lia.
  replace (2 * m + 3 + 2) with (S (S (S (2 * m + 2)))) by lia.
  replace (2 * m + 5) with (S (S (S (2 * m + 2)))) by lia.
  rewrite lsum_pow_high_full.
  unfold hz_mid2.
  replace (2 * m + 5) with (S (S (2 * m + 3))) by lia.
  cbn[pow_down].
  replace (2 * m + 3) with (S (2 * m + 2)) by lia.
  change (pow_down_ge2 (S (2 * m + 2)) +l
    (0 :: Helper.lpow [0] (S (2 * m + 2)) ++ [1; 0; 0]) +l
    (2 ^ S (S (2 * m + 2)) :: pow_counts_dup (S (2 * m + 2))) =
    2 ^ S (S (S (2 * m + 2))) :: pow_down (S (S (2 * m + 2)))).
  apply hzi_tail_combine_strong.
Qed.

Lemma hz_hd1_HZI m: HZI (hz_hd1 m) (hz_mid2 m).
Proof.
  unfold hz_hd1. replace (2 * m + 4) with (S (2 * m + 3)) by lia.
  cbn[pow_down_ge2].
  replace (2 ^ S (S (2 * m + 3))) with
    (2 ^ S (2 * m + 3) * 2) by pow_lia.
  eapply HZI_exact.
  - apply pow_down_ge2_WF'.
  - apply pow_down_ge2_gray0.
  - rewrite pow_down_ge2_length. pow_lia.
  - replace (2 ^ S (2 * m + 3) * 2) with (2 ^ (2 * m + 5)) by pow_lia.
    symmetry. apply hz_hd1_HZI_target.
Qed.

Lemma hz_mid2_HD_target m:
  let tail := pow_down (2 * m + 4) in
  tail +l L1 (ctzS (gray tail)) +l
    lsum (1 + gray tail - 2 ^ (2 * m + 5)) (2 ^ (2 * m + 5)) =
    hz_hd2 m.
Proof.
  pose proof (pow_down_tp_gray (2 * m + 4)) as [_ Hgray].
  cbn zeta in *. rewrite Hgray.
  replace (2 * m + 5) with (S (2 * m + 4)) by lia.
  rewrite ctzS_pow_sub1.
  replace (1 + (2 ^ S (2 * m + 4) - 1) - 2 ^ S (2 * m + 4))
    with 0 by pow_lia.
  rewrite lsum_0_pow_succ, pow_down_add_counts_dup.
  unfold hz_hd2.
  replace (2 * m + 4) with (S (2 * m + 3)) by lia.
  cbn[pow_down_ge2 L1 lmul2 ladd]. f_equal; pow_lia.
Qed.

Lemma hz_mid2_HD m: HD (hz_mid2 m) (hz_hd2 m).
Proof.
  pose proof (pow_down_length (2 * m + 4)) as Hlen.
  pose proof (pow_down_WF (2 * m + 4)) as Hwf.
  pose proof (pow_down_tp_gray (2 * m + 4)) as [Htp Hgray].
  unfold hz_mid2. replace (2 * m + 5) with (S (2 * m + 4)) by lia.
  cbn[pow_down]. eapply HD_exact.
  - exact Hwf.
  - rewrite Hgray, Hlen. pow_lia.
  - cbn[tp]. rewrite Htp, odd_pow_S. reflexivity.
  - replace (2 ^ S (2 * m + 4)) with (2 ^ (2 * m + 5)) by pow_lia.
    symmetry. apply hz_mid2_HD_target.
Qed.

Lemma hz_hd2_HZI_target m:
  let tail := pow_down_ge2 (2 * m + 3) +l lmul2 (L1 (2 * m + 4)) in
  tail +l (Helper.lpow [0] (length tail - 1) ++ [1; 0; 0]) +l
    lsum (2 ^ length tail - 1) (2 ^ (2 * m + 5)) = hz_low m.
Proof.
  replace (2 * m + 4) with (S (2 * m + 3)) by lia.
  pose proof (pow_down_ge2_last2_data (2 * m + 3)) as [Hlen _].
  cbn zeta in *. rewrite Hlen.
  replace (2 * m + 3 + 2 - 1) with (S (2 * m + 3)) by lia.
  replace (2 * m + 3 + 2) with (S (S (2 * m + 3))) by lia.
  replace (2 * m + 5) with (S (S (2 * m + 3))) by lia.
  rewrite lsum_pow_full. unfold hz_low. apply hzi_tail_combine_low.
Qed.

Lemma hz_hd2_HZI m: HZI (hz_hd2 m) (hz_low m).
Proof.
  pose proof (pow_down_ge2_last2_data (2 * m + 3)) as [Hlen [Hwf Hgray]].
  unfold hz_hd2. replace (2 * m + 4) with (S (2 * m + 3)) by lia.
  replace (2 ^ (2 * m + 5)) with
    (2 ^ S (2 * m + 3) * 2) by pow_lia.
  eapply HZI_exact.
  - exact Hwf.
  - exact Hgray.
  - rewrite Hlen. pow_lia.
  - replace (2 ^ S (2 * m + 3) * 2) with
      (2 ^ (2 * m + 5)) by pow_lia.
    replace (S (2 * m + 3)) with (2 * m + 4) by lia.
    symmetry. apply hz_hd2_HZI_target.
Qed.

Lemma hz_low_next m: hz_low m = hz_low_odd (S m).
Proof.
  unfold hz_low.
  replace (2 * m + 3) with (2 * S m + 1) by lia.
  apply hz_low_from_odd.
Qed.

Lemma prefix_run m:
  S1 (di_mid m) 0 -->* S1 (hz_low_odd (S m)) 0.
Proof.
  rewrite <-hz_low_next.
  eapply evstep_trans; [apply HD_run, di_mid_HD|].
  eapply evstep_trans; [apply HZI_run, hz_hd0_HZI|].
  eapply evstep_trans; [apply HD_run, hz_mid1_HD|].
  eapply evstep_trans; [apply HZI_run, hz_hd1_HZI|].
  eapply evstep_trans; [apply HD_run, hz_mid2_HD|].
  apply HZI_run, hz_hd2_HZI.
Qed.

Import ListNotations.


Lemma HDZD_exact a tail dst:
  WF tail ->
  2 <= length tail ->
  2 ^ (length tail - 2) <= 1 + gray tail < 2 ^ length tail ->
  a < 2 ^ length tail ->
  tp ((1 + gray tail) + (1 + a) :: tail) = tp1 ->
  dst = tail +l L1 (ctzS (gray tail)) +l lsum 0 (1 + gray tail) +l
    (Helper.lpow [0] (length tail - 1) ++ [1; 0; 0]) +l
    lsum (2 ^ length tail - 1 - a) a ->
  HDZD ((1 + gray tail) + (1 + a) :: tail) dst.
Proof.
  intros Hwf Hlen Hrange Ha Htp ->.
  destruct (HDZD_spec a tail Hwf Hlen Hrange Ha Htp) as [ys H].
  replace
    (tail +l L1 (ctzS (gray tail)) +l lsum 0 (1 + gray tail) +l
      (Helper.lpow [0] (length tail - 1) ++ [1; 0; 0]) +l
      lsum (2 ^ length tail - 1 - a) a)
    with ys.
  - exact H.
  - inversion H; subst.
    match goal with
    | H : gray tail + S ?a0 = gray tail + S a |- _ =>
        replace a0 with a in * by lia
    end.
    rewrite <-L1_fold. reflexivity.
Qed.

Lemma HI_exact a tail dst:
  WF tail ->
  gray tail <> 0 ->
  a + (gray tail - 1) < 2 ^ length tail ->
  tp (a :: tail) = tp0 ->
  dst = tail +l L1 (ctzS (gray tail - 1)) +l
    lsum (gray tail - 1) a ->
  HI (a :: tail) dst.
Proof.
  intros Hwf Hgray Hbound Htp ->.
  destruct (HI_spec a tail Hwf Hgray Hbound Htp) as [ys H].
  replace
    (tail +l L1 (ctzS (gray tail - 1)) +l
      lsum (gray tail - 1) a)
    with ys.
  - exact H.
  - inversion H; subst. rewrite <-L1_fold. reflexivity.
Qed.


Lemma lsum_pow_S_sub2_add1 n:
  lsum (2 ^ S n - 2) (2 ^ S n + 1) =
  (2 ^ n + 1) :: lsum 0 (2 ^ n).
Proof.
  replace (2 ^ S n - 2) with ((2 ^ n - 1) * 2) by
    (cbn[Nat.pow]; lia).
  replace (2 ^ S n + 1) with (S (2 * S (2 ^ n - 1))) by
    (cbn[Nat.pow]; lia).
  rewrite lsum_S'.
  replace ((2 ^ n - 1) * 2 + 2 * S (2 ^ n - 1))
    with ((2 * 2 ^ n - 1) * 2) by lia.
  rewrite ctzS_0, lsum_even_pairs.
  replace (S (2 ^ n - 1)) with (2 ^ n) by lia.
  rewrite lsum_pow_pred_cycle. cbn[Helper.lpow app ladd]. f_equal; pow_lia.
Qed.

Lemma odd_pow_S_add_even n k:
  Nat.Even k -> Nat.odd (2 ^ S n + k) = tp0.
Proof.
  intros [j ->].
  replace (2 ^ S n + 2 * j) with ((2 ^ n + j) * 2) by
    (cbn[Nat.pow]; lia).
  apply odd_0.
Qed.

Lemma odd_pow_S_add_odd n k:
  Nat.Odd k -> Nat.odd (2 ^ S n + k) = tp1.
Proof.
  intros [j ->].
  replace (2 ^ S n + (2 * j + 1)) with (1 + (2 ^ n + j) * 2) by
    (cbn[Nat.pow]; lia).
  apply odd_1.
Qed.

Lemma reentry_tail_WF m: WF (reentry_tail m).
Proof.
  induction m.
  - do 4 (constructor; [lia|]).
    change (WF (Helper.lpow [0] 1)). apply WF_O.
  - cbn[reentry_tail]. repeat constructor; try exact IHm; pow_lia.
Qed.

Lemma reentry_tail_tp_gray m:
  tp (reentry_tail m) = tp1 /\
  gray (reentry_tail m) = 2 ^ (2 * m + 4) - 1.
Proof.
  induction m as [|m [Htp Hgray]].
  - split; reflexivity.
  - cbn[reentry_tail tp gray]. rewrite Htp, Hgray.
    assert (Hodd5: Nat.odd (2 ^ (2 * m + 5) + 2) = tp0).
    { replace (2 * m + 5) with (S (2 * m + 4)) by lia.
      apply odd_pow_S_add_even. exists 1. reflexivity. }
    assert (Hodd4: Nat.odd (2 ^ (2 * m + 4)) = tp0).
    { replace (2 * m + 4) with (S (2 * m + 3)) by lia.
      apply odd_pow_S. }
    rewrite Hodd5, Hodd4.
    split; [reflexivity|].
    replace (2 * S m + 4) with (S (S (2 * m + 4))) by lia.
    cbn[Nat.pow]. remember (2 ^ (2 * m + 4)) as p.
    assert (0 < p) by (subst p; lia).
    destruct p; cbn in *; lia.
Qed.

Lemma reentry_prev_tail_WF m: WF (reentry_prev_tail m).
Proof.
  induction m.
  - do 4 (constructor; [lia|]). change (WF (Helper.lpow [0] 2)). apply WF_O.
  - cbn[reentry_prev_tail]. repeat constructor; try exact IHm; pow_lia.
Qed.

Lemma reentry_prev_tail_tp_gray m:
  tp (reentry_prev_tail m) = tp1 /\
  gray (reentry_prev_tail m) = 2 ^ (2 * m + 4) - 1.
Proof.
  induction m as [|m [Htp Hgray]].
  - split; reflexivity.
  - cbn[reentry_prev_tail tp gray]. rewrite Htp, Hgray.
    assert (Hodd5: Nat.odd (2 ^ (2 * m + 5)) = tp0).
    { replace (2 * m + 5) with (S (2 * m + 4)) by lia.
      apply odd_pow_S. }
    assert (Hodd4: Nat.odd (2 ^ (2 * m + 4) + 2) = tp0).
    { replace (2 * m + 4) with (S (2 * m + 3)) by lia.
      apply odd_pow_S_add_even. exists 1. reflexivity. }
    rewrite Hodd5, Hodd4.
    split; [reflexivity|].
    replace (2 * S m + 4) with (S (S (2 * m + 4))) by lia.
    cbn[Nat.pow]. remember (2 ^ (2 * m + 4)) as p.
    assert (0 < p) by (subst p; lia).
    destruct p; cbn in *; nia.
Qed.

Lemma reentry_tail_cons_data m:
  WF (2 ^ (2 * m + 4) :: reentry_tail m) /\
  tp (2 ^ (2 * m + 4) :: reentry_tail m) = tp1 /\
  gray (2 ^ (2 * m + 4) :: reentry_tail m) =
    2 ^ (2 * m + 5) - 1 /\
  length (2 ^ (2 * m + 4) :: reentry_tail m) = 2 * m + 6.
Proof.
  pose proof (reentry_tail_tp_gray m) as [Htp Hgray].
  repeat split.
  - constructor; [pow_lia|apply reentry_tail_WF].
  - cbn[tp]. rewrite Htp.
    replace (2 * m + 4) with (S (2 * m + 3)) by lia.
    rewrite odd_pow_S. reflexivity.
  - cbn[gray tp]. rewrite Htp.
    assert (Hodd: Nat.odd (2 ^ (2 * m + 4)) = tp0).
    { replace (2 * m + 4) with (S (2 * m + 3)) by lia.
      apply odd_pow_S. }
    rewrite Hodd, Hgray.
    replace (2 * m + 5) with (S (2 * m + 4)) by lia.
    cbn[Nat.pow]. remember (2 ^ (2 * m + 4)) as p.
    assert (0 < p) by (subst p; lia). destruct p; cbn in *; lia.
  - cbn[length]. rewrite reentry_tail_length. lia.
Qed.

Lemma HI_tail m:
  reentry_prev_tail m +l lsum 0 (2 ^ (2 * m + 4)) =
  2 ^ (2 * m + 4) :: reentry_tail m.
Proof.
  induction m.
  - reflexivity.
  - cbn[reentry_prev_tail reentry_tail].
    replace (2 * S m + 4) with (S (S (2 * m + 4))) by lia.
    replace (2 ^ S (S (2 * m + 4))) with
      ((2 * 2 ^ (2 * m + 4)) * 2) by (cbn[Nat.pow]; lia).
    rewrite lsum_0_double_pos by pow_lia.
    replace (2 * 2 ^ (2 * m + 4)) with (2 ^ (2 * m + 4) * 2) by lia.
    rewrite lsum_0_double_pos by pow_lia.
    cbn[ladd]. f_equal; [pow_lia|]. f_equal; [pow_lia|exact IHm].
Qed.

Definition hdzd_core m :=
  (2 ^ (2 * m + 4) :: reentry_tail m) +l L1 (2 * m + 5) +l
  pow_counts_dup (2 * m + 4) +l
  (Helper.lpow [0] (2 * m + 5) ++ [1; 0; 0]).

Lemma hdzd_core_eq m:
  hdzd_core m =
  2 ^ (2 * m + 5) :: (2 ^ (2 * m + 4) + 2) ::
    reentry_prev_tail m.
Proof.
  induction m.
  - reflexivity.
  - unfold hdzd_core in IHm |- *.
    cbn[reentry_tail reentry_prev_tail].
    replace (2 * S m + 5) with (S (S (2 * m + 5))) by lia.
    replace (2 * S m + 4) with (S (S (2 * m + 4))) by lia.
    cbn[L1 pow_counts_dup Helper.lpow app ladd].
    f_equal; [pow_lia|]. f_equal; [pow_lia|exact IHm].
Qed.

Lemma pre_reentry_HDZD m: HDZD (pre_reentry m) (reentry_prev m).
Proof.
  pose proof (reentry_tail_cons_data m) as [Hwf [Htp [Hgray Hlen]]].
  assert (Hsource: pre_reentry m =
    ((1 + gray (2 ^ (2 * m + 4) :: reentry_tail m)) + (1 + 1)) ::
      2 ^ (2 * m + 4) :: reentry_tail m).
  { unfold pre_reentry. rewrite Hgray. f_equal. pow_lia. }
  rewrite Hsource.
  apply HDZD_exact.
  - exact Hwf.
  - rewrite Hlen. lia.
  - rewrite Hlen, Hgray.
    replace (2 * m + 6 - 2) with (2 * m + 4) by lia.
    replace (2 * m + 5) with (S (2 * m + 4)) by lia.
    replace (2 * m + 6) with (S (S (2 * m + 4))) by lia.
    cbn[Nat.pow]. remember (2 ^ (2 * m + 4)) as p.
    assert (0 < p) by (subst p; lia). lia.
  - rewrite Hlen. pow_lia.
  - rewrite <-Hsource. unfold pre_reentry.
    change (xorb (tp (2 ^ (2 * m + 4) :: reentry_tail m))
      (Nat.odd (2 ^ (2 * m + 5) + 2)) = tp1).
    rewrite Htp.
    assert (Hodd: Nat.odd (2 ^ (2 * m + 5) + 2) = tp0).
    { replace (2 * m + 5) with (S (2 * m + 4)) by lia.
      apply odd_pow_S_add_even. exists 1. reflexivity. }
    rewrite Hodd. reflexivity.
  - rewrite Hgray, Hlen, ctzS_pow_sub1.
    replace (1 + (2 ^ (2 * m + 5) - 1)) with (2 ^ (2 * m + 5))
      by pow_lia.
    replace (lsum 0 (2 ^ (2 * m + 5)))
      with (pow_counts_dup (2 * m + 4)).
    2:{ replace (2 * m + 5) with (S (2 * m + 4)) by lia.
        symmetry. apply lsum_0_pow_succ. }
    replace (2 * m + 6 - 1) with (2 * m + 5) by lia.
    rewrite lsum_1.
    replace (ctzS (2 ^ (2 * m + 6) - 1 - 1)) with 0.
    2:{ replace (2 * m + 6) with (S (2 * m + 5)) by lia.
        replace (2 ^ S (2 * m + 5) - 1 - 1)
          with (2 ^ S (2 * m + 5) - 2) by lia.
        symmetry. apply ctzS_pow_S_sub2. }
    unfold reentry_prev.
    fold (hdzd_core m). rewrite hdzd_core_eq.
    cbn[L1 ladd]. reflexivity.
Qed.

Lemma reentry_prev_tail_data m:
  WF ((2 ^ (2 * m + 4) + 2) :: reentry_prev_tail m) /\
  tp ((2 ^ (2 * m + 4) + 2) :: reentry_prev_tail m) = tp1 /\
  gray ((2 ^ (2 * m + 4) + 2) :: reentry_prev_tail m) =
    2 ^ (2 * m + 5) - 1 /\
  length ((2 ^ (2 * m + 4) + 2) :: reentry_prev_tail m) = 2 * m + 7.
Proof.
  pose proof (reentry_prev_tail_tp_gray m) as [Htp Hgray].
  repeat split.
  - constructor; [pow_lia|apply reentry_prev_tail_WF].
  - cbn[tp]. rewrite Htp.
    replace (2 * m + 4) with (S (2 * m + 3)) by lia.
    rewrite odd_pow_S_add_even by (exists 1; reflexivity). reflexivity.
  - cbn[gray tp]. rewrite Htp.
    assert (Hodd: Nat.odd (2 ^ (2 * m + 4) + 2) = tp0).
    { replace (2 * m + 4) with (S (2 * m + 3)) by lia.
      apply odd_pow_S_add_even. exists 1. reflexivity. }
    rewrite Hodd, Hgray.
    replace (2 * m + 5) with (S (2 * m + 4)) by lia.
    cbn[Nat.pow]. remember (2 ^ (2 * m + 4)) as p.
    assert (0 < p) by (subst p; lia). destruct p; cbn in *; lia.
  - cbn[length]. rewrite reentry_prev_tail_length. lia.
Qed.

Lemma reentry_prev_HI m: HI (reentry_prev m) (reentry m).
Proof.
  pose proof (reentry_prev_tail_data m) as [Hwf [Htp [Hgray Hlen]]].
  unfold reentry_prev at 1.
  apply HI_exact; try assumption.
  - rewrite Hgray. pow_lia.
  - rewrite Hgray, Hlen. pow_lia.
  - change (xorb
      (tp (2 ^ (2 * m + 4) + 2 :: reentry_prev_tail m))
      (Nat.odd (2 ^ (2 * m + 5) + 1)) = tp0).
    rewrite Htp.
    assert (Hodd: Nat.odd (2 ^ (2 * m + 5) + 1) = tp1).
    { replace (2 * m + 5) with (S (2 * m + 4)) by lia.
      apply odd_pow_S_add_odd. exists 0. reflexivity. }
    rewrite Hodd. reflexivity.
  - rewrite Hgray.
    replace (ctzS (2 ^ (2 * m + 5) - 1 - 1)) with 0.
    2:{ replace (2 * m + 5) with (S (2 * m + 4)) by lia.
        replace (2 ^ S (2 * m + 4) - 1 - 1)
          with (2 ^ S (2 * m + 4) - 2) by lia.
        symmetry. apply ctzS_pow_S_sub2. }
    replace
      (lsum (2 ^ (2 * m + 5) - 1 - 1) (2 ^ (2 * m + 5) + 1))
      with ((2 ^ (2 * m + 4) + 1) ::
        lsum 0 (2 ^ (2 * m + 4))).
    2:{ replace (2 * m + 5) with (S (2 * m + 4)) by lia.
        replace (2 ^ S (2 * m + 4) - 1 - 1)
          with (2 ^ S (2 * m + 4) - 2) by lia.
        symmetry. apply lsum_pow_S_sub2_add1. }
    cbn[L1 ladd]. rewrite ladd_nil_r, HI_tail.
    unfold reentry. f_equal. pow_lia.
Qed.

Lemma reentry_tail_S m: reentry_tail (S m) = pre_reentry m.
Proof. unfold pre_reentry. cbn[reentry_tail]. f_equal; pow_lia. Qed.

Lemma overflow_tail m:
  S1 (hz_low_odd (S m)) 0 -->* S1 (reentry m) 0.
Proof.
  eapply evstep_trans.
  - pose proof (HZBridge_run _ _ _ (hz_bridge m)) as H.
    rewrite reentry_tail_S in H. exact H.
  - eapply evstep_trans.
    + eapply HDZD_run, pre_reentry_HDZD.
    + eapply HI_run, reentry_prev_HI.
Qed.

Import ListNotations.


Ltac pow_flia :=
  repeat first [rewrite Nat.pow_add_r in * | cbn[Nat.pow] in *];
  flia.

Fixpoint hoi_bank m :=
match m with
| 0 => [8; 3; 1; 1; 0]
| S m => 2 ^ (2 * m + 5) :: (2 ^ (2 * m + 4) - 2) :: hoi_bank m
end.

Definition hoi_pending m :=
match m with
| 0 => [7; 3; 1; 1; 0]
| S m => (2 ^ (2 * m + 5) - 1) ::
    (2 ^ (2 * m + 4) - 2) :: hoi_bank m
end.

Definition di_suffix q :=
match q with
| 0 => hoi_bank 0
| S q => 2 ^ (2 * S q + 3) :: di_tail q
end.

Fixpoint di_prefix start count tail :=
match count with
| 0 => tail
| S count =>
    2 ^ (2 * (start + count) + 5) ::
    (2 ^ (2 * (start + count) + 4) - 2) ::
    di_prefix start count tail
end.

Definition active_tail q p :=
  (2 ^ (2 * (q + p + 1) + 4) - 3) ::
  (2 ^ (2 * (q + p + 1) + 3) - 1) ::
  (2 ^ (2 * (q + p + 1) + 2) - 2) ::
  di_prefix q p (di_suffix q).

Definition active q p :=
  (2 ^ (2 * (q + p + 1) + 5) - 2) :: active_tail q p.

Definition top0_tail m :=
  (2 ^ (2 * m + 4) - 3) ::
  (2 ^ (2 * m + 3) - 1) ::
  (2 ^ (2 * m + 2) - 1) ::
  (2 ^ (2 * m + 1) - 1) :: pow_down (2 * m).

Definition top0 m := (2 ^ (2 * m + 5) - 2) :: top0_tail m.

Definition top1_tail m :=
  (2 ^ (2 * m + 4) - 2) ::
  (2 ^ (2 * m + 3) - 1) ::
  (2 ^ (2 * m + 2) - 1) :: pow_down (2 * m + 1).

Definition top1 m := (2 ^ (2 * m + 5) - 2) :: top1_tail m.

Lemma lsum_pow_pred_double_full n:
  lsum (2 ^ S n - 1) (2 ^ S (S n) - 1) =
  (2 ^ S n - 1) :: pow_counts_dup n.
Proof.
  induction n.
  - reflexivity.
  - replace (2 ^ S (S n) - 1) with
      (1 + (2 ^ S n - 1) * 2) by pow_lia.
    replace (2 ^ S (S (S n)) - 1) with
      (2 ^ S (S (S n)) - 2 + 1) by pow_lia.
    rewrite lsum_add.
    replace (2 ^ S (S (S n)) - 2) with
      (2 * S (2 ^ S (S n) - 2)) by pow_lia.
    rewrite lsum_odd_pairs.
    replace (S (2 ^ S (S n) - 2)) with (2 ^ S (S n) - 1) by pow_lia.
    rewrite IHn, lsum_1.
    replace (ctzS (1 + (2 ^ S n - 1) * 2 +
      2 * (2 ^ S (S n) - 1))) with 1.
    2:{ replace (1 + (2 ^ S n - 1) * 2 + 2 * (2 ^ S (S n) - 1))
          with (1 + ((2 ^ S n - 1) + (2 ^ S (S n) - 1)) * 2) by lia.
        rewrite ctzS_1.
        replace ((2 ^ S n - 1) + (2 ^ S (S n) - 1)) with
          ((3 * 2 ^ n - 1) * 2) by pow_lia.
        rewrite ctzS_0. reflexivity. }
    cbn[pow_counts_dup L1 ladd]. f_equal; [pow_lia|].
    f_equal; [pow_lia|]. rewrite ladd_nil_r. reflexivity.
Qed.

Lemma lsum_pow_double_sub2 n:
  lsum (2 ^ S (S n) - 1) (2 ^ S (S (S n)) - 2) =
  (2 ^ S (S n) - 1) :: (2 ^ S n - 1) :: pow_counts_dup n.
Proof.
  replace (2 ^ S (S n) - 1) with
    (1 + (2 ^ S n - 1) * 2) by pow_lia.
  replace (2 ^ S (S (S n)) - 2) with
    (2 * S (2 ^ S (S n) - 2)) by pow_lia.
  rewrite lsum_odd_pairs.
  replace (S (2 ^ S (S n) - 2)) with (2 ^ S (S n) - 1) by pow_lia.
  rewrite lsum_pow_pred_double_full. f_equal; pow_lia.
Qed.

Lemma lsum_pow_high_double_sub4 n:
  lsum (2 ^ S (S (S n)) - 1) (2 ^ S (S (S (S n))) - 4) =
  (2 ^ S (S (S n)) - 2) ::
  (2 ^ S (S n) - 1) :: (2 ^ S n - 1) :: pow_counts_dup n.
Proof.
  replace (2 ^ S (S (S n)) - 1) with
    (1 + (2 ^ S (S n) - 1) * 2) by pow_lia.
  replace (2 ^ S (S (S (S n))) - 4) with
    (2 * S (2 ^ S (S (S n)) - 3)) by pow_lia.
  rewrite lsum_odd_pairs.
  replace (S (2 ^ S (S (S n)) - 3)) with
    (2 ^ S (S (S n)) - 2) by pow_lia.
  rewrite lsum_pow_double_sub2. reflexivity.
Qed.

Lemma source_body_tail_bank m:
  (source_body_tail m ++ [1; 0; 0; 0]) +l pow_counts_dup (2 * m + 3) =
  (2 ^ (2 * m + 4) - 2) :: hoi_bank m.
Proof.
  induction m.
  - reflexivity.
  - cbn[source_body_tail hoi_bank].
    replace (2 * S m + 3) with (S (S (2 * m + 3))) by lia.
    cbn[pow_counts_dup app ladd]. f_equal.
    + assert (2 <= 2 ^ (2 * m + 5)).
      { change (2 ^ 1 <= 2 ^ (2 * m + 5)). apply Nat.pow_le_mono_r; lia. }
      replace (S (S (2 * m + 3))) with (2 * m + 5) by lia.
      replace (2 * S m + 4) with (S (2 * m + 5)) by lia.
      cbn[Nat.pow]. lia.
    + f_equal.
      * pow_lia.
      * exact IHm.
Qed.

Lemma source_pending_eq m:
  (List.tl (source_body_tail m) ++ [1; 0; 0; 0]) +l
    ((2 ^ (2 * m + 2) - 1) :: pow_counts_dup (2 * m + 1)) =
  hoi_pending m.
Proof.
  induction m.
  - reflexivity.
  - cbn[source_body_tail hoi_pending List.tl].
    replace (2 * S m + 2) with (S (S (2 * m + 2))) by lia.
    replace (2 * S m + 1) with (S (S (2 * m + 1))) by lia.
    cbn[pow_counts_dup app ladd]. f_equal; [pow_lia|].
    replace (2 ^ S (S (2 * m + 1)) :: 2 ^ S (2 * m + 1) ::
      pow_counts_dup (2 * m + 1)) with (pow_counts_dup (2 * m + 3)).
    + apply source_body_tail_bank.
    + replace (2 * m + 3) with (S (S (2 * m + 1))) by lia. reflexivity.
Qed.

Lemma source_after_hoi_shape m:
  source_after_hoi m =
  (2 ^ (2 * m + 5) - 2) ::
  (2 ^ (2 * m + 4) - 3) :: hoi_pending m.
Proof.
  unfold source_after_hoi.
  rewrite source_body_length.
  unfold source_body.
  replace (2 ^ (2 * m + 3) * 2 - 1) with
    (2 ^ S (S (S (2 * m + 1))) - 1) by pow_lia.
  replace ((2 ^ (2 * m + 4) - 2) * 2) with
    (2 ^ S (S (S (S (2 * m + 1)))) - 4) by pow_lia.
  rewrite lsum_pow_high_double_sub4. cbn[app ladd].
  f_equal; [pow_lia|]. rewrite <-source_pending_eq.
  destruct m.
  - reflexivity.
  - cbn[source_body_tail List.tl app ladd]. f_equal.
    + assert (2 <= 2 ^ (2 * m + 5)).
      { change (2 ^ 1 <= 2 ^ (2 * m + 5)). apply Nat.pow_le_mono_r; lia. }
      replace (S (S (2 * S m + 1))) with (2 * m + 5) by lia.
      replace (2 * S m + 4) with (S (2 * m + 5)) by lia.
      cbn[Nat.pow]. lia.
    + replace (2 * S m + 2) with (S (2 * S m + 1)) by lia. reflexivity.
Qed.

Lemma di_prefix_bank p: di_prefix 0 p (hoi_bank 0) = hoi_bank p.
Proof.
  induction p.
  - reflexivity.
  - cbn[di_prefix].
    change (hoi_bank (S p)) with
      (2 ^ (2 * p + 5) :: (2 ^ (2 * p + 4) - 2) :: hoi_bank p).
    rewrite IHp. repeat f_equal; lia.
Qed.

Lemma source_after_hoi_0: source_after_hoi 0 = top0 0.
Proof. rewrite source_after_hoi_shape. reflexivity. Qed.

Lemma source_after_hoi_S p: source_after_hoi (S p) = active 0 p.
Proof.
  rewrite source_after_hoi_shape.
  unfold active, active_tail. cbn[hoi_pending di_suffix].
  rewrite di_prefix_bank.
  replace (2 * (0 + p + 1) + 5) with (2 * S p + 5) by lia.
  replace (2 * (0 + p + 1) + 4) with (2 * S p + 4) by lia.
  replace (2 * (0 + p + 1) + 3) with (2 * p + 5) by lia.
  replace (2 * (0 + p + 1) + 2) with (2 * p + 4) by lia.
  reflexivity.
Qed.

Lemma odd_pow_SSS_sub3 n: Nat.odd (2 ^ S (S (S n)) - 3) = tp1.
Proof.
  cbn[Nat.pow].
  replace (2 * (2 * (2 * 2 ^ n)) - 3) with
    (1 + (4 * 2 ^ n - 2) * 2) by lia.
  apply odd_1.
Qed.

Lemma di_suffix_data q:
  length (di_suffix q) = 2 * q + 5 /\
  WF (di_suffix q) /\ tp (di_suffix q) = tp1 /\
  gray (di_suffix q) = 2 ^ (2 * q + 4) - 5.
Proof.
  destruct q.
  - cbn[di_suffix hoi_bank length tp gray].
    split; [reflexivity|]. split.
    + do 4 (constructor; [lia|]). change (WF (Helper.lpow [0] 1)). apply WF_O.
    + split; reflexivity.
  - pose proof (di_tail_data q) as [Hlen [Hwf [Htp Hgray]]].
    cbn[di_suffix length]. repeat split.
    + lia.
    + constructor; [pow_lia|exact Hwf].
    + cbn[tp]. rewrite Htp.
      replace (2 * S q + 3) with (S (2 * S q + 2)) by lia.
      rewrite odd_pow_S. reflexivity.
    + cbn[gray tp]. rewrite Htp.
      replace (2 * S q + 3) with (S (2 * S q + 2)) by lia.
      rewrite odd_pow_S, Hgray.
      assert (8 <= 2 ^ (2 * q + 5)).
      { change (2 ^ 3 <= 2 ^ (2 * q + 5)). apply Nat.pow_le_mono_r; lia. }
      replace (2 * S q + 4) with (S (2 * q + 5)) by lia.
      cbn[Nat.pow xorb]. lia.
Qed.

Lemma di_prefix_data start count tail:
  length tail = 2 * start + 5 -> WF tail -> tp tail = tp1 ->
  gray tail = 2 ^ (2 * start + 4) - 5 ->
  length (di_prefix start count tail) = 2 * (start + count) + 5 /\
  WF (di_prefix start count tail) /\
  tp (di_prefix start count tail) = tp1 /\
  gray (di_prefix start count tail) =
    2 ^ (2 * (start + count) + 4) - 2 ^ (2 * count + 2) - 1.
Proof.
  intros Hlen Hwf Htp Hgray. induction count.
  - cbn[di_prefix]. split; [lia|]. split; [exact Hwf|].
    split; [exact Htp|]. rewrite Hgray.
    assert (8 <= 2 ^ (2 * start + 4)).
    { change (2 ^ 3 <= 2 ^ (2 * start + 4)). apply Nat.pow_le_mono_r; lia. }
    replace (2 * (start + 0) + 4) with (2 * start + 4) by lia.
    replace (2 * 0 + 2) with 2 by lia. cbn[Nat.pow]. lia.
  - destruct IHcount as [Hlen' [Hwf' [Htp' Hgray']]].
    cbn[di_prefix length]. split.
    + rewrite Hlen'. lia.
    + split.
      * repeat constructor; try exact Hwf'; pow_lia.
      * split.
        -- cbn[tp]. rewrite Htp'.
      replace (2 * (start + count) + 4) with
        (S (S (2 * (start + count) + 2))) by lia.
      rewrite odd_pow_SS_sub2.
      replace (2 * (start + count) + 5) with
        (S (2 * (start + count) + 4)) by lia.
      rewrite odd_pow_S. reflexivity.
        -- cbn[gray tp]. rewrite Htp'.
      replace (2 * (start + count) + 4) with
        (S (S (2 * (start + count) + 2))) by lia.
      rewrite odd_pow_SS_sub2.
      replace (2 * (start + count) + 5) with
        (S (2 * (start + count) + 4)) by lia.
      rewrite odd_pow_S, Hgray'.
      assert (Hlt: 2 ^ (2 * count + 2) <
        2 ^ (2 * (start + count) + 4)).
      { apply Nat.pow_lt_mono_r; lia. }
      replace (2 * (start + S count) + 4) with
        (S (S (2 * (start + count) + 4))) by lia.
      replace (2 * S count + 2) with (S (S (2 * count + 2))) by lia.
      cbn[Nat.pow xorb]. lia.
Qed.

Lemma active_tail_data q p:
  length (active_tail q p) = 2 * (q + p + 1) + 6 /\
  WF (active_tail q p) /\ tp (active_tail q p) = tp1 /\
  gray (active_tail q p) =
    2 ^ (2 * (q + p + 1) + 5) - 2 ^ (2 * p + 5) - 3.
Proof.
  pose proof (di_suffix_data q) as [Hslen [Hswf [Hstp Hsgray]]].
  pose proof (di_prefix_data q p (di_suffix q)
    Hslen Hswf Hstp Hsgray) as [Hlen [Hwf [Htp Hgray]]].
  unfold active_tail. cbn[length]. repeat split.
  - rewrite Hlen. lia.
  - repeat constructor; try exact Hwf; pow_lia.
  - cbn[tp]. rewrite Htp.
    replace (2 * (q + p + 1) + 2) with
      (S (S (2 * (q + p + 1)))) by lia.
    rewrite odd_pow_SS_sub2.
    replace (2 * (q + p + 1) + 3) with
      (S (2 * (q + p + 1) + 2)) by lia.
    rewrite odd_pow_S_sub1.
    replace (2 * (q + p + 1) + 4) with
      (S (S (S (2 * (q + p + 1) + 1)))) by lia.
    rewrite odd_pow_SSS_sub3. reflexivity.
  - cbn[gray tp]. rewrite Htp, Hgray.
    replace (2 * (q + p + 1) + 2) with
      (S (S (2 * (q + p + 1)))) by lia.
    rewrite odd_pow_SS_sub2.
    replace (2 * (q + p + 1) + 3) with
      (S (2 * (q + p + 1) + 2)) by lia.
    rewrite odd_pow_S_sub1.
    replace (2 * (q + p + 1) + 4) with
      (S (S (S (2 * (q + p + 1) + 1)))) by lia.
    rewrite odd_pow_SSS_sub3.
    assert (Hlt: 2 ^ (2 * p + 2) < 2 ^ (2 * (q + p) + 4)).
    { apply Nat.pow_lt_mono_r; lia. }
    replace (2 * (q + p + 1) + 5) with
      (S (S (S (2 * (q + p) + 4)))) by lia.
    replace (2 * p + 5) with (S (S (S (2 * p + 2)))) by lia.
    cbn[Nat.pow xorb]. lia.
Qed.

Lemma active_as_HDZD q p:
  active q p =
  ((1 + gray (active_tail q p)) +
    (1 + (2 ^ (2 * p + 5) - 1))) :: active_tail q p.
Proof.
  pose proof (active_tail_data q p) as [_ [_ [_ Hgray]]].
  unfold active. rewrite Hgray. f_equal.
  assert (H4: 2 ^ (2 * p + 7) <=
    2 ^ (2 * (q + p + 1) + 5)).
  { apply Nat.pow_le_mono_r; lia. }
  replace (2 * p + 7) with (S (S (2 * p + 5))) in H4 by lia.
  cbn[Nat.pow] in H4.
  remember (2 ^ (2 * (q + p + 1) + 5)) as a.
  remember (2 ^ (2 * p + 5)) as b. lia.
Qed.


Fixpoint counts_above base count :=
match count with
| 0 => []
| S count => 2 ^ (base + count) :: counts_above base count
end.

Lemma pow_gap_room c d:
  2 ^ S d + 2 <= 2 ^ (S (S c) + S d).
Proof.
  assert (H: 4 * 2 ^ S d <= 2 ^ (S (S c) + S d)).
  { replace (4 * 2 ^ S d) with (2 ^ S (S (S d))) by pow_lia.
    apply Nat.pow_le_mono_r; lia. }
  assert (2 <= 2 ^ S d).
  { change (2 ^ 1 <= 2 ^ S d). apply Nat.pow_le_mono_r; lia. }
  lia.
Qed.

Lemma pow_gap_step c d:
  2 ^ (S (S c) + S (S d)) - 2 ^ S (S d) - 2 =
  2 * S (2 ^ (S (S c) + S d) - 2 ^ S d - 2).
Proof.
  pose proof (pow_gap_room c d) as Hroom.
  replace (S (S c) + S (S d)) with (S (S (S c) + S d)) by lia.
  cbn[Nat.pow] in Hroom |- *. lia.
Qed.

Lemma pow_gap_ctz0 c d:
  ctzS (2 ^ (S (S c) + S d) - 2 ^ S d - 2) = 0.
Proof.
  replace (2 ^ (S (S c) + S d) - 2 ^ S d - 2) with
    ((2 ^ (S (S c) + d) - 2 ^ d - 1) * 2).
  - apply ctzS_0.
  - replace (S (S c) + S d) with (S (S (S c) + d)) by lia.
    cbn[Nat.pow]. pose proof (pow_gap_room c d). lia.
Qed.

Lemma lsum_0_pow_gap_combo c d:
  lsum 0 (2 ^ (S (S c) + S d) - 2 ^ S d - 2) +l pow_counts d =
  (2 ^ (S (S c) + d) - 1) :: counts_above (S (S c)) d ++
  (2 ^ S c - 1) :: pow_counts c.
Proof.
  induction d.
  - cbn[pow_counts counts_above app].
    replace (S (S c) + 1) with (S (S (S c))) by lia.
    replace (S (S c) + 0) with (S (S c)) by lia.
    replace (2 ^ S (S (S c)) - 2 ^ 1 - 2) with
      (2 * S (2 ^ S (S c) - 3)) by pow_lia.
    change 0 with (0 * 2) at 1. rewrite lsum_even_pairs.
    replace (S (2 ^ S (S c) - 3)) with (2 ^ S (S c) - 2) by pow_lia.
    rewrite lsum_0_pow_SS_sub2. cbn[ladd]. f_equal; pow_lia.
  - cbn[pow_counts counts_above app]. rewrite pow_gap_step.
    change 0 with (0 * 2) at 1. rewrite lsum_even_pairs. cbn[ladd].
    f_equal.
    + pose proof (pow_gap_room c d). pow_lia.
    + replace (S (2 ^ (S (S c) + S d) - 2 ^ S d - 2)) with
        ((2 ^ (S (S c) + S d) - 2 ^ S d - 2) + 1)
        by (pose proof (pow_gap_room c d); lia).
      rewrite lsum_add.
      replace (0 + (2 ^ (S (S c) + S d) - 2 ^ S d - 2)) with
        (2 ^ (S (S c) + S d) - 2 ^ S d - 2) by lia.
      rewrite lsum_1, pow_gap_ctz0.
      rewrite ladd_swap, IHd. cbn[L1 ladd]. f_equal.
      * pow_lia.
      * rewrite ladd_nil_r. reflexivity.
Qed.

Lemma pow_sub_block n d:
  2 ^ (n + d) - 1 - (2 ^ n - 1) = (2 ^ d - 1) * 2 ^ n.
Proof.
  rewrite Nat.pow_add_r. remember (2 ^ n) as a. remember (2 ^ d) as b.
  assert (0 < a) by (subst a; lia). assert (0 < b) by (subst b; lia).
  destruct a, b; cbn in *; nia.
Qed.

Lemma lsum_pow_block_pred m d:
  lsum ((2 ^ d - 1) * 2 ^ S m) (2 ^ S m - 1) = pow_counts m.
Proof.
  revert d. induction m; intro d.
  - cbn[Nat.pow]. rewrite lsum_1, ctzS_0. reflexivity.
  - replace (2 ^ S (S m) - 1) with (2 * (2 ^ S m - 1) + 1) by pow_lia.
    rewrite lsum_add.
    replace ((2 ^ d - 1) * 2 ^ S (S m)) with
      (((2 ^ d - 1) * 2 ^ S m) * 2) by pow_lia.
    replace (2 * (2 ^ S m - 1)) with (2 * S (2 ^ S m - 2)) by pow_lia.
    rewrite lsum_even_pairs.
    replace (S (2 ^ S m - 2)) with (2 ^ S m - 1) by pow_lia.
    rewrite IHm.
    replace (((2 ^ d - 1) * 2 ^ S m) * 2 + 2 * (2 ^ S m - 1))
      with (((2 ^ d - 1) * 2 ^ S m + (2 ^ S m - 1)) * 2) by lia.
    rewrite lsum_1, ctzS_0. cbn[L1 ladd pow_counts]. f_equal; [pow_lia|].
    rewrite ladd_nil_r. reflexivity.
Qed.

Definition active_combo q p :=
  (2 ^ (2 * (q + p + 1) + 4) - 1) ::
  counts_above (2 * q + 2) (2 * p + 4) ++
  (2 ^ S (2 * q) - 1) :: pow_counts (2 * q).

Definition hdzd_suffix_core q :=
  (2 ^ (2 * q + 3) - 1) ::
  (2 ^ (2 * q + 2) - 2) :: pow_down_ge2 (2 * q).

Definition hdzd_suffix q :=
match q with
| 0 => [7; 2; 2; 1; 0; 0]
| S q => (2 ^ (2 * S q + 3) - 1) ::
    (2 ^ (2 * S q + 2) - 2) :: pow_down (2 * S q + 1) ++ [0]
end.

Fixpoint hdzd_prefix start count tail :=
match count with
| 0 => tail
| S count => (2 ^ (2 * (start + count) + 5) - 2) ::
    2 ^ (2 * (start + count) + 4) :: hdzd_prefix start count tail
end.

Definition active_hdzd_core q p :=
  (2 ^ (2 * (q + p + 1) + 5) - 4) ::
  2 ^ (2 * (q + p + 1) + 4) ::
  (2 ^ (2 * (q + p + 1) + 3) - 2) ::
  2 ^ (2 * (q + p + 1) + 2) :: hdzd_prefix q p (hdzd_suffix_core q).

Definition active_hdzd q p :=
  (2 ^ (2 * (q + p + 1) + 5) - 4) ::
  2 ^ (2 * (q + p + 1) + 4) ::
  (2 ^ (2 * (q + p + 1) + 3) - 2) ::
  2 ^ (2 * (q + p + 1) + 2) :: hdzd_prefix q p (hdzd_suffix q).

Lemma ctzS_pow_gap_sub3 m d:
  2 <= m -> 1 <= d -> ctzS (2 ^ (m + d) - 2 ^ m - 3) = 1.
Proof.
  destruct m as [|[|m]]; intros Hm Hd; try lia.
  replace (2 ^ (S (S m) + d) - 2 ^ S (S m) - 3) with
    (1 + (2 ^ (S m + d) - 2 ^ S m - 2) * 2).
  - rewrite ctzS_1.
    replace (2 ^ (S m + d) - 2 ^ S m - 2) with
      ((2 ^ (m + d) - 2 ^ m - 1) * 2).
    + rewrite ctzS_0. reflexivity.
    + replace (S m + d) with (S (m + d)) by lia.
      cbn[Nat.pow].
      assert (2 ^ m < 2 ^ (m + d)) by (apply Nat.pow_lt_mono_r; lia).
      lia.
  - replace (S (S m) + d) with (S (S (m + d))) by lia.
    replace (S m + d) with (S (m + d)) by lia.
    cbn[Nat.pow].
    assert (2 ^ m < 2 ^ (m + d)) by (apply Nat.pow_lt_mono_r; lia).
    lia.
Qed.

Lemma active_tail_ctz q p: ctzS (gray (active_tail q p)) = 1.
Proof.
  pose proof (active_tail_data q p) as [_ [_ [_ Hgray]]]. rewrite Hgray.
  replace (2 * (q + p + 1) + 5) with (2 * p + 5 + (2 * q + 2)) by lia.
  apply ctzS_pow_gap_sub3; lia.
Qed.

Lemma active_lsum_combo q p:
  lsum 0 (1 + gray (active_tail q p)) +l pow_counts (2 * p + 4) =
  active_combo q p.
Proof.
  pose proof (active_tail_data q p) as [_ [_ [_ Hgray]]].
  unfold active_combo. rewrite Hgray.
  replace (1 + (2 ^ (2 * (q + p + 1) + 5) - 2 ^ (2 * p + 5) - 3))
    with (2 ^ (S (S (2 * q)) + S (2 * p + 4)) -
      2 ^ S (2 * p + 4) - 2).
  2:{ replace (S (S (2 * q)) + S (2 * p + 4)) with
        (2 * (q + p + 1) + 5) by lia.
      replace (S (2 * p + 4)) with (2 * p + 5) by lia.
      pose proof (pow_gap_room (2 * q) (2 * p + 4)) as Hroom.
      replace (S (S (2 * q)) + S (2 * p + 4)) with
        (2 * (q + p + 1) + 5) in Hroom by lia.
      replace (S (2 * p + 4)) with (2 * p + 5) in Hroom by lia.
      assert (4 <= 2 ^ (2 * p + 5)).
      { change (2 ^ 2 <= 2 ^ (2 * p + 5)). apply Nat.pow_le_mono_r; lia. }
      assert (4 * 2 ^ (2 * p + 5) <=
        2 ^ (2 * (q + p + 1) + 5)).
      { replace (4 * 2 ^ (2 * p + 5)) with (2 ^ (2 * p + 7)) by pow_lia.
        apply Nat.pow_le_mono_r; lia. }
      lia. }
  replace (2 * (q + p + 1) + 4) with
    (S (S (2 * q)) + (2 * p + 4)) by lia.
  replace (2 * q + 2) with (S (S (2 * q))) by lia.
  apply lsum_0_pow_gap_combo.
Qed.

Lemma active_lsum_last q p:
  lsum (2 ^ (2 * (q + p + 1) + 6) - 1 -
    (2 ^ (2 * p + 5) - 1)) (2 ^ (2 * p + 5) - 1) =
  pow_counts (2 * p + 4).
Proof.
  replace (2 * p + 5) with (S (2 * p + 4)) by lia.
  replace (2 ^ (2 * (q + p + 1) + 6) - 1 -
    (2 ^ S (2 * p + 4) - 1)) with
    ((2 ^ (2 * q + 3) - 1) * 2 ^ S (2 * p + 4)).
  2:{ replace (2 * (q + p + 1) + 6) with
        (S (2 * p + 4) + (2 * q + 3)) by lia.
      symmetry. apply pow_sub_block. }
  apply lsum_pow_block_pred.
Qed.

Lemma suffix_core_carry q:
  di_suffix q +l
    (counts_above (2 * q + 2) 2 ++
      (2 ^ S (2 * q) - 1) :: pow_counts (2 * q)) =
  2 ^ (2 * q + 4) :: hdzd_suffix_core q.
Proof.
  destruct q.
  - reflexivity.
  - unfold hdzd_suffix_core. cbn[di_suffix counts_above di_tail app ladd].
    f_equal.
    + assert (2 <= 2 ^ (2 * S q + 3)).
      { change (2 ^ 1 <= 2 ^ (2 * S q + 3)). apply Nat.pow_le_mono_r; lia. }
      replace (2 * S q + 4) with (S (2 * S q + 3)) by lia.
      replace (2 * S q + 2 + 1) with (2 * S q + 3) by lia.
      cbn[Nat.pow]. lia.
    + f_equal.
      * replace (2 * S q + 3) with (S (2 * q + 4)) by lia.
        replace (2 * S q + 2) with (2 * q + 4) by lia.
        cbn[Nat.pow]. pow_lia.
      * f_equal.
        -- replace (2 * S q + 2) with (S (2 * q + 3)) by lia.
           replace (S (2 * S q)) with (2 * q + 3) by lia.
           cbn[Nat.pow]. pow_lia.
        -- replace (2 * S q) with (2 * q + 2) by lia.
           apply pow_down_add_counts.
Qed.

Lemma prefix_core_carry q p:
  di_prefix q p (di_suffix q) +l
    (counts_above (2 * q + 2) (2 * p + 2) ++
      (2 ^ S (2 * q) - 1) :: pow_counts (2 * q)) =
  2 ^ (2 * (q + p) + 4) :: hdzd_prefix q p (hdzd_suffix_core q).
Proof.
  induction p.
  - cbn[di_prefix hdzd_prefix]. replace (q + 0) with q by lia.
    replace (2 * 0 + 2) with 2 by lia. apply suffix_core_carry.
  - cbn[di_prefix hdzd_prefix].
    replace (2 * S p + 2) with (S (S (2 * p + 2))) by lia.
    cbn[counts_above app ladd]. f_equal.
    + replace (2 * (q + S p) + 4) with (S (2 * (q + p) + 5)) by lia.
      replace (2 * q + 2 + S (2 * p + 2)) with
        (2 * (q + p) + 5) by lia. pow_lia.
    + f_equal.
      * replace (2 * (q + p) + 5) with (S (2 * (q + p) + 4)) by lia.
        replace (2 * q + 2 + (2 * p + 2)) with
          (2 * (q + p) + 4) by lia. cbn[Nat.pow]. pow_lia.
      * exact IHp.
Qed.

Lemma active_core_carry q p:
  active_tail q p +l (Helper.lpow [0] 1 ++ [1]) +l active_combo q p =
  active_hdzd_core q p.
Proof.
  unfold active_tail, active_combo, active_hdzd_core.
  replace (2 * p + 4) with (S (S (2 * p + 2))) by lia.
  cbn[counts_above app Helper.lpow ladd]. rewrite prefix_core_carry.
  f_equal.
  - replace (2 * (q + p + 1) + 5) with
      (S (2 * (q + p + 1) + 4)) by lia.
    cbn[Nat.pow]. pow_lia.
  - f_equal.
    + replace (2 * (q + p + 1) + 4) with
        (S (2 * (q + p + 1) + 3)) by lia.
      replace (2 * q + 2 + S (2 * p + 2)) with
        (2 * (q + p + 1) + 3) by lia. pow_lia.
    + f_equal.
      * replace (2 * (q + p + 1) + 3) with
          (S (2 * (q + p + 1) + 2)) by lia.
        replace (2 * q + 2 + (2 * p + 2)) with
          (2 * (q + p + 1) + 2) by lia. cbn[Nat.pow]. pow_lia.
      * flia.
Qed.

Lemma pow_down_ge2_marker n:
  pow_down_ge2 n +l (Helper.lpow [0] (S n) ++ [1; 0; 0]) =
  pow_down (S n) ++ [0].
Proof.
  induction n.
  - reflexivity.
  - cbn[pow_down_ge2 pow_down Helper.lpow app ladd]. f_equal; [lia|exact IHn].
Qed.

Lemma suffix_core_marker q:
  hdzd_suffix_core q +l
    (Helper.lpow [0] (2 * q + 3) ++ [1; 0; 0]) = hdzd_suffix q.
Proof.
  destruct q.
  - reflexivity.
  - unfold hdzd_suffix_core. cbn[hdzd_suffix].
    replace (Helper.lpow [0] (2 * S q + 3) ++ [1; 0; 0]) with
      (0 :: 0 :: (Helper.lpow [0] (2 * S q + 1) ++ [1; 0; 0])).
    2:{ replace (2 * S q + 3) with (S (S (2 * S q + 1))) by lia.
        reflexivity. }
    cbn[ladd]. f_equal; [lia|]. f_equal; [lia|].
    replace (2 * S q + 1) with (S (2 * S q)) by lia.
    apply pow_down_ge2_marker.
Qed.

Lemma prefix_core_marker q p:
  hdzd_prefix q p (hdzd_suffix_core q) +l
    (Helper.lpow [0] (2 * q + 2 * p + 3) ++ [1; 0; 0]) =
  hdzd_prefix q p (hdzd_suffix q).
Proof.
  induction p.
  - cbn[hdzd_prefix]. replace (2 * q + 2 * 0 + 3) with (2 * q + 3) by lia.
    apply suffix_core_marker.
  - cbn[hdzd_prefix].
    replace (Helper.lpow [0] (2 * q + 2 * S p + 3) ++ [1; 0; 0]) with
      (0 :: 0 :: (Helper.lpow [0] (2 * q + 2 * p + 3) ++ [1; 0; 0])).
    2:{ replace (2 * q + 2 * S p + 3) with
          (S (S (2 * q + 2 * p + 3))) by lia. reflexivity. }
    cbn[ladd]. f_equal; [lia|]. f_equal; [lia|exact IHp].
Qed.

Lemma active_core_marker q p:
  active_hdzd_core q p +l
    (Helper.lpow [0] (2 * (q + p + 1) + 5) ++ [1; 0; 0]) =
  active_hdzd q p.
Proof.
  unfold active_hdzd_core, active_hdzd.
  replace (Helper.lpow [0] (2 * (q + p + 1) + 5) ++ [1; 0; 0]) with
    (0 :: 0 :: 0 :: 0 ::
      (Helper.lpow [0] (2 * q + 2 * p + 3) ++ [1; 0; 0])).
  2:{ replace (2 * (q + p + 1) + 5) with
        (S (S (S (S (2 * q + 2 * p + 3))))) by lia. reflexivity. }
  cbn[ladd]. f_equal; [lia|]. f_equal; [lia|].
  f_equal; [lia|]. f_equal; [lia|]. apply prefix_core_marker.
Qed.

Lemma active_HDZD q p: HDZD (active q p) (active_hdzd q p).
Proof.
  pose proof (active_tail_data q p) as [Hlen [Hwf [Htp Hgray]]].
  rewrite active_as_HDZD. eapply HDZD_exact.
  - exact Hwf.
  - lia.
  - rewrite Hgray, Hlen. split.
    + replace (2 * (q + p + 1) + 6 - 2) with
        (2 * (q + p + 1) + 4) by lia.
      assert (Hlow: 2 ^ (2 * p + 5) + 2 <= 2 ^ (2 * p + 6)).
      { replace (2 * p + 6) with (S (2 * p + 5)) by lia.
        cbn[Nat.pow]. assert (2 <= 2 ^ (2 * p + 5)).
        { change (2 ^ 1 <= 2 ^ (2 * p + 5)).
          apply Nat.pow_le_mono_r; lia. }
        lia. }
      assert (Hmono: 2 ^ (2 * p + 6) <=
        2 ^ (2 * (q + p + 1) + 4)).
      { apply Nat.pow_le_mono_r; lia. }
      replace (2 * (q + p + 1) + 5) with
        (S (2 * (q + p + 1) + 4)) by lia.
      cbn[Nat.pow]. lia.
    + assert (2 ^ (2 * (q + p + 1) + 5) <
        2 ^ (2 * (q + p + 1) + 6))
        by (apply Nat.pow_lt_mono_r; lia).
      lia.
  - rewrite Hlen.
    assert (2 ^ (2 * p + 5) < 2 ^ (2 * (q + p + 1) + 6))
      by (apply Nat.pow_lt_mono_r; lia).
    lia.
  - rewrite <- (active_as_HDZD q p). unfold active.
    change (xorb (tp (active_tail q p))
      (Nat.odd (2 ^ (2 * (q + p + 1) + 5) - 2)) = tp1).
    rewrite Htp.
    replace (2 * (q + p + 1) + 5) with
      (S (S (2 * (q + p + 1) + 3))) by lia.
    rewrite odd_pow_SS_sub2. reflexivity.
  - symmetry.
    rewrite active_tail_ctz, Hlen, active_lsum_last, ladd_swap.
    change (L1 1) with (Helper.lpow [0] 1 ++ [1]).
    rewrite <- (ladd_assoc
      (active_tail q p +l (Helper.lpow [0] 1 ++ [1]))
      (lsum 0 (1 + gray (active_tail q p)))
      (pow_counts (2 * p + 4))).
    rewrite active_lsum_combo, active_core_carry.
    replace (2 * (q + p + 1) + 6 - 1) with
      (2 * (q + p + 1) + 5) by lia.
    apply active_core_marker.
Qed.

Lemma pow_down_marker_data n:
  length (pow_down n ++ [0]) = n + 3 /\ WF (pow_down n ++ [0]) /\
  tp (pow_down n ++ [0]) = tp1 /\
  gray (pow_down n ++ [0]) = 2 ^ S n - 1.
Proof.
  induction n as [|n [Hlen [Hwf [Htp Hgray]]]].
  - cbn[pow_down app length tp gray]. split; [reflexivity|]. split.
    + constructor; [lia|]. change (WF (Helper.lpow [0] 2)). apply WF_O.
    + split; reflexivity.
  - cbn[pow_down app length]. split; [lia|]. split.
    + constructor; [pow_lia|exact Hwf].
    + split.
      * cbn[tp]. rewrite Htp, odd_pow_S. reflexivity.
      * cbn[gray tp]. rewrite Htp, odd_pow_S, Hgray.
        cbn[Nat.pow xorb]. pow_lia.
Qed.

Lemma hdzd_suffix_data q:
  length (hdzd_suffix q) = 2 * q + 6 /\ WF (hdzd_suffix q) /\
  tp (hdzd_suffix q) = tp0 /\ gray (hdzd_suffix q) = 2 ^ (2 * q + 4) - 2.
Proof.
  destruct q.
  - cbn[hdzd_suffix length tp gray]. split; [reflexivity|]. split.
    + do 4 (constructor; [lia|]). change (WF (Helper.lpow [0] 2)). apply WF_O.
    + split; reflexivity.
  - pose proof (pow_down_marker_data (2 * S q + 1)) as
      [Hlen [Hwf [Htp Hgray]]].
    cbn[hdzd_suffix length]. split; [lia|]. split.
    + constructor.
      * replace (2 * S q + 3) with (S (2 * S q + 2)) by lia.
        cbn[Nat.pow]. lia.
      * constructor.
        -- replace (2 * S q + 2) with (S (S (2 * S q))) by lia.
           cbn[Nat.pow]. lia.
        -- exact Hwf.
    + split.
      * cbn[tp]. rewrite Htp.
        replace (2 * S q + 2) with (S (S (2 * S q))) by lia.
        rewrite odd_pow_SS_sub2.
        replace (2 * S q + 3) with (S (2 * S q + 2)) by lia.
        rewrite odd_pow_S_sub1. reflexivity.
      * cbn[gray tp]. rewrite Htp, Hgray.
        replace (2 * S q + 2) with (S (S (2 * S q))) by lia.
        rewrite odd_pow_SS_sub2.
        replace (2 * S q + 3) with (S (2 * S q + 2)) by lia.
        rewrite odd_pow_S_sub1.
        replace (2 * S q + 4) with (S (S (S (2 * S q + 1)))) by lia.
        replace (2 * S q + 3) with (S (S (2 * S q + 1))) by lia.
        cbn[Nat.pow xorb]. pow_lia.
Qed.

Lemma hdzd_prefix_data start count tail:
  length tail = 2 * start + 6 -> WF tail -> tp tail = tp0 ->
  gray tail = 2 ^ (2 * start + 4) - 2 ->
  length (hdzd_prefix start count tail) = 2 * (start + count) + 6 /\
  WF (hdzd_prefix start count tail) /\ tp (hdzd_prefix start count tail) = tp0 /\
  gray (hdzd_prefix start count tail) =
    2 ^ (2 * (start + count) + 4) - 2 ^ (2 * count + 1).
Proof.
  intros Hlen Hwf Htp Hgray. induction count.
  - cbn[hdzd_prefix]. split; [lia|]. split; [exact Hwf|].
    split; [exact Htp|]. rewrite Hgray. flia.
  - destruct IHcount as [Hlen' [Hwf' [Htp' Hgray']]].
    cbn[hdzd_prefix length]. split; [lia|]. split.
    + repeat constructor; try exact Hwf'; pow_lia.
    + split.
      * cbn[tp]. rewrite Htp'.
        replace (2 * (start + count) + 4) with
          (S (2 * (start + count) + 3)) by lia.
        rewrite odd_pow_S.
        replace (2 * (start + count) + 5) with
          (S (S (2 * (start + count) + 3))) by lia.
        rewrite odd_pow_SS_sub2. reflexivity.
      * cbn[gray tp]. rewrite Htp'.
        replace (2 * (start + count) + 4) with
          (S (2 * (start + count) + 3)) by lia.
        rewrite odd_pow_S.
        replace (2 * (start + count) + 5) with
          (S (S (2 * (start + count) + 3))) by lia.
        rewrite odd_pow_SS_sub2, Hgray'.
        assert (2 ^ (2 * count + 1) <
          2 ^ (2 * (start + count) + 4)) by (apply Nat.pow_lt_mono_r; lia).
        replace (2 * (start + S count) + 4) with
          (S (S (2 * (start + count) + 4))) by lia.
        replace (2 * S count + 1) with (S (S (2 * count + 1))) by lia.
        cbn[Nat.pow xorb]. lia.
Qed.

Lemma active_hdzd_tail_data q p:
  length (List.tl (active_hdzd q p)) = 2 * (q + p + 1) + 7 /\
  WF (List.tl (active_hdzd q p)) /\
  gray (List.tl (active_hdzd q p)) =
    2 ^ (2 * (q + p + 1) + 5) - 2 ^ (2 * p + 4).
Proof.
  pose proof (hdzd_suffix_data q) as [Hslen [Hswf [Hstp Hsgray]]].
  pose proof (hdzd_prefix_data q p (hdzd_suffix q)
    Hslen Hswf Hstp Hsgray) as [Hlen [Hwf [Htp Hgray]]].
  unfold active_hdzd. cbn[List.tl length]. split; [lia|]. split.
  - repeat constructor; try exact Hwf; pow_lia.
  - cbn[gray tp]. rewrite Htp, Hgray.
    replace (2 * (q + p + 1) + 2) with
      (S (2 * (q + p + 1) + 1)) by lia. rewrite odd_pow_S.
    replace (2 * (q + p + 1) + 3) with
      (S (S (2 * (q + p + 1) + 1))) by lia. rewrite odd_pow_SS_sub2.
    replace (2 * (q + p + 1) + 4) with
      (S (2 * (q + p + 1) + 3)) by lia. rewrite odd_pow_S.
    assert (2 ^ (2 * p + 1) < 2 ^ (2 * (q + p) + 4))
      by (apply Nat.pow_lt_mono_r; lia).
    replace (2 * (q + p + 1) + 5) with
      (S (S (S (2 * (q + p) + 4)))) by lia.
    replace (2 * p + 4) with (S (S (S (2 * p + 1)))) by lia.
    cbn[Nat.pow xorb]. lia.
Qed.

Lemma active_HI q p dst:
  dst = List.tl (active_hdzd q p) +l
    L1 (ctzS (gray (List.tl (active_hdzd q p)) - 1)) +l
    lsum (gray (List.tl (active_hdzd q p)) - 1)
      (List.hd 0 (active_hdzd q p)) ->
  HI (active_hdzd q p) dst.
Proof.
  intro Hdst.
  pose proof (active_hdzd_tail_data q p) as [Hlen [Hwf Hgray]].
  eapply HI_exact.
  - change (WF (List.tl (active_hdzd q p))). exact Hwf.
  - change (gray (List.tl (active_hdzd q p)) <> 0). rewrite Hgray.
    assert (2 ^ (2 * p + 4) < 2 ^ (2 * (q + p + 1) + 5))
      by (apply Nat.pow_lt_mono_r; lia).
    lia.
  - change (List.hd 0 (active_hdzd q p) +
      (gray (List.tl (active_hdzd q p)) - 1) <
      2 ^ length (List.tl (active_hdzd q p))).
    rewrite Hgray, Hlen. unfold active_hdzd. cbn[List.hd].
    assert (Hsmall: 2 ^ (2 * p + 4) <
      2 ^ (2 * (q + p + 1) + 5)) by (apply Nat.pow_lt_mono_r; lia).
    assert (4 <= 2 ^ (2 * (q + p + 1) + 5)).
    { change (2 ^ 2 <= 2 ^ (2 * (q + p + 1) + 5)).
      apply Nat.pow_le_mono_r; lia. }
    replace (2 * (q + p + 1) + 7) with
      (S (S (2 * (q + p + 1) + 5))) by lia.
    cbn[Nat.pow]. lia.
  - pose proof (active_HDZD q p) as Hhd.
    inversion Hhd; subst. exact HDZD_d.
  - exact Hdst.
Qed.

Lemma ctzS_pow_SSS_sub4 n: ctzS (2 ^ S (S (S n)) - 4) = 0.
Proof.
  replace (2 ^ S (S (S n)) - 4) with ((2 ^ S (S n) - 2) * 2) by pow_lia.
  apply ctzS_0.
Qed.

Lemma ctzS_pow_SSS_sub5 n: ctzS (2 ^ S (S (S n)) - 5) = 2.
Proof.
  replace (2 ^ S (S (S n)) - 5) with
    (1 + (2 ^ S (S n) - 3) * 2) by pow_lia.
  rewrite ctzS_1, ctzS_pow_SS_sub3. reflexivity.
Qed.

Lemma lsum_pow_SSS_sub2_sub1 n:
  lsum (2 ^ S (S (S n)) - 2) (2 ^ S (S (S n)) - 1) =
  2 ^ S (S n) :: (2 ^ S n - 1) :: pow_counts_dup n.
Proof.
  replace (2 ^ S (S (S n)) - 2) with
    ((2 ^ S (S n) - 1) * 2) by pow_lia.
  replace (2 ^ S (S (S n)) - 1) with
    (2 * S (2 ^ S (S n) - 2) + 1) by pow_lia.
  rewrite lsum_add, lsum_even_pairs.
  replace (S (2 ^ S (S n) - 2)) with (2 ^ S (S n) - 1) by pow_lia.
  rewrite lsum_pow_pred_full.
  replace ((2 ^ S (S n) - 1) * 2 + 2 * (2 ^ S (S n) - 1)) with
    (2 ^ S (S (S (S n))) - 4) by pow_lia.
  rewrite lsum_1, ctzS_pow_SSS_sub4. cbn[L1 ladd]. f_equal; pow_lia.
Qed.

Lemma pow_counts_dup_as_counts_marker n:
  pow_counts_dup n = pow_counts n ++ [1].
Proof. induction n; cbn[pow_counts_dup pow_counts app]; congruence. Qed.

Lemma lsum_pow_gap_pred_full c d:
  3 <= c ->
  lsum (2 ^ (c + S d) - 2 ^ S d - 1) (2 ^ (c + S d) - 1) =
  (2 ^ (c + S d - 1) - 1) :: pow_counts (c + S d - 2) ++ [1].
Proof.
  intro Hc. revert c Hc. induction d; intros c Hc.
  - destruct c as [|[|[|c]]]; try lia.
    replace (S (S (S c)) + 1) with (S (S (S (S c)))) by lia.
    replace (S (S (S (S c))) - 1) with (S (S (S c))) by lia.
    replace (S (S (S (S c))) - 2) with (S (S c)) by lia.
    replace (2 ^ S (S (S (S c))) - 2 ^ 1 - 1) with
      (2 ^ S (S (S (S c))) - 3) by lia.
    replace (2 ^ S (S (S (S c))) - 1) with
      (2 ^ S (S (S (S c))) - 2 + 1) at 1 by pow_lia.
    rewrite lsum_add.
    replace (2 ^ S (S (S (S c))) - 3) with
      (1 + (2 ^ S (S (S c)) - 2) * 2) by pow_lia.
    replace (2 ^ S (S (S (S c))) - 2) with
      (2 * S (2 ^ S (S (S c)) - 2)) by pow_lia.
    rewrite lsum_odd_pairs.
    replace (S (2 ^ S (S (S c)) - 2)) with
      (2 ^ S (S (S c)) - 1) by pow_lia.
    rewrite lsum_pow_SSS_sub2_sub1.
    replace (1 + (2 ^ S (S (S c)) - 2) * 2 +
      2 * (2 ^ S (S (S c)) - 1)) with
      (2 ^ S (S (S (S (S c)))) - 5) by pow_lia.
    rewrite lsum_1, ctzS_pow_SSS_sub5.
    cbn[L1 ladd pow_counts]. rewrite pow_counts_dup_as_counts_marker.
    cbn[app]. f_equal; [pow_lia|]. f_equal; [pow_lia|].
    f_equal; [pow_lia|]. rewrite ladd_nil_r. reflexivity.
  - replace (2 ^ (c + S (S d)) - 1) with
      (2 ^ (c + S (S d)) - 2 + 1) at 1 by pow_lia.
    rewrite lsum_add.
    replace (2 ^ (c + S (S d)) - 2 ^ S (S d) - 1) with
      (1 + (2 ^ (c + S d) - 2 ^ S d - 1) * 2).
    2:{ replace (c + S (S d)) with (S (c + S d)) by lia.
        assert (Hlt: 2 ^ S d < 2 ^ (c + S d))
          by (apply Nat.pow_lt_mono_r; lia).
        cbn[Nat.pow] in Hlt |- *.
        lia. }
    replace (2 ^ (c + S (S d)) - 2) with
      (2 * S (2 ^ (c + S d) - 2)).
    2:{ replace (c + S (S d)) with (S (c + S d)) by lia.
        cbn[Nat.pow]. pow_lia. }
    rewrite lsum_odd_pairs.
    replace (S (2 ^ (c + S d) - 2)) with (2 ^ (c + S d) - 1) by pow_lia.
    rewrite IHd by exact Hc.
    replace (1 + (2 ^ (c + S d) - 2 ^ S d - 1) * 2 +
      2 * (2 ^ (c + S d) - 1)) with
      (1 + ((2 ^ (c + S d) - 2 ^ d - 1) * 2) * 2).
    2:{ replace (2 ^ S d) with (2 * 2 ^ d) by pow_lia.
        assert (Hlt: 2 ^ S d < 2 ^ (c + S d))
          by (apply Nat.pow_lt_mono_r; lia).
        replace (2 ^ S d) with (2 * 2 ^ d) in Hlt by pow_lia.
        lia. }
    rewrite lsum_1, ctzS_1, ctzS_0.
    replace (c + S (S d) - 1) with (c + S d) by lia.
    replace (c + S (S d) - 2) with (S (c + S d - 2)) by lia.
    cbn[L1 ladd pow_counts]. f_equal.
    + lia.
    + cbn[pow_counts]. f_equal.
      * rewrite ladd_nil_r.
        replace (c + S d - 1) with (S (c + S d - 2)) by lia.
        assert (Hhead: 2 ^ S (c + S d - 2) - 1 + 1 =
          2 ^ S (c + S d - 2)) by flia.
        cbn[app]. rewrite Hhead. reflexivity.
Qed.

Lemma active_hi_lsum q p:
  lsum (2 ^ (2 * (q + p + 1) + 5) - 2 ^ (2 * p + 4) - 1)
    (2 ^ (2 * (q + p + 1) + 5) - 4) =
  (2 ^ (2 * (q + p + 1) + 4) - 2) ::
  (2 ^ (2 * (q + p + 1) + 3) - 1) ::
  (2 ^ (2 * (q + p + 1) + 2) - 1) ::
  pow_counts (2 * (q + p + 1) + 1) ++ [1].
Proof.
  replace (2 ^ (2 * (q + p + 1) + 5) - 2 ^ (2 * p + 4) - 1) with
    (1 + (2 ^ (2 * (q + p + 1) + 4) -
      2 ^ (2 * p + 3) - 1) * 2).
  2:{ replace (2 * (q + p + 1) + 5) with
        (S (2 * (q + p + 1) + 4)) by lia.
      replace (2 * p + 4) with (S (2 * p + 3)) by lia.
      cbn[Nat.pow].
      assert (2 ^ (2 * p + 3) < 2 ^ (2 * (q + p + 1) + 4))
        by (apply Nat.pow_lt_mono_r; lia).
      lia. }
  replace (2 ^ (2 * (q + p + 1) + 5) - 4) with
    (2 * S (2 ^ (2 * (q + p + 1) + 4) - 3)).
  2:{ replace (2 * (q + p + 1) + 5) with
        (S (2 * (q + p + 1) + 4)) by lia.
      cbn[Nat.pow]. pow_lia. }
  rewrite lsum_odd_pairs.
  replace (S (2 ^ (2 * (q + p + 1) + 4) - 3)) with
    (2 ^ (2 * (q + p + 1) + 4) - 2) by pow_lia.
  replace (2 ^ (2 * (q + p + 1) + 4) - 2 ^ (2 * p + 3) - 1) with
    (1 + (2 ^ (2 * (q + p + 1) + 3) -
      2 ^ (2 * p + 2) - 1) * 2).
  2:{ replace (2 * (q + p + 1) + 4) with
        (S (2 * (q + p + 1) + 3)) by lia.
      replace (2 * p + 3) with (S (2 * p + 2)) by lia.
      cbn[Nat.pow].
      assert (2 ^ (2 * p + 2) < 2 ^ (2 * (q + p + 1) + 3))
        by (apply Nat.pow_lt_mono_r; lia).
      lia. }
  replace (2 ^ (2 * (q + p + 1) + 4) - 2) with
    (2 * S (2 ^ (2 * (q + p + 1) + 3) - 2)).
  2:{ replace (2 * (q + p + 1) + 4) with
        (S (2 * (q + p + 1) + 3)) by lia.
      cbn[Nat.pow]. pow_lia. }
  rewrite lsum_odd_pairs.
  replace (S (2 ^ (2 * (q + p + 1) + 3) - 2)) with
    (2 ^ (2 * (q + p + 1) + 3) - 1) by pow_lia.
  replace (2 * (q + p + 1) + 3) with
    ((2 * q + 3) + S (2 * p + 1)) by lia.
  replace (2 * p + 2) with (S (2 * p + 1)) by lia.
  rewrite lsum_pow_gap_pred_full by lia.
  replace ((2 * q + 3) + S (2 * p + 1) - 1) with
    (2 * (q + p + 1) + 2) by lia.
  replace ((2 * q + 3) + S (2 * p + 1) - 2) with
    (2 * (q + p + 1) + 1) by lia.
  reflexivity.
Qed.

Lemma ctzS_pow_gap_sub1 m d:
  1 <= d -> ctzS (2 ^ (m + d) - 2 ^ m - 1) = m.
Proof.
  revert d. induction m; intros d Hd.
  - destruct d; [lia|]. replace (0 + S d) with (S d) by lia.
    replace (2 ^ S d - 2 ^ 0 - 1) with (2 ^ S d - 2) by lia.
    apply ctzS_pow_S_sub2.
  - replace (2 ^ (S m + d) - 2 ^ S m - 1) with
      (1 + (2 ^ (m + d) - 2 ^ m - 1) * 2).
    + rewrite ctzS_1, IHm by lia. reflexivity.
    + replace (S m + d) with (S (m + d)) by lia.
      cbn[Nat.pow].
      assert (2 ^ m < 2 ^ (m + d)) by (apply Nat.pow_lt_mono_r; lia).
      lia.
Qed.

Lemma active_hi_rank q p:
  ctzS (gray (List.tl (active_hdzd q p)) - 1) = 2 * p + 4.
Proof.
  pose proof (active_hdzd_tail_data q p) as [_ [_ Hgray]]. rewrite Hgray.
  replace (2 * (q + p + 1) + 5) with (2 * p + 4 + (2 * q + 3)) by lia.
  apply ctzS_pow_gap_sub1. lia.
Qed.

Lemma pow_down_marker_add_counts_marker n:
  (pow_down n ++ [0]) +l (pow_counts n ++ [1]) = pow_down (S n).
Proof.
  induction n.
  - reflexivity.
  - cbn[pow_down pow_counts app ladd]. f_equal; [pow_lia|exact IHn].
Qed.

Lemma hi_carry_top q:
  hdzd_suffix q +l (Helper.lpow [0] 1 ++ [1]) +l
    (pow_counts (2 * q + 3) ++ [1]) =
  (2 ^ (2 * q + 4) - 1) :: (2 ^ (2 * q + 3) - 1) ::
    pow_down (2 * q + 2).
Proof.
  destruct q.
  - reflexivity.
  - cbn[hdzd_suffix].
    replace (2 * S q + 3) with (S (S (2 * S q + 1))) by lia.
    cbn[pow_counts app L1 Helper.lpow ladd]. f_equal.
    + replace (2 * S q + 4) with (S (2 * S q + 3)) by lia.
      cbn[Nat.pow]. pow_lia.
    + f_equal.
      * replace (2 * S q + 3) with (S (2 * S q + 2)) by lia.
        cbn[Nat.pow]. pow_lia.
      * replace (2 * S q + 2) with (S (2 * S q + 1)) by lia.
        rewrite ladd_nil_r. apply pow_down_marker_add_counts_marker.
Qed.

Lemma hi_carry_active q p:
  hdzd_prefix q (S p) (hdzd_suffix q) +l
    (Helper.lpow [0] (2 * p + 3) ++ [1]) +l
    (pow_counts (2 * (q + p) + 5) ++ [1]) =
  (2 ^ (2 * (q + p) + 6) - 2) ::
    di_prefix (S q) p (di_suffix (S q)).
Proof.
  induction p.
  - cbn[hdzd_prefix di_prefix].
    replace (2 * 0 + 3) with 3 by lia.
    replace (2 * (q + 0) + 5) with (S (S (2 * q + 3))) by lia.
    cbn[pow_counts app L1 Helper.lpow ladd]. f_equal.
    + assert (4 <= 2 ^ (2 * q + 3)).
      { change (2 ^ 2 <= 2 ^ (2 * q + 3)). apply Nat.pow_le_mono_r; lia. }
      replace (2 * (q + 0) + 6) with (S (S (S (2 * q + 3)))) by lia.
      cbn[Nat.pow]. flia.
    + cbn[di_suffix di_tail]. f_equal.
      * replace (2 * (q + 0) + 4) with (S (2 * q + 3)) by lia.
        replace (2 * S q + 3) with (S (S (2 * q + 3))) by lia.
        pow_lia.
      * apply hi_carry_top.
  - cbn[hdzd_prefix di_prefix].
    replace (2 * (q + S p) + 5) with (S (S (2 * (q + p) + 5))) by lia.
    replace (2 * S p + 3) with (S (S (2 * p + 3))) by lia.
    cbn[pow_counts app L1 Helper.lpow ladd]. f_equal.
    + replace (2 * (q + S p) + 6) with
        (S (S (S (2 * (q + p) + 5)))) by lia.
      cbn[Nat.pow]. flia.
    + f_equal.
      * replace (2 * (S q + p) + 5) with (2 * (q + S p) + 5) by lia.
        replace (2 * (q + S p) + 5) with (S (2 * (q + S p) + 4)) by lia.
        replace (2 * (q + S p) + 4) with (S (2 * (q + p) + 5)) by lia.
        pow_lia.
      * replace (2 * (S q + p) + 4) with (2 * (q + p) + 6) by lia.
        exact IHp.
Qed.

Lemma active_HI_top q:
  HI (active_hdzd q 0) (top0 (S q)).
Proof.
  eapply active_HI. symmetry.
  rewrite active_hi_rank.
  pose proof (active_hdzd_tail_data q 0) as [_ [_ Hgray]].
  rewrite Hgray.
  unfold active_hdzd at 1. cbn[List.tl List.hd hdzd_prefix].
  rewrite active_hi_lsum.
  unfold top0, top0_tail.
  replace (2 * 0 + 4) with 4 by lia.
  replace (2 * (q + 0 + 1) + 1) with (2 * q + 3) by lia.
  cbn[L1 Helper.lpow app ladd]. rewrite hi_carry_top.
  replace (2 * (q + 0 + 1)) with (2 * S q) by lia.
  replace (2 ^ (2 * S q + 4) + 0 + (2 ^ (2 * S q + 4) - 2)) with
    (2 ^ (2 * S q + 5) - 2) by pow_flia.
  replace (2 ^ (2 * S q + 3) - 2 + 0 + (2 ^ (2 * S q + 3) - 1)) with
    (2 ^ (2 * S q + 4) - 3) by pow_flia.
  replace (2 ^ (2 * S q + 2) + 0 + (2 ^ (2 * S q + 2) - 1)) with
    (2 ^ (2 * S q + 3) - 1) by pow_flia.
  replace (2 * S q) with (2 * q + 2) by lia.
  replace (2 * q + 2 + 2) with (2 * q + 4) by lia.
  replace (2 * q + 2 + 1) with (2 * q + 3) by lia. reflexivity.
Qed.

Lemma active_HI_next q p:
  HI (active_hdzd q (S p)) (active (S q) p).
Proof.
  eapply active_HI. symmetry.
  rewrite active_hi_rank.
  pose proof (active_hdzd_tail_data q (S p)) as [_ [_ Hgray]].
  rewrite Hgray.
  unfold active_hdzd at 1. cbn[List.tl List.hd].
  rewrite active_hi_lsum.
  unfold active, active_tail.
  replace (2 * S p + 4) with (S (S (S (2 * p + 3)))) by lia.
  cbn[L1 Helper.lpow app ladd].
  replace (2 * (q + S p + 1) + 1) with (2 * (q + p) + 5) by lia.
  rewrite <- L1_fold. rewrite hi_carry_active.
  replace (2 * (q + S p + 1)) with (2 * (S q + p + 1)) by lia.
  replace (2 ^ (2 * (S q + p + 1) + 4) + 0 +
      (2 ^ (2 * (S q + p + 1) + 4) - 2)) with
    (2 ^ (2 * (S q + p + 1) + 5) - 2) by pow_flia.
  replace (2 ^ (2 * (S q + p + 1) + 3) - 2 + 0 +
      (2 ^ (2 * (S q + p + 1) + 3) - 1)) with
    (2 ^ (2 * (S q + p + 1) + 4) - 3) by pow_flia.
  replace (2 ^ (2 * (S q + p + 1) + 2) + 0 +
      (2 ^ (2 * (S q + p + 1) + 2) - 1)) with
    (2 ^ (2 * (S q + p + 1) + 3) - 1) by pow_flia.
  replace (2 * (q + p) + 6) with (2 * (S q + p + 1) + 2) by lia.
  reflexivity.
Qed.

Lemma active_run q p:
  S1 (active q p) 0 -->* S1 (top0 (S (q + p))) 0.
Proof.
  revert q. induction p; intro q.
  - eapply evstep_trans; [apply HDZD_run, active_HDZD|].
    replace (S (q + 0)) with (S q) by lia. apply HI_run, active_HI_top.
  - eapply evstep_trans; [apply HDZD_run, active_HDZD|].
    eapply evstep_trans; [apply HI_run, active_HI_next|].
    replace (S (q + S p)) with (S (S q + p)) by lia. apply IHp.
Qed.

Import ListNotations.



Definition top0_hdzd m :=
  (2 ^ (2 * m + 5) - 4) ::
  2 ^ (2 * m + 4) ::
  (2 ^ (2 * m + 3) - 1) ::
  (2 ^ (2 * m + 2) - 2) ::
  pow_down (2 * m + 1) ++ [0].

Definition top1_hdzd m :=
  (2 ^ (2 * m + 5) - 3) ::
  (2 ^ (2 * m + 4) - 2) ::
  2 ^ (2 * m + 3) ::
  2 ^ (2 * m + 2) ::
  pow_down (2 * m + 1) ++ [0].

Lemma ctzS_pow_SSS_sub6 n: ctzS (2 ^ S (S (S n)) - 6) = 0.
Proof.
  replace (2 ^ S (S (S n)) - 6) with ((2 ^ S (S n) - 3) * 2) by pow_lia.
  apply ctzS_0.
Qed.

Lemma ctzS_pow_SSS_sub7 n: ctzS (2 ^ S (S (S n)) - 7) = 1.
Proof.
  replace (2 ^ S (S (S n)) - 7) with
    (1 + (2 ^ S (S n) - 4) * 2) by pow_lia.
  rewrite ctzS_1. replace (2 ^ S (S n) - 4) with
    ((2 ^ S n - 2) * 2) by pow_lia. rewrite ctzS_0. reflexivity.
Qed.

Lemma ctzS_pow_SSS_sub8 n: ctzS (2 ^ S (S (S n)) - 8) = 0.
Proof.
  replace (2 ^ S (S (S n)) - 8) with ((2 ^ S (S n) - 4) * 2) by pow_lia.
  apply ctzS_0.
Qed.

Lemma ctzS_pow_SSSSS_sub11 n:
  ctzS (2 ^ S (S (S (S (S n)))) - 11) = 1.
Proof.
  replace (2 ^ S (S (S (S (S n)))) - 11) with
    (1 + (2 ^ S (S (S (S n))) - 6) * 2) by pow_lia.
  rewrite ctzS_1, ctzS_pow_SSS_sub6. reflexivity.
Qed.

Lemma lsum_0_pow_SSS_sub3 n:
  lsum 0 (2 ^ S (S (S n)) - 3) =
  (2 ^ S (S n) - 1) :: lsum 0 (2 ^ S (S n) - 2).
Proof.
  replace (2 ^ S (S (S n)) - 3) with
    ((2 ^ S (S n) - 2) * 2 + 1) by pow_lia.
  rewrite lsum_add, lsum_0_double_pos by pow_lia.
  replace (0 + (2 ^ S (S n) - 2) * 2) with
    ((2 ^ S (S n) - 2) * 2) by lia.
  rewrite lsum_1, ctzS_0. cbn[L1 ladd]. rewrite ladd_nil_r.
  f_equal; pow_flia.
Qed.

Lemma lsum_0_pow_SSSS_sub5 n:
  lsum 0 (2 ^ S (S (S (S n))) - 5) =
  (2 ^ S (S (S n)) - 2) :: (2 ^ S (S n) - 1) ::
  lsum 0 (2 ^ S (S n) - 2).
Proof.
  replace (2 ^ S (S (S (S n))) - 5) with
    ((2 ^ S (S (S n)) - 3) * 2 + 1) by pow_lia.
  rewrite lsum_add, lsum_0_double_pos by pow_lia.
  replace (0 + (2 ^ S (S (S n)) - 3) * 2) with
    ((2 ^ S (S (S n)) - 3) * 2) by lia.
  rewrite lsum_1, ctzS_0. cbn[L1 ladd]. rewrite ladd_nil_r.
  f_equal; [pow_flia|apply lsum_0_pow_SSS_sub3].
Qed.

Lemma lsum_0_pow_SSSSS_sub10 n:
  lsum 0 (2 ^ S (S (S (S (S n)))) - 10) =
  (2 ^ S (S (S (S n))) - 5) ::
  (2 ^ S (S (S n)) - 2) :: (2 ^ S (S n) - 1) ::
  (2 ^ S n - 1) :: pow_counts n.
Proof.
  replace (2 ^ S (S (S (S (S n)))) - 10) with
    ((2 ^ S (S (S (S n))) - 5) * 2) by pow_lia.
  rewrite lsum_0_double_pos by pow_lia.
  rewrite lsum_0_pow_SSSS_sub5, lsum_0_pow_SS_sub2. reflexivity.
Qed.

Lemma lsum_pow_SSS_sub8_7 n:
  lsum (2 ^ S (S (S n)) - 8) 7 = [4; 2; 1].
Proof.
  cbn[lsum]. rewrite ctzS_pow_SSS_sub8.
  replace (S (2 ^ S (S (S n)) - 8)) with
    (2 ^ S (S (S n)) - 7) by pow_flia. rewrite ctzS_pow_SSS_sub7.
  replace (S (2 ^ S (S (S n)) - 7)) with
    (2 ^ S (S (S n)) - 6) by pow_flia. rewrite ctzS_pow_SSS_sub6.
  replace (S (2 ^ S (S (S n)) - 6)) with
    (2 ^ S (S (S n)) - 5) by pow_flia. rewrite ctzS_pow_SSS_sub5.
  replace (S (2 ^ S (S (S n)) - 5)) with
    (2 ^ S (S (S n)) - 4) by pow_flia. rewrite ctzS_pow_SSS_sub4.
  replace (S (2 ^ S (S (S n)) - 4)) with
    (2 ^ S (S (S n)) - 3) by pow_flia.
  rewrite ctzS_pow_SS_sub3.
  replace (S (2 ^ S (S (S n)) - 3)) with
    (2 ^ S (S (S n)) - 2) by pow_flia.
  rewrite ctzS_pow_S_sub2. reflexivity.
Qed.

Lemma pow_down_add_counts_marker n:
  pow_down n +l pow_counts n +l
    (Helper.lpow [0] (S n) ++ [1; 0; 0]) = pow_down (S n) ++ [0].
Proof. rewrite pow_down_add_counts. apply pow_down_ge2_marker. Qed.

Lemma top0_tail_data m:
  length (top0_tail m) = 2 * m + 6 /\
  WF (top0_tail m) /\ tp (top0_tail m) = tp1 /\
  gray (top0_tail m) = 2 ^ (2 * m + 5) - 11.
Proof.
  pose proof (pow_down_tp_gray (2 * m)) as [Htp Hgray].
  unfold top0_tail. cbn[length]. rewrite pow_down_length. split; [lia|]. split.
  - repeat constructor; try apply pow_down_WF; pow_flia.
  - replace (2 * m + 1) with (S (2 * m)) by lia.
    replace (2 * m + 2) with (S (S (2 * m))) by lia.
    replace (2 * m + 3) with (S (S (S (2 * m)))) by lia.
    replace (2 * m + 4) with (S (S (S (2 * m + 1)))) by lia.
    cbn[tp gray]. rewrite Htp, Hgray, odd_pow_SSS_sub3.
    repeat rewrite odd_pow_S_sub1. cbn[xorb]. split; [reflexivity|]. pow_flia.
Qed.

Lemma top1_tail_data m:
  length (top1_tail m) = 2 * m + 6 /\
  WF (top1_tail m) /\ tp (top1_tail m) = tp1 /\
  gray (top1_tail m) = 2 ^ (2 * m + 5) - 5.
Proof.
  pose proof (pow_down_tp_gray (2 * m + 1)) as [Htp Hgray].
  unfold top1_tail. cbn[length]. rewrite pow_down_length. split; [lia|]. split.
  - repeat constructor; try apply pow_down_WF; pow_flia.
  - replace (2 * m + 2) with (S (S (2 * m))) by lia.
    replace (2 * m + 3) with (S (S (2 * m + 1))) by lia.
    replace (2 * m + 4) with (S (S (2 * m + 2))) by lia.
    cbn[tp gray]. rewrite Htp, Hgray, odd_pow_SS_sub2.
    repeat rewrite odd_pow_S_sub1. cbn[xorb]. split; [reflexivity|]. pow_flia.
Qed.

Lemma top0_as_HDZD m:
  top0 m = ((1 + gray (top0_tail m)) + (1 + 7)) :: top0_tail m.
Proof.
  pose proof (top0_tail_data m) as [_ [_ [_ Hgray]]].
  unfold top0. rewrite Hgray. f_equal. pow_flia.
Qed.

Lemma top1_as_HDZD m:
  top1 m = ((1 + gray (top1_tail m)) + (1 + 1)) :: top1_tail m.
Proof.
  pose proof (top1_tail_data m) as [_ [_ [_ Hgray]]].
  unfold top1. rewrite Hgray. f_equal. pow_flia.
Qed.

Lemma top0_HDZD_target m:
  top0_tail m +l L1 (ctzS (gray (top0_tail m))) +l
    lsum 0 (1 + gray (top0_tail m)) +l
    (Helper.lpow [0] (length (top0_tail m) - 1) ++ [1; 0; 0]) +l
    lsum (2 ^ length (top0_tail m) - 1 - 7) 7 = top0_hdzd m.
Proof.
  pose proof (top0_tail_data m) as [Hlen [_ [_ Hgray]]].
  rewrite Hlen, Hgray.
  replace (ctzS (2 ^ (2 * m + 5) - 11)) with 1.
  2:{ replace (2 * m + 5) with (S (S (S (S (S (2 * m)))))) by lia.
      symmetry. apply ctzS_pow_SSSSS_sub11. }
  replace (1 + (2 ^ (2 * m + 5) - 11)) with
    (2 ^ S (S (S (S (S (2 * m))))) - 10) by pow_flia.
  rewrite lsum_0_pow_SSSSS_sub10.
  replace (2 ^ (2 * m + 6) - 1 - 7) with
    (2 ^ S (S (S (2 * m + 3))) - 8) by pow_flia.
  rewrite lsum_pow_SSS_sub8_7.
  unfold top0_tail, top0_hdzd.
  replace (2 * m + 5) with (S (S (S (S (S (2 * m)))))) by lia.
  replace (2 * m + 4) with (S (S (S (S (2 * m))))) by lia.
  replace (2 * m + 3) with (S (S (S (2 * m)))) by lia.
  replace (2 * m + 2) with (S (S (2 * m))) by lia.
  replace (2 * m + 1) with (S (2 * m)) by lia.
  replace (2 * m + 6 - 1) with (S (S (S (S (S (2 * m)))))) by lia.
  cbn[Nat.pow L1 Helper.lpow app ladd pow_counts].
  remember (2 ^ (2 * m)) as p. assert (0 < p) by (subst p; lia).
  apply (@f_equal2 nat (list nat) (list nat) (@cons nat)); [flia|].
  apply (@f_equal2 nat (list nat) (list nat) (@cons nat)); [flia|].
  apply (@f_equal2 nat (list nat) (list nat) (@cons nat)); [flia|].
  apply (@f_equal2 nat (list nat) (list nat) (@cons nat)); [flia|].
  change (pow_down (2 * m) +l pow_counts (2 * m) +l
    (Helper.lpow [0] (S (2 * m)) ++ [1; 0; 0]) =
    pow_down (S (2 * m)) ++ [0]).
  apply pow_down_add_counts_marker.
Qed.

Lemma top0_HDZD m: HDZD (top0 m) (top0_hdzd m).
Proof.
  pose proof (top0_tail_data m) as [Hlen [Hwf [Htp Hgray]]].
  rewrite top0_as_HDZD. eapply HDZD_exact.
  - exact Hwf.
  - lia.
  - rewrite Hgray, Hlen.
    replace (2 * m + 6 - 2) with (2 * m + 4) by lia.
    assert (16 <= 2 ^ (2 * m + 4)).
    { change (2 ^ 4 <= 2 ^ (2 * m + 4)). apply Nat.pow_le_mono_r; lia. }
    split; pow_flia.
  - rewrite Hlen. pow_flia.
  - rewrite <- top0_as_HDZD. unfold top0. cbn[tp].
    rewrite Htp. replace (2 * m + 5) with (S (S (2 * m + 3))) by lia.
    rewrite odd_pow_SS_sub2. reflexivity.
  - symmetry. apply top0_HDZD_target.
Qed.

Lemma lsum_pow_SSSSS_sub5_sub4 n:
  lsum (2 ^ S (S (S (S (S n)))) - 5)
    (2 ^ S (S (S (S (S n)))) - 4) =
  (2 ^ S (S (S (S n))) - 2) ::
  (2 ^ S (S (S n)) - 1) :: 2 ^ S (S n) ::
  (2 ^ S n - 1) :: pow_counts_dup n.
Proof.
  replace (2 ^ S (S (S (S (S n)))) - 5) with
    (1 + (2 ^ S (S (S (S n))) - 3) * 2) by pow_lia.
  replace (2 ^ S (S (S (S (S n)))) - 4) with
    (2 * S (2 ^ S (S (S (S n))) - 3)) by pow_lia.
  rewrite lsum_odd_pairs.
  replace (S (2 ^ S (S (S (S n))) - 3)) with
    (2 ^ S (S (S (S n))) - 2) by pow_flia.
  replace (2 ^ S (S (S (S n))) - 3) with
    (1 + (2 ^ S (S (S n)) - 2) * 2) by pow_lia.
  replace (2 ^ S (S (S (S n))) - 2) with
    (2 * S (2 ^ S (S (S n)) - 2)) by pow_lia.
  rewrite lsum_odd_pairs.
  replace (S (2 ^ S (S (S n)) - 2)) with
    (2 ^ S (S (S n)) - 1) by pow_flia.
  rewrite lsum_pow_SSS_sub2_sub1. reflexivity.
Qed.

Lemma top0_hdzd_tail_data m:
  length (List.tl (top0_hdzd m)) = 2 * m + 7 /\
  WF (List.tl (top0_hdzd m)) /\
  gray (List.tl (top0_hdzd m)) = 2 ^ (2 * m + 5) - 4.
Proof.
  pose proof (pow_down_marker_data (2 * m + 1)) as
    [Hlen [Hwf [Htp Hgray]]].
  unfold top0_hdzd. cbn[List.tl length]. split; [lia|]. split.
  - repeat constructor; try exact Hwf; pow_flia.
  - replace (2 * m + 2) with (S (S (2 * m))) by lia.
    replace (2 * m + 3) with (S (S (2 * m + 1))) by lia.
    replace (2 * m + 4) with (S (S (S (2 * m + 1)))) by lia.
    cbn[gray tp]. rewrite Htp, Hgray, odd_pow_S, odd_pow_S_sub1,
      odd_pow_SS_sub2. cbn[xorb]. pow_flia.
Qed.

Lemma top0_HI_target m:
  List.tl (top0_hdzd m) +l
    L1 (ctzS (gray (List.tl (top0_hdzd m)) - 1)) +l
    lsum (gray (List.tl (top0_hdzd m)) - 1)
      (List.hd 0 (top0_hdzd m)) = top1 m.
Proof.
  pose proof (top0_hdzd_tail_data m) as [_ [_ Hgray]]. rewrite Hgray.
  unfold top0_hdzd at 1. cbn[List.tl List.hd].
  replace (2 ^ (2 * m + 5) - 4 - 1) with
    (2 ^ S (S (S (S (S (2 * m))))) - 5) by pow_flia.
  rewrite ctzS_pow_SSS_sub5.
  replace (2 ^ (2 * m + 5) - 4 - 1) with
    (2 ^ S (S (S (S (S (2 * m))))) - 5) by pow_flia.
  change (List.hd 0 (top0_hdzd m)) with (2 ^ (2 * m + 5) - 4).
  replace (2 ^ (2 * m + 5) - 4) with
    (2 ^ S (S (S (S (S (2 * m))))) - 4) by flia.
  rewrite lsum_pow_SSSSS_sub5_sub4.
  unfold top1, top1_tail.
  replace (2 * m + 5) with (S (S (S (S (S (2 * m)))))) by lia.
  replace (2 * m + 4) with (S (S (S (S (2 * m))))) by lia.
  replace (2 * m + 3) with (S (S (S (2 * m)))) by lia.
  replace (2 * m + 2) with (S (S (2 * m))) by lia.
  replace (2 * m + 1) with (S (2 * m)) by lia.
  cbn[Nat.pow L1 Helper.lpow app ladd].
  remember (2 ^ (2 * m)) as p. assert (0 < p) by (subst p; lia).
  replace (2 * (2 * (2 * (2 * p))) + 0 +
      (2 * (2 * (2 * (2 * p))) - 2)) with
    (2 * (2 * (2 * (2 * (2 * p)))) - 2) by flia.
  replace (2 * (2 * (2 * p)) - 1 + 0 + (2 * (2 * (2 * p)) - 1)) with
    (2 * (2 * (2 * (2 * p))) - 2) by flia.
  replace (2 * (2 * p) - 2 + 1 + 2 * (2 * p)) with
    (2 * (2 * (2 * p)) - 1) by flia.
  rewrite ladd_nil_r. cbn[pow_down app ladd].
  replace (2 ^ S (2 * m) + (2 * p - 1)) with
    (2 * (2 * p) - 1) by (rewrite Heqp; pow_flia).
  assert (Htail: (pow_down (2 * m) ++ [0]) +l pow_counts_dup (2 * m) =
    pow_down (S (2 * m))).
  { rewrite pow_counts_dup_as_counts_marker.
    apply pow_down_marker_add_counts_marker. }
  rewrite Htail. reflexivity.
Qed.

Lemma top0_HI m: HI (top0_hdzd m) (top1 m).
Proof.
  pose proof (top0_hdzd_tail_data m) as [Hlen [Hwf Hgray]].
  eapply (HI_exact (List.hd 0 (top0_hdzd m))
    (List.tl (top0_hdzd m)) (top1 m)).
  - exact Hwf.
  - rewrite Hgray. pow_flia.
  - rewrite Hgray, Hlen.
    change (2 ^ (2 * m + 5) - 4 + (2 ^ (2 * m + 5) - 4 - 1) <
      2 ^ (2 * m + 7)).
    assert (4 <= 2 ^ (2 * m + 5)).
    { change (2 ^ 2 <= 2 ^ (2 * m + 5)). apply Nat.pow_le_mono_r; lia. }
    pow_flia.
  - pose proof (top0_HDZD m) as Hhd. inversion Hhd; subst. exact HDZD_d.
  - symmetry. apply top0_HI_target.
Qed.

Lemma lsum_0_pow_SSSSS_sub4 n:
  lsum 0 (2 ^ S (S (S (S (S n)))) - 4) =
  (2 ^ S (S (S (S n))) - 2) ::
  (2 ^ S (S (S n)) - 1) :: pow_counts (S (S n)).
Proof.
  replace (2 ^ S (S (S (S (S n)))) - 4) with
    ((2 ^ S (S (S (S n))) - 2) * 2) by pow_lia.
  rewrite lsum_0_double_pos by pow_lia.
  rewrite lsum_0_pow_SS_sub2. reflexivity.
Qed.

Lemma top1_HDZD_target m:
  top1_tail m +l L1 (ctzS (gray (top1_tail m))) +l
    lsum 0 (1 + gray (top1_tail m)) +l
    (Helper.lpow [0] (length (top1_tail m) - 1) ++ [1; 0; 0]) +l
    lsum (2 ^ length (top1_tail m) - 1 - 1) 1 = top1_hdzd m.
Proof.
  pose proof (top1_tail_data m) as [Hlen [_ [_ Hgray]]].
  rewrite Hlen, Hgray.
  replace (ctzS (2 ^ (2 * m + 5) - 5)) with 2.
  2:{ replace (2 * m + 5) with (S (S (S (2 * m + 2)))) by lia.
      symmetry. apply ctzS_pow_SSS_sub5. }
  replace (1 + (2 ^ (2 * m + 5) - 5)) with
    (2 ^ S (S (S (S (S (2 * m))))) - 4) by pow_flia.
  rewrite lsum_0_pow_SSSSS_sub4, lsum_1.
  replace (ctzS (2 ^ (2 * m + 6) - 1 - 1)) with 0.
  2:{ replace (2 ^ (2 * m + 6) - 1 - 1) with
        (2 ^ S (2 * m + 5) - 2) by pow_flia.
      symmetry. apply ctzS_pow_S_sub2. }
  unfold top1_tail, top1_hdzd.
  replace (2 * m + 5) with (S (S (S (S (S (2 * m)))))) by lia.
  replace (2 * m + 4) with (S (S (S (S (2 * m))))) by lia.
  replace (2 * m + 3) with (S (S (S (2 * m)))) by lia.
  replace (2 * m + 2) with (S (S (2 * m))) by lia.
  replace (2 * m + 1) with (S (2 * m)) by lia.
  replace (2 * m + 6 - 1) with (S (S (S (S (S (2 * m)))))) by lia.
  cbn[Nat.pow L1 Helper.lpow app ladd pow_counts].
  remember (2 ^ (2 * m)) as p. assert (0 < p) by (subst p; lia).
  replace (2 * (2 * (2 * (2 * p))) - 2 + 0 +
      (2 * (2 * (2 * (2 * p))) - 2) + 0 + 1) with
    (2 * (2 * (2 * (2 * (2 * p)))) - 3) by flia.
  replace (2 * (2 * (2 * p)) - 1 + 0 +
      (2 * (2 * (2 * p)) - 1) + 0) with
    (2 * (2 * (2 * (2 * p))) - 2) by flia.
  replace (2 * (2 * p) - 1 + 1 + 2 * (2 * p) + 0) with
    (2 * (2 * (2 * p))) by flia.
  rewrite ladd_nil_r. cbn[pow_down ladd].
  replace (2 ^ S (2 * m) + 2 * p + 0) with
    (2 * (2 * p)) by (rewrite Heqp; pow_flia).
  rewrite pow_down_add_counts_marker. reflexivity.
Qed.

Lemma top1_HDZD m: HDZD (top1 m) (top1_hdzd m).
Proof.
  pose proof (top1_tail_data m) as [Hlen [Hwf [Htp Hgray]]].
  rewrite top1_as_HDZD. eapply HDZD_exact.
  - exact Hwf.
  - lia.
  - rewrite Hgray, Hlen. replace (2 * m + 6 - 2) with (2 * m + 4) by lia.
    assert (8 <= 2 ^ (2 * m + 4)).
    { change (2 ^ 3 <= 2 ^ (2 * m + 4)). apply Nat.pow_le_mono_r; lia. }
    split; pow_flia.
  - rewrite Hlen. pow_flia.
  - rewrite <- top1_as_HDZD. unfold top1. cbn[tp]. rewrite Htp.
    replace (2 * m + 5) with (S (S (2 * m + 3))) by lia.
    rewrite odd_pow_SS_sub2. reflexivity.
  - symmetry. apply top1_HDZD_target.
Qed.

Lemma lsum_pow_SSSS_sub2_sub3 n:
  lsum (2 ^ S (S (S (S n))) - 2)
    (2 ^ S (S (S (S n))) - 3) =
  (2 ^ S (S (S n)) - 1) :: (2 ^ S (S n) - 1) ::
  (2 ^ S n - 1) :: pow_counts_dup n.
Proof.
  replace (2 ^ S (S (S (S n))) - 2) with
    ((2 ^ S (S (S n)) - 1) * 2) by pow_lia.
  replace (2 ^ S (S (S (S n))) - 3) with
    (2 * S (2 ^ S (S (S n)) - 3) + 1) by pow_lia.
  rewrite lsum_add, lsum_even_pairs.
  replace (S (2 ^ S (S (S n)) - 3)) with
    (2 ^ S (S (S n)) - 2) by pow_flia.
  rewrite lsum_pow_high_sub2.
  replace ((2 ^ S (S (S n)) - 1) * 2 +
      2 * (2 ^ S (S (S n)) - 2)) with
    (2 ^ S (S (S (S (S n)))) - 6) by pow_lia.
  rewrite lsum_1, ctzS_pow_SSS_sub6. cbn[L1 ladd].
  f_equal; pow_flia.
Qed.

Lemma top1_hdzd_tail_data m:
  length (List.tl (top1_hdzd m)) = 2 * m + 7 /\
  WF (List.tl (top1_hdzd m)) /\
  gray (List.tl (top1_hdzd m)) = 2 ^ (2 * m + 5) - 1.
Proof.
  pose proof (pow_down_marker_data (2 * m + 1)) as
    [Hlen [Hwf [Htp Hgray]]].
  unfold top1_hdzd. cbn[List.tl length]. split; [lia|]. split.
  - repeat constructor; try exact Hwf; pow_flia.
  - replace (2 * m + 2) with (S (S (2 * m))) by lia.
    replace (2 * m + 3) with (S (2 * m + 2)) by lia.
    replace (2 * m + 4) with (S (S (2 * m + 2))) by lia.
    cbn[gray tp]. rewrite Htp, Hgray, odd_pow_SS_sub2.
    repeat rewrite odd_pow_S.
    cbn[xorb]. pow_flia.
Qed.

Lemma top1_HI_target m:
  List.tl (top1_hdzd m) +l
    L1 (ctzS (gray (List.tl (top1_hdzd m)) - 1)) +l
    lsum (gray (List.tl (top1_hdzd m)) - 1)
      (List.hd 0 (top1_hdzd m)) = di_mid m.
Proof.
  pose proof (top1_hdzd_tail_data m) as [_ [_ Hgray]]. rewrite Hgray.
  unfold top1_hdzd at 1. cbn[List.tl].
  replace (2 ^ (2 * m + 5) - 1 - 1) with
    (2 ^ S (2 * m + 4) - 2) by pow_flia.
  rewrite ctzS_pow_S_sub2.
  replace (2 ^ (2 * m + 5) - 1 - 1) with
    (2 ^ S (S (S (S (2 * m + 1)))) - 2) by pow_flia.
  change (List.hd 0 (top1_hdzd m)) with (2 ^ (2 * m + 5) - 3).
  replace (2 ^ (2 * m + 5) - 3) with
    (2 ^ S (S (S (S (2 * m + 1)))) - 3) by flia.
  replace (S (2 * m + 4)) with (S (S (S (S (2 * m + 1))))) by lia.
  rewrite lsum_pow_SSSS_sub2_sub3.
  unfold di_mid, di_tail.
  replace (2 * m + 5) with (S (S (S (S (S (2 * m)))))) by lia.
  replace (2 * m + 4) with (S (S (S (S (2 * m))))) by lia.
  replace (2 * m + 3) with (S (S (S (2 * m)))) by lia.
  replace (2 * m + 2) with (S (S (2 * m))) by lia.
  replace (2 * m + 1) with (S (2 * m)) by lia.
  cbn[Nat.pow L1 Helper.lpow app ladd].
  remember (2 ^ (2 * m)) as p. assert (0 < p) by (subst p; lia).
  replace (2 * (2 * (2 * (2 * p))) - 2 + 1 +
      (2 * (2 * (2 * (2 * p))) - 1)) with
    (2 * (2 * (2 * (2 * (2 * p)))) - 2) by flia.
  replace (2 * (2 * (2 * p)) + 0 + (2 * (2 * (2 * p)) - 1)) with
    (2 * (2 * (2 * (2 * p))) - 1) by flia.
  replace (2 * (2 * p) + 0 + (2 * (2 * p) - 1)) with
    (2 * (2 * (2 * p)) - 1) by flia.
  replace (2 * (2 * (2 * p)) + (2 * (2 * (2 * p)) - 1)) with
    (2 * (2 * (2 * (2 * p))) - 1) by flia.
  replace (2 * (2 * p) + (2 * (2 * p) - 1)) with
    (2 * (2 * (2 * p)) - 1) by flia.
  rewrite pow_counts_dup_as_counts_marker, pow_down_marker_add_counts_marker.
  reflexivity.
Qed.

Lemma top1_HI m: HI (top1_hdzd m) (di_mid m).
Proof.
  pose proof (top1_hdzd_tail_data m) as [Hlen [Hwf Hgray]].
  eapply (HI_exact (List.hd 0 (top1_hdzd m))
    (List.tl (top1_hdzd m)) (di_mid m)).
  - exact Hwf.
  - rewrite Hgray. pow_flia.
  - rewrite Hgray, Hlen.
    change (2 ^ (2 * m + 5) - 3 + (2 ^ (2 * m + 5) - 1 - 1) <
      2 ^ (2 * m + 7)).
    assert (4 <= 2 ^ (2 * m + 5)).
    { change (2 ^ 2 <= 2 ^ (2 * m + 5)). apply Nat.pow_le_mono_r; lia. }
    pow_flia.
  - pose proof (top1_HDZD m) as Hhd. inversion Hhd; subst. exact HDZD_d.
  - symmetry. apply top1_HI_target.
Qed.

Lemma top_run m:
  S1 (top0 m) 0 -->* S1 (di_mid m) 0.
Proof.
  eapply evstep_trans; [apply HDZD_run, top0_HDZD|].
  eapply evstep_trans; [apply HI_run, top0_HI|].
  eapply evstep_trans; [apply HDZD_run, top1_HDZD|].
  apply HI_run, top1_HI.
Qed.


Lemma HOI_run x y: HOI x y -> S1 x 0 -->* S1 y 0.
Proof. intro H. inversion H. exact HOI_b. Qed.

Lemma source_after_hoi_run m:
  S1 (source_after_hoi m) 0 -->* S1 (top0 m) 0.
Proof.
  destruct m as [|p].
  - rewrite source_after_hoi_0. constructor.
  - rewrite source_after_hoi_S.
    replace (top0 (S p)) with (top0 (S (0 + p))) by reflexivity.
    apply active_run.
Qed.

Lemma source_di_mid_run m:
  S1 (source m) 0 -->* S1 (di_mid m) 0.
Proof.
  eapply evstep_trans; [apply HOI_run, source_HOI|].
  eapply evstep_trans; [apply source_after_hoi_run|].
  apply top_run.
Qed.

Lemma overflow_cycle m:
  S1 (source m) 0 -->* S1 (reentry m) 0.
Proof.
  eapply evstep_trans; [apply source_di_mid_run|].
  eapply evstep_trans; [apply prefix_run|].
  apply overflow_tail.
Qed.

Import ListNotations.

Definition full_cycle_delta q :=
  [12; 6; 3] ++ repeat 2 (ctzS q) ++ [1].

Lemma lsum_2 a:
  lsum a 2 = L1 (ctzS a) +l L1 (ctzS (S a)).
Proof. cbn[lsum]. rewrite !L1_fold, ladd_nil_r. reflexivity. Qed.

Lemma lsum_TGray_true_2 g:
  lsum (TGray true g) 2 = L1 (S (ctzS g)) +l L1 0.
Proof.
  rewrite lsum_2. unfold TGray. rewrite ctzS_1.
  replace (S (1 + g * 2)) with ((S g) * 2) by lia.
  rewrite ctzS_0. reflexivity.
Qed.

Lemma lsum_TGray_false_sub2_2 g:
  1 <= g ->
  lsum (TGray false g - 2) 2 = L1 0 +l L1 (S (ctzS (g - 1))).
Proof.
  intro Hg. rewrite lsum_2.
  change
    (L1 (ctzS (g * 2 - 2)) +l L1 (ctzS (S (g * 2 - 2))) =
      L1 0 +l L1 (S (ctzS (g - 1)))).
  replace (g * 2 - 2) with ((g - 1) * 2) by lia.
  rewrite ctzS_0.
  replace (S ((g - 1) * 2)) with (1 + (g - 1) * 2) by lia.
  rewrite ctzS_1. reflexivity.
Qed.


Lemma repeat_two_add_L1 n:
  repeat 2 n +l lmul2 (L1 n) = repeat 2 (S n).
Proof.
  induction n; cbn[L1 lmul2 ladd repeat] in *.
  - reflexivity.
  - change (2 :: (repeat 2 n +l lmul2 (L1 n)) =
      2 :: 2 :: repeat 2 n).
    rewrite IHn. reflexivity.
Qed.

Lemma repeat_two_add_one n:
  repeat 2 n +l L1 n = repeat 2 n ++ [1].
Proof.
  induction n; cbn[L1 ladd repeat] in *.
  - reflexivity.
  - change (2 :: (repeat 2 n +l L1 n) =
      2 :: (repeat 2 n ++ [1])).
    f_equal. exact IHn.
Qed.

Lemma Add2sDelta_pair n:
  Add2sDelta n +l Add2sDelta (S n) = repeat 2 (S (S n)).
Proof.
  induction n using nat_ind2.
  - reflexivity.
  - reflexivity.
  - cbn[Add2sDelta].
    change
      ((lmul2 (L1 (S (S n))) +l Add2sDelta n) +l
       (lmul2 (L1 (S (S (S n)))) +l Add2sDelta (S n)) =
       repeat 2 (S (S (S (S n))))).
    rewrite <- ladd_assoc.
    rewrite (ladd_assoc (Add2sDelta n)
      (lmul2 (L1 (S (S (S n))))) (Add2sDelta (S n))).
    rewrite (ladd_swap (Add2sDelta n)
      (lmul2 (L1 (S (S (S n))))) (Add2sDelta (S n))).
    rewrite ladd_assoc.
    rewrite (ladd_comm (lmul2 (L1 (S (S n))))
      (Add2sDelta n +l Add2sDelta (S n))).
    rewrite IHn, !repeat_two_add_L1. reflexivity.
Qed.

Lemma carry_adds r:
  carry_cur_add r +l carry_prev_add r = repeat 2 r.
Proof.
  destruct r as [|[|r]]; cbn[carry_cur_add carry_prev_add repeat].
  - reflexivity.
  - reflexivity.
  - apply Add2sDelta_pair.
Qed.

Ltac finish_cycle_delta q :=
  unfold full_cycle_delta;
  repeat rewrite ladd_assoc;
  ladd_swaps (carry_prev_add (2 + ctzS q));
  ladd_swaps (carry_cur_add (2 + ctzS q));
  rewrite <- ladd_assoc;
  rewrite (ladd_comm (carry_prev_add (2 + ctzS q))
    (carry_cur_add (2 + ctzS q)));
  rewrite carry_adds;
  ladd_swaps (lmul2 (L1 (2 + ctzS q)));
  rewrite <- ladd_assoc, repeat_two_add_L1;
  ladd_swaps (L1 (S (2 + ctzS q)));
  rewrite <- ladd_assoc, repeat_two_add_one;
  cbn[Add2sDelta lmul2 L1 ladd repeat]; reflexivity.


Lemma cycle_num_effect h v q:
  4 <= v ->
  ctzS h = 1 -> ctzS (S h) = 0 ->
  ctzS (S (S h)) = 2 + ctzS q ->
  ctzS (S (S (S h))) = 0 ->
  ctzS (S (S (S (S h)))) = 1 ->
  ctzS v = 0 -> ctzS (v + 1) = 1 ->
  ctzS (v - 1) = 2 + ctzS q ->
  ctzS (v - 2) = 0 -> ctzS (v - 3) = 1 ->
  num_effects 8 (tp1, v + 2, h) =
    mkEffect false (full_cycle_delta q) (full_cycle_delta q).
Proof.
  intros Hv Hh0 Hh1 Hh2 Hh3 Hh4 Hv0 Hvp Hv1 Hv2 Hv3.
  Ltac effect_normalize_gray v :=
    repeat match goal with
    | |- context [v + 2 - 1] => replace (v + 2 - 1) with (v + 1) by lia
    | |- context [v + 1 - 1] => replace (v + 1 - 1) with v by lia
    | |- context [v - 1 - 1] => replace (v - 1 - 1) with (v - 2) by lia
    | |- context [v - 2 - 1] => replace (v - 2 - 1) with (v - 3) by lia
    end.
  Ltac rewrite_facts :=
    repeat match goal with H: ctzS ?x = ?r |- context [ctzS ?x] => rewrite H end;
    rewrite ?even_add2;
    repeat match goal with
    | H: Nat.even ?x = ?b |- context [Nat.even ?x] => rewrite H
    end.
  Ltac normalize_step v :=
    unfold num_step, next_inc, next_cur_gray, next_prev_gray;
    unfold num_rank, batch_rank;
    cbn[negb]; effect_normalize_gray v; rewrite_facts;
    cbn[Nat.even negb]; effect_normalize_gray v.
  Ltac rank_solve v :=
    unfold num_rank, batch_rank; cbn[negb]; effect_normalize_gray v;
    rewrite_facts; assumption || reflexivity.
  Ltac flatten_effect :=
    unfold effect_compose, compose_swap, compose_cur_add, compose_prev_add,
      batch_swap;
    cbn[e_swap e_cur e_prev Nat.even negb xorb];
    rewrite_facts; cbn[Nat.even negb xorb].
  Ltac effect_step v r k :=
    rewrite num_effects_acc_S;
    lazymatch goal with
    | |- context [num_effect (?inc, ?gc, ?gp)] =>
      rewrite (num_effect_ranks inc gc gp r k ltac:(rank_solve v)
        ltac:(normalize_step v; assumption || reflexivity))
    end;
    normalize_step v; flatten_effect.
  Ltac finish_effect v :=
    repeat rewrite lsum_TGray_true_2;
    repeat rewrite lsum_TGray_false_sub2_2 by lia;
    cbn[num_effects_acc]; effect_normalize_gray v; rewrite_facts;
    cbn[effect_id e_swap e_cur e_prev ladd Nat.even negb xorb].
  rewrite <- num_effects_acc_id.
  effect_step v 1 0. effect_step v 0 (2 + ctzS q).
  destruct (Nat.even (ctzS q)) eqn:Hpar.
  - effect_step v (2 + ctzS q) 0. effect_step v 0 1.
    effect_step v 1 0. effect_step v 0 (2 + ctzS q).
    effect_step v (2 + ctzS q) 0. effect_step v 0 1.
    finish_effect v.
    f_equal; finish_cycle_delta q.
  - effect_step v (2 + ctzS q) 0.
    effect_step v 0 (2 + ctzS q).
    effect_step v (2 + ctzS q) 0. effect_step v 0 1.
    effect_step v 1 0. effect_step v 0 1.
    finish_effect v.
    f_equal; finish_cycle_delta q.
Qed.

Lemma q_steps_effect m q:
  q <= last_q m ->
  steps_effect 8 (q_feature m (S q)) =
    mkEffect false (full_cycle_delta q) (full_cycle_delta q).
Proof.
  intro Hq. rewrite steps_effect_num. unfold q_feature.
  cbn[closed_num].
  eapply cycle_num_effect; eauto using high_ctz, high_succ1_ctz,
    high_succ2_ctz, high_succ3_ctz, high_succ4_ctz,
    low_ctz0, low_ctz_plus1, low_ctz1, low_ctz2, low_ctz3.
  lia.
Qed.

Lemma q_closed_cycle_effect x m q:
  q <= last_q m ->
  ClosedRep x (q_feature m (S q)) ->
  exists y,
    ClosedPath 8 x (q_feature m (S q)) y /\
    ClosedRep y (q_feature m q) /\
    PairEffect (steps_effect 8 (q_feature m (S q))) x y.
Proof.
  intros Hq Hrep.
  eapply ClosedRep_numeric_path; [apply q_numeric_path; exact Hq|exact Hrep].
Qed.

Lemma q_closed_cycle_effect_full x m q:
  q <= last_q m ->
  ClosedRep x (q_feature m (S q)) ->
  exists y,
    ClosedPath 8 x (q_feature m (S q)) y /\
    ClosedRep y (q_feature m q) /\
    PairLadd false (full_cycle_delta q) (full_cycle_delta q) x y.
Proof.
  intros Hq Hrep.
  destruct (q_closed_cycle_effect x m q Hq Hrep)
    as [y [Hpath [Hy Heffect]]].
  exists y. split; [exact Hpath|]. split; [exact Hy|].
  unfold PairEffect in Heffect.
  rewrite (q_steps_effect m q Hq) in Heffect.
  cbn[e_swap e_cur e_prev] in Heffect.
  exact Heffect.
Qed.

Fixpoint q_cycles_delta q :=
match q with
| 0 => []
| S q => q_cycles_delta q +l full_cycle_delta q
end.

Lemma q_run_down_effect x m q:
  q <= S (last_q m) ->
  ClosedRep x (q_feature m q) ->
  exists y,
    S2 x -->* S2 y /\
    ClosedRep y (q_feature m 0) /\
    PairLadd false (q_cycles_delta q) (q_cycles_delta q) x y.
Proof.
  revert x. induction q as [|q IH]; intros x Hq Hrep.
  - exists x. split; [constructor|]. split; [exact Hrep|apply PairLadd_refl].
  - destruct (q_closed_cycle_effect_full x m q ltac:(lia) Hrep)
      as [y [Hpath [Hy Heffect]]].
    destruct (IH y ltac:(lia) Hy) as [z [Hrun [Hz Htail]]].
    exists z. split.
    + eapply evstep_trans; [eapply ClosedPath_run, Hpath|exact Hrun].
    + split; [exact Hz|].
      cbn[q_cycles_delta].
      pose proof (PairLadd_trans false (full_cycle_delta q)
        (full_cycle_delta q) false (q_cycles_delta q)
        (q_cycles_delta q) x y z Heffect Htail) as Htotal.
      cbn[compose_swap compose_cur_add compose_prev_add] in Htotal.
      rewrite (ladd_comm (q_cycles_delta q) (full_cycle_delta q)).
      exact Htotal.
Qed.

Lemma ctzS_4n_add3 n: ctzS (4 * n + 3) = 2 + ctzS n.
Proof. replace (4 * n + 3) with (4 * S n - 1) by lia. apply low_ctz1. Qed.

Lemma ctzS_4n_add4 n: ctzS (4 * n + 4) = 0.
Proof. replace (4 * n + 4) with (4 * S n) by lia. apply low_ctz0. Qed.

Lemma ctzS_4n_add5 n: ctzS (4 * n + 5) = 1.
Proof. replace (4 * n + 5) with (4 * S n + 1) by lia. apply low_ctz_plus1. Qed.

Lemma ctzS_4n_add6 n: ctzS (4 * n + 6) = 0.
Proof. replace (4 * n + 6) with ((2 * n + 3) * 2) by lia. apply ctzS_0. Qed.

Lemma repeat_two_add2 r:
  repeat 2 (2 + r) = [2; 2] ++ repeat 2 r.
Proof. reflexivity. Qed.

Lemma four_cycle_delta n:
  full_cycle_delta (4 * n + 3) +l
  full_cycle_delta (4 * n + 4) +l
  full_cycle_delta (4 * n + 5) +l
  full_cycle_delta (4 * n + 6) =
    [48; 24] ++ full_cycle_delta n.
Proof.
  unfold full_cycle_delta.
  rewrite ctzS_4n_add3, ctzS_4n_add4,
    ctzS_4n_add5, ctzS_4n_add6.
  rewrite repeat_two_add2.
  cbn[repeat app ladd].
  rewrite ladd_nil_r.
  cbn[Nat.add]. reflexivity.
Qed.

Lemma four_cycle_delta_r n:
  full_cycle_delta (4 * n + 3) +l
  (full_cycle_delta (4 * n + 4) +l
  (full_cycle_delta (4 * n + 5) +l full_cycle_delta (4 * n + 6))) =
    [48; 24] ++ full_cycle_delta n.
Proof. repeat rewrite ladd_assoc. apply four_cycle_delta. Qed.

Lemma q_cycles_delta_add4 n:
  q_cycles_delta (n + 4) =
    q_cycles_delta n +l full_cycle_delta n +l
    full_cycle_delta (n + 1) +l
    full_cycle_delta (n + 2) +l full_cycle_delta (n + 3).
Proof.
  replace (n + 4) with (S (S (S (S n)))) by lia.
  cbn[q_cycles_delta].
  replace (S (S (S n))) with (n + 3) by lia.
  replace (S (S n)) with (n + 2) by lia.
  replace (S n) with (n + 1) by lia. reflexivity.
Qed.

Lemma q_cycles_delta_scale n:
  q_cycles_delta (4 * n + 3) =
    [48 * n + 36; 24 * n + 18] ++
      (q_cycles_delta n +l [9; 4; 1]).
Proof.
  induction n as [|n IH].
  - reflexivity.
  - replace (4 * S n + 3) with ((4 * n + 3) + 4) by lia.
    rewrite q_cycles_delta_add4, IH.
    replace (4 * n + 3 + 1) with (4 * n + 4) by lia.
    replace (4 * n + 3 + 2) with (4 * n + 5) by lia.
    replace (4 * n + 3 + 3) with (4 * n + 6) by lia.
    repeat rewrite <- ladd_assoc. rewrite four_cycle_delta_r.
    cbn[app ladd]. f_equal; [lia|]. f_equal; [lia|].
    cbn[q_cycles_delta]. apply ladd_swap.
Qed.

Import ListNotations.



Lemma reentry_ready m: HDZD_ready (reentry m).
Proof.
  pose proof (reentry_tail_cons_data m) as [Hwf [Htp [Hgray Hlen]]].
  unfold reentry, HDZD_ready. cbn[List.tl List.hd].
  repeat split.
  - constructor; [pow_lia|exact Hwf].
  - change (xorb (tp (2 ^ (2 * m + 4) :: reentry_tail m))
      (Nat.odd (2 ^ (2 * m + 5) + 4)) = tp1). rewrite Htp.
    replace (2 * m + 5) with (S (2 * m + 4)) by lia.
    rewrite odd_pow_S_add_even by (exists 2; reflexivity). reflexivity.
  - rewrite Hlen. lia.
  - rewrite Hlen, Hgray.
    replace (2 * m + 6 - 2) with (2 * m + 4) by lia.
    assert (2 <= 2 ^ (2 * m + 5)).
    { change (2 ^ 1 <= 2 ^ (2 * m + 5)). apply Nat.pow_le_mono_r; lia. }
    pow_flia.
  - rewrite Hlen, Hgray. pow_flia.
  - rewrite Hgray. lia.
  - rewrite Hlen, Hgray. pow_flia.
Qed.

Lemma reentry_prev_ready m: HI_ready (reentry_prev m).
Proof.
  pose proof (reentry_prev_tail_data m) as [Hwf [Htp [Hgray Hlen]]].
  unfold reentry_prev, HI_ready. cbn[List.tl List.hd].
  repeat split.
  - constructor; [pow_lia|exact Hwf].
  - change (xorb
      (tp (2 ^ (2 * m + 4) + 2 :: reentry_prev_tail m))
      (Nat.odd (2 ^ (2 * m + 5) + 1)) = tp0). rewrite Htp.
    replace (2 * m + 5) with (S (2 * m + 4)) by lia.
    rewrite odd_pow_S_add_odd by (exists 0; reflexivity). reflexivity.
  - rewrite Hgray. pow_flia.
  - rewrite Hgray, Hlen. pow_flia.
Qed.

Lemma start_state_WF m: St_WF (start_state m).
Proof.
  unfold start_state, St_of. eapply St_WF_2 with
    (ls:=pre_reentry m) (ls0:=reentry_prev m) (ls1:=reentry m) (n:=0).
  - apply pre_reentry_HDZD.
  - apply reentry_prev_HI.
  - unfold reentry, pre_reentry. cbn[L1 ladd]. f_equal; pow_flia.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma start_state_rep m: ClosedRep (start_state m) (start_feature m).
Proof.
  exists (reentry m), (reentry_prev m).
  split.
  - unfold start_state. rewrite start_rank. reflexivity.
  - split.
    + apply start_state_WF.
    + split.
      * unfold start_state. cbn[St_Ready St_of]. apply reentry_ready.
      * split.
        -- unfold start_state. cbn[St_PrevReady St_Ready St_of negb].
           apply reentry_prev_ready.
        -- split.
           ++ pose proof (reentry_tail_cons_data m) as
                [_ [_ [Hgray _]]]. exact Hgray.
           ++ split.
              ** pose proof (reentry_tail_cons_data m) as
                   [_ [_ [_ Hlen]]]. exact Hlen.
              ** split.
                 --- pose proof (reentry_prev_tail_data m) as
                       [_ [_ [Hgray _]]]. exact Hgray.
                 --- pose proof (reentry_prev_tail_data m) as
                       [_ [_ [_ Hlen]]].
                     unfold reentry_prev, start_feature.
                     cbn[c_prev_len List.tl]. rewrite Hlen. lia.
Qed.

Lemma prefix_lsum_false m:
  lsum (TGray false (mid_pow m - 1) - 2) 2 = [1; 1].
Proof.
  rewrite lsum_TGray_false_sub2_2 by (unfold mid_pow; pow_lia).
  replace (mid_pow m - 1 - 1) with (mid_pow m - 2)
    by (unfold mid_pow; pow_lia).
  rewrite mid_sub2_ctz. reflexivity.
Qed.

Lemma prefix_lsum_true_sub1 m:
  lsum (TGray true (mid_pow m - 1)) 2 =
    L1 (2 * m + 6) +l L1 0.
Proof.
  rewrite lsum_TGray_true_2.
  replace (ctzS (mid_pow m - 1)) with (2 * m + 5).
  2:{ unfold mid_pow. symmetry. apply ctzS_pow_sub1. }
  replace (S (2 * m + 5)) with (2 * m + 6) by lia.
  reflexivity.
Qed.

Lemma prefix_lsum_true m:
  lsum (TGray true (mid_pow m)) 2 = [1; 1].
Proof. rewrite lsum_TGray_true_2, mid_ctz. reflexivity. Qed.

Lemma prefix_effect m:
  steps_effect 3 (start_feature m) =
    mkEffect true [5; 3] ([2; 3] +l L1 (2 * m + 6)).
Proof.
  rewrite (steps_effect_S 2 (start_feature m)).
  rewrite (step_effect_ranks (start_feature m) 0 1
    (start_rank m) ltac:(rewrite prefix_step0; apply prefix_rank1)).
  rewrite prefix_step0, (steps_effect_S 1).
  rewrite (step_effect_ranks _ 1 0 (prefix_rank1 m)
    ltac:(rewrite prefix_step1; apply prefix_rank2)).
  rewrite prefix_step1, (steps_effect_S 0).
  rewrite (step_effect_ranks _ 0 1 (prefix_rank2 m)
    ltac:(rewrite prefix_step2; apply prefix_rank3)).
  rewrite prefix_step2.
  cbn[start_feature c_inc c_cur_gray c_prev_gray Nat.even negb].
  rewrite prefix_lsum_false, prefix_lsum_true_sub1,
    prefix_lsum_true.
  cbn[steps_effect effect_id effect_compose compose_swap compose_cur_add
    compose_prev_add e_swap e_cur e_prev batch_swap carry_cur_add
    carry_prev_add Add2sDelta lmul2 L1 negb Nat.even xorb].
  replace (2 * m + 6) with (S (S (2 * m + 4))) by lia.
  rewrite effect_compose_id_r.
  unfold effect_compose, compose_swap, compose_cur_add, compose_prev_add.
  cbn[e_swap e_cur e_prev xorb lmul2 L1 ladd Nat.add].
  rewrite ladd_nil_r. reflexivity.
Qed.

Lemma q0_effect m:
  step_effect (q_feature m 0) = mkEffect true [4] [1; 0; 1].
Proof.
  rewrite (step_effect_ranks (q_feature m 0) 1 0 (q0_rank m)
    ltac:(rewrite q0_step; apply pre_rank)).
  unfold q_feature, high. cbn[c_inc c_cur_gray c_prev_gray Nat.mul Nat.add
    Nat.sub negb Nat.even batch_swap carry_cur_add carry_prev_add
    Add2sDelta lmul2 L1].
  rewrite lsum_TGray_false_sub2_2 by lia.
  cbn[ctzS ladd]. reflexivity.
Qed.

Definition regular_dcur m :=
  q_cycles_delta (first_q m) +l [6; 3] +l L1 (2 * m + 6).

Definition regular_dprev m :=
  q_cycles_delta (first_q m) +l [6; 3; 1].

Lemma regular_effect m:
  effect_compose
    (effect_compose
      (mkEffect true [5; 3] ([2; 3] +l L1 (2 * m + 6)))
      (mkEffect false (q_cycles_delta (first_q m))
        (q_cycles_delta (first_q m))))
    (mkEffect true [4] [1; 0; 1]) =
  mkEffect false (regular_dcur m) (regular_dprev m).
Proof.
  unfold effect_compose, compose_swap, compose_cur_add, compose_prev_add,
    regular_dcur, regular_dprev.
  cbn[e_swap e_cur e_prev xorb]. f_equal.
  - rewrite (ladd_swap ([2; 3] +l L1 (2 * m + 6))
      (q_cycles_delta (first_q m)) [4]).
    rewrite (ladd_swap [2; 3] (L1 (2 * m + 6)) [4]).
    rewrite (ladd_comm
      (([2; 3] +l [4]) +l L1 (2 * m + 6))
      (q_cycles_delta (first_q m))).
    rewrite ladd_assoc. reflexivity.
  - rewrite (ladd_swap [5; 3] (q_cycles_delta (first_q m))
      [1; 0; 1]).
    rewrite (ladd_comm ([5; 3] +l [1; 0; 1])
      (q_cycles_delta (first_q m))). reflexivity.
Qed.

Lemma start_to_pre_effect x m:
  ClosedRep x (start_feature m) ->
  exists y,
    S2 x -->* S2 y /\
    ClosedRep y (pre_feature m) /\
    PairLadd false (regular_dcur m) (regular_dprev m) x y.
Proof.
  intro Hrep.
  destruct (ClosedRep_numeric_path 3 x _ _ (prefix_numeric_path m) Hrep)
    as [y [Hprefix [Hy Hprefix_effect]]].
  rewrite prefix_effect in Hprefix_effect.
  destruct (q_run_down_effect y m (first_q m)
    ltac:(unfold first_q; lia) Hy) as [z [Hq [Hz Hq_effect]]].
  destruct (q0_to_pre z m Hz) as [w [Hq0 Hw]].
  assert (Hq0': embanked_batch (c_rank (q_feature m 0)) z w).
  { rewrite q0_rank. exact Hq0. }
  pose proof (closed_batch_effect z (q_feature m 0) w Hz
    (q0_numeric m) Hq0') as Hq0_effect.
  rewrite q0_effect in Hq0_effect.
  change (PairEffect
    (mkEffect false (q_cycles_delta (first_q m))
      (q_cycles_delta (first_q m))) y z) in Hq_effect.
  pose proof (PairEffect_compose _ _ _ _ _ Hprefix_effect Hq_effect)
    as Hfirst.
  pose proof (PairEffect_compose _ _ _ _ _ Hfirst Hq0_effect) as Heffect.
  rewrite regular_effect in Heffect.
  exists w. split.
  - eapply evstep_trans; [eapply ClosedPath_run, Hprefix|].
    eapply evstep_trans; [exact Hq|exact (embanked_batch_run 1 z w Hq0)].
  - split; [exact Hw|exact Heffect].
Qed.

Definition regular_pre_source_prev m :=
  (2 ^ (2 * m + 7) - 5) :: (2 ^ (2 * m + 6) - 1) ::
  source_tail (S m).

Lemma first_q_closed m: first_q m = 2 ^ (2 * m + 3) - 1.
Proof. unfold first_q, last_q. pow_flia. Qed.

Lemma first_q_succ m: first_q (S m) = 4 * first_q m + 3.
Proof.
  rewrite !first_q_closed.
  replace (2 * S m + 3) with (2 * m + 3 + 2) by lia.
  rewrite Nat.pow_add_r. cbn[Nat.pow]. flia.
Qed.

Lemma pow_2S_shift m k: 2 ^ (2 * S m + k) = 4 * 2 ^ (2 * m + k).
Proof.
  replace (2 * S m + k) with (2 * m + k + 2) by lia.
  rewrite Nat.pow_add_r. cbn[Nat.pow]. lia.
Qed.

Lemma ladd_shift base d fixed move extra tail:
  base +l (d +l (fixed +l (move +l extra))) +l tail =
  ((base +l move) +l (d +l fixed) +l tail) +l extra.
Proof.
  repeat rewrite ladd_assoc.
  rewrite (ladd_swap base move d).
  rewrite (ladd_swap (base +l d) move fixed).
  rewrite (ladd_swap (base +l d +l fixed +l move) tail extra).
  reflexivity.
Qed.

Lemma ladd_shift_prev base d:
  base +l (d +l [10; 4; 1]) =
  ((base +l [1]) +l (d +l [6; 3; 1])) +l [3; 1].
Proof.
  replace [10; 4; 1] with
    ([6; 3; 1] +l ([1] +l [3; 1])) by reflexivity.
  pose proof (ladd_shift base d [6; 3; 1] [1] [3; 1] []) as H.
  rewrite !ladd_nil_r in H. exact H.
Qed.

Lemma regular_prev_eq m:
  reentry_prev m +l regular_dprev m = regular_pre_source_prev m.
Proof.
  induction m as [|m IH].
  - reflexivity.
  - unfold regular_dprev. rewrite first_q_succ, q_cycles_delta_scale,
      first_q_closed.
    cbn[reentry_prev reentry_prev_tail regular_pre_source_prev source_tail
      app ladd].
    unfold regular_pre_source_prev. cbn[source_tail].
    repeat rewrite pow_2S_shift.
    f_equal; [pow_flia|]. f_equal; [pow_flia|].
    change
      ((2 ^ (2 * m + 5) :: (2 ^ (2 * m + 4) + 2) ::
          reentry_prev_tail m) +l
       ((q_cycles_delta (2 ^ (2 * m + 3) - 1) +l [9; 4; 1]) +l [1]) =
       (4 * 2 ^ (2 * m + 5) - 2) ::
       (4 * 2 ^ (2 * m + 4)) :: source_tail (S m)).
    replace
      ((4 * 2 ^ (2 * m + 5) - 2) ::
       (4 * 2 ^ (2 * m + 4)) :: source_tail (S m))
      with (regular_pre_source_prev m +l [3; 1]).
    2:{ unfold regular_pre_source_prev. cbn[ladd].
        f_equal; [pow_flia|]. f_equal; pow_flia. }
    rewrite <- (ladd_assoc
      (q_cycles_delta (2 ^ (2 * m + 3) - 1)) [9; 4; 1] [1]).
    replace ([9; 4; 1] +l [1]) with [10; 4; 1] by reflexivity.
    rewrite ladd_shift_prev.
    replace
      ((2 ^ (2 * m + 5) :: (2 ^ (2 * m + 4) + 2) ::
        reentry_prev_tail m) +l [1]) with (reentry_prev m)
      by (unfold reentry_prev; reflexivity).
    rewrite <- first_q_closed.
    change ((reentry_prev m +l regular_dprev m) +l [3; 1] =
      regular_pre_source_prev m +l [3; 1]).
    rewrite IH. reflexivity.
Qed.

Lemma regular_pre_source_open m:
  regular_pre_source_prev m +l [1; 1] = source (S m).
Proof.
  unfold regular_pre_source_prev, source.
  cbn[ladd].
  replace (2 * S m + 5) with (2 * m + 7) by lia.
  replace (2 * S m + 4) with (2 * m + 6) by lia.
  f_equal.
  - assert (5 <= 2 ^ (2 * m + 7)).
    { pose proof (Nat.pow_le_mono_r 2 3 (2 * m + 7) ltac:(lia)) as H.
      cbn[Nat.pow] in H. lia. }
    flia.
  - f_equal; flia.
Qed.

Lemma regular_run m:
  S1 (reentry m) 0 -->* S1 (source (S m)) 0.
Proof.
  destruct (start_to_pre_effect (start_state m) m (start_state_rep m))
    as [y [Hrun [Hy Hdelta]]].
  destruct (pre_to_source_open y m Hy)
    as [z [Hopen [_ Hopen_delta]]].
  unfold PairLadd in Hdelta, Hopen_delta.
  cbn in Hdelta, Hopen_delta.
  destruct Hdelta as [_ Hprev]. destruct Hopen_delta as [Hcur _].
  rewrite Hprev in Hcur.
  change (St_cur z =
    (reentry_prev m +l regular_dprev m) +l [1; 1]) in Hcur.
  rewrite regular_prev_eq, regular_pre_source_open in Hcur.
  change (S1 (reentry m) 0 -->* S2 y) in Hrun.
  eapply evstep_trans; [exact Hrun|].
  pose proof (embanked_run y z Hopen) as Hfinal.
  destruct z as [cur prev gc gp len inc mark].
  cbn[St_cur] in Hcur. subst cur.
  cbn[S2] in Hfinal. exact Hfinal.
Qed.

Lemma top_loop m:
  S1 (reentry m) 0 -->* S1 (reentry (S m)) 0.
Proof.
  eapply evstep_trans; [apply regular_run|apply overflow_cycle].
Qed.


Lemma init_to_reentry:
  c0 -->* S1 (reentry 0) 0.
Proof.
  unfold reentry. cbn[reentry_tail]. unfold S1. esx.
Qed.

Lemma reach_reentry n:
  c0 -->* S1 (reentry n) 0.
Proof.
  induction n.
  - apply init_to_reentry.
  - eapply evstep_trans; [exact IHn|apply top_loop].
Qed.

Lemma LC_score ls:
  exists c,
    length ls <= c /\
    sigma_score_side (LC ls) c.
Proof.
  induction ls.
  - exists 0. split; [cbn; lia|constructor].
  - destruct IHls as [c [Hlen Hscore]].
    eexists. split.
    2:{ cbn[LC].
      repeat (apply sigma_score_Str_app || apply sigma_score_lpow ||
        (cbn; reflexivity)).
      exact Hscore. }
    cbn. lia.
Qed.

Lemma S1_score ls n:
  exists c,
    length ls <= c /\
    sigma_score (S1 ls n) c.
Proof.
  destruct (LC_score ls) as [c [Hlen Hscore]].
  eexists. split.
  2:{ unfold S1. solve_sigma_score. exact Hscore. }
  lia.
Qed.

Theorem nonhalt: ~ halts tm c0.
Proof.
  apply sigma_score_unbounded_nonhalt. intro n.
  destruct (S1_score (reentry n) 0) as [c [Hlen Hscore]].
  exists (S1 (reentry n) 0), c. repeat split.
  - apply reach_reentry.
  - exact Hscore.
  - rewrite reentry_length in Hlen. lia.
Qed.

End TM1.
