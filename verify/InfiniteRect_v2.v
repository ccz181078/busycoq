From BusyCoq Require Import Individual62 Longitudinal LongN InfiniteRect.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import List String.

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).

Ltac segRLs_n_0 :=
  eapply segRLs_n_trans with (h1:=[_]) (h2:=[]); [segRLs_n_S| |apply Nat.le_refl|apply Nat.le_refl].

Ltac segRLs_n_1 :=
  eapply segRLs_n_trans with (h1:=[_]) (h2:=[_]); [segRLs_n_lrcons_1| |apply Nat.le_refl|apply Nat.le_refl].

Ltac segRLs_n_2 :=
  eapply segRLs_n_trans with (h1:=[_]) (h2:=[_;_]); [segRLs_n_lrcons_2| |apply Nat.le_refl|apply Nat.le_refl].

Module TM1.
  
Definition tm := Eval compute in (TM_from_str "1RB0RA_1RC0RE_0RD1RE_0LE---_1LF0LC_1RA0LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (B,<[0;0;1]).
Notation hL := (C,[0;1;0]).
Notation hR' := (A,<[0]).
Notation h := [(hR,hL)].
Notation h' := [(hR',hL)].
Notation hLR := [(hL,hR)].
Notation hLR' := [(hL,hR')].

Notation w := [1;0;1;0].
Notation d0 := [1;0;0;1;1;1;0].
Notation d1 := [1;0;0;1;0;1;0].

Definition LC a b := 0inf <* <[1;0;1;1]^^a <* <[0;0] <* <[1;0;1;1]^^b.
Definition tm' := flip tm.

Lemma LInc a b:
  sideRLs tm' hLR (LC a (1+b)) (LC (1+a) b).
Proof.
  ut; esx.
Qed.

Lemma LOv a:
  sideRLs tm' (hLR') (LC a 0) (LC 0 (1+a)).
Proof.
  ut; esx.
Qed.

Definition D1 a b := w^^a ++ [0]^^b.

Lemma D1_Inc2 a b:
  segRLs_n tm (h^^2++h') [] (D1 a (6+b)) (D1 (1+a) b) 1.
Proof.
  ut.
  do 2 segRLs_n_0.
  segRLs_n_S.
Qed.

Lemma D1_Inc3 a b:
  segRLs_n tm (h^^3++h') [] (D1 a (6+b)) (D1 (1+a) b) 1.
Proof.
  ut.
  do 3 segRLs_n_0.
  segRLs_n_S.
Qed.

Definition D2 a := w^^a ++ d0 ++ w.

Lemma D1_Ov a:
  segRLs_n tm (h^^4++h'++h^^4++h'++h) [] (D1 a 15) (D2 a) 1.
Proof.
  ut.
  do 10 segRLs_n_0.
  segRLs_n_S.
Qed.

Lemma D2_Inc a:
  segRLs_n tm (h^^2) h (D2 a) (D2 a) 1.
Proof.
  ut.
  segRLs_n_0.
  segRLs_n_lrcons_1.
Qed.

Lemma D2_Ov a:
  segRLs_n tm (h'++h^^2) (h++h') (D2 a) (D2 a) 1.
Proof.
  ut.
  segRLs_n_0.
  segRLs_n_1.
  segRLs_n_lrcons_1.
Qed.

Lemma D2_Ov' a:
  segRLs_n tm (h++h'++h^^2) (h++h') (D2 a) (D2 a) 1.
Proof.
  ut.
  do 2 segRLs_n_0.
  segRLs_n_1.
  segRLs_n_lrcons_1.
Qed.

Lemma D2_IncsOv a n:
  segRLs_n tm (h^^n++h'++h^^2) (h^^(n/2+1)++h') (D2 a) (D2 a) 1.
Proof.
  induction n using lt_wf_ind.
  destruct n.
  1: apply D2_Ov.
  destruct n.
  1: apply D2_Ov'.
  change (S(S n)) with (2+n).
  replace ((2+n)/2+1) with (1+(n/2+1)) by lia.
  do 2 rewrite lpow_add.
  repeat rewrite <-List.app_assoc.
  eapply segRLs_n_trans.
  3,4: apply Nat.le_refl.
  1: apply D2_Inc.
  apply H; lia.
Qed.

Lemma D1_Incs a b k i:
  (i=2\/i=3) ->
  k<>O ->
  segRLs_n tm ((h^^i++h')^^k) [] (D1 a (k*6+b)) (D1 (k+a) b) 1.
Proof.
  intro Hi.
  gen a.
  induction k; intros.
  1: lia.
  destruct k.
  - destruct Hi; subst.
    + apply D1_Inc2.
    + apply D1_Inc3.
  - remember (S k) as k'.
    cbn[lpow].
    eapply segRLs_n_trans with (h2:=[]).
    3,4: constructor.
    2: applys_eq (IHk (1+a)); flia.
    destruct Hi; subst.
    + apply D1_Inc2.
    + apply D1_Inc3.
Qed.

Lemma init:
  c0 -->*
  LC 2 5 {{{ (hR,R) }}} D2 4 *> 0inf.
Proof.
  esx.
Qed.

CoFixpoint HLR(a b:nat) :=
match b with
| O => hLR*>HLR 0 (1+a)
| S b => hLR'*>HLR (1+a) b
end.

CoFixpoint H (a:nat)(f:nat->nat) :=
match a with
| O => h'*>H (f O) (fun n => f (S n))
| S n => h*>H n f
end.

Lemma H_S a f:
  H (S a) f = h*>H a f.
Proof.
  rewrite (Cons_unfold _ (H (S a) f)).
  reflexivity.
Qed.

Lemma H_O f:
  H O f = h'*>H (f O) (fun n => f (S n)).
Proof.
  rewrite (Cons_unfold _ (H 0 f)).
  reflexivity.
Qed.

Lemma H_add k a f:
  H (k+a) f = h^^k*>H a f.
Proof.
  induction k.
  - trivial.
  - cbn[Nat.add].
    rewrite H_S.
    cbn.
    rewrite IHk.
    reflexivity.
Qed.


Lemma H_spec a f:
  H a f = (h^^a++h') *> H (f O) (fun n => f (S n)).
Proof.
  replace (H a) with (H (a+0)) by flia.
  rewrite H_add.
  rewrite Str_app_assoc.
  rewrite H_O.
  reflexivity.
Qed.

Inductive P1: _->_->_->Prop :=
| P1_intro a f a0:
    (forall n,2<=f n) ->
    P1 (H a f) (H (1+a/2) (fun n=>(f n)/2)) (D2 a0).

Lemma H_D2 L R w:
  P1 L R w ->
  downRect tm L R w 1.
Proof.
  intro H.
  eapply segRLs_n_inf_trans.
  2: apply H.
  clear.
  intros.
  inverts H0.
  eexists (h^^a++h'++h^^2),(h^^(1+a/2)++h'),_,
  (H (f O-2) (fun n => f (S n))),_.
  split.
  { cbn; lia. }
  split.
  { specialize (H1 O).
    rewrite H_spec.
    replace (H (f O)) with (H (2+((f O)-2))) by flia.
    rewrite H_add.
    repeat rewrite Str_app_assoc.
    reflexivity. }
  split.
  { rewrite H_spec.
    specialize (H1 O).
    replace (1+(f O-2)/2) with ((f O)/2) by lia.
    reflexivity. }
  split.
  1: applys_eq D2_IncsOv; flia.
  applys_eq P1_intro.
  - specialize (H1 O).
    flia.
  - intros.
    apply H1.
Qed.

Definition H0 a b := fun n => (a+n)/2^b.

Ltac fext :=
  apply FunctionalExtensionality.functional_extensionality; intro.

Lemma H0_S a b:
  (fun n => H0 a b (S n)) =
  (H0 (S a) b).
Proof.
  unfold H0.
  fext.
  flia.
Qed.

Definition H1 a b := H (H0 a b O) (fun n => H0 a b (S n)).

Lemma H1_S a b:
  H1 a b = (h^^(a/2^b)++h') *> H1 (1+a) b.
Proof.
  unfold H1.
  rewrite H_spec,<-H0_S.
  unfold H0; flia.
Qed.

Lemma H1_Ss a b i:
  a<=2^b ->
  H1 (i*2^b+a) b = (h^^i++h')^^(2^b-a) *> H1 ((1+i)*2^b) b.
Proof.
  remember (2^b-a) as c.
  gen a b i.
  induction c; intros.
  - cbn; flia.
  - rewrite H1_S.
    rewrite Nat.div_add_l by lia.
    rewrite Nat.div_small by lia.
    cbn[lpow].
    replace (1+(i*2^b+a)) with (i*2^b+S a) by lia.
    rewrite IHc by lia.
    repeat rewrite Str_app_assoc.
    flia.
Qed.

Definition H2 i := (H1 (2*2^(2+i)+2) (2+i)).

Opaque H1.

Lemma H1_downRect i:
  downRect tm (H2 i) (H2 (1+i)) (D1 0 ((2^(2+i)-2)*6+((2^(2+i)-0)*6+15))) 1.
Proof.
  unfold H2.
  rewrite H1_Ss by (cbn; lia).
  eapply segRLs_n_downRect_trans with (hR:=[]).
  1: apply D1_Incs; (cbn; lia).
  rewrite <-(Nat.add_0_r ((1+2)*2^(2+i))).
  rewrite H1_Ss by (cbn; lia).
  eapply segRLs_n_downRect_trans with (hR:=[]).
  1: apply D1_Incs; (cbn; lia).
  rewrite H1_S.
  rewrite Nat.div_mul by lia.
  rewrite H1_S.
  rewrite Nat.div_add by lia.
  unfold H1 at 1.
  rewrite H0_S.
  unfold H0 at 1.
  match goal with
  | |- context[H ?a] => replace a with 4
  end.
  2:{
    rewrite Nat.add_0_r.
    rewrite Nat.add_assoc.
    rewrite Nat.div_add by lia.
    rewrite Nat.div_small by (cbn; lia).
    lia.
  }
  rewrite Nat.div_small by (cbn; lia).
  rewrite H_S.
  do 2 rewrite <-Str_app_assoc.
  eapply segRLs_n_downRect_trans with (hR:=[]).
  1: apply D1_Ov.
  apply H_D2.
  Transparent H1.
  applys_eq P1_intro.
  - unfold H1.
    f_equal.
    + unfold H0.
      rewrite Nat.add_0_r.
      rewrite Nat.div_add_l by lia.
      rewrite Nat.div_small by (cbn; lia).
      lia.
    + fext.
      unfold H0.
      rewrite Nat.Div0.div_div.
      f_equal; cbn; lia.
  - intros.
    unfold H0.
    match goal with
    | |- context[2<= ?a/_ ] => replace a with (4*2^(2+i)+(3+n)) by lia
    end.
    rewrite Nat.div_add_l by lia.
    lia.
Qed.

Definition H3 := H 6 (fun n => 8+n).
Definition H4 := H 4 (fun n => 4+n/2).
Definition H5 := H1 9 2.

Lemma H3_downRect a:
  downRect tm H3 H4 (D2 a) 1.
Proof.
  unfold H3,H4.
  eapply H_D2.
  applys_eq P1_intro.
  - f_equal.
    fext; lia.
  - intros; cbn; lia.
Qed.

Opaque H1.

Lemma H4_downRect:
  downRect tm H4 H5 (D1 0 15) 1.
Proof.
  unfold H4,H5.
  rewrite H_spec.
  rewrite H_spec.
  do 2 rewrite Nat.add_0_r.
  rewrite H_S.
  do 2 rewrite <-Str_app_assoc.
  eapply segRLs_n_downRect_trans with (hR:=[]).
  1: apply D1_Ov.
  apply H_D2.
  Transparent H1.
  applys_eq P1_intro.
  - unfold H1.
    rewrite H0_S.
    f_equal.
    unfold H0.
    fext.
    lia.
  - intros; cbn; lia.
Qed.

Opaque H2.

Lemma H5_downRect:
  downRect tm H5 (H2 1) (D1 0 (3*6+(4*6+15))) 1.
Proof.
  unfold H5.
  change 9 with (2*2^2+1) at 1.
  rewrite H1_Ss by lia.
  eapply segRLs_n_downRect_trans with (hR:=[]).
  1: apply D1_Incs; (cbn; lia).
  change ((1+2)*2^2) with (3*2^2+0).
  rewrite H1_Ss by lia.
  eapply segRLs_n_downRect_trans with (hR:=[]).
  1: apply D1_Incs; (cbn; lia).
  rewrite H1_S.
  rewrite H1_S.
  unfold H1.
  match goal with
  | |- context[H ?a] => change a with 4
  end.
  rewrite H_S.
  do 2 rewrite <-Str_app_assoc.
  rewrite H0_S.
  eapply segRLs_n_downRect_trans with (hR:=[]).
  1: apply D1_Ov.
  eapply H_D2.
  Transparent H2.
  applys_eq P1_intro.
  - unfold H2,H1,H0.
    f_equal.
    fext; lia.
  - intros.
    unfold H0.
    lia.
Qed.

Inductive P2: _->_->Prop :=
| P2_intro i:
  P2 (H2 i) 0inf.

Inductive P3:_->_->_->Prop :=
| P3_S a b:
  P3 hR (H (2+b) (fun n => ((2+a+b)+n))) (LC a (1+b))
| P3_O a:
  P3 hR (H 1 (fun n => (2+a)+n)) (LC (1+a) 0)
| P3_O' a:
  P3 hR' (H 0 (fun n => (2+a)+n)) (LC 0 (2+a))
.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply quadRect_nonhalt with (L:=H3).
  - eapply downRect_quadRect_concat.
    1: apply H3_downRect.
    rewrite <-(lpow_all0 [0] 15) by solve_const0_eq.
    eapply downRect_quadRect_concat.
    1: apply H4_downRect.
    rewrite <-(lpow_all0 [0] 57) by solve_const0_eq.
    eapply downRect_quadRect_concat.
    1: apply H5_downRect.
    eapply downRect_inf_concat with (P:=P2).
    2: constructor.
    intros.
    inverts H6.
    eexists _,0inf,(D1 0 _),1%nat.
    split.
    1: lia.
    split.
    1:{
      unfold D1.
      cbn[lpow app].
      rewrite lpow_all0; solve_const0_eq.
    }
    split.
    1: eapply H1_downRect.
    constructor.
  - eapply leftRealizes_inf_concat with (P:=P3).
    2:{
      unfold H3.
      apply (P3_S 2 4).
    }
    intros.
    inverts H6.
    + eexists h,_,_,hLR,_.
      split.
      1: cbn; lia.
      split.
      { cbn[Nat.add].
        rewrite H_S; reflexivity. }
      split.
      1: reflexivity.
      split.
      1: apply LInc.
      destruct b.
      * applys_eq (P3_O a).
        f_equal.
        fext; lia.
      * applys_eq (P3_S (1+a) b).
        f_equal.
        fext; lia.
    + eexists h,_,_,hLR',_.
      split.
      1: cbn; lia.
      split.
      { rewrite H_S; reflexivity. }
      split.
      1: reflexivity.
      split.
      1: apply LOv.
      apply P3_O'.
    + eexists h',_,_,hLR,_.
      split.
      1: cbn; lia.
      split.
      { rewrite H_O; reflexivity. }
      split.
      1: reflexivity.
      change (2+a) with (1+(1+a)).
      split.
      1: apply LInc.
      applys_eq (P3_S 1 a).
      f_equal.
      1: lia.
      fext; lia.
Qed.

End TM1.

