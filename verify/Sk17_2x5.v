(* BB(2,5): column-flow closure and two blank-tape nonhalting proofs.
   No BB(6)-specialized imports or additional axioms. *)

From Coq Require Import List Bool Arith ZifyNat Lia.
From BusyCoq Require Import Helper.
Import ListNotations.
Set Implicit Arguments.

Fixpoint Alt (p:bool) n := match n with
| 0 => [] | S n => p :: Alt (negb p) n end.
Definition Ret n := Alt (negb (Nat.odd n)) n ++ [true;true;true].

Lemma odd0 n : Nat.odd (n*2)=false.
Proof. rewrite Nat.odd_mul; cbn; apply andb_false_r. Qed.
Lemma odd1 n : Nat.odd (1+n*2)=true.
Proof. rewrite Nat.odd_add, odd0; reflexivity. Qed.
Lemma oddS n : Nat.odd (S n)=negb (Nat.odd n).
Proof. rewrite Nat.odd_succ, Nat.negb_odd; reflexivity. Qed.
Inductive Pass : list bool -> nat -> nat -> list bool -> Prop :=
| pass_nil a : Pass [] a a []
| pass_P w a b o : Pass w (1+a) b o -> Pass (true::w) a b o
| pass_I w a b o : a<>0 -> Pass w a b o ->
    Pass (false::w) a b (Nat.odd a::o).

Lemma pass_app u v a b c p q : Pass u a b p -> Pass v b c q ->
  Pass (u++v) a c (p++q).
Proof. intro H; induction H; cbn; eauto using pass_nil, pass_P, pass_I. Qed.

Lemma pass_two p a w b o : a<>0 -> Pass w (1+a) b o ->
  Pass (p::negb p::w) a b (xorb (Nat.odd a) p::o).
Proof.
  destruct p; cbn; intros H HP.
  - rewrite xorb_true_r, <- oddS; apply pass_P, pass_I; [lia|assumption].
  - rewrite xorb_false_r; apply pass_I; [assumption|apply pass_P; assumption].
Qed.

Lemma pass_even k : forall p a, a<>0 ->
  Pass (Alt p (k*2)) a (a+k) (Alt (xorb (Nat.odd a) p) k).
Proof.
  induction k; intros p a HA.
  - cbn; rewrite Nat.add_0_r; constructor.
  - replace (S k*2) with (2+k*2) by lia; cbn[Alt Nat.add].
    rewrite negb_involutive, Nat.add_succ_r.
    replace (negb (xorb (Nat.odd a) p)) with (xorb (Nat.odd (S a)) p)
      by (rewrite oddS; destruct (Nat.odd a),p; reflexivity).
    apply pass_two; [assumption|apply IHk; lia].
Qed.

Lemma pass_odd_P k a :
  Pass (Alt true (1+k*2)) a (1+a+k) (Alt (negb (Nat.odd a)) k).
Proof.
  cbn[Nat.add Alt]; apply pass_P.
  pose proof (@pass_even k false (S a) ltac:(lia)) as H.
  rewrite oddS, xorb_false_r in H; exact H.
Qed.
Lemma pass_odd_I k a : a<>0 ->
  Pass (Alt false (1+k*2)) a (a+k) (Alt (Nat.odd a) (1+k)).
Proof.
  intro HA; cbn[Nat.add Alt]; apply pass_I; [assumption|].
  pose proof (@pass_even k true a HA) as H.
  rewrite xorb_true_r in H; exact H.
Qed.

Definition Trans a w v := exists b o, Pass w a b o /\ v=o++Ret b.
Lemma trans_app u v a b p q : Pass u a b p -> Trans b v q ->
  Trans a (u++v) (p++q).
Proof.
  intros H [c [o [H' ->]]]; exists c, (p++o); split.
  - eapply pass_app; eauto.
  - rewrite app_assoc; reflexivity.
Qed.
Lemma trans_end a : Trans a [true;true;true] (Ret (3+a)).
Proof. exists (3+a), (@nil bool); split; [repeat constructor|reflexivity]. Qed.

Lemma trans_I a w v : Trans a w v -> a<>0 ->
  Trans a (false::w) (Nat.odd a::v).
Proof. intros [b [o [H ->]]] HA; exists b, (Nat.odd a::o); split; [constructor; assumption|reflexivity]. Qed.
Lemma trans_P a w v : Trans (1+a) w v -> Trans a (true::w) v.
Proof. intros [b [o [H ->]]]; exists b,o; split; [constructor; assumption|reflexivity]. Qed.

Inductive Carry : nat -> list bool -> Prop :=
| carry_end n : Carry n (Alt true (3+n*3) ++ [true;true;true])
| carry_step n w : Carry (1+n*2) w ->
    Carry n (Alt true (3+n*3) ++ false::w).

Inductive Num : nat -> list bool -> Prop :=
| num_end0 n : Num n (Alt (negb (Nat.odd n)) (n*3) ++ [true;true;true])
| num_end1 n : Num n (Alt (negb (Nat.odd n)) (2+n*3) ++ [true;true;true])
| num_zero n w : Num (n*2) w ->
    Num n (Alt (negb (Nat.odd n)) (n*3) ++ false::w)
| num_one n w : Num (1+n*2) w ->
    Num n (Alt (negb (Nat.odd n)) (1+n*3) ++ true::w)
| num_carry n w : Carry (1+n*2) w ->
    Num n (Alt (negb (Nat.odd n)) (2+n*3) ++ false::w).

Lemma carry_num n w : Carry n w -> Nat.odd n=true -> Num (1+n) w.
Proof.
  intro H; induction H; intro E.
  - replace (3+n*3) with ((1+n)*3) by lia.
    assert (E' : negb (Nat.odd (1+n))=true) by (rewrite oddS,E; reflexivity).
    rewrite <- E' at 1.
    constructor.
  - replace (3+n*3) with ((1+n)*3) by lia.
    assert (E' : negb (Nat.odd (1+n))=true) by (rewrite oddS,E; reflexivity).
    rewrite <- E' at 1.
    apply num_zero; replace ((1+n)*2) with (1+(1+n*2)) by lia.
    apply IHCarry, odd1.
Qed.

Lemma pass_even_P k a : a<>0 ->
  Pass (Alt true (k*2)) a (a+k) (Alt (negb (Nat.odd a)) k).
Proof. intro H; pose proof (@pass_even k true a H) as H'; rewrite xorb_true_r in H'; exact H'. Qed.

Lemma odd6 n : Nat.odd (n*6)=false.
Proof. rewrite Nat.odd_mul; cbn; apply andb_false_r. Qed.
Lemma odd12 n : Nat.odd (n*12)=false.
Proof. rewrite Nat.odd_mul; cbn; apply andb_false_r. Qed.

Lemma carry_trans n w : Carry n w ->
  (forall k, n=1+k*4 -> exists v, Trans (1+k*6) w v /\ Num (1+k*2) v) /\
  (forall k, n=3+k*4 -> exists v, Trans (4+k*6) w v /\ Carry (1+k*2) v).
Proof.
  intro H; induction H as [n|n w H [IH0 IH1]]; split; intros k ->.
  - pose proof (@pass_even_P (3+k*6) (1+k*6) ltac:(lia)) as HP.
    rewrite Nat.odd_add, odd6 in HP; cbn[negb Nat.odd xorb] in HP.
    replace ((3+k*6)*2) with (3+(1+k*4)*3) in HP by lia.
    replace (1+k*6+(3+k*6)) with (4+k*12) in HP by lia.
    exists (Alt false (3+k*6) ++ Ret (7+k*12)); split.
    + apply (trans_app HP); replace (7+k*12) with (3+(4+k*12)) by lia; apply trans_end.
    + unfold Ret; rewrite Nat.odd_add, odd12; cbn[Nat.odd xorb negb].
      change (Num (1+k*2) (Alt false (3+k*6) ++ false::(Alt true (6+k*12) ++ [true;true;true]))).
      pose proof (@num_zero (1+k*2) _ (num_end0 ((1+k*2)*2))) as HN.
      rewrite odd1, odd0 in HN; cbn[negb] in HN.
      replace ((1+k*2)*3) with (3+k*6) in HN by lia.
      replace ((1+k*2)*2*3) with (6+k*12) in HN by lia; exact HN.
  - pose proof (@pass_even_P (6+k*6) (4+k*6) ltac:(lia)) as HP.
    rewrite Nat.odd_add, odd6 in HP; cbn[negb Nat.odd xorb] in HP.
    replace ((6+k*6)*2) with (3+(3+k*4)*3) in HP by lia.
    replace (4+k*6+(6+k*6)) with (10+k*12) in HP by lia.
    exists (Alt true (6+k*6) ++ Ret (13+k*12)); split.
    + apply (trans_app HP); replace (13+k*12) with (3+(10+k*12)) by lia; apply trans_end.
    + unfold Ret; rewrite Nat.odd_add, odd12; cbn[Nat.odd xorb negb].
      change (Carry (1+k*2) (Alt true (6+k*6) ++ false::(Alt true (12+k*12) ++ [true;true;true]))).
      pose proof (@carry_step (1+k*2) _ (carry_end (1+(1+k*2)*2))) as HC.
      replace (3+(1+k*2)*3) with (6+k*6) in HC by lia.
      replace (3+(1+(1+k*2)*2)*3) with (12+k*12) in HC by lia; exact HC.
  - destruct (IH1 (k*2) ltac:(lia)) as [v [HV HN]].
    replace (4+k*2*6) with (4+k*12) in HV by lia.
    pose proof (@pass_even_P (3+k*6) (1+k*6) ltac:(lia)) as HP.
    rewrite Nat.odd_add, odd6 in HP; cbn[negb Nat.odd xorb] in HP.
    replace ((3+k*6)*2) with (3+(1+k*4)*3) in HP by lia.
    replace (1+k*6+(3+k*6)) with (4+k*12) in HP by lia.
    exists (Alt false (3+k*6) ++ false::v); split.
    + apply (trans_app HP). destruct HV as [b [o [HV ->]]].
      exists b, (false::o); split; [|reflexivity].
      assert (E : Nat.odd (4+k*12)=false) by (rewrite Nat.odd_add, odd12; reflexivity).
      rewrite <- E at 2.
      apply pass_I; [lia|exact HV].
    + apply carry_num in HN; [|apply odd1].
      replace (1+(1+k*2*2)) with ((1+k*2)*2) in HN by lia.
      pose proof (@num_zero (1+k*2) _ HN) as HN'.
      rewrite odd1 in HN'; cbn[negb] in HN'.
      replace ((1+k*2)*3) with (3+k*6) in HN' by lia; exact HN'.
  - destruct (IH1 (1+k*2) ltac:(lia)) as [v [HV HN]].
    replace (4+(1+k*2)*6) with (10+k*12) in HV by lia.
    pose proof (@pass_even_P (6+k*6) (4+k*6) ltac:(lia)) as HP.
    rewrite Nat.odd_add, odd6 in HP; cbn[negb Nat.odd xorb] in HP.
    replace ((6+k*6)*2) with (3+(3+k*4)*3) in HP by lia.
    replace (4+k*6+(6+k*6)) with (10+k*12) in HP by lia.
    exists (Alt true (6+k*6) ++ false::v); split.
    + apply (trans_app HP). destruct HV as [b [o [HV ->]]].
      exists b, (false::o); split; [|reflexivity].
      assert (E : Nat.odd (10+k*12)=false) by (rewrite Nat.odd_add, odd12; reflexivity).
      rewrite <- E at 2.
      apply pass_I; [lia|exact HV].
    + pose proof (@carry_step (1+k*2) _ HN) as HC.
      replace (3+(1+k*2)*3) with (6+k*6) in HC by lia; exact HC.
Qed.

Inductive OddNum : nat -> list bool -> Prop :=
| on_one n w : Num (1+n*2) w ->
    OddNum n (Alt (negb (Nat.odd n)) (1+n*3) ++ true::w)
| on_carry n w : Carry (1+n*2) w ->
    OddNum n (Alt (negb (Nat.odd n)) (2+n*3) ++ false::w).
Lemma oddnum_num n w : OddNum n w -> Num n w.
Proof. intro H; destruct H; eauto using num_one, num_carry. Qed.

Ltac parity :=
  repeat (rewrite Nat.odd_add || rewrite Nat.odd_mul);
  cbn[Nat.odd Nat.even andb xorb negb];
  repeat (rewrite andb_true_r || rewrite andb_false_r || rewrite xorb_false_r ||
    rewrite xorb_true_r || rewrite negb_involutive).
Ltac words := unfold Ret; parity; cbn[Alt app Nat.add Nat.mul]; flia.

Lemma num_trans n w : Num n w ->
  (forall m, n=m*2 -> m<>0 -> exists v, Trans (m*3) w v /\ Num m v) /\
  (forall m, n=1+m*2 -> exists v,
    Trans (2+m*3) w (Nat.odd m::v) /\ OddNum m v).
Proof.
  intro H; induction H as [n|n|n w H [IH0 IH1]|n w H [IH0 IH1]|n w HC];
    split; intros m ->; try intro HM; parity.
  - exists (Alt (negb (Nat.odd m)) (m*3) ++ Ret (3+m*6)); split.
    + applys_eq (trans_app (@pass_even_P (m*3) (m*3) ltac:(lia))
        (trans_end (m*3+m*3))); parity; flia.
    + applys_eq (@num_zero m _ (num_end1 (m*2))); words.
  - exists (Alt (negb (Nat.odd m)) (1+m*3) ++ Ret (6+m*6)); split.
    + applys_eq (trans_app (@pass_odd_I (1+m*3) (2+m*3) ltac:(lia))
        (trans_end (2+m*3+(1+m*3)))); parity; cbn[Alt app Nat.add Nat.mul]; flia.
    + applys_eq (@on_one m _ (num_end1 (1+m*2))); words.
  - exists (Alt (negb (Nat.odd m)) (1+m*3) ++ Ret (4+m*6)); split.
    + applys_eq (trans_app (@pass_even_P (1+m*3) (m*3) ltac:(lia))
        (trans_end (m*3+(1+m*3)))); parity; flia.
    + applys_eq (@num_one m _ (num_end0 (1+m*2))); words.
  - exists (Alt (negb (Nat.odd m)) (2+m*3) ++ Ret (7+m*6)); split.
    + applys_eq (trans_app (@pass_odd_I (2+m*3) (2+m*3) ltac:(lia))
        (trans_end (2+m*3+(2+m*3)))); parity; cbn[Alt app Nat.add Nat.mul]; flia.
    + applys_eq (@on_carry m _ (carry_end (1+m*2))); words.
  - destruct (IH0 (m*2) ltac:(lia) ltac:(lia)) as [v [HV HN]].
    exists (Alt (negb (Nat.odd m)) (m*3) ++ false::v); split.
    + eapply trans_app with (b:=m*2*3).
      * applys_eq (@pass_even_P (m*3) (m*3) ltac:(lia)); parity; flia.
      * applys_eq (trans_I HV ltac:(lia)); parity; flia.
    + apply num_zero; assumption.
  - destruct (IH0 (1+m*2) ltac:(lia) ltac:(lia)) as [v [HV HN]].
    exists (Alt (negb (Nat.odd m)) (1+m*3) ++ true::v); split.
    + assert (HP : Pass (Alt false ((1+m*2)*3)) (2+m*3) ((1+m*2)*3)
        (Nat.odd m::Alt (negb (Nat.odd m)) (1+m*3))).
      { applys_eq (@pass_odd_I (1+m*3) (2+m*3) ltac:(lia)); parity; cbn[Alt Nat.add Nat.mul]; flia. }
      apply (trans_app HP). applys_eq (trans_I HV ltac:(lia)); parity; flia.
    + constructor; assumption.
  - destruct (IH1 (m*2) ltac:(lia)) as [v [HV HN]].
    exists (Alt (negb (Nat.odd m)) (m*3) ++ false::v); split.
    + eapply trans_app with (b:=1+m*6).
      * applys_eq (@pass_odd_P (m*3) (m*3)); parity; flia.
      * apply trans_P. applys_eq HV; parity; flia.
    + apply num_zero, oddnum_num; assumption.
  - destruct (IH1 (1+m*2) ltac:(lia)) as [v [HV HN]].
    exists (Alt (negb (Nat.odd m)) (1+m*3) ++ true::v); split.
    + assert (HP : Pass (Alt false (1+(1+m*2)*3)) (2+m*3) (4+m*6)
        (Nat.odd m::Alt (negb (Nat.odd m)) (1+m*3))).
      { applys_eq (@pass_even (2+m*3) false (2+m*3) ltac:(lia)); parity; cbn[Alt Nat.add Nat.mul]; flia. }
      apply (trans_app HP), trans_P. applys_eq HV; parity; flia.
    + constructor; apply oddnum_num; assumption.
  - destruct (proj1 (carry_trans HC) m ltac:(lia)) as [v [HV HN]].
    exists (Alt (negb (Nat.odd m)) (1+m*3) ++ true::v); split.
    + eapply trans_app with (b:=1+m*6).
      * applys_eq (@pass_even_P (1+m*3) (m*3) ltac:(lia)); parity; flia.
      * applys_eq (trans_I HV ltac:(lia)); parity; flia.
    + constructor; assumption.
  - destruct (proj2 (carry_trans HC) m ltac:(lia)) as [v [HV HN]].
    exists (Alt (negb (Nat.odd m)) (2+m*3) ++ false::v); split.
    + assert (HP : Pass (Alt false (2+(1+m*2)*3)) (2+m*3) (4+m*6)
        (Nat.odd m::Alt (negb (Nat.odd m)) (2+m*3))).
      { applys_eq (@pass_odd_I (2+m*3) (2+m*3) ltac:(lia)); parity; cbn[Alt Nat.add Nat.mul]; flia. }
      apply (trans_app HP). applys_eq (trans_I HV ltac:(lia)); parity; flia.
    + constructor; assumption.
Qed.

Inductive Good : list bool -> Prop :=
| good_PP w : Num 1 w -> Good (true::true::w)
| good_IPP w : Num 1 w -> Good (false::true::true::w)
| good_IPII w : Carry 1 w -> Good (false::true::false::false::w).

Lemma oddnum_good w : OddNum 0 w -> Good (false::w).
Proof. intro H; inversion H; subst; cbn[Alt Nat.odd Nat.mul Nat.add negb app]; constructor; assumption. Qed.

Lemma good_trans p w : Good (p::w) -> exists v, Trans (Nat.b2n p) w v /\ Good v.
Proof.
  intro H; inversion H; subst.
  - destruct (proj2 (num_trans H1) 0 eq_refl) as [v [HV HN]].
    exists (false::v); split; [apply trans_P; exact HV|apply oddnum_good; assumption].
  - destruct (proj2 (num_trans H1) 0 eq_refl) as [v [HV HN]].
    exists (false::v); split; [apply trans_P, trans_P; exact HV|apply oddnum_good; assumption].
  - destruct (proj1 (carry_trans H1) 0 eq_refl) as [v [HV HN]].
    exists (true::true::v); split.
    + apply trans_P. change (Trans 1 (false::false::w0) (Nat.odd 1::Nat.odd 1::v)).
      apply trans_I; [apply trans_I; [exact HV|lia]|lia].
    + constructor; assumption.
Qed.

Lemma num1_I w : Num 1 w -> In false w.
Proof. intro H; inversion H; subst; cbn[Alt Nat.odd Nat.even Nat.mul Nat.add negb app In]; auto. Qed.
Lemma good_I p w : Good (p::w) -> In false w.
Proof. intro H; inversion H; subst; cbn; eauto using num1_I. Qed.

(* Finite-prefix semantics: a point column is included as the last entry. *)
Inductive LInc : bool -> list nat -> list nat -> Prop :=
| inc_P a xs : LInc true (a::xs) (1+a::xs)
| inc_I a xs ys : a<>0 -> LInc (Nat.odd a) xs ys -> LInc false (a::xs) (a::ys)
| inc_edge a : a<>0 -> LInc false [a] [a;Nat.b2n (Nat.odd a)].
Inductive Run : list bool -> list nat -> list nat -> Prop :=
| run_nil xs : Run [] xs xs
| run_cons p w xs ys zs : LInc p xs ys -> Run w ys zs -> Run (p::w) xs zs.

Lemma run_app u v xs zs : Run (u++v) xs zs <-> exists ys, Run u xs ys /\ Run v ys zs.
Proof.
  split.
  - revert xs; induction u; cbn; intros xs H.
    + eauto using run_nil.
    + inversion H; subst. destruct (IHu _ H5) as [cut [Hu Hv]]; eauto using run_cons.
  - intros [ys [H H']]; induction H; cbn; eauto using run_cons.
Qed.
Lemma run_P k a xs : Run (repeat true k) (a::xs) (a+k::xs).
Proof.
  revert a; induction k; intros; cbn.
  - rewrite Nat.add_0_r; constructor.
  - replace (a+S k) with (S a+k) by lia; econstructor; [constructor|apply IHk].
Qed.
Lemma pass_length w a b o : Pass w a b o -> length o<=length w.
Proof. intro H; induction H; cbn; lia. Qed.
Lemma pass_sound w a b o : Pass w a b o ->
  forall xs ys, Run o xs ys -> Run w (a::xs) (b::ys).
Proof.
  intro H; induction H; intros xs ys HR.
  - inversion HR; subst; constructor.
  - econstructor; [constructor|eauto].
  - inversion HR; subst; econstructor; [eapply inc_I; eauto|eauto].
Qed.
Lemma pass_split u v a b o : Pass (u++v) a b o ->
  exists c p q, Pass u a c p /\ Pass v c b q /\ o=p++q.
Proof.
  revert a o; induction u as [|s u IH]; cbn; intros a o H.
  - exists a, (@nil bool),o; auto using pass_nil.
  - inversion H; subst; match goal with
    | H : Pass (u++v) _ _ _ |- _ => destruct (IH _ _ H) as [c [p [q [HP [HQ ->]]]]]
    end; do 3 eexists; repeat split; eauto using pass_P,pass_I.
Qed.

Inductive Life : list bool -> list nat -> list bool -> list nat -> Prop :=
| life_internal w a xs b o : xs<>[] -> Pass w a b o ->
    Life w (a::xs) (o++Ret b) xs
| life_point k u a c o : a+k<>0 -> Pass u (a+k) c o ->
    Life (repeat true k++false::u) [a] (o++Ret c) [Nat.b2n (Nat.odd (a+k))].
CoInductive InfiniteLife : list bool -> list nat -> Prop :=
| life_more w xs v ys : Life w xs v ys -> InfiniteLife v ys -> InfiniteLife w xs.

Lemma terminal_prefix k u p q : repeat true k++false::u=p++q ->
  (exists j, p=repeat true j) \/ (exists v z, u=v++z /\ p=repeat true k++false::v).
Proof.
  revert p; induction k; intros [|s p] H; cbn in H.
  - left; exists 0; reflexivity.
  - inversion H; subst; right; exists p,q; auto.
  - left; exists 0; reflexivity.
  - inversion H; subst; destruct (IHk p H2) as [[j ->]|[v [z [Hu Hp]]]].
    + left; exists (S j); reflexivity.
    + right; exists v,z; cbn; subst; auto.
Qed.
Lemma life_nonempty w xs : InfiniteLife w xs -> xs<>[].
Proof. intros H E; destruct H as [w xs v ys H _]; inversion H; subst; discriminate. Qed.

Lemma infinite_prefix n : forall p q xs,
  length xs+length p<=n -> InfiniteLife (p++q) xs -> exists ys, Run p xs ys.
Proof.
  induction n as [|n IH]; intros p q xs Hn.
  - intro H; apply life_nonempty in H; destruct xs; cbn in Hn; congruence || lia.
  - remember (p++q) as w eqn:Ew; intro HI; destruct HI as [w xs v ys HL HI].
    destruct HL as [w a xs b o Hne HP|k u a c o Hpos HP].
    + rewrite Ew in HP; destruct (pass_split p q HP) as [d [o1 [o2 [H1 [H2 Eo]]]]].
      subst o; rewrite <- app_assoc in HI.
      destruct (IH o1 (o2++Ret b) xs) as [ys HR]; eauto.
      * apply pass_length in H1; cbn in Hn; lia.
      * exists (d::ys); eapply pass_sound; eauto.
    + destruct (terminal_prefix k u p q Ew) as [[j ->]|[u1 [u2 [Eu Ep]]]].
      * eauto using run_P.
      * subst u p; destruct (pass_split u1 u2 HP) as [d [o1 [o2 [H1 [H2 Eo]]]]].
        subst o; rewrite <- app_assoc in HI.
        destruct (IH o1 (o2++Ret c) [Nat.b2n (Nat.odd (a+k))]) as [ys HR]; eauto.
        -- apply pass_length in H1; rewrite length_app,repeat_length in Hn; cbn in *; lia.
        -- exists (d::ys); apply run_app; eexists; split; [apply run_P|].
           econstructor; [constructor; assumption|eapply pass_sound; eauto].
Qed.

Lemma inc_functional p xs ys : LInc p xs ys -> forall zs, LInc p xs zs -> ys=zs.
Proof.
  intro H; induction H; intros zs Hz; inversion Hz; subst; auto.
  - f_equal; eauto.
  - match goal with H : LInc _ [] _ |- _ => inversion H end.
  - match goal with H : LInc _ [] _ |- _ => inversion H end.
Qed.
Lemma run_functional w xs ys : Run w xs ys -> forall zs, Run w xs zs -> ys=zs.
Proof.
  intro H; induction H; intros last Hz; inversion Hz; subst; auto.
  match goal with H1 : LInc ?p ?xs ?ys, H2 : LInc ?p ?xs ?zs |- _ =>
    assert (ys=zs) by (eapply inc_functional; eauto); subst end; eauto.
Qed.
Lemma life_sound w xs v ys : Life w xs v ys -> forall zs, Run v ys zs ->
  exists a tail, Run w xs (a::tail) /\ Run (Ret a) tail zs.
Proof.
  intros H zs HR; destruct H; apply run_app in HR; destruct HR as [cut [Ho Hr]].
  - eauto using pass_sound.
  - exists c,cut; split; [|assumption]; apply run_app.
    eexists; split; [apply run_P|]; econstructor; [constructor; assumption|].
    eapply pass_sound; eauto.
Qed.
Inductive Macro : list nat -> list nat -> Prop :=
| macro_retire a xs ys : Run (Ret a) xs ys -> Macro (a::xs) ys.
CoInductive InfiniteMacro : list nat -> Prop :=
| macro_more xs ys : Macro xs ys -> InfiniteMacro ys -> InfiniteMacro xs.

Theorem infinite_life_sound w xs : InfiniteLife w xs -> forall ys, Run w xs ys -> InfiniteMacro ys.
Proof.
  revert w xs; cofix CIH; intros w xs HI ys HR; destruct HI as [w xs v pending HL HI].
  assert (HR' : InfiniteLife (v++[]) pending) by (rewrite app_nil_r; exact HI).
  destruct (@infinite_prefix (length pending+length v) v [] pending ltac:(lia) HR') as [zs HZ].
  destruct (life_sound HL HZ) as [a [tail [Hrun Hmacro]]].
  assert (ys=a::tail) by (eapply run_functional; eauto); subst ys.
  econstructor; [constructor; eassumption|eapply (CIH v pending HI); exact HZ].
Qed.

Lemma pass_first w a b o : Pass w a b o -> In false w ->
  exists k u v, w=repeat true k++false::u /\ a+k<>0 /\
    Pass u (a+k) b v /\ o=Nat.odd (a+k)::v.
Proof.
  intro H; induction H; intro HI.
  - contradiction.
  - cbn in HI; destruct HI as [HI|HI]; [discriminate|].
    destruct (IHPass HI) as [k [u [v [E [HN [HP EO]]]]]].
    exists (S k),u,v; replace (a+S k) with (1+a+k) by lia; cbn; subst; auto.
  - exists 0,w,o; rewrite Nat.add_0_r; cbn; auto.
Qed.

Lemma good_life p w : Good (p::w) -> exists q v,
  Life w [Nat.b2n p] v [Nat.b2n q] /\ Good (q::v).
Proof.
  intro H; destruct (good_trans H) as [z [[b [o [HP ->]]] HG]].
  destruct (pass_first HP (good_I H)) as [k [u [v [-> [HN [HU ->]]]]]].
  exists (Nat.odd (Nat.b2n p+k)),(v++Ret b); split; [constructor; assumption|exact HG].
Qed.
Lemma good_infinite p w : Good (p::w) -> InfiniteLife w [Nat.b2n p].
Proof.
  revert p w; cofix CIH; intros p w H; destruct (good_life H) as [q [v [HL HG]]].
  econstructor; [exact HL|apply CIH; exact HG].
Qed.

Theorem seed_infinite : InfiniteMacro [1;1].
Proof.
  apply (@infinite_life_sound [] [1;1]); [|constructor].
  eapply life_more with (v:=Ret 1) (ys:=[1]).
  - apply (@life_internal [] 1 [1] 1 []); [discriminate|constructor].
  - eapply life_more with (v:=Ret 4) (ys:=[1]).
    + apply (@life_point 0 [true;true;true] 1 4 []); [lia|repeat constructor].
    + apply (@good_infinite true). change (Good (true::true::(Alt false 3++[true;true;true]))).
      constructor; apply num_end0.
Qed.

(* Raw-machine interpretation and the two concrete machines. *)

From BusyCoq Require Import Individual25.
From Coq Require Import Arith Bool ZifyNat Lia String List.
Import ListNotations.
Set Implicit Arguments.

Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB3RB1LB---2RB_2LA1RA4LB2LA2RA").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Definition W n := [4]^^n ++ [1;2].

Lemma column_A_even a l r :
  l {{A}}> W (2+a*2) *> r -->+ l <{{B}} W (1+a*2) *> [4] *> r.
Proof. unfold W; es. Qed.
Lemma column_B_odd a l r :
  l {{B}}> W (1+a*2) *> r -->+ l <{{B}} W (a*2) *> [4] *> r.
Proof. unfold W; es. Qed.
Lemma column_A_odd a r r' :
  (forall l, l {{B}}> r -->+ l <{{B}} r') ->
  forall l, l {{A}}> W (1+a*2) *> r -->+
    l <{{B}} W (a*2) *> [4] *> r'.
Proof. intros H l; unfold W; es; er; follow100 H; es. Qed.
Lemma column_B_even a r r' :
  (forall l, l {{B}}> r -->+ l <{{B}} r') ->
  forall l, l {{B}}> W (2+a*2) *> r -->+
    l <{{B}} W (1+a*2) *> [4] *> r'.
Proof. intros H l; unfold W; es; er; follow100 H; es. Qed.

Lemma point_B_even a l : l {{B}}> [4]^^(2+a*2) *> 0inf -->+
  l <{{B}} W (1+a*2) *> 0inf.
Proof. unfold W; es. Qed.
Lemma point_B_odd a l : l {{B}}> [4]^^(1+a*2) *> 0inf -->+
  l <{{B}} W (a*2) *> [4] *> 0inf.
Proof. unfold W; es. Qed.

Lemma retire r : 0inf << 1 {{A}}> W 0 *> r -->+
  0inf << 1 {{A}}> [4]^^3 *> r.
Proof. unfold W; es. Qed.

Fixpoint RC (xs:list nat) := match xs with
| [] => 0inf | [a] => [4]^^a *> 0inf | a::xs => W a *> RC xs end.
Definition C xs := 0inf << 1 {{A}}> RC xs.
Definition Active n xs := 0inf << 1 {{A}}> W n *> RC xs.

Lemma RC_cons a xs : xs<>[] -> RC (a::xs)=W a *> RC xs.
Proof. destruct xs; [contradiction|reflexivity]. Qed.
Lemma RC_P a xs : RC (1+a::xs)=4 >> RC (a::xs).
Proof. destruct xs; reflexivity. Qed.
Lemma inc_nonempty p xs ys : LInc p xs ys -> xs<>[] /\ ys<>[].
Proof. intro H; destruct H; split; discriminate. Qed.

Definition Signal (p:bool) r r' := if p then r'=4 >> r else
  exists s, r'=4 >> s /\ forall l, l {{B}}> r -->+ l <{{B}} s.

Lemma mod2 n : (exists k, n=k*2) \/ (exists k, n=1+k*2).
Proof.
  induction n as [|n [[k ->]|[k ->]]].
  - left; exists 0%nat; reflexivity.
  - right; exists k; reflexivity.
  - left; exists (1+k); lia.
Qed.

Lemma inc_spec p xs ys : LInc p xs ys -> Signal p (RC xs) (RC ys).
Proof.
  intro H; induction H as [a xs|a xs ys HA H IH|a HA].
  - apply RC_P.
  - destruct (inc_nonempty H) as [HX HY]; rewrite !RC_cons by assumption.
    destruct (mod2 a) as [[k ->]|[k ->]].
    + destruct k as [|k]; [lia|]. rewrite odd0 in IH; destruct IH as [r [-> IH]].
      exists (W (1+k*2) *> [4] *> r); split.
      * unfold W; simpl_tape; reflexivity.
      * apply column_B_even; exact IH.
    + rewrite odd1 in IH; cbn[Signal] in IH; rewrite IH.
      exists (W (k*2) *> [4] *> RC xs); split.
      * unfold W; simpl_tape; reflexivity.
      * intro l; apply column_B_odd.
  - destruct (mod2 a) as [[k ->]|[k ->]].
    + destruct k as [|k]; [lia|]; rewrite odd0; cbn[Nat.b2n RC].
      exists (W (1+k*2) *> 0inf); split.
      * unfold W; simpl_tape; reflexivity.
      * intro l; apply point_B_even.
    + rewrite odd1; cbn[Nat.b2n RC].
      exists (W (k*2) *> [4] *> 0inf); split.
      * unfold W; simpl_tape; reflexivity.
      * intro l; apply point_B_odd.
Qed.

Lemma active_step n xs ys : LInc (Nat.odd n) xs ys ->
  Active (1+n) xs -->+ Active n ys.
Proof.
  intro H; apply inc_spec in H; destruct (mod2 n) as [[k ->]|[k ->]].
  - rewrite odd0 in H; destruct H as [r [ER HR]].
    unfold Active; rewrite ER; follow10 (@column_A_odd k (RC xs) r HR); es.
  - rewrite odd1 in H; cbn[Signal] in H; unfold Active; rewrite H.
    follow10 (column_A_even k); es.
Qed.
Lemma active_run n xs ys : Run (Alt (negb (Nat.odd n)) n) xs ys ->
  Active n xs -->* Active 0 ys.
Proof.
  revert xs; induction n; intros xs H.
  - inversion H; subst; apply evstep_refl.
  - rewrite oddS,negb_involutive in H; cbn[Alt] in H.
    inversion H as [|p w source cut target HL HR]; subst.
    follow100 (active_step n HL); apply IHn; assumption.
Qed.
Lemma run3_RC xs ys : Run [true;true;true] xs ys -> RC ys=[4]^^3 *> RC xs.
Proof.
  intro H; destruct xs as [|a xs].
  - inversion H; match goal with H:LInc _ [] _ |- _ => inversion H end.
  - assert (E:ys=(a+3)::xs) by (eapply run_functional; [exact H|apply (run_P 3)]).
    subst ys; replace (a+3) with (1+(1+(1+a))) by lia; rewrite !RC_P; reflexivity.
Qed.
Lemma macro_spec xs ys : Macro xs ys -> C xs -->+ C ys.
Proof.
  intro H; destruct H as [a xs ys H].
  assert (HX:xs<>[]).
  { destruct xs; [|discriminate]. destruct a; cbn[Ret Alt] in H;
      inversion H; match goal with H:LInc _ [] _ |- _ => inversion H end. }
  unfold Ret in H; apply run_app in H; destruct H as [mid [HA HP]].
  unfold C at 1; rewrite RC_cons by assumption; change (Active a xs -->+ C ys).
  eapply evstep_progress_trans; [apply active_run; exact HA|].
  apply run3_RC in HP; unfold Active,C; rewrite HP; apply retire.
Qed.
Lemma first_cut : c0 -->* C [1;1]%nat.
Proof. unfold C; cbn[RC]; unfold W; es. Qed.

Lemma infinite_nonhalt xs : InfiniteMacro xs -> ~halts tm (C xs).
Proof.
  intro HI; eapply progress_nonhalt with
    (P:=fun c => exists ys, InfiniteMacro ys /\ c=C ys).
  - intros c [ys [H ->]]; destruct H as [ys zs HM HI'].
    exists (C zs); split; [exists zs; auto|apply macro_spec; assumption].
  - exists xs; auto.
Qed.
Theorem nonhalt : ~halts tm c0.
Proof. eapply multistep_nonhalt; [apply first_cut|apply infinite_nonhalt,seed_infinite]. Qed.
End TM2.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB3RA2LB1LB1RB_2LA2RA4LA1LA---").
Definition swap_q q := match q with A => B | B => A end.
Definition swap_s s := match s with 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 end.

CoInductive Related : side -> side -> Prop :=
| related_hd l r : Streams.hd r=swap_s (Streams.hd l) ->
    Related (Streams.tl l) (Streams.tl r) -> Related l r.
Lemma related s l r : Related l r -> Related (s >> l) (swap_s s >> r).
Proof. intro H; constructor; [reflexivity|exact H]. Qed.
Inductive Conj : Q*tape -> Q*tape -> Prop :=
| conj q s l r l' r' : Related l r' -> Related r l' ->
    Conj (q;; l {{s}} r) (swap_q q;; l' {{swap_s s}} r').

Lemma swap_transition q s s' d q' : tm (q,s)=Some(s',d,q') ->
  TM2.tm (swap_q q,swap_s s)=Some(swap_s s',flip_dir d,swap_q q').
Proof. destruct q,s; cbn; intro H; inversion H; reflexivity. Qed.

Lemma conj_step c d : c -[tm]-> d -> forall c', Conj c c' ->
  exists d', c' -[TM2.tm]-> d' /\ Conj d d'.
Proof.
  intro H; destruct H; intros c' HC; inversion HC; subst;
    destruct l as [x l], r as [y r];
    repeat match goal with H:Related (Cons _ _) ?z |- _ =>
      destruct z; inversion H; cbn[Streams.hd Streams.tl] in *; subst; clear H end;
    eexists; split.
  - eapply step_right; exact (@swap_transition q s s' L q' H).
  - constructor; eauto using related.
  - eapply step_left; exact (@swap_transition q s s' R q' H).
  - constructor; eauto using related.
Qed.
Lemma conj_halted c c' : Conj c c' -> halted tm c -> halted TM2.tm c'.
Proof. intros H; destruct H; destruct q,s; cbn; congruence. Qed.
Lemma conj_multistep n c d : c -[tm]->> n / d -> forall c', Conj c c' ->
  exists d', c' -[TM2.tm]->> n / d' /\ Conj d d'.
Proof.
  intro H; induction H; intros start HC.
  - exists start; split; [constructor|assumption].
  - destruct (@conj_step _ _ H _ HC) as [mid [HS HC']].
    destruct (IHmultistep _ HC') as [last [HM HC'']].
    exists last; split; [econstructor; eassumption|assumption].
Qed.
Lemma conj_nonhalt c c' : Conj c c' -> ~halts TM2.tm c' -> ~halts tm c.
Proof.
  intros HC HN [n [d [HM HH]]].
  destruct (@conj_multistep _ _ _ HM _ HC) as [d' [HM' HC']].
  apply HN; exists n,d'; split; [exact HM'|eapply conj_halted; eassumption].
Qed.
Lemma related_blank : Related 0inf 0inf.
Proof. cofix H; constructor; [reflexivity|exact H]. Qed.

Definition cut := 0inf <* <[3;1;2;3] <{{B}} [2] *> 0inf.
Lemma first_cut : c0 -[tm]->* cut.
Proof. unfold cut; es. Qed.
Lemma cut_conj : Conj cut (TM2.C [1;1]%nat).
Proof.
  unfold cut,TM2.C,TM2.RC,TM2.W; cbn; constructor;
    [do 3 apply related; apply related_blank|apply related; apply related_blank].
Qed.
Theorem nonhalt : ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply first_cut|].
  eapply conj_nonhalt; [apply cut_conj|apply TM2.infinite_nonhalt,seed_infinite].
Qed.
End TM1.
