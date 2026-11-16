From BusyCoq Require Import Individual62 Longitudinal BinaryCounter_v2 DivModCases.
Require Import ZifyNat Lia PeanoNat String List.

Module Dynamics7a.

Open Scope nat.

Definition half (n:nat) : nat := ((n-1)/2)%nat.

Lemma half_odd q: half (1+q*2)=q.
Proof.
  unfold half.
  replace (1+q*2-1) with (q*2) by lia.
  rewrite Nat.div_mul by lia.
  reflexivity.
Qed.

Lemma half_even_pos q: half ((S q)*2)=q.
Proof.
  unfold half.
  replace (S q*2-1) with (q*2+1) by lia.
  rewrite Nat.div_add_l by lia.
  change (1/2)%nat with 0%nat.
  lia.
Qed.

Lemma half_decomp n:
  1 <= n -> exists q, (n=1+q*2 \/ n=(S q)*2) /\ half n=q.
Proof.
  intros Hn.
  destruct (mod2 n); subst n.
  - destruct a.
    + lia.
    + exists a. split; [right; lia|apply half_even_pos].
  - exists a. split; [left; lia|apply half_odd].
Qed.

Lemma half_single_bound a b:
  1 <= b -> half b <= half (a+b+2).
Proof.
  intros Hb.
  destruct (half_decomp b Hb) as [qb [[Eb|Eb] Hbq]];
  destruct (half_decomp (a+b+2) ltac:(lia)) as [qy [[Ey|Ey] Hyq]];
  subst; lia.
Qed.

Lemma half_pair_bound b0 a1 b1:
  1 <= b0 -> 1 <= b1 -> b0 <= a1 ->
  half b0 + half b1 <= half (a1+b1+2).
Proof.
  intros Hb0 Hb1 Hle.
  destruct (half_decomp b0 Hb0) as [q0 [[E0|E0] H0]];
  destruct (half_decomp b1 Hb1) as [q1 [[E1|E1] H1]];
  destruct (half_decomp (a1+b1+2) ltac:(lia)) as [qy [[Ey|Ey] Hy]];
  subst; lia.
Qed.

Fixpoint score (x:list nat) : nat :=
match x with
| _::b::xs => half b + score xs
| _ => 0
end.

Fixpoint pair_sum (x:list nat) : list nat :=
match x with
| a::b::xs => (a+b+2)::pair_sum xs
| _ => []
end.

Inductive sorted_from: nat -> list nat -> Prop :=
| sorted_nil lo: sorted_from lo []
| sorted_cons lo a xs: lo <= a -> sorted_from a xs -> sorted_from lo (a::xs).

Inductive even_len: list nat -> Prop :=
| even_len_nil: even_len []
| even_len_cons a b xs: even_len xs -> even_len (a::b::xs).

Inductive odd_pos: list nat -> Prop :=
| odd_pos_nil: odd_pos []
| odd_pos_cons a b xs: 1 <= b -> odd_pos xs -> odd_pos (a::b::xs).

Definition WF x := sorted_from 0 x /\ even_len x /\ odd_pos x.

Lemma sorted_from_weaken lo lo' xs:
  lo <= lo' -> sorted_from lo' xs -> sorted_from lo xs.
Proof.
  intros Hle Hs.
  induction Hs; constructor; auto; lia.
Qed.

Lemma pair_sum_sorted_from lo x:
  sorted_from lo x -> odd_pos x -> sorted_from (2*lo+2) (pair_sum x).
Proof.
  intros Hs Ho. revert lo Hs.
  induction Ho; intros lo Hs.
  - constructor.
  - inversion Hs; subst; clear Hs.
    match goal with Hs: sorted_from a (b::xs) |- _ =>
      inversion Hs; subst; clear Hs
    end.
    cbn.
    constructor.
    + lia.
    + eapply sorted_from_weaken.
      2: eapply IHHo; eauto.
      lia.
Qed.

Lemma pair_sum_sorted x:
  WF x -> sorted_from 2 (pair_sum x).
Proof.
  intros [Hs [_ Ho]].
  eapply sorted_from_weaken.
  2: eapply pair_sum_sorted_from; eauto.
  lia.
Qed.

Lemma sorted_2s_tail lo k ys:
  lo <= 2 -> sorted_from 2 ys -> sorted_from lo ([2%nat]^^k ++ ys).
Proof.
  intros Hlo Hys.
  revert lo Hlo.
  induction k.
  - intros lo Hlo. cbn. eapply sorted_from_weaken; eauto.
  - intros lo Hlo. cbn. constructor; [lia|]. apply IHk. lia.
Qed.

Lemma sorted_prefix00 k ys:
  sorted_from 2 ys -> sorted_from 0 ([2%nat]^^k ++ ys).
Proof. apply sorted_2s_tail; lia. Qed.

Lemma sorted_prefix01 k ys:
  sorted_from 2 ys -> sorted_from 0 (0%nat::[2%nat]^^k ++ ys).
Proof.
  intros H. cbn. constructor; [lia|]. eapply sorted_2s_tail; eauto; lia.
Qed.

Lemma sorted_prefix10 k ys:
  sorted_from 2 ys -> sorted_from 0 (1%nat::[2%nat]^^k ++ ys).
Proof.
  intros H. cbn. constructor; [lia|]. eapply sorted_2s_tail; eauto; lia.
Qed.

Lemma sorted_prefix11 k ys:
  sorted_from 2 ys -> sorted_from 0 (0%nat::1%nat::[2%nat]^^k ++ ys).
Proof.
  intros H. cbn. constructor; [lia|]. constructor; [lia|]. eapply sorted_2s_tail; eauto; lia.
Qed.

Lemma even_len_of_length xs k:
  length xs = k*2 -> even_len xs.
Proof.
  revert xs.
  induction k; intros xs H; destruct xs as [|a [|b xs]]; cbn in H; try lia.
  - constructor.
  - constructor. apply IHk. lia.
Qed.

Lemma even_len_length xs:
  even_len xs -> exists k, length xs = k*2.
Proof.
  induction 1.
  - exists 0. reflexivity.
  - destruct IHeven_len as [k Hk].
    exists (S k). cbn. lia.
Qed.

Lemma sorted_even_odd_pos lo xs:
  1 <= lo -> sorted_from lo xs -> even_len xs -> odd_pos xs.
Proof.
  intros Hlo Hs He. revert lo Hlo Hs.
  induction He.
  - intros. constructor.
  - intros lo Hlo Hs.
    inversion Hs; subst; clear Hs.
    match goal with Hs: sorted_from a (b::xs) |- _ =>
      inversion Hs; subst; clear Hs
    end.
    constructor; [lia|].
    eapply (IHHe b).
    + lia.
    + eauto.
Qed.

Lemma odd_pos_0_cons xs:
  sorted_from 1 xs -> even_len (0%nat::xs) -> odd_pos (0%nat::xs).
Proof.
  intros Hs He.
  destruct xs as [|b xs].
  - inversion He.
  - inversion He; subst; clear He.
    inversion Hs; subst; clear Hs.
    constructor; [lia|].
    eapply sorted_even_odd_pos; eauto; lia.
Qed.

Lemma WF_prefix00 k ys:
  sorted_from 2 ys -> even_len ([2%nat]^^k ++ ys) -> WF ([2%nat]^^k ++ ys).
Proof.
  intros Hs He.
  repeat split.
  - apply sorted_prefix00; auto.
  - exact He.
  - eapply (sorted_even_odd_pos 1).
    + lia.
    + apply sorted_2s_tail; auto; lia.
    + exact He.
Qed.

Lemma WF_prefix01 k ys:
  sorted_from 2 ys -> even_len (0%nat::[2%nat]^^k ++ ys) -> WF (0%nat::[2%nat]^^k ++ ys).
Proof.
  intros Hs He.
  repeat split.
  - apply sorted_prefix01; auto.
  - exact He.
  - apply odd_pos_0_cons.
    + apply sorted_2s_tail; auto; lia.
    + exact He.
Qed.

Lemma WF_prefix10 k ys:
  sorted_from 2 ys -> even_len (1%nat::[2%nat]^^k ++ ys) -> WF (1%nat::[2%nat]^^k ++ ys).
Proof.
  intros Hs He.
  repeat split.
  - apply sorted_prefix10; auto.
  - exact He.
  - eapply (sorted_even_odd_pos 1).
    + lia.
    + cbn. constructor; [lia|]. apply sorted_2s_tail; auto; lia.
    + exact He.
Qed.

Lemma WF_prefix11 k ys:
  sorted_from 2 ys -> even_len (0%nat::1%nat::[2%nat]^^k ++ ys) -> WF (0%nat::1%nat::[2%nat]^^k ++ ys).
Proof.
  intros Hs He.
  repeat split.
  - apply sorted_prefix11; auto.
  - exact He.
  - apply odd_pos_0_cons.
    + constructor; [lia|]. apply sorted_2s_tail; auto; lia.
    + exact He.
Qed.

Lemma WF_tail2 a b xs:
  WF (a::b::xs) -> WF xs.
Proof.
  intros [Hs [He Ho]].
  inversion Hs as [|lo0 a0 xs0 Hlo Htail]; subst; clear Hs.
  inversion Htail as [|lo1 b0 xs1 Hab Hxs]; subst; clear Htail.
  inversion He; subst; clear He.
  inversion Ho; subst; clear Ho.
  repeat split.
  - eapply (sorted_from_weaken 0 b); [lia|exact Hxs].
  - assumption.
  - assumption.
Qed.

Lemma score_pair_sum_even_len n x:
  length x <= n -> WF x -> even_len (pair_sum x) -> score x <= score (pair_sum x).
Proof.
  revert x.
  induction n as [|n IH]; intros x Hlen HWF Heps.
  - destruct x; cbn in *; try lia.
  - destruct x as [|a [|b [|c [|d xs]]]]; cbn in *.
    + lia.
    + destruct HWF as [_ [He _]].
      destruct (even_len_length _ He) as [k Hk]. cbn in Hk. lia.
    + inversion Heps.
    + destruct HWF as [_ [He _]].
      destruct (even_len_length _ He) as [k Hk]. cbn in Hk. lia.
    + assert (Htail: WF xs).
      { apply WF_tail2 in HWF. apply WF_tail2 in HWF. exact HWF. }
      assert (He_tail: even_len (pair_sum xs)).
      { inversion Heps; subst; assumption. }
      pose proof (IH xs ltac:(cbn in Hlen; lia) Htail He_tail) as Hrec.
      destruct HWF as [Hs [He Ho]].
      inversion Hs as [|lo0 a0 xs0 Ha Hsb]; subst; clear Hs.
      inversion Hsb as [|lo1 b0 xs1 Hb Hsc]; subst; clear Hsb.
      inversion Hsc as [|lo2 c0 xs2 Hc Hsd]; subst; clear Hsc.
      inversion Ho as [|a0' b0' xs0' Hbpos Hox]; subst; clear Ho.
      inversion Hox as [|c0' d0' xs1' Hdpos Hoxs]; subst; clear Hox.
      cbn.
      pose proof (half_pair_bound b c d Hbpos Hdpos Hc) as Hbd.
      change (half b + (half d + score xs) <= half (c + d + 2) + score (pair_sum xs)).
      rewrite Nat.add_assoc.
      apply Nat.add_le_mono.
      * exact Hbd.
      * exact Hrec.
Qed.

Lemma score_pair_sum_even x:
  WF x -> even_len (pair_sum x) -> score x <= score (pair_sum x).
Proof.
  eapply score_pair_sum_even_len; [reflexivity|..].
Qed.

Lemma score_pair_sum_odd x:
  WF x -> even_len (0::pair_sum x) -> score x <= score (0::pair_sum x).
Proof.
  destruct x as [|a [|b [|c xs]]]; intros HWF Heps; cbn in *.
  - inversion Heps.
  - destruct HWF as [_ [He _]].
    destruct (even_len_length _ He) as [k Hk]. cbn in Hk. lia.
  - destruct HWF as [Hs [He Ho]].
    repeat match goal with
    | H: sorted_from _ (_::_) |- _ => inversion H; subst; clear H
    | H: odd_pos (_::_::_) |- _ => inversion H; subst; clear H
    end.
    cbn.
    pose proof (half_single_bound a b ltac:(lia)) as Hab.
    change (half b + 0 <= half (a + b + 2) + 0).
    lia.
  - assert (Htail: WF (c::xs)).
    { apply WF_tail2 in HWF. exact HWF. }
    assert (He_tail: even_len (pair_sum (c::xs))).
    { inversion Heps; subst; assumption. }
    pose proof (score_pair_sum_even _ Htail He_tail) as Hrec.
    destruct HWF as [Hs [He Ho]].
    repeat match goal with
    | H: sorted_from _ (_::_) |- _ => inversion H; subst; clear H
    | H: odd_pos (_::_::_) |- _ => inversion H; subst; clear H
    end.
    cbn.
    pose proof (half_single_bound a b ltac:(lia)) as Hab.
    apply Nat.add_le_mono.
    + exact Hab.
    + exact Hrec.
Qed.

Lemma score_twos_even a ys:
  score ([2%nat]^^(a*2) ++ ys) = score ys.
Proof.
  induction a.
  - cbn. reflexivity.
  - replace (S a*2) with (2+a*2) by lia.
    rewrite lpow_add.
    cbn.
    rewrite IHa.
    reflexivity.
Qed.

Lemma score_twos_odd a ys:
  score ([2%nat]^^(1+a*2) ++ ys) = score (0%nat::ys).
Proof.
  induction a.
  - cbn. destruct ys; reflexivity.
  - replace (1+S a*2) with (2+(1+a*2)) by lia.
    rewrite lpow_add.
    cbn.
    change (score ([2%nat]^^(1+a*2) ++ ys) = score (0%nat::ys)).
    exact IHa.
Qed.

Lemma even_len_twos_even a ys:
  even_len ([2%nat]^^(a*2) ++ ys) -> even_len ys.
Proof.
  intros He.
  destruct (even_len_length _ He) as [q Hq].
  apply (even_len_of_length ys (q-a)).
  rewrite length_app in Hq.
  rewrite lpow_length in Hq.
  cbn in Hq.
  lia.
Qed.

Lemma even_len_twos_odd a ys:
  even_len ([2%nat]^^(1+a*2) ++ ys) -> even_len (0%nat::ys).
Proof.
  intros He.
  destruct (even_len_length _ He) as [q Hq].
  apply (even_len_of_length (0%nat::ys) (q-a)).
  rewrite length_app in Hq.
  rewrite lpow_length in Hq.
  cbn in Hq.
  cbn.
  lia.
Qed.

Lemma score_prefix00_growth k x:
  WF x -> even_len ([2%nat]^^k ++ pair_sum x) ->
  score x <= score ([2%nat]^^k ++ pair_sum x).
Proof.
  intros HWF He.
  destruct (mod2 k); subst k.
  - rewrite score_twos_even.
    apply score_pair_sum_even; auto.
    eapply even_len_twos_even; eauto.
  - rewrite score_twos_odd.
    apply score_pair_sum_odd; auto.
    eapply even_len_twos_odd; eauto.
Qed.

Lemma score_cons_change a b xs:
  score (a::xs) = score (b::xs).
Proof.
  destruct xs; reflexivity.
Qed.

Lemma even_len_cons_change a b xs:
  even_len (a::xs) -> even_len (b::xs).
Proof.
  destruct xs as [|c xs]; intro He.
  - inversion He.
  - inversion He; subst. constructor; assumption.
Qed.

Lemma score_zero_twos_even a ys:
  score (0%nat::[2%nat]^^(a*2) ++ ys) = score (0%nat::ys).
Proof.
  induction a.
  - cbn. reflexivity.
  - replace (S a*2) with (2+a*2) by lia.
    rewrite lpow_add.
    cbn.
    change (score (2%nat::[2%nat]^^(a*2) ++ ys) = score (0%nat::ys)).
    rewrite score_cons_change with (b:=0%nat).
    exact IHa.
Qed.

Lemma score_zero_twos_odd a ys:
  score (0%nat::[2%nat]^^(1+a*2) ++ ys) = score ys.
Proof.
  induction a.
  - cbn. reflexivity.
  - replace (1+S a*2) with (2+(1+a*2)) by lia.
    rewrite lpow_add.
    cbn.
    change (score (2%nat::[2%nat]^^(1+a*2) ++ ys) = score ys).
    rewrite score_cons_change with (b:=0%nat).
    exact IHa.
Qed.

Lemma even_len_zero_twos_even a ys:
  even_len (0%nat::[2%nat]^^(a*2) ++ ys) -> even_len (0%nat::ys).
Proof.
  intros He.
  destruct (even_len_length _ He) as [q Hq].
  apply (even_len_of_length (0%nat::ys) (q-a)).
  cbn in Hq.
  rewrite length_app in Hq.
  rewrite lpow_length in Hq.
  cbn in Hq.
  cbn.
  lia.
Qed.

Lemma even_len_zero_twos_odd a ys:
  even_len (0%nat::[2%nat]^^(1+a*2) ++ ys) -> even_len ys.
Proof.
  intros He.
  destruct (even_len_length _ He) as [q Hq].
  apply (even_len_of_length ys (q-a-1)).
  cbn in Hq.
  rewrite length_app in Hq.
  rewrite lpow_length in Hq.
  cbn in Hq.
  lia.
Qed.

Lemma score_prefix01_growth k x:
  WF x -> even_len (0%nat::[2%nat]^^k ++ pair_sum x) ->
  score x <= score (0%nat::[2%nat]^^k ++ pair_sum x).
Proof.
  intros HWF He.
  destruct (mod2 k); subst k.
  - rewrite score_zero_twos_even.
    apply score_pair_sum_odd; auto.
    eapply even_len_zero_twos_even; eauto.
  - rewrite score_zero_twos_odd.
    apply score_pair_sum_even; auto.
    eapply even_len_zero_twos_odd; eauto.
Qed.

Lemma score_prefix10_growth k x:
  WF x -> even_len (1%nat::[2%nat]^^k ++ pair_sum x) ->
  score x <= score (1%nat::[2%nat]^^k ++ pair_sum x).
Proof.
  intros HWF He.
  rewrite score_cons_change with (b:=0%nat).
  apply score_prefix01_growth; auto.
  eapply even_len_cons_change; eauto.
Qed.

Lemma score_prefix11_growth k x:
  WF x -> even_len (0%nat::1%nat::[2%nat]^^k ++ pair_sum x) ->
  score x <= score (0%nat::1%nat::[2%nat]^^k ++ pair_sum x).
Proof.
  intros HWF He.
  cbn.
  change (score x <= score ([2%nat]^^k ++ pair_sum x)).
  apply score_prefix00_growth; auto.
  inversion He; subst.
  assumption.
Qed.

End Dynamics7a.

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB---_0LC0LF_1RD0LB_1RE0RC_0RF1RA_1LB0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation hL := (F,[]).
Notation hR := (C,[]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Notation LD := (list (nat*nat)).
Notation LD' := (list (nat)).

Fixpoint LC0(x:LD):side :=
match x with
| [] => 0inf
| (x0,x1)::x2 => LC0 x2 <* <[1;1;1;0]^^x0 <* <[1;0]^^x1 <* <[1;1;0;0]
end.

Fixpoint LC1(x:LD'):side :=
match x with
| [] => 0inf
| (x1)::x2 => LC1 x2 <* <[1;0]^^x1 <* <[1;1;0;0]
end.

Fixpoint L_empty(x:LD):LD' :=
match x with
| [] => []
| (x0,x1)::x2 => (x0*2+x1)::L_empty x2
end.

Fixpoint L_rest(x:LD):nat :=
match x with
| [] => O
| (x0,x1)::x2 => x0 + L_rest x2
end.

Lemma L_empty_spec x:
  sideRLs tm' (hLR^^(L_rest x)) (LC0 x) (LC1 (L_empty x)).
Proof.
  induction x as [|[x0 x1] x].
  1: esx.
  cbn - [Str_app].
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: rewrite <-Str_app_assoc.
  2: eapply segRLs_sideRLs_concat.
  3: apply IHx.
  2: eapply segRLs_wall.
  2: solve_seg.
  2: solve_seg.
  clear.
  gen x1.
  induction x0; intros.
  1: esx.
  replace (S x0) with (1+x0) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (IHx0 (2+x1)); flia.
  esx.
Qed.

Notation "l |> r" := (l <* <[1;1;1] {{A}}> r) (at level 30).

Inductive LRst: LD'->LD->Prop :=
| LRst_0: LRst [] []
| LRst_1 a0 a1 x x':
  LRst x x' ->
  LRst ((a1)::(a0*2+1)::x) ((a0,a1+3)::x')
| LRst_2 a0 a1 x x':
  LRst x x' ->
  LRst ((a1)::(a0*2+2)::x) ((a0,a1+4)::x')
.

Lemma LRst_spec x x':
  LRst x x' ->
  forall r,
  LC1 x {{{ (hL,L) }}} r -->+
  LC0 x' {{{ (hR,R) }}} [0;0;1] *> r.
Proof.
  intros I.
  induction I; cbn[LC0]; cbn[LC1]; intros.
  all: es; er; follow100 IHI; es.
Qed.

Definition RC0 a := [0;0;1;0]^^a *> 0inf.
Definition RC1 a b := [0;1;0;1;0;0;0;1]^^a *> [0;1;0;0;0;1] *> [1;0;0;0]^^b *> 0inf.
Definition RC2 a b := [0;1;0;1;0;0;0;1]^^a *> [0;1;0;0;0;1] *> [0;0;0;1]^^b *> 0inf.
Definition RC3 a b := [0;1;0;1;0;0;0;1]^^a *> [0;0;0;1]^^b *> 0inf.

Lemma RIncs1 a b:
  sideRLs tm (hRL^^(1+a)) (RC0 (1+a*2+b)) (RC1 a b).
Proof.
  unfold RC0,RC1.
  gen b.
  induction a; intros.
  1: esx.
  replace (1+S a) with (1+a+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHa (2+b)); flia.
  esx.
Qed.

Lemma RIncs2 a b:
  sideRLs tm (hRL^^b) (RC1 a 0) (RC2 a b).
Proof.
  unfold RC1,RC2.
  induction b.
  1: esx.
  replace (S b) with (b+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHb.
  esx.
Qed.

Lemma RIncs3 a b:
  sideRLs tm (hRL^^(1+b)) (RC1 a 1) (RC3 (1+a) (1+b)).
Proof.
  unfold RC1,RC3.
  induction b.
  1: esx.
  replace (1+S b) with (1+b+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHb.
  esx.
Qed.

Lemma RIncs1_1 a b:
  sideRLs tm (hRL^^(1+a+b)) (RC0 (a*2+1)) (RC2 a b).
Proof.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (RIncs1 a O); flia.
  apply RIncs2.
Qed.

Lemma RIncs1_2 a b:
  sideRLs tm (hRL^^(1+a+(1+b))) (RC0 (a*2+2)) (RC3 (1+a) (1+b)).
Proof.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (RIncs1 a 1); flia.
  apply RIncs3.
Qed.

Lemma LC1_app a n x:
  LC1 ([a]^^n++x) = LC1 x <* (<[1;0]^^a <+ <[1;1;0;0])^^n.
Proof.
  induction n.
  1: reflexivity.
  cbn.
  rewrite IHn.
  simpl_tape.
  reflexivity.
Qed.

Lemma Rst3_0 x a b:
  LC1 x {{{ (hR,R) }}} RC3 a b -->*
  LC1 ([2]^^a++x) {{{ (hR,R) }}} RC3 0 b.
Proof.
  unfold RC3.
  rewrite LC1_app.
  st.
  sr.
  finish.
Qed.

Lemma Rst3_1 x a b:
  LC1 x {{{ (hR,R) }}} RC3 a (1+b) -->*
  LC1 (O::[2]^^a++x) {{{ (hR,R) }}} RC3 0 b.
Proof.
  unfold RC3.
  cbn[LC1].
  rewrite LC1_app.
  es.
Qed.

Lemma Rst2_0 x a b:
  LC1 x {{{ (hR,R) }}} RC2 a b -->*
  LC1 ((1%nat)::[2]^^a++x) {{{ (hR,R) }}} RC3 0 b.
Proof.
  unfold RC3,RC2.
  cbn[LC1].
  rewrite LC1_app.
  es.
Qed.

Lemma Rst2_1 x a b:
  LC1 x {{{ (hR,R) }}} RC2 a (1+b) -->*
  LC1 (O::(1%nat)::[2]^^a++x) {{{ (hR,R) }}} RC3 0 b.
Proof.
  unfold RC3,RC2.
  cbn[LC1].
  rewrite LC1_app.
  es.
Qed.

Definition S0 '(x,n) := LC1 x {{{ (hR,R) }}} RC3 0 n.

Lemma Rst x n x':
  LRst x x' ->
  S0 (x,n) -->+
  LC0 x' {{{ (hR,R) }}} RC0 (2+n).
Proof.
  unfold S0,RC3,RC0.
  intros I.
  eapply LRst_spec in I.
  es; er.
  follow100 I.
  es.
Qed.

Lemma BigStep00 x n x':
  LRst x x' ->
  n+2 <= L_rest x' ->
  S0 (x,n*2) -->+
  S0 ([2]^^(1+n)++L_empty x',L_rest x'-n-1).
Proof.
  intros I I0.
  unfold S0.
  eapply Rst in I.
  follow10 I. clear I.
  epose proof (RIncs1_2 n (L_rest x'-n-2)) as HR.
  replace (1+n+(1+(L_rest x'-n-2))) with (L_rest x') in HR by lia.
  replace (n*2+2) with (2+n*2) in HR by lia.
  epose proof (sideRLs_concat_1 HR (L_empty_spec _)) as I1.
  follow I1.
  follow Rst3_0.
  finish.
Qed.

Lemma BigStep01 x n x':
  LRst x x' ->
  n+2 <= L_rest x' ->
  S0 (x,n*2) -->+
  S0 (O::[2]^^(1+n)++L_empty x',L_rest x'-n-2).
Proof.
  intros I I0.
  unfold S0.
  eapply Rst in I.
  follow10 I. clear I.
  epose proof (RIncs1_2 n (L_rest x'-n-2)) as HR.
  replace (1+n+(1+(L_rest x'-n-2))) with (L_rest x') in HR by lia.
  replace (n*2+2) with (2+n*2) in HR by lia.
  epose proof (sideRLs_concat_1 HR (L_empty_spec _)) as I1.
  follow I1.
  follow Rst3_1.
  finish.
Qed.

Lemma BigStep10 x n x':
  LRst x x' ->
  n+2 <= L_rest x' ->
  S0 (x,n*2+1) -->+
  S0 ((1%nat)::[2]^^(1+n)++L_empty x',L_rest x'-n-2).
Proof.
  intros I I0.
  unfold S0.
  eapply Rst in I.
  follow10 I. clear I.
  epose proof (RIncs1_1 (1+n) (L_rest x'-n-2)) as HR.
  replace (1+(1+n)+(L_rest x'-n-2)) with (L_rest x') in HR by lia.
  replace ((1+n)*2+1) with (2+(n*2+1)) in HR by lia.
  epose proof (sideRLs_concat_1 HR (L_empty_spec _)) as I1.
  follow I1.
  follow Rst2_0.
  finish.
Qed.

Lemma BigStep11 x n x':
  LRst x x' ->
  n+3 <= L_rest x' ->
  S0 (x,n*2+1) -->+
  S0 (O::(1%nat)::[2]^^(1+n)++L_empty x',L_rest x'-n-3).
Proof.
  intros I I0.
  unfold S0.
  eapply Rst in I.
  follow10 I. clear I.
  epose proof (RIncs1_1 (1+n) (1+(L_rest x'-n-3))) as HR.
  replace (1+(1+n)+(1+(L_rest x'-n-3))) with (L_rest x') in HR by lia.
  replace ((1+n)*2+1) with (2+(n*2+1)) in HR by lia.
  epose proof (sideRLs_concat_1 HR (L_empty_spec _)) as I1.
  follow I1.
  follow Rst2_1.
  finish.
Qed.

Lemma init:
  c0 -->*
  S0 ([2;5],O).
Proof.
  unfold S0.
  esx.
Qed.

Import Dynamics7a.
Open Scope nat.

Definition good (i:LD' * nat) : Prop :=
match i with
| (x,n) => exists x', LRst x x' /\ WF x /\ 5 <= L_rest x' /\ n < L_rest x'
end.

Lemma LRst_score x x':
  LRst x x' -> L_rest x' = score x.
Proof.
  induction 1; cbn - [half].
  - reflexivity.
  - rewrite IHLRst.
    replace (a0*2+1) with (1+a0*2) by lia.
    rewrite half_odd.
    lia.
  - rewrite IHLRst.
    replace (a0*2+2) with ((S a0)*2) by lia.
    rewrite half_even_pos.
    lia.
Qed.

Lemma LRst_pair_sum x x':
  LRst x x' -> L_empty x' = pair_sum x.
Proof.
  induction 1; cbn.
  - reflexivity.
  - rewrite IHLRst. f_equal. lia.
  - rewrite IHLRst. f_equal. lia.
Qed.

Lemma LRst_exists x:
  even_len x -> odd_pos x -> exists x', LRst x x'.
Proof.
  intros He Ho.
  induction He as [|u v xs He IH].
  - exists ([]:LD). constructor.
  - inversion Ho as [|u' v' xs' Hv Hox]; subst; clear Ho.
    destruct (IH Hox) as [x' Hx'].
    destruct (mod2 v) as [q|q]; subst v.
    + destruct q as [|q].
      * lia.
      * replace (S q*2) with (q*2+2) by lia.
        exists ((q,u+4)::x'). apply LRst_2. exact Hx'.
    + replace (1+q*2) with (q*2+1) by lia.
      exists ((q,u+3)::x'). apply LRst_1. exact Hx'.
Qed.

Lemma init2:
  c0 -->* S0 ([0;1;2;13],1).
Proof.
  assert (H1: S0 ([2;5],O) -->+ S0 ([2;9],1)).
  { change (S0 ([2;5],0*2) -->+
      S0 ([2]^^(1+0) ++ L_empty [(2,5)],L_rest [(2,5)]-0-1)).
    eapply BigStep00.
    - exact (LRst_1 2 2 [] [] LRst_0).
    - cbn. lia. }
  assert (H2: S0 ([2;9],1) -->+ S0 ([0;1;2;13],1)).
  { change (S0 ([2;9],0*2+1) -->+
      S0 (O::(1%nat)::[2]^^(1+0) ++ L_empty [(4,5)],L_rest [(4,5)]-0-3)).
    eapply BigStep11.
    - exact (LRst_1 4 2 [] [] LRst_0).
    - cbn. lia. }
  eapply evstep_trans.
  - apply init.
  - eapply evstep_trans.
    + apply progress_evstep. exact H1.
    + apply progress_evstep. exact H2.
Qed.

Lemma good_progress i:
  good i -> exists i', S0 i -->+ S0 i' /\ good i'.
Proof.
  destruct i as [x n].
  intros [x' [HLR [HWF [Hge Hn]]]].
  pose proof (LRst_score _ _ HLR) as Hscore.
  pose proof (LRst_pair_sum _ _ HLR) as Hempty.
  assert (Hsorted: sorted_from 2 (L_empty x')).
  { rewrite Hempty. apply pair_sum_sorted. exact HWF. }
  destruct (mod2 n) as [a|a]; subst n.
  - set (base := [2%nat]^^(1+a) ++ L_empty x').
    destruct (mod2 (length base)) as [q Hlenbase|q Hlenbase].
    + exists (base,L_rest x'-a-1). split.
      * subst base. eapply BigStep00; [exact HLR|lia].
      * assert (He: even_len base).
        { apply (even_len_of_length base q). exact Hlenbase. }
        assert (HWFnext: WF base).
        { subst base. apply WF_prefix00; assumption. }
        destruct HWFnext as [Hsnext [Henext Honext]].
        destruct (LRst_exists _ Henext Honext) as [znext Hznext].
        exists znext.
        split; [exact Hznext|].
        split; [repeat split; assumption|].
        split.
        -- subst base.
           pose proof (LRst_score _ _ Hznext) as Hzscore.
           pose proof (score_prefix00_growth (1+a) x HWF) as Hgrow.
           rewrite <- Hempty in Hgrow.
           specialize (Hgrow Henext).
           rewrite Hzscore. lia.
        -- subst base.
           pose proof (LRst_score _ _ Hznext) as Hzscore.
           pose proof (score_prefix00_growth (1+a) x HWF) as Hgrow.
           rewrite <- Hempty in Hgrow.
           specialize (Hgrow Henext).
           rewrite Hzscore. lia.
    + exists (0%nat::base,L_rest x'-a-2). split.
      * subst base. eapply BigStep01; [exact HLR|lia].
      * assert (He: even_len (0%nat::base)).
        { apply (even_len_of_length (0%nat::base) (S q)).
          change (S (length base) = S q*2).
          rewrite Hlenbase. lia. }
        assert (HWFnext: WF (0%nat::base)).
        { subst base. apply WF_prefix01; assumption. }
        destruct HWFnext as [Hsnext [Henext Honext]].
        destruct (LRst_exists _ Henext Honext) as [znext Hznext].
        exists znext.
        split; [exact Hznext|].
        split; [repeat split; assumption|].
        split.
        -- subst base.
           pose proof (LRst_score _ _ Hznext) as Hzscore.
           pose proof (score_prefix01_growth (1+a) x HWF) as Hgrow.
           rewrite <- Hempty in Hgrow.
           specialize (Hgrow Henext).
           rewrite Hzscore. lia.
        -- subst base.
           pose proof (LRst_score _ _ Hznext) as Hzscore.
           pose proof (score_prefix01_growth (1+a) x HWF) as Hgrow.
           rewrite <- Hempty in Hgrow.
           specialize (Hgrow Henext).
           rewrite Hzscore. lia.
  - set (base := 1%nat::[2%nat]^^(1+a) ++ L_empty x').
    destruct (mod2 (length base)) as [q Hlenbase|q Hlenbase].
    + exists (base,L_rest x'-a-2). split.
      * subst base.
        replace (1+a*2) with (a*2+1) by lia.
        eapply BigStep10; [exact HLR|lia].
      * assert (He: even_len base).
        { apply (even_len_of_length base q). exact Hlenbase. }
        assert (HWFnext: WF base).
        { subst base. apply WF_prefix10; assumption. }
        destruct HWFnext as [Hsnext [Henext Honext]].
        destruct (LRst_exists _ Henext Honext) as [znext Hznext].
        exists znext.
        split; [exact Hznext|].
        split; [repeat split; assumption|].
        split.
        -- subst base.
           pose proof (LRst_score _ _ Hznext) as Hzscore.
           pose proof (score_prefix10_growth (1+a) x HWF) as Hgrow.
           rewrite <- Hempty in Hgrow.
           specialize (Hgrow Henext).
           rewrite Hzscore. lia.
        -- subst base.
           pose proof (LRst_score _ _ Hznext) as Hzscore.
           pose proof (score_prefix10_growth (1+a) x HWF) as Hgrow.
           rewrite <- Hempty in Hgrow.
           specialize (Hgrow Henext).
           rewrite Hzscore. lia.
    + exists (0%nat::base,L_rest x'-a-3). split.
      * subst base.
        replace (1+a*2) with (a*2+1) by lia.
        eapply BigStep11; [exact HLR|lia].
      * assert (He: even_len (0%nat::base)).
        { apply (even_len_of_length (0%nat::base) (S q)).
          change (S (length base) = S q*2).
          rewrite Hlenbase. lia. }
        assert (HWFnext: WF (0%nat::base)).
        { subst base. apply WF_prefix11; assumption. }
        destruct HWFnext as [Hsnext [Henext Honext]].
        destruct (LRst_exists _ Henext Honext) as [znext Hznext].
        exists znext.
        split; [exact Hznext|].
        split; [repeat split; assumption|].
        split.
        -- subst base.
           pose proof (LRst_score _ _ Hznext) as Hzscore.
           pose proof (score_prefix11_growth (1+a) x HWF) as Hgrow.
           rewrite <- Hempty in Hgrow.
           specialize (Hgrow Henext).
           rewrite Hzscore. lia.
        -- subst base.
           pose proof (LRst_score _ _ Hznext) as Hzscore.
           pose proof (score_prefix11_growth (1+a) x HWF) as Hgrow.
           rewrite <- Hempty in Hgrow.
           specialize (Hgrow Henext).
           rewrite Hzscore. lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init2.
  eapply progress_nonhalt_cond with
    (A:=(LD' * nat)%type)
    (C:=fun i => S0 i)
    (P:=good).
  - apply good_progress.
  - exists [(0,3);(6,5)].
    split; [exact (LRst_1 0 0 [2;13] [(6,5)] (LRst_1 6 2 [] [] LRst_0))|].
    split.
    + repeat split.
      * repeat constructor; lia.
      * repeat constructor.
      * repeat constructor; lia.
    + split; cbn; lia.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1LB0RC_0LC0LA_1RD0LB_1RE0RC_0RA1RF_1RB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation hL := (A,[]).
Notation hR := (C,[]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Notation LD := (list (nat*nat)).
Notation LD' := (list (nat)).

Fixpoint LC0(x:LD):side :=
match x with
| [] => 0inf
| (x0,x1)::x2 => LC0 x2 <* <[1;1;1;0]^^x0 <* <[1;0]^^x1 <* <[1;1;0;0]
end.

Fixpoint LC1(x:LD'):side :=
match x with
| [] => 0inf
| (x1)::x2 => LC1 x2 <* <[1;0]^^x1 <* <[1;1;0;0]
end.

Fixpoint L_empty(x:LD):LD' :=
match x with
| [] => []
| (x0,x1)::x2 => (x0*2+x1)::L_empty x2
end.

Fixpoint L_rest(x:LD):nat :=
match x with
| [] => O
| (x0,x1)::x2 => x0 + L_rest x2
end.

Lemma L_empty_spec x:
  sideRLs tm' (hLR^^(L_rest x)) (LC0 x) (LC1 (L_empty x)).
Proof.
  induction x as [|[x0 x1] x].
  1: esx.
  cbn - [Str_app].
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: rewrite <-Str_app_assoc.
  2: eapply segRLs_sideRLs_concat.
  3: apply IHx.
  2: eapply segRLs_wall.
  2: solve_seg.
  2: solve_seg.
  clear.
  gen x1.
  induction x0; intros.
  1: esx.
  replace (S x0) with (1+x0) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (IHx0 (2+x1)); flia.
  esx.
Qed.

Notation "l |> r" := (l <* <[1;1;1] {{A}}> r) (at level 30).

Inductive LRst: LD'->LD->Prop :=
| LRst_0: LRst [] []
| LRst_1 a0 a1 x x':
  LRst x x' ->
  LRst ((a1)::(a0*2+1)::x) ((a0,a1+3)::x')
| LRst_2 a0 a1 x x':
  LRst x x' ->
  LRst ((a1)::(a0*2+2)::x) ((a0,a1+4)::x')
.

Lemma LRst_spec x x':
  LRst x x' ->
  forall r,
  LC1 x {{{ (hL,L) }}} r -->+
  LC0 x' {{{ (hR,R) }}} [0;0;1] *> r.
Proof.
  intros I.
  induction I; cbn[LC0]; cbn[LC1]; intros.
  all: es; er; follow100 IHI; es.
Qed.

Definition RC0 a := [0;0;1;0]^^a *> 0inf.
Definition RC1 a b := [0;1;0;1;0;0;0;1]^^a *> [0;1;0;0;0;1] *> [1;0;0;0]^^b *> 0inf.
Definition RC2 a b := [0;1;0;1;0;0;0;1]^^a *> [0;1;0;0;0;1] *> [0;0;0;1]^^b *> 0inf.
Definition RC3 a b := [0;1;0;1;0;0;0;1]^^a *> [0;0;0;1]^^b *> 0inf.

Lemma RIncs1 a b:
  sideRLs tm (hRL^^(1+a)) (RC0 (1+a*2+b)) (RC1 a b).
Proof.
  unfold RC0,RC1.
  gen b.
  induction a; intros.
  1: esx.
  replace (1+S a) with (1+a+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHa (2+b)); flia.
  esx.
Qed.

Lemma RIncs2 a b:
  sideRLs tm (hRL^^b) (RC1 a 0) (RC2 a b).
Proof.
  unfold RC1,RC2.
  induction b.
  1: esx.
  replace (S b) with (b+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHb.
  esx.
Qed.

Lemma RIncs3 a b:
  sideRLs tm (hRL^^(1+b)) (RC1 a 1) (RC3 (1+a) (1+b)).
Proof.
  unfold RC1,RC3.
  induction b.
  1: esx.
  replace (1+S b) with (1+b+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHb.
  esx.
Qed.

Lemma RIncs1_1 a b:
  sideRLs tm (hRL^^(1+a+b)) (RC0 (a*2+1)) (RC2 a b).
Proof.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (RIncs1 a O); flia.
  apply RIncs2.
Qed.

Lemma RIncs1_2 a b:
  sideRLs tm (hRL^^(1+a+(1+b))) (RC0 (a*2+2)) (RC3 (1+a) (1+b)).
Proof.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (RIncs1 a 1); flia.
  apply RIncs3.
Qed.

Lemma LC1_app a n x:
  LC1 ([a]^^n++x) = LC1 x <* (<[1;0]^^a <+ <[1;1;0;0])^^n.
Proof.
  induction n.
  1: reflexivity.
  cbn.
  rewrite IHn.
  simpl_tape.
  reflexivity.
Qed.

Lemma Rst3_0 x a b:
  LC1 x {{{ (hR,R) }}} RC3 a b -->*
  LC1 ([2]^^a++x) {{{ (hR,R) }}} RC3 0 b.
Proof.
  unfold RC3.
  rewrite LC1_app.
  st.
  sr.
  finish.
Qed.

Lemma Rst3_1 x a b:
  LC1 x {{{ (hR,R) }}} RC3 a (1+b) -->*
  LC1 (O::[2]^^a++x) {{{ (hR,R) }}} RC3 0 b.
Proof.
  unfold RC3.
  cbn[LC1].
  rewrite LC1_app.
  es.
Qed.

Lemma Rst2_0 x a b:
  LC1 x {{{ (hR,R) }}} RC2 a b -->*
  LC1 ((1%nat)::[2]^^a++x) {{{ (hR,R) }}} RC3 0 b.
Proof.
  unfold RC3,RC2.
  cbn[LC1].
  rewrite LC1_app.
  es.
Qed.

Lemma Rst2_1 x a b:
  LC1 x {{{ (hR,R) }}} RC2 a (1+b) -->*
  LC1 (O::(1%nat)::[2]^^a++x) {{{ (hR,R) }}} RC3 0 b.
Proof.
  unfold RC3,RC2.
  cbn[LC1].
  rewrite LC1_app.
  es.
Qed.

Definition S0 '(x,n) := LC1 x {{{ (hR,R) }}} RC3 0 n.

Lemma Rst x n x':
  LRst x x' ->
  S0 (x,n) -->+
  LC0 x' {{{ (hR,R) }}} RC0 (2+n).
Proof.
  unfold S0,RC3,RC0.
  intros I.
  eapply LRst_spec in I.
  es; er.
  follow100 I.
  es.
Qed.

Lemma BigStep00 x n x':
  LRst x x' ->
  n+2 <= L_rest x' ->
  S0 (x,n*2) -->+
  S0 ([2]^^(1+n)++L_empty x',L_rest x'-n-1).
Proof.
  intros I I0.
  unfold S0.
  eapply Rst in I.
  follow10 I. clear I.
  epose proof (RIncs1_2 n (L_rest x'-n-2)) as HR.
  replace (1+n+(1+(L_rest x'-n-2))) with (L_rest x') in HR by lia.
  replace (n*2+2) with (2+n*2) in HR by lia.
  epose proof (sideRLs_concat_1 HR (L_empty_spec _)) as I1.
  follow I1.
  follow Rst3_0.
  finish.
Qed.

Lemma BigStep01 x n x':
  LRst x x' ->
  n+2 <= L_rest x' ->
  S0 (x,n*2) -->+
  S0 (O::[2]^^(1+n)++L_empty x',L_rest x'-n-2).
Proof.
  intros I I0.
  unfold S0.
  eapply Rst in I.
  follow10 I. clear I.
  epose proof (RIncs1_2 n (L_rest x'-n-2)) as HR.
  replace (1+n+(1+(L_rest x'-n-2))) with (L_rest x') in HR by lia.
  replace (n*2+2) with (2+n*2) in HR by lia.
  epose proof (sideRLs_concat_1 HR (L_empty_spec _)) as I1.
  follow I1.
  follow Rst3_1.
  finish.
Qed.

Lemma BigStep10 x n x':
  LRst x x' ->
  n+2 <= L_rest x' ->
  S0 (x,n*2+1) -->+
  S0 ((1%nat)::[2]^^(1+n)++L_empty x',L_rest x'-n-2).
Proof.
  intros I I0.
  unfold S0.
  eapply Rst in I.
  follow10 I. clear I.
  epose proof (RIncs1_1 (1+n) (L_rest x'-n-2)) as HR.
  replace (1+(1+n)+(L_rest x'-n-2)) with (L_rest x') in HR by lia.
  replace ((1+n)*2+1) with (2+(n*2+1)) in HR by lia.
  epose proof (sideRLs_concat_1 HR (L_empty_spec _)) as I1.
  follow I1.
  follow Rst2_0.
  finish.
Qed.

Lemma BigStep11 x n x':
  LRst x x' ->
  n+3 <= L_rest x' ->
  S0 (x,n*2+1) -->+
  S0 (O::(1%nat)::[2]^^(1+n)++L_empty x',L_rest x'-n-3).
Proof.
  intros I I0.
  unfold S0.
  eapply Rst in I.
  follow10 I. clear I.
  epose proof (RIncs1_1 (1+n) (1+(L_rest x'-n-3))) as HR.
  replace (1+(1+n)+(1+(L_rest x'-n-3))) with (L_rest x') in HR by lia.
  replace ((1+n)*2+1) with (2+(n*2+1)) in HR by lia.
  epose proof (sideRLs_concat_1 HR (L_empty_spec _)) as I1.
  follow I1.
  follow Rst2_1.
  finish.
Qed.

Lemma init:
  c0 -->*
  S0 ([1%nat;5],O).
Proof.
  unfold S0.
  esx.
Qed.

Import Dynamics7a.
Open Scope nat.

Definition good (i:LD' * nat) : Prop :=
match i with
| (x,n) => exists x', LRst x x' /\ WF x /\ 5 <= L_rest x' /\ n < L_rest x'
end.

Lemma LRst_score x x':
  LRst x x' -> L_rest x' = score x.
Proof.
  induction 1; cbn - [half].
  - reflexivity.
  - rewrite IHLRst.
    replace (a0*2+1) with (1+a0*2) by lia.
    rewrite half_odd.
    lia.
  - rewrite IHLRst.
    replace (a0*2+2) with ((S a0)*2) by lia.
    rewrite half_even_pos.
    lia.
Qed.

Lemma LRst_pair_sum x x':
  LRst x x' -> L_empty x' = pair_sum x.
Proof.
  induction 1; cbn.
  - reflexivity.
  - rewrite IHLRst. f_equal. lia.
  - rewrite IHLRst. f_equal. lia.
Qed.

Lemma LRst_exists x:
  even_len x -> odd_pos x -> exists x', LRst x x'.
Proof.
  intros He Ho.
  induction He as [|u v xs He IH].
  - exists ([]:LD). constructor.
  - inversion Ho as [|u' v' xs' Hv Hox]; subst; clear Ho.
    destruct (IH Hox) as [x' Hx'].
    destruct (mod2 v) as [q|q]; subst v.
    + destruct q as [|q].
      * lia.
      * replace (S q*2) with (q*2+2) by lia.
        exists ((q,u+4)::x'). apply LRst_2. exact Hx'.
    + replace (1+q*2) with (q*2+1) by lia.
      exists ((q,u+3)::x'). apply LRst_1. exact Hx'.
Qed.

Lemma init2:
  c0 -->* S0 ([0;1;2;12],0).
Proof.
  assert (H1: S0 ([1%nat;5],O) -->+ S0 ([2;8],1)).
  { change (S0 ([1%nat;5],0*2) -->+
      S0 ([2]^^(1+0) ++ L_empty [(2,4)],L_rest [(2,4)]-0-1)).
    eapply BigStep00.
    - exact (LRst_1 2 1 [] [] LRst_0).
    - cbn. lia. }
  assert (H2: S0 ([2;8],1) -->+ S0 ([0;1;2;12],0)).
  { change (S0 ([2;8],0*2+1) -->+
      S0 (O::(1%nat)::[2]^^(1+0) ++ L_empty [(3,6)],L_rest [(3,6)]-0-3)).
    eapply BigStep11.
    - exact (LRst_2 3 2 [] [] LRst_0).
    - cbn. lia. }
  eapply evstep_trans.
  - apply init.
  - eapply evstep_trans.
    + apply progress_evstep. exact H1.
    + apply progress_evstep. exact H2.
Qed.

Lemma good_progress i:
  good i -> exists i', S0 i -->+ S0 i' /\ good i'.
Proof.
  destruct i as [x n].
  intros [x' [HLR [HWF [Hge Hn]]]].
  pose proof (LRst_score _ _ HLR) as Hscore.
  pose proof (LRst_pair_sum _ _ HLR) as Hempty.
  assert (Hsorted: sorted_from 2 (L_empty x')).
  { rewrite Hempty. apply pair_sum_sorted. exact HWF. }
  destruct (mod2 n) as [a|a]; subst n.
  - set (base := [2%nat]^^(1+a) ++ L_empty x').
    destruct (mod2 (length base)) as [q Hlenbase|q Hlenbase].
    + exists (base,L_rest x'-a-1). split.
      * subst base. eapply BigStep00; [exact HLR|lia].
      * assert (He: even_len base).
        { apply (even_len_of_length base q). exact Hlenbase. }
        assert (HWFnext: WF base).
        { subst base. apply WF_prefix00; assumption. }
        destruct HWFnext as [Hsnext [Henext Honext]].
        destruct (LRst_exists _ Henext Honext) as [znext Hznext].
        exists znext.
        split; [exact Hznext|].
        split; [repeat split; assumption|].
        split.
        -- subst base.
           pose proof (LRst_score _ _ Hznext) as Hzscore.
           pose proof (score_prefix00_growth (1+a) x HWF) as Hgrow.
           rewrite <- Hempty in Hgrow.
           specialize (Hgrow Henext).
           rewrite Hzscore. lia.
        -- subst base.
           pose proof (LRst_score _ _ Hznext) as Hzscore.
           pose proof (score_prefix00_growth (1+a) x HWF) as Hgrow.
           rewrite <- Hempty in Hgrow.
           specialize (Hgrow Henext).
           rewrite Hzscore. lia.
    + exists (0%nat::base,L_rest x'-a-2). split.
      * subst base. eapply BigStep01; [exact HLR|lia].
      * assert (He: even_len (0%nat::base)).
        { apply (even_len_of_length (0%nat::base) (S q)).
          change (S (length base) = S q*2).
          rewrite Hlenbase. lia. }
        assert (HWFnext: WF (0%nat::base)).
        { subst base. apply WF_prefix01; assumption. }
        destruct HWFnext as [Hsnext [Henext Honext]].
        destruct (LRst_exists _ Henext Honext) as [znext Hznext].
        exists znext.
        split; [exact Hznext|].
        split; [repeat split; assumption|].
        split.
        -- subst base.
           pose proof (LRst_score _ _ Hznext) as Hzscore.
           pose proof (score_prefix01_growth (1+a) x HWF) as Hgrow.
           rewrite <- Hempty in Hgrow.
           specialize (Hgrow Henext).
           rewrite Hzscore. lia.
        -- subst base.
           pose proof (LRst_score _ _ Hznext) as Hzscore.
           pose proof (score_prefix01_growth (1+a) x HWF) as Hgrow.
           rewrite <- Hempty in Hgrow.
           specialize (Hgrow Henext).
           rewrite Hzscore. lia.
  - set (base := 1%nat::[2%nat]^^(1+a) ++ L_empty x').
    destruct (mod2 (length base)) as [q Hlenbase|q Hlenbase].
    + exists (base,L_rest x'-a-2). split.
      * subst base.
        replace (1+a*2) with (a*2+1) by lia.
        eapply BigStep10; [exact HLR|lia].
      * assert (He: even_len base).
        { apply (even_len_of_length base q). exact Hlenbase. }
        assert (HWFnext: WF base).
        { subst base. apply WF_prefix10; assumption. }
        destruct HWFnext as [Hsnext [Henext Honext]].
        destruct (LRst_exists _ Henext Honext) as [znext Hznext].
        exists znext.
        split; [exact Hznext|].
        split; [repeat split; assumption|].
        split.
        -- subst base.
           pose proof (LRst_score _ _ Hznext) as Hzscore.
           pose proof (score_prefix10_growth (1+a) x HWF) as Hgrow.
           rewrite <- Hempty in Hgrow.
           specialize (Hgrow Henext).
           rewrite Hzscore. lia.
        -- subst base.
           pose proof (LRst_score _ _ Hznext) as Hzscore.
           pose proof (score_prefix10_growth (1+a) x HWF) as Hgrow.
           rewrite <- Hempty in Hgrow.
           specialize (Hgrow Henext).
           rewrite Hzscore. lia.
    + exists (0%nat::base,L_rest x'-a-3). split.
      * subst base.
        replace (1+a*2) with (a*2+1) by lia.
        eapply BigStep11; [exact HLR|lia].
      * assert (He: even_len (0%nat::base)).
        { apply (even_len_of_length (0%nat::base) (S q)).
          change (S (length base) = S q*2).
          rewrite Hlenbase. lia. }
        assert (HWFnext: WF (0%nat::base)).
        { subst base. apply WF_prefix11; assumption. }
        destruct HWFnext as [Hsnext [Henext Honext]].
        destruct (LRst_exists _ Henext Honext) as [znext Hznext].
        exists znext.
        split; [exact Hznext|].
        split; [repeat split; assumption|].
        split.
        -- subst base.
           pose proof (LRst_score _ _ Hznext) as Hzscore.
           pose proof (score_prefix11_growth (1+a) x HWF) as Hgrow.
           rewrite <- Hempty in Hgrow.
           specialize (Hgrow Henext).
           rewrite Hzscore. lia.
        -- subst base.
           pose proof (LRst_score _ _ Hznext) as Hzscore.
           pose proof (score_prefix11_growth (1+a) x HWF) as Hgrow.
           rewrite <- Hempty in Hgrow.
           specialize (Hgrow Henext).
           rewrite Hzscore. lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init2.
  eapply progress_nonhalt_cond with
    (A:=(LD' * nat)%type)
    (C:=fun i => S0 i)
    (P:=good).
  - apply good_progress.
  - exists [(0,3);(5,6)].
    split; [exact (LRst_1 0 0 [2;12] [(5,6)] (LRst_2 5 2 [] [] LRst_0))|].
    split.
    + repeat split.
      * repeat constructor; lia.
      * repeat constructor.
      * repeat constructor; lia.
    + split; cbn; lia.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB0RE_0RC1RF_1LD0RE_0LE0LC_1RA0LD_1RD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation hL := (C,[]).
Notation hR := (E,[]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Notation LD := (list (nat*nat)).
Notation LD' := (list (nat)).

Fixpoint LC0(x:LD):side :=
match x with
| [] => 0inf
| (x0,x1)::x2 => LC0 x2 <* <[1;1;1;0]^^x0 <* <[1;0]^^x1 <* <[1;1;0;0]
end.

Fixpoint LC1(x:LD'):side :=
match x with
| [] => 0inf
| (x1)::x2 => LC1 x2 <* <[1;0]^^x1 <* <[1;1;0;0]
end.

Fixpoint L_empty(x:LD):LD' :=
match x with
| [] => []
| (x0,x1)::x2 => (x0*2+x1)::L_empty x2
end.

Fixpoint L_rest(x:LD):nat :=
match x with
| [] => O
| (x0,x1)::x2 => x0 + L_rest x2
end.

Lemma L_empty_spec x:
  sideRLs tm' (hLR^^(L_rest x)) (LC0 x) (LC1 (L_empty x)).
Proof.
  induction x as [|[x0 x1] x].
  1: esx.
  cbn - [Str_app].
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: rewrite <-Str_app_assoc.
  2: eapply segRLs_sideRLs_concat.
  3: apply IHx.
  2: eapply segRLs_wall.
  2: solve_seg.
  2: solve_seg.
  clear.
  gen x1.
  induction x0; intros.
  1: esx.
  replace (S x0) with (1+x0) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: applys_eq (IHx0 (2+x1)); flia.
  esx.
Qed.

Notation "l |> r" := (l <* <[1;1;1] {{A}}> r) (at level 30).

Inductive LRst: LD'->LD->Prop :=
| LRst_0: LRst [] []
| LRst_1 a0 a1 x x':
  LRst x x' ->
  LRst ((a1)::(a0*2+1)::x) ((a0,a1+3)::x')
| LRst_2 a0 a1 x x':
  LRst x x' ->
  LRst ((a1)::(a0*2+2)::x) ((a0,a1+4)::x')
.

Lemma LRst_spec x x':
  LRst x x' ->
  forall r,
  LC1 x {{{ (hL,L) }}} r -->+
  LC0 x' {{{ (hR,R) }}} [0;0;1] *> r.
Proof.
  intros I.
  induction I; cbn[LC0]; cbn[LC1]; intros.
  all: es; er; follow100 IHI; es.
Qed.

Definition RC0 a := [0;0;1;0]^^a *> 0inf.
Definition RC1 a b := [0;1;0;1;0;0;0;1]^^a *> [0;1;0;0;0;1] *> [1;0;0;0]^^b *> 0inf.
Definition RC2 a b := [0;1;0;1;0;0;0;1]^^a *> [0;1;0;0;0;1] *> [0;0;0;1]^^b *> 0inf.
Definition RC3 a b := [0;1;0;1;0;0;0;1]^^a *> [0;0;0;1]^^b *> 0inf.

Lemma RIncs1 a b:
  sideRLs tm (hRL^^(1+a)) (RC0 (1+a*2+b)) (RC1 a b).
Proof.
  unfold RC0,RC1.
  gen b.
  induction a; intros.
  1: esx.
  replace (1+S a) with (1+a+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHa (2+b)); flia.
  esx.
Qed.

Lemma RIncs2 a b:
  sideRLs tm (hRL^^b) (RC1 a 0) (RC2 a b).
Proof.
  unfold RC1,RC2.
  induction b.
  1: esx.
  replace (S b) with (b+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHb.
  esx.
Qed.

Lemma RIncs3 a b:
  sideRLs tm (hRL^^(1+b)) (RC1 a 1) (RC3 (1+a) (1+b)).
Proof.
  unfold RC1,RC3.
  induction b.
  1: esx.
  replace (1+S b) with (1+b+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHb.
  esx.
Qed.

Lemma RIncs1_1 a b:
  sideRLs tm (hRL^^(1+a+b)) (RC0 (a*2+1)) (RC2 a b).
Proof.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (RIncs1 a O); flia.
  apply RIncs2.
Qed.

Lemma RIncs1_2 a b:
  sideRLs tm (hRL^^(1+a+(1+b))) (RC0 (a*2+2)) (RC3 (1+a) (1+b)).
Proof.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (RIncs1 a 1); flia.
  apply RIncs3.
Qed.

Lemma LC1_app a n x:
  LC1 ([a]^^n++x) = LC1 x <* (<[1;0]^^a <+ <[1;1;0;0])^^n.
Proof.
  induction n.
  1: reflexivity.
  cbn.
  rewrite IHn.
  simpl_tape.
  reflexivity.
Qed.

Lemma Rst3_0 x a b:
  LC1 x {{{ (hR,R) }}} RC3 a b -->*
  LC1 ([2]^^a++x) {{{ (hR,R) }}} RC3 0 b.
Proof.
  unfold RC3.
  rewrite LC1_app.
  st.
  sr.
  finish.
Qed.

Lemma Rst3_1 x a b:
  LC1 x {{{ (hR,R) }}} RC3 a (1+b) -->*
  LC1 (O::[2]^^a++x) {{{ (hR,R) }}} RC3 0 b.
Proof.
  unfold RC3.
  cbn[LC1].
  rewrite LC1_app.
  es.
Qed.

Lemma Rst2_0 x a b:
  LC1 x {{{ (hR,R) }}} RC2 a b -->*
  LC1 ((1%nat)::[2]^^a++x) {{{ (hR,R) }}} RC3 0 b.
Proof.
  unfold RC3,RC2.
  cbn[LC1].
  rewrite LC1_app.
  es.
Qed.

Lemma Rst2_1 x a b:
  LC1 x {{{ (hR,R) }}} RC2 a (1+b) -->*
  LC1 (O::(1%nat)::[2]^^a++x) {{{ (hR,R) }}} RC3 0 b.
Proof.
  unfold RC3,RC2.
  cbn[LC1].
  rewrite LC1_app.
  es.
Qed.

Definition S0 '(x,n) := LC1 x {{{ (hR,R) }}} RC3 0 n.

Lemma Rst x n x':
  LRst x x' ->
  S0 (x,n) -->+
  LC0 x' {{{ (hR,R) }}} RC0 (2+n).
Proof.
  unfold S0,RC3,RC0.
  intros I.
  eapply LRst_spec in I.
  es; er.
  follow100 I.
  es.
Qed.

Lemma BigStep00 x n x':
  LRst x x' ->
  n+2 <= L_rest x' ->
  S0 (x,n*2) -->+
  S0 ([2]^^(1+n)++L_empty x',L_rest x'-n-1).
Proof.
  intros I I0.
  unfold S0.
  eapply Rst in I.
  follow10 I. clear I.
  epose proof (RIncs1_2 n (L_rest x'-n-2)) as HR.
  replace (1+n+(1+(L_rest x'-n-2))) with (L_rest x') in HR by lia.
  replace (n*2+2) with (2+n*2) in HR by lia.
  epose proof (sideRLs_concat_1 HR (L_empty_spec _)) as I1.
  follow I1.
  follow Rst3_0.
  finish.
Qed.

Lemma BigStep01 x n x':
  LRst x x' ->
  n+2 <= L_rest x' ->
  S0 (x,n*2) -->+
  S0 (O::[2]^^(1+n)++L_empty x',L_rest x'-n-2).
Proof.
  intros I I0.
  unfold S0.
  eapply Rst in I.
  follow10 I. clear I.
  epose proof (RIncs1_2 n (L_rest x'-n-2)) as HR.
  replace (1+n+(1+(L_rest x'-n-2))) with (L_rest x') in HR by lia.
  replace (n*2+2) with (2+n*2) in HR by lia.
  epose proof (sideRLs_concat_1 HR (L_empty_spec _)) as I1.
  follow I1.
  follow Rst3_1.
  finish.
Qed.

Lemma BigStep10 x n x':
  LRst x x' ->
  n+2 <= L_rest x' ->
  S0 (x,n*2+1) -->+
  S0 ((1%nat)::[2]^^(1+n)++L_empty x',L_rest x'-n-2).
Proof.
  intros I I0.
  unfold S0.
  eapply Rst in I.
  follow10 I. clear I.
  epose proof (RIncs1_1 (1+n) (L_rest x'-n-2)) as HR.
  replace (1+(1+n)+(L_rest x'-n-2)) with (L_rest x') in HR by lia.
  replace ((1+n)*2+1) with (2+(n*2+1)) in HR by lia.
  epose proof (sideRLs_concat_1 HR (L_empty_spec _)) as I1.
  follow I1.
  follow Rst2_0.
  finish.
Qed.

Lemma BigStep11 x n x':
  LRst x x' ->
  n+3 <= L_rest x' ->
  S0 (x,n*2+1) -->+
  S0 (O::(1%nat)::[2]^^(1+n)++L_empty x',L_rest x'-n-3).
Proof.
  intros I I0.
  unfold S0.
  eapply Rst in I.
  follow10 I. clear I.
  epose proof (RIncs1_1 (1+n) (1+(L_rest x'-n-3))) as HR.
  replace (1+(1+n)+(1+(L_rest x'-n-3))) with (L_rest x') in HR by lia.
  replace ((1+n)*2+1) with (2+(n*2+1)) in HR by lia.
  epose proof (sideRLs_concat_1 HR (L_empty_spec _)) as I1.
  follow I1.
  follow Rst2_1.
  finish.
Qed.

Lemma init:
  c0 -->*
  S0 ([2;6],O).
Proof.
  unfold S0.
  esx.
Qed.

Import Dynamics7a.
Open Scope nat.

Definition good (i:LD' * nat) : Prop :=
match i with
| (x,n) => exists x', LRst x x' /\ WF x /\ 5 <= L_rest x' /\ n < L_rest x'
end.

Lemma LRst_score x x':
  LRst x x' -> L_rest x' = score x.
Proof.
  induction 1; cbn - [half].
  - reflexivity.
  - rewrite IHLRst.
    replace (a0*2+1) with (1+a0*2) by lia.
    rewrite half_odd.
    lia.
  - rewrite IHLRst.
    replace (a0*2+2) with ((S a0)*2) by lia.
    rewrite half_even_pos.
    lia.
Qed.

Lemma LRst_pair_sum x x':
  LRst x x' -> L_empty x' = pair_sum x.
Proof.
  induction 1; cbn.
  - reflexivity.
  - rewrite IHLRst. f_equal. lia.
  - rewrite IHLRst. f_equal. lia.
Qed.

Lemma LRst_exists x:
  even_len x -> odd_pos x -> exists x', LRst x x'.
Proof.
  intros He Ho.
  induction He as [|u v xs He IH].
  - exists ([]:LD). constructor.
  - inversion Ho as [|u' v' xs' Hv Hox]; subst; clear Ho.
    destruct (IH Hox) as [x' Hx'].
    destruct (mod2 v) as [q|q]; subst v.
    + destruct q as [|q].
      * lia.
      * replace (S q*2) with (q*2+2) by lia.
        exists ((q,u+4)::x'). apply LRst_2. exact Hx'.
    + replace (1+q*2) with (q*2+1) by lia.
      exists ((q,u+3)::x'). apply LRst_1. exact Hx'.
Qed.

Lemma init2:
  c0 -->* S0 ([0;1;2;14],1).
Proof.
  assert (H1: S0 ([2;6],O) -->+ S0 ([2;10],1)).
  { change (S0 ([2;6],0*2) -->+
      S0 ([2]^^(1+0) ++ L_empty [(2,6)],L_rest [(2,6)]-0-1)).
    eapply BigStep00.
    - exact (LRst_2 2 2 [] [] LRst_0).
    - cbn. lia. }
  assert (H2: S0 ([2;10],1) -->+ S0 ([0;1;2;14],1)).
  { change (S0 ([2;10],0*2+1) -->+
      S0 (O::(1%nat)::[2]^^(1+0) ++ L_empty [(4,6)],L_rest [(4,6)]-0-3)).
    eapply BigStep11.
    - exact (LRst_2 4 2 [] [] LRst_0).
    - cbn. lia. }
  eapply evstep_trans.
  - apply init.
  - eapply evstep_trans.
    + apply progress_evstep. exact H1.
    + apply progress_evstep. exact H2.
Qed.

Lemma good_progress i:
  good i -> exists i', S0 i -->+ S0 i' /\ good i'.
Proof.
  destruct i as [x n].
  intros [x' [HLR [HWF [Hge Hn]]]].
  pose proof (LRst_score _ _ HLR) as Hscore.
  pose proof (LRst_pair_sum _ _ HLR) as Hempty.
  assert (Hsorted: sorted_from 2 (L_empty x')).
  { rewrite Hempty. apply pair_sum_sorted. exact HWF. }
  destruct (mod2 n) as [a|a]; subst n.
  - set (base := [2%nat]^^(1+a) ++ L_empty x').
    destruct (mod2 (length base)) as [q Hlenbase|q Hlenbase].
    + exists (base,L_rest x'-a-1). split.
      * subst base. eapply BigStep00; [exact HLR|lia].
      * assert (He: even_len base).
        { apply (even_len_of_length base q). exact Hlenbase. }
        assert (HWFnext: WF base).
        { subst base. apply WF_prefix00; assumption. }
        destruct HWFnext as [Hsnext [Henext Honext]].
        destruct (LRst_exists _ Henext Honext) as [znext Hznext].
        exists znext.
        split; [exact Hznext|].
        split; [repeat split; assumption|].
        split.
        -- subst base.
           pose proof (LRst_score _ _ Hznext) as Hzscore.
           pose proof (score_prefix00_growth (1+a) x HWF) as Hgrow.
           rewrite <- Hempty in Hgrow.
           specialize (Hgrow Henext).
           rewrite Hzscore. lia.
        -- subst base.
           pose proof (LRst_score _ _ Hznext) as Hzscore.
           pose proof (score_prefix00_growth (1+a) x HWF) as Hgrow.
           rewrite <- Hempty in Hgrow.
           specialize (Hgrow Henext).
           rewrite Hzscore. lia.
    + exists (0%nat::base,L_rest x'-a-2). split.
      * subst base. eapply BigStep01; [exact HLR|lia].
      * assert (He: even_len (0%nat::base)).
        { apply (even_len_of_length (0%nat::base) (S q)).
          change (S (length base) = S q*2).
          rewrite Hlenbase. lia. }
        assert (HWFnext: WF (0%nat::base)).
        { subst base. apply WF_prefix01; assumption. }
        destruct HWFnext as [Hsnext [Henext Honext]].
        destruct (LRst_exists _ Henext Honext) as [znext Hznext].
        exists znext.
        split; [exact Hznext|].
        split; [repeat split; assumption|].
        split.
        -- subst base.
           pose proof (LRst_score _ _ Hznext) as Hzscore.
           pose proof (score_prefix01_growth (1+a) x HWF) as Hgrow.
           rewrite <- Hempty in Hgrow.
           specialize (Hgrow Henext).
           rewrite Hzscore. lia.
        -- subst base.
           pose proof (LRst_score _ _ Hznext) as Hzscore.
           pose proof (score_prefix01_growth (1+a) x HWF) as Hgrow.
           rewrite <- Hempty in Hgrow.
           specialize (Hgrow Henext).
           rewrite Hzscore. lia.
  - set (base := 1%nat::[2%nat]^^(1+a) ++ L_empty x').
    destruct (mod2 (length base)) as [q Hlenbase|q Hlenbase].
    + exists (base,L_rest x'-a-2). split.
      * subst base.
        replace (1+a*2) with (a*2+1) by lia.
        eapply BigStep10; [exact HLR|lia].
      * assert (He: even_len base).
        { apply (even_len_of_length base q). exact Hlenbase. }
        assert (HWFnext: WF base).
        { subst base. apply WF_prefix10; assumption. }
        destruct HWFnext as [Hsnext [Henext Honext]].
        destruct (LRst_exists _ Henext Honext) as [znext Hznext].
        exists znext.
        split; [exact Hznext|].
        split; [repeat split; assumption|].
        split.
        -- subst base.
           pose proof (LRst_score _ _ Hznext) as Hzscore.
           pose proof (score_prefix10_growth (1+a) x HWF) as Hgrow.
           rewrite <- Hempty in Hgrow.
           specialize (Hgrow Henext).
           rewrite Hzscore. lia.
        -- subst base.
           pose proof (LRst_score _ _ Hznext) as Hzscore.
           pose proof (score_prefix10_growth (1+a) x HWF) as Hgrow.
           rewrite <- Hempty in Hgrow.
           specialize (Hgrow Henext).
           rewrite Hzscore. lia.
    + exists (0%nat::base,L_rest x'-a-3). split.
      * subst base.
        replace (1+a*2) with (a*2+1) by lia.
        eapply BigStep11; [exact HLR|lia].
      * assert (He: even_len (0%nat::base)).
        { apply (even_len_of_length (0%nat::base) (S q)).
          change (S (length base) = S q*2).
          rewrite Hlenbase. lia. }
        assert (HWFnext: WF (0%nat::base)).
        { subst base. apply WF_prefix11; assumption. }
        destruct HWFnext as [Hsnext [Henext Honext]].
        destruct (LRst_exists _ Henext Honext) as [znext Hznext].
        exists znext.
        split; [exact Hznext|].
        split; [repeat split; assumption|].
        split.
        -- subst base.
           pose proof (LRst_score _ _ Hznext) as Hzscore.
           pose proof (score_prefix11_growth (1+a) x HWF) as Hgrow.
           rewrite <- Hempty in Hgrow.
           specialize (Hgrow Henext).
           rewrite Hzscore. lia.
        -- subst base.
           pose proof (LRst_score _ _ Hznext) as Hzscore.
           pose proof (score_prefix11_growth (1+a) x HWF) as Hgrow.
           rewrite <- Hempty in Hgrow.
           specialize (Hgrow Henext).
           rewrite Hzscore. lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init2.
  eapply progress_nonhalt_cond with
    (A:=(LD' * nat)%type)
    (C:=fun i => S0 i)
    (P:=good).
  - apply good_progress.
  - exists [(0,3);(6,6)].
    split; [exact (LRst_1 0 0 [2;14] [(6,6)] (LRst_2 6 2 [] [] LRst_0))|].
    split.
    + repeat split.
      * repeat constructor; lia.
      * repeat constructor.
      * repeat constructor; lia.
    + split; cbn; lia.
Qed.

End TM3.

