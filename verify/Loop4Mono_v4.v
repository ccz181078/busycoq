From BusyCoq Require Import Individual62.

Require Import ZArith ZifyNat Lia String List.
From BusyCoq Require Import Longitudinal ES_v3.

Import ListNotations.
Open Scope list_scope.

Ltac es_v3_pre ::= ut.

Definition D1 n := [0;1;1] ++ [1;1]^^n.
Definition D2 n := [0;1] ++ [1;1]^^n.

Inductive word := W1 (n:nat) | W2 (n:nat).

Definition word_side w r :=
  match w with
  | W1 n => D1 n *> r
  | W2 n => D2 n *> r
  end.

Fixpoint words_side ws : side :=
  match ws with
  | [] => 0inf
  | w::ws => word_side w (words_side ws)
  end.

Fixpoint signal (ws:list word) : option (list word) :=
  match ws with
  | [] => Some [W2 2]
  | W1 n::ws =>
      match signal ws with
      | Some ws' => Some(W1 n::ws')
      | None => None
      end
  | W2 n::[] => Some [W1 (n+2)]
  | W2 n::W1 m::ws => Some (W1 (n+2)::W2 m::ws)
  | W2 n::W2 0::ws => None
  | W2 n::W2 (S m)::ws => Some (W1 (n+2)::W1 m::ws)
  end.

Fixpoint signals (k:nat) (ws:list word) : option (list word) :=
  match k with
  | O => Some ws
  | S k =>
      match signal ws with Some ws' => signals k ws' | None => None end
  end.

Definition reset ws : option (list word) :=
  match signals 2 ws with
  | Some (W1 a::W1 b::ws') => signals (3*(a+2)) (W2 b::ws')
  | _ => None
  end.

Inductive character := M3 | M1 | Z0 | P2 | P5.

Inductive phase :=
| P0 | P1 | P2q | P3 | P4 | P5q | P6 | P7 | P8 | P9 | P10 | P11
| P12 | P13 | P14 | P15 | P16 | P17 | P18 | P19 | P20 | P21 | P22
| P23 | P24.

Definition transition q c : option (phase*list character) :=
  match q,c with
  | P0,Z0 => Some (P10,[Z0;Z0;Z0;Z0;Z0;Z0])
  | P1,Z0 => Some (P10,[Z0;P5;M3;Z0;Z0;Z0])
  | P2q,Z0 => Some (P10,[Z0;Z0;Z0;P2;Z0;Z0])
  | P3,Z0 => Some (P0,[P5;M3;Z0;Z0;P5;M1;Z0])
  | P4,Z0 => Some (P8,[M3;Z0;Z0;Z0;Z0;Z0;Z0])
  | P5q,Z0 => Some (P6,[M3;Z0;Z0;Z0;Z0;P5;M1])
  | P6,Z0 => Some (P9,[Z0;Z0;Z0;Z0;Z0;Z0;Z0])
  | P7,Z0 => Some (P8,[Z0;Z0;Z0;Z0;Z0;Z0;Z0])
  | P8,Z0 => Some (P9,[P5;M3;Z0;Z0;Z0;Z0;Z0])
  | P8,P2 => Some (P15,[P5;M3;Z0;Z0;Z0;Z0;Z0])
  | P8,P5 => Some (P23,[P5;M3;Z0;Z0;Z0;Z0;Z0])
  | P9,Z0 => Some (P8,[Z0;P2;Z0;Z0;Z0;Z0;Z0])
  | P9,P2 => Some (P14,[Z0;P2;Z0;Z0;Z0;Z0;Z0])
  | P9,P5 => Some (P22,[Z0;P2;Z0;Z0;Z0;Z0;Z0])
  | P10,Z0 => Some (P9,[Z0;Z0;P2;Z0;Z0;Z0;Z0])
  | P10,P5 => Some (P23,[Z0;Z0;P2;Z0;Z0;Z0;Z0])
  | P11,Z0 => Some (P7,[P2;Z0;Z0;Z0;Z0;P5;M1])
  | P12,Z0 => Some (P4,[P2;Z0;Z0;Z0;Z0;Z0;Z0;P5])
  | P13,Z0 => Some (P19,[M3;Z0;Z0;Z0])
  | P14,Z0 => Some (P18,[P5;M3;Z0;Z0])
  | P15,Z0 => Some (P17,[Z0;P2;Z0;Z0])
  | P16,Z0 => Some (P20,[P2;Z0;Z0;Z0])
  | P17,Z0 => Some (P2q,[Z0;Z0;Z0;P5;M3])
  | P18,Z0 => Some (P21,[Z0;Z0;Z0;Z0;P2;Z0])
  | P19,Z0 => Some (P2q,[Z0;P5;M1;Z0;Z0])
  | P20,Z0 => Some (P21,[Z0;P5;M1;Z0;Z0;Z0])
  | P21,Z0 => Some (P1,[Z0;P5;M3;Z0;Z0;Z0])
  | P21,P5 => Some (P24,[Z0;P5;M3;Z0;Z0;Z0])
  | P22,M3 => Some (P5q,[P5])
  | P22,M1 => Some (P13,[P5])
  | P23,M3 => Some (P11,[Z0])
  | P23,M1 => Some (P16,[Z0])
  | P24,M3 => Some (P3,[Z0])
  | _,_ => None
  end.

Fixpoint run q cs : option phase :=
  match cs with
  | [] => Some q
  | c::cs =>
      match transition q c with Some(q',_) => run q' cs | None => None end
  end.

Lemma run_app q xs ys:
  run q (xs++ys)=
  match run q xs with Some q' => run q' ys | None => None end.
Proof.
  revert q.
  induction xs as [|x xs IH]; intros q; cbn; auto.
  destruct (transition q x) as [[q' p]|]; cbn; auto.
Qed.

Inductive allowed : phase -> phase -> Prop :=
| A0_20 : allowed P0 P20
| A1_9 : allowed P1 P9
| A2_2 : allowed P2q P2q
| A2_5 : allowed P2q P5q
| A3_8 : allowed P3 P8
| A4_22 : allowed P4 P22
| A5_22 : allowed P5q P22
| A6_13 : allowed P6 P13
| A7_16 : allowed P7 P16
| A8_9 : allowed P8 P9
| A9_8 : allowed P9 P8
| A9_10 : allowed P9 P10
| A10_2 : allowed P10 P2q
| A10_9 : allowed P10 P9
| A11_9 : allowed P11 P9
| A12_8 : allowed P12 P8
| A13_22 : allowed P13 P22
| A14_9 : allowed P14 P9
| A15_8 : allowed P15 P8
| A16_9 : allowed P16 P9
| A17_21 : allowed P17 P21
| A18_9 : allowed P18 P9
| A19_8 : allowed P19 P8
| A20_1 : allowed P20 P1
| A21_1 : allowed P21 P1
| A21_18 : allowed P21 P18
| A22_9 : allowed P22 P9
| A23_8 : allowed P23 P8
| A23_10 : allowed P23 P10
| A24_9 : allowed P24 P9.

Lemma transition_nonempty q c q' p:
  transition q c=Some(q',p) -> p<>[].
Proof. destruct q,c; cbn; congruence. Qed.

Lemma allowed_extend q e c q' p:
  allowed q e -> transition q c=Some(q',p) ->
  exists e', run e p=Some e' /\ allowed q' e'.
Proof.
  intros H Ht.
  destruct H; destruct c; cbn in Ht; try discriminate; inverts Ht.
  all: eexists; split.
  all: try reflexivity.
  all: constructor.
Qed.

Definition offset q :=
  match q with
  | P0 | P1 | P2q | P3 => 18
  | P4 | P5q | P6 | P7 | P8 | P9 | P10 | P11 => 19
  | P12 => 20
  | P13 | P14 | P15 | P16 => 13
  | P17 | P18 | P19 | P20 => 16
  | P21 => 17
  | P22 | P23 => 4
  | P24 => 3
  end.

Definition has_difference c a b :=
  match c with
  | M3 => b=a+3 | M1 => b=a+1 | Z0 => a=b
  | P2 => a=b+2 | P5 => a=b+5
  end.

Lemma transition_length q c q' p a b n:
  transition q c=Some(q',p) -> has_difference c a b ->
  3*(a+2)=S n+offset q ->
  3*((b+2)+2)=n+length p+offset q'.
Proof.
  destruct q,c; cbn; intros Ht Hd Hn; try discriminate;
    inverts Ht; cbn; lia.
Qed.

Definition phase_suffix q : list word :=
  match q with
  | P0 => [W1 4;W1 4;W1 4;W1 4;W1 4;W1 4;W1 4;W1 4]
  | P1 => [W1 6;W1 6;W1 1;W1 4;W1 4;W1 4;W1 4;W1 4]
  | P2q => [W1 6;W1 6;W1 6;W1 6;W1 4;W1 4;W1 4;W1 4]
  | P3 => [W1 8;W1 3;W1 6;W2 4;W1 4;W1 4;W1 4;W1 4]
  | P4 => [W1 1;W1 4;W1 4;W1 4;W1 4;W1 4;W1 4;W2 2]
  | P5q => [W1 3;W1 6;W1 6;W1 6;W2 4;W1 4;W1 4;W1 4]
  | P6 => [W1 4;W1 4;W1 4;W1 4;W1 4;W1 4;W1 4;W1 4]
  | P7 => [W1 4;W1 4;W1 4;W1 4;W1 4;W1 4;W1 4;W2 2]
  | P8 => [W1 6;W1 1;W1 4;W1 4;W1 4;W1 4;W1 4;W1 4]
  | P9 => [W1 6;W1 6;W1 4;W1 4;W1 4;W1 4;W1 4;W2 2]
  | P10 => [W1 6;W1 6;W1 6;W1 4;W1 4;W1 4;W1 4;W1 4]
  | P11 => [W1 8;W1 6;W1 6;W1 6;W2 4;W1 4;W1 4;W2 2]
  | P12 => [W1 6;W1 4;W1 4;W1 4;W1 4;W1 4;W1 4;W2 2]
  | P13 => [W1 3;W1 6;W1 6;W1 6;W2 4;W1 4;W1 4;W1 4]
  | P14 => [W1 6;W1 1;W1 4;W1 4;W1 4;W1 4;W1 4;W1 4]
  | P15 => [W1 6;W1 6;W1 4;W1 4;W1 4;W1 4;W1 4;W2 2]
  | P16 => [W1 8;W1 6;W1 6;W1 6;W2 4;W1 4;W1 4;W2 2]
  | P17 => [W1 6;W1 6;W1 6;W1 6;W1 1;W1 4;W1 4;W1 4]
  | P18 => [W1 6;W1 6;W1 6;W1 6;W1 6;W1 4;W1 4;W2 2]
  | P19 => [W1 8;W1 8;W1 3;W1 4;W1 4;W1 4;W1 4;W1 4]
  | P20 => [W1 8;W1 8;W1 3;W1 4;W1 4;W1 4;W1 4;W2 2]
  | P21 => [W1 6;W1 6;W1 1;W1 4;W1 4;W1 4;W1 4;W2 2]
  | P22 => [W1 6;W1 1;W1 4;W1 4;W1 4;W1 4;W1 4;W1 4]
  | P23 => [W1 6;W1 6;W1 4;W1 4;W1 4;W1 4;W1 4;W2 2]
  | P24 => [W1 6;W1 6;W1 1;W1 4;W1 4;W1 4;W1 4;W1 4]
  end.

Definition phase_head q :=
  match phase_suffix q with W1 n::_ => n | _ => O end.

Definition prepared_suffix q :=
  match signals 2 (phase_suffix q) with Some ws => ws | None => [] end.

Definition prepared_tail q := tl (prepared_suffix q).

Inductive diffs (z:nat) : list character -> list nat -> Prop :=
| diffs_nil : diffs z [] []
| diffs_cons c cs x xs:
    has_difference c x (hd z xs) -> diffs z cs xs ->
    diffs z (c::cs) (x::xs).

Lemma diffs_length z cs xs:
  diffs z cs xs -> length cs=length xs.
Proof. induction 1; cbn; congruence. Qed.

Lemma diffs_add z cs xs k:
  diffs z cs xs -> diffs (z+k) cs (map (fun x => x+k) xs).
Proof.
  induction 1; cbn.
  - constructor.
  - constructor; auto.
    destruct c; cbn in *; destruct xs; cbn in *; lia.
Qed.

Lemma diffs_app z z' cs xs p ys:
  diffs z cs xs -> diffs z' p ys -> hd z' ys=z ->
  diffs z' (cs++p) (xs++ys).
Proof.
  intros H.
  induction H; intros Hp Hz; cbn.
  - exact Hp.
  - constructor; auto.
    destruct xs; cbn in *; auto. now rewrite Hz.
Qed.

Lemma signals_add k l ws:
  signals (k+l) ws=
  match signals k ws with Some ws' => signals l ws' | None => None end.
Proof.
  revert ws.
  induction k as [|k IH]; intros ws; cbn; auto.
  destruct (signal ws); cbn; auto.
Qed.

Lemma signal_prefix xs ws:
  signal (map W1 xs++ws)=
  option_map (fun ws' => map W1 xs++ws') (signal ws).
Proof.
  induction xs as [|x xs IH].
  - cbn. destruct (signal ws); reflexivity.
  - cbn. rewrite IH. destruct (signal ws); reflexivity.
Qed.

Lemma signals_prefix k xs ws:
  signals k (map W1 xs++ws)=
  option_map (fun ws' => map W1 xs++ws') (signals k ws).
Proof.
  revert xs ws.
  induction k as [|k IH]; intros xs ws; cbn; auto.
  rewrite signal_prefix.
  destruct (signal ws); cbn; auto.
Qed.

Lemma signals_sweep b xs z tail:
  signals (S(length xs)) (W2 b::map W1 xs++W1 z::tail)=
  Some (map W1 (map (fun x => x+2) (b::xs))++W2 z::tail).
Proof.
  revert b.
  induction xs as [|x xs IH]; intros b; cbn.
  - reflexivity.
  - change (signals (S(length xs))
      (map W1 [b+2]++W2 x::map W1 xs++W1 z::tail)=
      Some (map W1 (map (fun y => y+2) (b::x::xs))++W2 z::tail)).
    rewrite signals_prefix,IH. reflexivity.
Qed.

Lemma prepared_suffix_spec q:
  signals 2 (phase_suffix q)=Some(prepared_suffix q).
Proof. destruct q; reflexivity. Qed.

Lemma prepared_suffix_shape q:
  prepared_suffix q=W1(phase_head q)::prepared_tail q.
Proof. destruct q; reflexivity. Qed.

Definition left_value c b :=
  match c with
  | M3 => b-3 | M1 => b-1 | Z0 => b | P2 => b+2 | P5 => b+5
  end.

Fixpoint prefix_values cs z :=
  match cs with
  | [] => []
  | c::cs =>
      let xs:=prefix_values cs z in left_value c (hd z xs)::xs
  end.

Lemma local_certificate q c q' p:
  transition q c=Some(q',p) ->
  signals (S(offset q)) (W2(phase_head q)::prepared_tail q)=
    Some(map W1 (prefix_values p (phase_head q'))++phase_suffix q') /\
  diffs (phase_head q') p (prefix_values p (phase_head q')) /\
  hd (phase_head q') (prefix_values p (phase_head q'))=phase_head q+2.
Proof.
  destruct q,c; cbn; intros H; try discriminate; inverts H.
  all: split; [reflexivity|].
  all: split; [|reflexivity].
  all: repeat (constructor; cbn; try lia).
Qed.

Lemma reset_physical q c q' p a b rest:
  transition q c=Some(q',p) -> 3*(a+2)=2+length rest+offset q ->
  reset (map W1 (a::b::rest)++phase_suffix q)=
  Some(map W1
    (map (fun x => x+2) (b::rest)++prefix_values p (phase_head q'))
    ++phase_suffix q').
Proof.
  intros Ht Hlen.
  unfold reset.
  rewrite signals_prefix,prepared_suffix_spec.
  cbn.
  rewrite prepared_suffix_shape.
  replace (a+2+(a+2+(a+2+O))) with
    (S(length rest)+S(offset q)) by lia.
  rewrite (signals_add (S(length rest)) (S(offset q))),signals_sweep.
  change (signals (S(offset q))
    (map W1 (map (fun x => x+2) (b::rest))++
      W2(phase_head q)::prepared_tail q)=
    Some(map W1
      (map (fun x => x+2) (b::rest)++prefix_values p (phase_head q'))
      ++phase_suffix q')).
  rewrite signals_prefix,(proj1 (local_certificate _ _ _ _ Ht)).
  cbn. now rewrite map_app,app_assoc.
Qed.

Lemma prefix_values_length cs z:
  length(prefix_values cs z)=length cs.
Proof. induction cs; cbn; congruence. Qed.

Inductive Good : list word -> Prop :=
| Good_intro q e cs xs:
    2<=length xs -> diffs (phase_head q) cs xs ->
    3*(hd O xs+2)=length cs+offset q ->
    run q cs=Some e -> allowed q e ->
    Good (map W1 xs++phase_suffix q).

Lemma diffs_uncons z c cs a b rest:
  diffs z (c::cs) (a::b::rest) ->
  has_difference c a b /\ diffs z cs (b::rest).
Proof. intros H. inverts H. cbn in *. auto. Qed.

Lemma Good_step ws:
  Good ws -> exists ws', reset ws=Some ws' /\ Good ws'.
Proof.
  intros Hgood.
  inversion Hgood as [q e cs xs Hxs Hdiff Hphase Hrun Hallow].
  subst ws.
  destruct xs as [|a [|b rest]]; cbn in Hxs; try lia.
  destruct cs as [|c cs].
  { apply diffs_length in Hdiff. cbn in Hdiff. discriminate. }
  destruct (diffs_uncons _ _ _ _ _ _ Hdiff) as [Hchar Htail].
  cbn in Hphase,Hrun.
  destruct (transition q c) as [[q' p]|] eqn:Ht; try discriminate.
  cbn in Hrun.
  destruct (allowed_extend _ _ _ _ _ Hallow Ht) as [e' [Hep Hall]].
  pose proof (local_certificate _ _ _ _ Ht) as [_ [Hpd Hhead]].
  set (ys:=prefix_values p (phase_head q')).
  exists (map W1 (map (fun x => x+2) (b::rest)++ys)++phase_suffix q').
  split.
  - eapply reset_physical; [exact Ht|].
    apply diffs_length in Hdiff. cbn in Hdiff. lia.
  - eapply Good_intro with (q:=q') (e:=e') (cs:=cs++p).
    + rewrite !length_app,!length_map.
      subst ys. rewrite prefix_values_length.
      pose proof (transition_nonempty _ _ _ _ Ht).
      destruct p; cbn in *; try congruence.
      apply le_n_S. rewrite Nat.add_succ_r.
      apply le_n_S,Nat.le_0_l.
    + eapply diffs_app.
      * apply diffs_add with (k:=2) in Htail. exact Htail.
      * exact Hpd.
      * exact Hhead.
    + change (3*((b+2)+2)=length(cs++p)+offset q').
      rewrite length_app. eapply transition_length; eauto.
    + rewrite run_app,Hrun,Hep. reflexivity.
    + exact Hall.
Qed.

Section ResetSound.
Variable tm:TM.
Variable h1:list(DH0*DH0).
Variable S0:nat*side -> Q*tape.

Hypothesis D1_Inc_spec:
  forall n, segRLs tm h1 h1 (D1 n) (D1 n).
Hypothesis rh_Inc_spec:
  sideRLs tm h1 0inf (D2 2 *> 0inf).
Hypothesis D21_Inc_spec:
  forall n m r,
    sideRLs tm h1 (D2 n *> D1 m *> r) (D1(2+n) *> D2 m *> r).
Hypothesis D22_Inc_spec:
  forall n m r,
    sideRLs tm h1 (D2 n *> D2(1+m) *> r) (D1(2+n) *> D1 m *> r).
Hypothesis D2_rh_Inc_spec:
  forall n, sideRLs tm h1 (D2 n *> 0inf) (D1(2+n) *> 0inf).
Hypothesis Inc_spec:
  forall n r r', sideRLs tm (h1^^3) r r' ->
    S0(S n,r) -[tm]->+ S0(n,r').
Hypothesis Ov_spec:
  forall n m r r', sideRLs tm (h1^^2) r (D1 n *> D1 m *> r') ->
    S0(O,r) -[tm]->+ S0(2+n,D2 m *> r').

Lemma signal_sound ws ws':
  signal ws=Some ws' -> sideRLs tm h1 (words_side ws) (words_side ws').
Proof.
  revert ws'.
  induction ws as [|[n|n] ws IH]; intros ws'; cbn.
  - intros [= <-]. exact rh_Inc_spec.
  - destruct (signal ws) as [ws0|] eqn:E; try discriminate.
    intros [= <-]. cbn.
    change (sideRLs tm h1 (D1 n *> words_side ws)
      (D1 n *> words_side ws0)).
    eapply segRLs_sideRLs_concat; [apply D1_Inc_spec|apply IH; reflexivity].
  - destruct ws as [|[m|m] ws]; cbn.
    + intros [= <-].
      change (sideRLs tm h1 (D2 n *> 0inf) (D1(n+2) *> 0inf)).
      replace (n+2) with (2+n) by lia. apply D2_rh_Inc_spec.
    + intros [= <-].
      change (sideRLs tm h1 (D2 n *> D1 m *> words_side ws)
        (D1(n+2) *> D2 m *> words_side ws)).
      replace (n+2) with (2+n) by lia. apply D21_Inc_spec.
    + destruct m; cbn.
      * discriminate.
      * intros [= <-].
        change (sideRLs tm h1 (D2 n *> D2(S m) *> words_side ws)
          (D1(n+2) *> D1 m *> words_side ws)).
        replace (n+2) with (2+n) by lia. apply D22_Inc_spec.
Qed.

Lemma signals_sound k ws ws':
  signals k ws=Some ws' ->
  sideRLs tm (h1^^k) (words_side ws) (words_side ws').
Proof.
  revert ws ws'.
  induction k as [|k IH]; intros ws ws'; cbn.
  - intros [= <-]. constructor.
  - destruct (signal ws) as [ws0|] eqn:E; try discriminate.
    intros H.
    change (sideRLs tm (h1++h1^^k) (words_side ws) (words_side ws')).
    eapply sideRLs_trans; [apply signal_sound,E|apply IH,H].
Qed.

Lemma countdown n r r':
  sideRLs tm (h1^^(3*n)) r r' -> S0(n,r) -[tm]->* S0(O,r').
Proof.
  revert r r'.
  induction n as [|n IH]; intros r r' H.
  - cbn in H. inverts H. constructor.
  - replace (3*S n) with (3+3*n) in H by lia.
    rewrite lpow_add in H.
    apply sideRLs_split in H as [r0 [H0 H]].
    eapply evstep_trans.
    + apply progress_evstep,Inc_spec,H0.
    + apply IH,H.
Qed.

Lemma machine_reset_sound ws ws':
  reset ws=Some ws' ->
  S0(O,words_side ws) -[tm]->+ S0(O,words_side ws').
Proof.
  unfold reset.
  destruct (signals 2 ws) as [ws0|] eqn:E; try discriminate.
  destruct ws0 as [|[a|a] ws0]; try discriminate.
  destruct ws0 as [|[b|b] ws0]; try discriminate.
  intros H.
  eapply progress_evstep_trans.
  - eapply Ov_spec.
    pose proof (signals_sound 2 ws (W1 a::W1 b::ws0) E) as HE.
    change (sideRLs tm (h1^^2) (words_side ws)
      (D1 a *> D1 b *> words_side ws0)) in HE.
    exact HE.
  - eapply countdown.
    replace (3*(a+2)) with (3*(2+a)) in H by lia.
    pose proof (signals_sound (3*(2+a)) (W2 b::ws0) ws' H) as HH.
    change (sideRLs tm (h1^^(3*(2+a)))
      (D2 b *> words_side ws0) (words_side ws')) in HH.
    exact HH.
Qed.
End ResetSound.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0RF_0LC0RD_1LD1LC_1RE1LB_---1RA_0LF0RC").

Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

Definition h1:list(DH0*DH0) := [((C,<[1;1;0;0]),(C,[]))].

Lemma D1_Inc n: segRLs tm h1 h1 (D1 n) (D1 n).
Proof. esx. Qed.

Lemma rh_Inc: sideRLs tm h1 0inf (D2 2 *> 0inf).
Proof. esx. Qed.

Lemma D21_Inc n m r:
  sideRLs tm h1 (D2 n *> D1 m *> r) (D1(2+n) *> D2 m *> r).
Proof. es' n m & r. Qed.

Lemma D22_Inc n m r:
  sideRLs tm h1 (D2 n *> D2(1+m) *> r) (D1(2+n) *> D1 m *> r).
Proof. es' n m & r. Qed.

Lemma D2_rh_Inc n:
  sideRLs tm h1 (D2 n *> 0inf) (D1(2+n) *> 0inf).
Proof. es' n. Qed.

Definition S' '(n,r) :=
  0inf <* <[1;1;1;1;0] <* <[1;1]^^n
    {{{ (C,<[1;1;0;0],R) }}} r.

Lemma Inc n r r':
  sideRLs tm (h1^^3) r r' -> S'(1+n,r) -->+ S'(n,r').
Proof.
  unfold S'. intros H.
  inverts H. inverts H6. inverts H7. inverts H8.
  follow10 H5. es; er.
  follow100 H4. es; er.
  follow100 H6. es.
Qed.

Lemma Ov n m r r':
  sideRLs tm (h1^^2) r (D1 n *> D1 m *> r') ->
  S'(O,r) -->+ S'(2+n,D2 m *> r').
Proof.
  unfold S'. intros H.
  inverts H. inverts H6. inverts H7.
  follow10 H5. es; er.
  follow100 H4. es' n m & r'.
Qed.

Lemma init: c0 -->* S'(O,(D1 4)^^5 *> 0inf).
Proof. esx. Qed.

Lemma reset_sound ws ws':
  reset ws=Some ws' -> S'(O,words_side ws) -->+ S'(O,words_side ws').
Proof.
  eapply machine_reset_sound; eauto using D1_Inc,rh_Inc,D21_Inc,D22_Inc,
    D2_rh_Inc,Inc,Ov.
Qed.

Definition entry:=map W1 [6;6;6;6]++phase_suffix P12.

Lemma seed: Good entry.
Proof.
  unfold entry.
  eapply Good_intro with
    (q:=P12) (e:=P8) (cs:=[Z0;Z0;Z0;Z0]) (xs:=[6;6;6;6]).
  - cbn; lia.
  - repeat constructor; reflexivity.
  - reflexivity.
  - reflexivity.
  - constructor.
Qed.

Definition State ws:=S'(O,words_side ws).

Lemma init_entry: c0 -->* State entry.
Proof.
  eapply evstep_trans; [exact init|].
  apply progress_evstep.
  change (S'(O,words_side [W1 4;W1 4;W1 4;W1 4;W1 4])
    -->+ S'(O,words_side entry)).
  apply reset_sound. reflexivity.
Qed.

Lemma Good_progress ws:
  Good ws -> exists ws', State ws -->+ State ws' /\ Good ws'.
Proof.
  intros H.
  destruct (Good_step _ H) as [ws' [Hr Hg]].
  exists ws'. split; auto. apply reset_sound,Hr.
Qed.

Lemma macro_nonhalt: ~halts tm (State entry).
Proof.
  eapply (progress_nonhalt_cond tm (list word) entry State Good).
  - exact Good_progress.
  - exact seed.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof. eapply multistep_nonhalt; [exact init_entry|exact macro_nonhalt]. Qed.

Print Assumptions nonhalt.
End TM1.

Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB1LA_1RC1LE_---1RD_1RE0RF_0LA0RB_0LF0RA").

Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

Definition h1:list(DH0*DH0) := [((A,<[1;1;0;0]),(A,[]))].

Lemma D1_Inc n: segRLs tm h1 h1 (D1 n) (D1 n).
Proof. esx. Qed.

Lemma rh_Inc: sideRLs tm h1 0inf (D2 2 *> 0inf).
Proof. esx. Qed.

Lemma D21_Inc n m r:
  sideRLs tm h1 (D2 n *> D1 m *> r) (D1(2+n) *> D2 m *> r).
Proof. es' n m & r. Qed.

Lemma D22_Inc n m r:
  sideRLs tm h1 (D2 n *> D2(1+m) *> r) (D1(2+n) *> D1 m *> r).
Proof. es' n m & r. Qed.

Lemma D2_rh_Inc n:
  sideRLs tm h1 (D2 n *> 0inf) (D1(2+n) *> 0inf).
Proof. es' n. Qed.

Definition S' '(n,r) :=
  0inf <* <[1;1;1;1;0] <* <[1;1]^^n
    {{{ (A,<[1;1;0;0],R) }}} r.

Lemma Inc n r r':
  sideRLs tm (h1^^3) r r' -> S'(1+n,r) -->+ S'(n,r').
Proof.
  unfold S'. intros H.
  inverts H. inverts H6. inverts H7. inverts H8.
  follow10 H5. es; er.
  follow100 H4. es; er.
  follow100 H6. es.
Qed.

Lemma Ov n m r r':
  sideRLs tm (h1^^2) r (D1 n *> D1 m *> r') ->
  S'(O,r) -->+ S'(2+n,D2 m *> r').
Proof.
  unfold S'. intros H.
  inverts H. inverts H6. inverts H7.
  follow10 H5. es; er.
  follow100 H4. es' n m & r'.
Qed.

Lemma init: c0 -->* S'(O,(D1 4)^^5 *> D2 2 *> 0inf).
Proof. esx. Qed.

Lemma reset_sound ws ws':
  reset ws=Some ws' -> S'(O,words_side ws) -->+ S'(O,words_side ws').
Proof.
  eapply machine_reset_sound; eauto using D1_Inc,rh_Inc,D21_Inc,D22_Inc,
    D2_rh_Inc,Inc,Ov.
Qed.

Definition entry:=map W1 [6;6;6;6;6]++phase_suffix P4.

Lemma seed: Good entry.
Proof.
  unfold entry.
  eapply Good_intro with
    (q:=P4) (e:=P22) (cs:=[Z0;Z0;Z0;Z0;P5])
    (xs:=[6;6;6;6;6]).
  - cbn; lia.
  - repeat constructor; reflexivity.
  - reflexivity.
  - reflexivity.
  - constructor.
Qed.

Definition State ws:=S'(O,words_side ws).

Lemma init_entry: c0 -->* State entry.
Proof.
  eapply evstep_trans; [exact init|].
  apply progress_evstep.
  change (S'(O,words_side
    [W1 4;W1 4;W1 4;W1 4;W1 4;W2 2])
    -->+ S'(O,words_side entry)).
  apply reset_sound. reflexivity.
Qed.

Lemma Good_progress ws:
  Good ws -> exists ws', State ws -->+ State ws' /\ Good ws'.
Proof.
  intros H.
  destruct (Good_step _ H) as [ws' [Hr Hg]].
  exists ws'. split; auto. apply reset_sound,Hr.
Qed.

Lemma macro_nonhalt: ~halts tm (State entry).
Proof.
  eapply (progress_nonhalt_cond tm (list word) entry State Good).
  - exact Good_progress.
  - exact seed.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof. eapply multistep_nonhalt; [exact init_entry|exact macro_nonhalt]. Qed.

Print Assumptions nonhalt.
End TM2.

