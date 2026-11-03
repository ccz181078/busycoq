(* 1RB1LE_0RC1RA_0LD0RB_1LA1LF_0LC1RF_---0LA does not halt from the blank tape.

   [q] marks the head in state q, on the cell to its right. An anchor is
     ... 0 1^a2 x2 0 1^a1 x1 0 [A] 0 1 (0 d1) (0 d2) ... (0 dw) 0 ...
   with a binary counter on the right, low digit first, and on the left a chain of tokens 1^a x 0, a = 2 s + 4.
   A visit of a token enters its last 0 in state E and comes back one cell to the right of it in state C ([Vis]).
   One tick ([tick]) adds 1 to the counter and makes one visit, for any digits with no overflow and any tape outside them.
   A token with x = 1 takes a visit by setting x to 0 and reads nothing else ([token1]). A token with x = 0 takes a visit by turning its run into a counter of s + 1 digits with value 2^s, which makes one visit of the next token;
   then 2^s - 1 ticks fill that counter, each with one visit of the next token, and its overflow restores the run with x = 1 ([token0], through [ticks], for every s).
   So K visits of a chain are numbers handed from token to token ([VS_token]), and K ticks that do not overflow the counter and that the chain can take happen at once ([skip]), also when K has hundreds of digits.

   [check] runs a simulator inside the VM: raw machine steps and, at an anchor, as many ticks as the digits and the chain it reads allow ([skip_core], with limits in the file).
   It runs from the blank tape to a configuration X D [C] 0^inf, then runs again from D [C] 0^inf with everything before D unreadable, and reaches W D [C] 0^inf.
   So for every X, X D [C] 0^inf -->+ X W D [C] 0^inf, and the machine never halts. The only data in this file are two run lengths and six constants (maxchain, minw, bigroom, bsize, plen, the 80 cells of start);
   D and W are computed in the VM. Measured outside this file: |D| = 195, |W| = 442064; the run reaches this configuration after about 1.9e94 steps, one period is about 1.2e87 steps. *)
From BusyCoq Require Import Individual62.
From Coq Require Import NArith Lia String.
From Coq Require Import Lists.List. Import ListNotations.
Set Default Goal Selector "!".

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB1LE_0RC1RA_0LD0RB_1LA1LF_0LC1RF_---0LA"%string).

Notation "c --> c'" := (c -[ tm ]-> c') (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition d2s (d : bool) : Sym := if d then S1 else S0.
Definition s2b (s : Sym) : bool := match s with S0 => false | S1 => true end.

(* The counter right of the anchor, low digit first: each digit d is the 2 cells 0 d. *)
Fixpoint W (ds : list bool) : list Sym :=
  match ds with
  | [] => []
  | d :: t => S0 :: d2s d :: W t
  end.

(* Add 1; None on overflow. *)
Fixpoint inc (ds : list bool) : option (list bool) :=
  match ds with
  | [] => None
  | false :: t => Some (true :: t)
  | true :: t =>
    match inc t with
    | Some t' => Some (false :: t')
    | None => None
    end
  end.

Lemma zeros_shift : forall k l,
  repeat S0 k *> S0 >> l = S0 >> repeat S0 k *> l.
Proof.
  induction k as [|k IH]; intros l; [reflexivity|].
  simpl. rewrite IH. reflexivity.
Qed.

Lemma ones_shift : forall k l,
  repeat S1 k *> S1 >> l = S1 >> repeat S1 k *> l.
Proof.
  induction k as [|k IH]; intros l; [reflexivity|].
  simpl. rewrite IH. reflexivity.
Qed.

Lemma down : forall k l r,
  repeat S1 k *> l {{A}}> S1 >> r -->* l {{A}}> S1 >> repeat S0 k *> r.
Proof.
  induction k as [|k IH]; intros l r.
  - finish.
  - simpl. do 3 step.
    follow (IH l (S0 >> r)).
    rewrite zeros_shift. finish.
Qed.

Lemma W_head : forall t r, exists r', W t *> S0 >> r = S0 >> r'.
Proof. intros [|d t] r; eexists; reflexivity. Qed.

Lemma bump : forall t l r,
  S1 >> l {{A}}> S0 >> S0 >> W t *> S0 >> r -->* l {{A}}> S1 >> S0 >> S1 >> W t *> S0 >> r.
Proof.
  intros t l r. destruct (W_head t r) as [r' E]. rewrite E. execute.
Qed.

Lemma up : forall ds ds' l r, inc ds = Some ds' ->
  S1 >> l {{A}}> W ds *> S0 >> r -->* l {{A}}> S1 >> W ds' *> S0 >> r.
Proof.
  induction ds as [|d t IH]; intros ds' l r H; [discriminate|].
  destruct d; simpl in H.
  - destruct (inc t) as [t'|]; [|discriminate].
    injection H as <-. simpl.
    do 2 step.
    follow (IH t' (S1 >> S1 >> l) r eq_refl).
    do 6 step. finish.
  - injection H as <-. simpl. apply bump.
Qed.

(* A visit: the head enters a 0 cell in state E and comes back one cell to its right in state C.
   P0 and P1 are what lies left of that 0. *)
Definition Vis (P0 P1 : side) : Prop :=
  forall R, P0 {{E}}> S0 >> R -->+ S0 >> P1 {{C}}> R.

(* One tick adds 1 to the counter and makes one visit. r is arbitrary, the cell after the counter must be 0. *)
Lemma tick : forall P0 P1 ds ds' r, Vis P0 P1 -> inc ds = Some ds' ->
  S0 >> P0 {{A}}> S0 >> S1 >> W ds *> S0 >> r -->+ S0 >> P1 {{A}}> S0 >> S1 >> W ds' *> S0 >> r.
Proof.
  intros P0 P1 ds ds' r HV H.
  eapply progress_intro; [prove_step|simpl_tape].
  step.
  follow (up ds ds' (S1 >> S0 >> P0) r H).
  do 4 step.
  destruct (W_head ds' r) as [r' E]. rewrite E.
  eapply evstep_trans; [apply progress_evstep; apply HV|].
  execute.
Qed.

Lemma over : forall n l r,
  l {{A}}> W (repeat true n) *> r -->* repeat S1 (2 * n) *> l {{A}}> r.
Proof.
  induction n as [|n IH]; intros l r.
  - finish.
  - assert (E : repeat S1 (2 * S n) *> l = repeat S1 (2 * n) *> S1 >> S1 >> l).
    { replace (2 * S n) with (S (S (2 * n))) by lia.
      cbn [repeat Str_app]. rewrite !ones_shift. reflexivity. }
    rewrite E. cbn [repeat W d2s Str_app]. do 2 step.
    exact (IH (S1 >> S1 >> l) r).
Qed.

Section Arith.
Local Open Scope N_scope.

Fixpoint val (ds : list bool) : N :=
  match ds with
  | [] => 0
  | d :: t => if d then N.succ_double (val t) else N.double (val t)
  end.

Fixpoint enc (w : nat) (v : N) : list bool :=
  match w with
  | O => []
  | S w' => N.odd v :: enc w' (N.div2 v)
  end.

Definition pw (w : nat) : N := 2 ^ N.of_nat w.

Lemma pw_S w : pw (S w) = 2 * pw w.
Proof. unfold pw. rewrite Nat2N.inj_succ, N.pow_succ_r'. reflexivity. Qed.

Lemma pw_pos w : 0 < pw w.
Proof. unfold pw. apply N.neq_0_lt_0. apply N.pow_nonzero. lia. Qed.

Lemma enc_double w m : enc (S w) (N.double m) = false :: enc w m.
Proof. destruct m; reflexivity. Qed.

Lemma enc_succ_double w m : enc (S w) (N.succ_double m) = true :: enc w m.
Proof. destruct m; reflexivity. Qed.

Lemma double_or v : exists m, v = N.double m \/ v = N.succ_double m.
Proof.
  destruct v as [|[p|p|]].
  - exists 0. left. reflexivity.
  - exists (Npos p). right. reflexivity.
  - exists (Npos p). left. reflexivity.
  - exists 0. right. reflexivity.
Qed.

Lemma inc_enc : forall w v, v + 1 < pw w -> inc (enc w v) = Some (enc w (v + 1)).
Proof.
  induction w as [|w IH]; intros v H.
  - unfold pw in H. simpl in H. lia.
  - rewrite pw_S in H.
    destruct (double_or v) as [m [Hm|Hm]]; subst v;
      rewrite ?N.double_spec, ?N.succ_double_spec in H.
    + rewrite enc_double. simpl inc.
      replace (N.double m + 1) with (N.succ_double m)
        by (rewrite N.double_spec, N.succ_double_spec; lia).
      rewrite enc_succ_double. reflexivity.
    + rewrite enc_succ_double. simpl inc.
      rewrite IH by lia.
      replace (N.succ_double m + 1) with (N.double (m + 1))
        by (rewrite N.double_spec, N.succ_double_spec; lia).
      rewrite enc_double. reflexivity.
Qed.

Lemma enc_val : forall ds, enc (length ds) (val ds) = ds.
Proof.
  induction ds as [|d t IH]; [reflexivity|].
  destruct d; simpl val; simpl length.
  - rewrite enc_succ_double, IH. reflexivity.
  - rewrite enc_double, IH. reflexivity.
Qed.

Lemma val_comp : forall ds, val ds + val (map negb ds) + 1 = pw (length ds).
Proof.
  induction ds as [|d t IH]; [reflexivity|].
  simpl length. rewrite pw_S. rewrite <- IH.
  destruct d; cbn [map val negb]; rewrite ?N.double_spec, ?N.succ_double_spec; lia.
Qed.

Lemma enc_top : forall s, enc (S s) (pw s) = repeat false s ++ [true].
Proof.
  induction s as [|s IH].
  - reflexivity.
  - assert (Ep : pw (S s) = N.double (pw s)) by (rewrite pw_S; symmetry; apply N.double_spec).
    rewrite Ep, enc_double, IH. reflexivity.
Qed.

Lemma enc_ones : forall n, enc n (pw n - 1) = repeat true n.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - assert (Ep : pw (S n) - 1 = N.succ_double (pw n - 1)).
    { rewrite pw_S, N.succ_double_spec. pose proof (pw_pos n). lia. }
    rewrite Ep, enc_succ_double, IH. reflexivity.
Qed.

(* K ticks at once, for any K with no overflow, along any sequence of visits. *)
Lemma ticks : forall (K : N) (st : N -> side) w v r,
  (forall i, i < K -> Vis (st i) (st (i + 1))) -> v + K < pw w ->
  S0 >> st 0 {{A}}> S0 >> S1 >> W (enc w v) *> S0 >> r -->*
  S0 >> st K {{A}}> S0 >> S1 >> W (enc w (v + K)) *> S0 >> r.
Proof.
  induction K as [|K IH] using N.peano_ind; intros st w v r HV Hv.
  - rewrite N.add_0_r. apply evstep_refl.
  - eapply evstep_trans.
    + apply IH.
      * intros i Hi. apply HV. lia.
      * lia.
    + apply progress_evstep.
      replace (N.succ K) with (K + 1) by lia.
      replace (v + (K + 1)) with (v + K + 1) by lia.
      apply tick.
      * apply HV. lia.
      * apply inc_enc. lia.
Qed.

Lemma W_top : forall s r,
  W (repeat false s ++ [true]) *> r = repeat S0 (2 * s) *> S0 >> S1 >> r.
Proof.
  induction s as [|s IH]; intros r.
  - reflexivity.
  - cbn [repeat app W d2s Str_app]. rewrite IH.
    replace (2 * S s)%nat with (S (S (2 * s))) by lia.
    reflexivity.
Qed.

Lemma path1 : forall e Q R,
  S0 >> repeat S1 (S (S (S (S e)))) *> S0 >> Q {{E}}> S0 >> R -->*
  Q {{E}}> S0 >> S1 >> repeat S0 (S e) *> S0 >> S1 >> S0 >> S0 >> R.
Proof.
  intros e Q R. cbn [repeat Str_app]. do 4 step.
  change (S1 >> repeat S1 e *> S0 >> Q) with (repeat S1 (S e) *> S0 >> Q).
  follow (down (S e) (S0 >> Q) (S0 >> S1 >> S0 >> S0 >> R)).
  step. finish.
Qed.

Lemma path2 : forall e Q r,
  S0 >> Q {{C}}> S1 >> repeat S0 (S e) *> S0 >> r -->+ S0 >> Q {{A}}> S0 >> S1 >> repeat S0 e *> S0 >> r.
Proof.
  intros e Q r. cbn [repeat Str_app]. rewrite zeros_shift.
  eapply progress_intro; [prove_step|simpl_tape].
  do 3 step. finish.
Qed.

Lemma over2 : forall s Q R,
  S0 >> Q {{A}}> S0 >> S1 >> W (repeat true (S s)) *> S0 >> S0 >> R -->*
  S0 >> S1 >> repeat S1 (S (S (S (S (2 * s))))) *> S0 >> Q {{C}}> R.
Proof.
  intros s Q R.
  assert (H := over (S s) (S1 >> S1 >> S0 >> Q) (S0 >> S0 >> R)).
  assert (Er : repeat S1 (S (S (S (S (2 * s))))) *> S0 >> Q = repeat S1 (2 * S s) *> S1 >> S1 >> S0 >> Q).
  { replace (2 * S s)%nat with (S (S (2 * s))) by lia. cbn [repeat Str_app]. rewrite !ones_shift. reflexivity. }
  rewrite Er.
  set (T := repeat S1 (2 * S s) *> S1 >> S1 >> S0 >> Q) in *. clearbody T.
  set (U := W (repeat true (S s)) *> S0 >> S0 >> R) in *. clearbody U.
  do 2 step. follow H. do 2 step. finish.
Qed.

(* A token with x = 0, with a run of a = 2 s + 4 ones left of x and a 0 left of the run: 2^s visits of what lies left of that 0 make one visit of the token, and x becomes 1.
   The 2^s visits are one that comes first, then 2^s - 1 ticks of a counter of s + 1 digits that the token itself writes. So this holds for every s. *)
Lemma token0 : forall s (st : N -> side),
  (forall i, i < pw s -> Vis (st i) (st (i + 1))) ->
  Vis (S0 >> repeat S1 (2 * s + 4) *> S0 >> st 0) (S1 >> repeat S1 (2 * s + 4) *> S0 >> st (pw s)).
Proof.
  intros s st HV R.
  pose proof (pw_pos s) as Hp.
  replace (2 * s + 4)%nat with (S (S (S (S (2 * s))))) by lia.
  eapply evstep_progress_trans; [apply path1|].
  eapply progress_trans; [apply HV; lia|].
  rewrite N.add_0_l.
  eapply progress_evstep_trans; [apply path2|].
  rewrite <- W_top, <- enc_top.
  set (K := pw s - 1).
  eapply evstep_trans.
  { apply (ticks K (fun i => st (1 + i)) (S s) (pw s) (S0 >> R)).
    - intros i Hi. replace (1 + (i + 1)) with (1 + i + 1) by lia. apply HV. lia.
    - rewrite pw_S. lia. }
  replace (1 + K) with (pw s) by lia.
  replace (pw s + K) with (pw (S s) - 1) by (rewrite pw_S; lia).
  rewrite enc_ones.
  apply over2.
Qed.

(* A cell 1 takes one visit and reads nothing else. *)
Lemma token1 : forall T, Vis (S1 >> T) (S0 >> T).
Proof.
  intros T R. execute.
Qed.

(* n visits in a row, from P0 to P1. *)
Definition VS (n : N) (P0 P1 : side) : Prop :=
  exists st : N -> side, st 0 = P0 /\ st n = P1 /\ forall i, i < n -> Vis (st i) (st (i + 1)).

Lemma VS_0 : forall P, VS 0 P P.
Proof.
  intros P. exists (fun _ : N => P). repeat split. intros i Hi. lia.
Qed.

Lemma VS_1 : forall T, VS 1 (S1 >> T) (S0 >> T).
Proof.
  intros T. exists (fun i : N => if N.eqb i 0 then S1 >> T else S0 >> T). repeat split.
  intros i Hi. replace i with 0 by lia. apply token1.
Qed.

(* How many of the first n visits find a token with digit x at 0. *)
Definition zz (x : bool) (n : N) : N := N.div2 (if x then n else N.succ n).

Lemma zz_mono : forall x a b, a <= b -> zz x a <= zz x b.
Proof.
  intros x a b H. unfold zz. rewrite !N.div2_div.
  apply N.Div0.div_le_mono. destruct x; lia.
Qed.

Lemma odd_double m : N.odd (N.double m) = false.
Proof. destruct m; reflexivity. Qed.

Lemma odd_succ_double m : N.odd (N.succ_double m) = true.
Proof. destruct m; reflexivity. Qed.

Lemma div2_double m : N.div2 (N.double m) = m.
Proof. destruct m; reflexivity. Qed.

Lemma div2_succ_double m : N.div2 (N.succ_double m) = m.
Proof. destruct m; reflexivity. Qed.

Lemma double_add1 m : N.double m + 1 = N.succ_double m.
Proof. rewrite N.double_spec, N.succ_double_spec. lia. Qed.

Lemma succ_double_add1 m : N.succ_double m + 1 = N.double (m + 1).
Proof. rewrite N.double_spec, N.succ_double_spec. lia. Qed.

(* One more visit of a token: x flips, and a visit that finds 0 counts. *)
Lemma x_step x i : xorb x (N.odd (i + 1)) = negb (xorb x (N.odd i)).
Proof.
  destruct (double_or i) as [m [-> | ->]];
    rewrite ?double_add1, ?succ_double_add1, ?odd_double, ?odd_succ_double; destruct x; reflexivity.
Qed.

Lemma zz_step x i : zz x (i + 1) = if xorb x (N.odd i) then zz x i else zz x i + 1.
Proof.
  unfold zz. rewrite <- !N.add_1_r.
  destruct (double_or i) as [m [-> | ->]]; destruct x;
    rewrite ?odd_double, ?odd_succ_double;
    repeat (rewrite double_add1 || rewrite succ_double_add1);
    rewrite ?div2_double, ?div2_succ_double; reflexivity.
Qed.

(* A chain of tokens: n visits of a token make zz x n * 2^s visits of what lies left of it. *)
Lemma VS_token : forall x s n P0 P1, VS (zz x n * pw s) P0 P1 ->
  VS n (d2s x >> repeat S1 (2 * s + 4) *> S0 >> P0)
       (d2s (xorb x (N.odd n)) >> repeat S1 (2 * s + 4) *> S0 >> P1).
Proof.
  intros x s n P0 P1 [st [H0 [H1 HV]]].
  exists (fun i : N => d2s (xorb x (N.odd i)) >> repeat S1 (2 * s + 4) *> S0 >> st (zz x i * pw s)).
  pose proof (pw_pos s) as Hp.
  repeat split.
  - cbn beta. replace (zz x 0) with 0 by (destruct x; reflexivity).
    rewrite N.mul_0_l, H0. destruct x; reflexivity.
  - cbn beta. rewrite H1. reflexivity.
  - intros i Hi. cbn beta.
    pose proof (zz_mono x (i + 1) n ltac:(lia)) as Hm.
    rewrite x_step, zz_step. rewrite zz_step in Hm.
    destruct (xorb x (N.odd i)); cbn [negb d2s].
    + apply token1.
    + assert (Hl : (zz x i + 1) * pw s <= zz x n * pw s) by (apply N.mul_le_mono_r; exact Hm).
      assert (Hd : (zz x i + 1) * pw s = zz x i * pw s + pw s) by lia.
      rewrite Hd.
      pose proof (token0 s (fun j => st (zz x i * pw s + j))) as H.
      cbn beta in H. rewrite N.add_0_r in H. apply H.
      intros j Hj. rewrite N.add_assoc. apply HV. lia.
Qed.

(* K ticks at once: K visits, K added to the counter. *)
Lemma skip : forall K P0 P1 w v r, VS K P0 P1 -> v + K < pw w ->
  S0 >> P0 {{A}}> S0 >> S1 >> W (enc w v) *> S0 >> r -->*
  S0 >> P1 {{A}}> S0 >> S1 >> W (enc w (v + K)) *> S0 >> r.
Proof.
  intros K P0 P1 w v r [st [H0 [H1 HV]]] Hv. subst P0 P1.
  apply ticks; assumption.
Qed.

(* Multiply by 2^s, and the other way. *)
Fixpoint shl (s : nat) (z : N) : N :=
  match s with
  | O => z
  | S s' => shl s' (N.double z)
  end.

Lemma shl_ok : forall s z, shl s z = z * pw s.
Proof.
  induction s as [|s IH]; intros z.
  - simpl. unfold pw. simpl. lia.
  - simpl shl. rewrite IH, pw_S, N.double_spec. lia.
Qed.

Fixpoint shr (s : nat) (c : N) : N :=
  match s with
  | O => c
  | S s' => shr s' (N.div2 c)
  end.

End Arith.

(* A concrete configuration (state, list ll, symbol under the head, list rr), each list read away from the head:
   blank beyond ll, an arbitrary stream X beyond rr. *)
Definition Cfg : Type := (Q * list Sym * Sym * list Sym)%type.

Definition lift (c : Cfg) (X : side) : Q * tape :=
  match c with (q, ll, a, rr) => (q, (rr *> X, a, ll *> const S0)) end.

(* One machine step. Fails if it would read X. *)
Definition cstep (c : Cfg) : option Cfg :=
  match c with
  | (q, ll, a, rr) =>
    match tm (q, a) with
    | None => None
    | Some (w, R, q2) =>
      match ll with
      | [] => Some (q2, [], S0, w :: rr)
      | b :: l' => Some (q2, l', b, w :: rr)
      end
    | Some (w, L, q2) =>
      match rr with
      | [] => None
      | b :: r' => Some (q2, w :: ll, b, r')
      end
    end
  end.

Lemma cstep_ok c c' X : cstep c = Some c' -> lift c X --> lift c' X.
Proof.
  destruct c as [[[q ll] a] rr]. unfold cstep.
  destruct (tm (q, a)) as [[[w d0] q2]|] eqn:Ht; intros H; [|discriminate].
  destruct d0.
  - destruct rr as [|b r']; [discriminate|].
    injection H as <-. exact (step_left Ht).
  - destruct ll as [|b l']; injection H as <-; exact (step_right Ht).
Qed.

Lemma cstep_then c c1 c' X :
  cstep c = Some c1 -> lift c1 X -->* lift c' X -> lift c X -->* lift c' X.
Proof.
  intros H1 H2. eapply evstep_step; [exact (cstep_ok _ _ _ H1)|exact H2].
Qed.

(* Reading the cells. *)
Fixpoint pairs (t : list Sym) : option (nat * list Sym) :=
  match t with
  | S0 :: t1 => Some (O, t1)
  | S1 :: S1 :: t' =>
    match pairs t' with
    | Some (s, t1) => Some (S s, t1)
    | None => None
    end
  | _ => None
  end.

Lemma pairs_ok : forall t s t1, pairs t = Some (s, t1) -> t = repeat S1 (2 * s) ++ S0 :: t1.
Proof.
  fix IH 1. intros t s t1 H.
  destruct t as [|a t]; [discriminate|].
  destruct a; simpl in H.
  - injection H as <- <-. reflexivity.
  - destruct t as [|b t']; [discriminate|].
    destruct b; [discriminate|].
    destruct (pairs t') as [[s' t2]|] eqn:Hp; [|discriminate].
    injection H as <- <-. rewrite (IH _ _ _ Hp).
    replace (2 * S s') with (S (S (2 * s'))) by lia. reflexivity.
Qed.

Definition parse_tok (r1 : list Sym) : option (nat * list Sym) :=
  match r1 with
  | S1 :: S1 :: S1 :: S1 :: t0 => pairs t0
  | _ => None
  end.

Lemma parse_tok_ok : forall r1 s t1, parse_tok r1 = Some (s, t1) ->
  r1 = repeat S1 (2 * s + 4) ++ S0 :: t1.
Proof.
  intros r1 s t1 H.
  destruct r1 as [|[|] [|[|] [|[|] [|[|] t0]]]]; try discriminate.
  simpl in H. rewrite (pairs_ok _ _ _ H).
  replace (2 * s + 4) with (S (S (S (S (2 * s))))) by lia. reflexivity.
Qed.

Fixpoint addones (n : nat) (l : list Sym) : list Sym :=
  match n with
  | O => l
  | S n' => addones n' (S1 :: l)
  end.

Lemma addones_ok : forall n l Q, addones n l *> Q = repeat S1 n *> l *> Q.
Proof.
  induction n as [|n IH]; intros l Q; [reflexivity|].
  simpl addones. rewrite IH. cbn [repeat Str_app]. rewrite ones_shift. reflexivity.
Qed.

(* n visits of the chain at rr. Left: rr afterwards. Right: how many visits the chain can take, as far as m tokens read tell. Only Left is used for proofs. *)
Fixpoint visits (m : nat) (n : N) (rr : list Sym) : list Sym + N :=
  match n with
  | N0 => inl rr
  | Npos p =>
    match m with
    | O => inr N0
    | S m' =>
      match rr with
      | [] => inr N0
      | x :: r1 =>
        match x, p with
        | S1, xH => inl (S0 :: r1)
        | _, _ =>
          match parse_tok r1 with
          | None => inr (match x with S0 => N0 | S1 => 1%N end)
          | Some (s, t1) =>
            match visits m' (shl s (zz (s2b x) (Npos p))) t1 with
            | inl t2 => inl (d2s (xorb (s2b x) (N.odd (Npos p))) :: addones (2 * s + 4) (S0 :: t2))
            | inr c =>
              inr (match x with
                   | S0 => N.double (shr s c)
                   | S1 => N.succ_double (shr s c)
                   end)
            end
          end
        end
      end
    end
  end.

Lemma visits_ok : forall m n rr rr' Q, visits m n rr = inl rr' -> VS n (rr *> Q) (rr' *> Q).
Proof.
  induction m as [|m IH]; intros n rr rr' Q H.
  - destruct n as [|p]; simpl in H; [|discriminate].
    injection H as <-. apply VS_0.
  - destruct n as [|p]; cbn [visits] in H.
    { injection H as <-. apply VS_0. }
    destruct rr as [|x r1]; [discriminate|].
    destruct x, p as [o|o|];
    [ destruct (parse_tok r1) as [[s t1]|] eqn:Ht; [|discriminate];
      lazymatch type of H with
      | context [visits m ?a t1] => destruct (visits m a t1) as [t2|c] eqn:Hv; [|discriminate]
      end;
      injection H as <-;
      rewrite (parse_tok_ok _ _ _ Ht);
      cbn [Str_app]; rewrite addones_ok, Str_app_assoc; cbn [Str_app];
      pose proof (IH _ _ _ Q Hv) as Hi; rewrite shl_ok in Hi;
      exact (VS_token _ s _ _ _ Hi) ..
    | injection H as <-; apply VS_1 ].
Qed.

(* How many ticks: room if the chain takes that many, else what it takes. *)
Definition pick (m : nat) (room : N) (rr1 : list Sym) : option (N * list Sym) :=
  match visits m room rr1 with
  | inl rr2 => Some (room, rr2)
  | inr c =>
    match N.min c room with
    | N0 => None
    | Npos k =>
      match visits m (Npos k) rr1 with
      | inl rr2 => Some (Npos k, rr2)
      | inr _ => None
      end
    end
  end.

Lemma pick_ok : forall m room rr1 K rr2 Q, pick m room rr1 = Some (K, rr2) ->
  (K <= room)%N /\ VS K (rr1 *> Q) (rr2 *> Q).
Proof.
  intros m room rr1 K rr2 Q H. unfold pick in H.
  destruct (visits m room rr1) as [r2|c] eqn:Hv.
  - injection H as <- <-. split; [lia|]. exact (visits_ok _ _ _ _ _ Hv).
  - pose proof (N.le_min_r c room) as Hm.
    destruct (N.min c room) as [|k] eqn:Hk; [discriminate|].
    destruct (visits m (Npos k) rr1) as [r2|c2] eqn:Hv2; [|discriminate].
    injection H as <- <-. split; [exact Hm|]. exact (visits_ok _ _ _ _ _ Hv2).
Qed.

Lemma d2s_s2b x : d2s (s2b x) = x.
Proof. destruct x; reflexivity. Qed.

(* The digits right of the anchor. Each digit is followed by a 0 cell or by the end of the list (blanks). *)
Fixpoint parseW (ll : list Sym) : list bool * list Sym :=
  match ll with
  | S0 :: b :: t =>
    match t with
    | [] => ([s2b b], [])
    | S0 :: _ => let '(ds, r) := parseW t in (s2b b :: ds, r)
    | S1 :: _ => ([], ll)
    end
  | _ => ([], ll)
  end.

Lemma parseW_ok' : forall n ll ds r, length ll <= n -> parseW ll = (ds, r) -> ll = W ds ++ r.
Proof.
  induction n as [|n IH]; intros ll ds r Hn H.
  - destruct ll; [|simpl in Hn; lia]. simpl in H. injection H as <- <-. reflexivity.
  - destruct ll as [|a [|b t]].
    + simpl in H. injection H as <- <-. reflexivity.
    + destruct a; simpl in H; injection H as <- <-; reflexivity.
    + destruct a; [|simpl in H; injection H as <- <-; reflexivity].
      destruct t as [|c t'].
      * simpl in H. injection H as <- <-. cbn. rewrite d2s_s2b. reflexivity.
      * destruct c; [|simpl in H; injection H as <- <-; reflexivity].
        change ((let '(ds', r') := parseW (S0 :: t') in (s2b b :: ds', r')) = (ds, r)) in H.
        destruct (parseW (S0 :: t')) as [t2 r2] eqn:Hp. injection H as <- <-.
        cbn [W app]. rewrite d2s_s2b, <- (IH (S0 :: t') t2 r2 ltac:(simpl in *; lia) Hp). reflexivity.
Qed.

Lemma parseW_ok ll ds r : parseW ll = (ds, r) -> ll = W ds ++ r.
Proof. apply (parseW_ok' (length ll)). lia. Qed.

(* Equal up to blanks at the far end of the lists. *)
Fixpoint allz (l : list Sym) : bool :=
  match l with
  | [] => true
  | S0 :: t => allz t
  | S1 :: _ => false
  end.

Fixpoint eqz (l1 l2 : list Sym) : bool :=
  match l1, l2 with
  | [], _ => allz l2
  | _, [] => allz l1
  | S0 :: t1, S0 :: t2 => eqz t1 t2
  | S1 :: t1, S1 :: t2 => eqz t1 t2
  | _, _ => false
  end.

Lemma allz_ok : forall l, allz l = true -> l *> const S0 = const S0.
Proof.
  induction l as [|[|] t IH]; intros H; simpl in *; try discriminate; [reflexivity|].
  rewrite IH by exact H. symmetry. apply const_unfold.
Qed.

Lemma eqz_ok : forall l1 l2, eqz l1 l2 = true -> l1 *> const S0 = l2 *> const S0.
Proof.
  induction l1 as [|a t1 IH]; intros l2 H.
  - simpl in H. rewrite (allz_ok _ H). reflexivity.
  - destruct l2 as [|b t2].
    + destruct a; [exact (allz_ok (S0 :: t1) H) | exact (allz_ok (S1 :: t1) H)].
    + destruct a, b; simpl in H; try discriminate; simpl; rewrite (IH _ H); reflexivity.
Qed.

(* m, minw and bigroom below only say when to skip: the soundness lemmas do not depend on them. The run lengths in check_run do. *)

(* At the end of the list the counter can grow, and the chain alone limits the ticks. *)
Definition skip_end (m minw : nat) (bigroom : N) (ds : list bool) (ll1 rr1 : list Sym) : option (list Sym * list Sym) :=
  if Nat.ltb (length ds) minw then None else
  match pick m bigroom rr1 with
  | Some (K, rr2) =>
    let w2 := S (N.size_nat (val ds + K)) in
    if eqz ll1 (W (enc w2 (val ds))) then Some (W (enc w2 (val ds + K)), rr2) else None
  | None => None
  end.

(* Before an obstacle the room in the digits read is a limit too. *)
Definition skip_mid (m : nat) (ds : list bool) (r rr1 : list Sym) : option (list Sym * list Sym) :=
  match val (map negb ds) with
  | N0 => None
  | Npos o =>
    match pick m (Npos o) rr1 with
    | Some (K, rr2) => Some (W (enc (length ds) (val ds + K)%N) ++ r, rr2)
    | None => None
    end
  end.

Definition skip_core (m minw : nat) (bigroom : N) (ll1 rr1 : list Sym) : option (list Sym * list Sym) :=
  let '(ds, r) := parseW ll1 in
  match r with
  | S1 :: _ => None
  | S0 :: _ :: _ => skip_mid m ds r rr1
  | _ => skip_end m minw bigroom ds ll1 rr1
  end.

Lemma size_lt : forall n, (n < pw (S (N.size_nat n)))%N.
Proof.
  assert (H : forall p, (Npos p < pw (Pos.size_nat p))%N).
  { induction p as [p IH|p IH|].
    - cbn [Pos.size_nat]. rewrite pw_S. change (Npos (xI p)) with (N.succ_double (Npos p)). rewrite N.succ_double_spec. lia.
    - cbn [Pos.size_nat]. rewrite pw_S. change (Npos (xO p)) with (N.double (Npos p)). rewrite N.double_spec. lia.
    - cbn [Pos.size_nat]. reflexivity. }
  intros [|p].
  - reflexivity.
  - rewrite pw_S. cbn [N.size_nat]. specialize (H p). lia.
Qed.

Lemma skip_end_ok : forall m minw bigroom ds ll1 rr1 l2 r2 X,
  skip_end m minw bigroom ds ll1 rr1 = Some (l2, r2) ->
  lift (A, S1 :: ll1, S0, S0 :: rr1) X -->* lift (A, S1 :: l2, S0, S0 :: r2) X.
Proof.
  intros m minw bigroom ds ll1 rr1 l2 r2 X H. unfold skip_end in H.
  destruct (Nat.ltb (length ds) minw); [discriminate|].
  destruct (pick m bigroom rr1) as [[K rr2]|] eqn:Hk; [|discriminate].
  cbv zeta in H.
  destruct (eqz ll1 (W (enc (S (N.size_nat (val ds + K))) (val ds)))) eqn:He; [|discriminate].
  injection H as <- <-.
  destruct (pick_ok _ _ _ _ _ X Hk) as [_ HV].
  pose proof (size_lt (val ds + K)) as Hs.
  pose proof (eqz_ok _ _ He) as Hz.
  pose proof (skip _ _ _ (S (N.size_nat (val ds + K))) (val ds) (const S0) HV Hs) as Hr.
  cbn [lift Str_app]. rewrite Hz.
  rewrite const_unfold. simpl.
  rewrite <- const_unfold in *. exact Hr.
Qed.

Lemma skip_mid_ok : forall m ds b r' rr1 l2 r2 X,
  skip_mid m ds (S0 :: b :: r') rr1 = Some (l2, r2) ->
  lift (A, S1 :: (W ds ++ S0 :: b :: r'), S0, S0 :: rr1) X -->* lift (A, S1 :: l2, S0, S0 :: r2) X.
Proof.
  intros m ds b r' rr1 l2 r2 X H. unfold skip_mid in H.
  destruct (val (map negb ds)) as [|o] eqn:Hroom; [discriminate|].
  destruct (pick m (Npos o) rr1) as [[K rr2]|] eqn:Hk; [|discriminate].
  injection H as <- <-.
  destruct (pick_ok _ _ _ _ _ X Hk) as [Hle HV].
  pose proof (val_comp ds) as Hc. rewrite Hroom in Hc.
  assert (Hlt : (val ds + K < pw (length ds))%N) by lia.
  pose proof (skip _ _ _ (length ds) (val ds) (b >> r' *> const S0) HV Hlt) as Hr.
  rewrite enc_val in Hr.
  cbn [lift Str_app]. rewrite !Str_app_assoc. cbn [Str_app]. exact Hr.
Qed.

Lemma skip_core_ok : forall m minw bigroom ll1 rr1 l2 r2 X, skip_core m minw bigroom ll1 rr1 = Some (l2, r2) ->
  lift (A, S1 :: ll1, S0, S0 :: rr1) X -->* lift (A, S1 :: l2, S0, S0 :: r2) X.
Proof.
  intros m minw bigroom ll1 rr1 l2 r2 X H. unfold skip_core in H.
  destruct (parseW ll1) as [ds r] eqn:Hp.
  destruct r as [|[|] [|b r']].
  - exact (skip_end_ok _ _ _ _ _ _ _ _ _ H).
  - exact (skip_end_ok _ _ _ _ _ _ _ _ _ H).
  - rewrite (parseW_ok _ _ _ Hp). exact (skip_mid_ok _ _ _ _ _ _ _ _ H).
  - discriminate.
  - discriminate.
Qed.

(* Raw steps, one per unit of n, with a try at a skip before each step in state A on a 0 with a 0 on its left and a 1 on its right. *)
Section Burst.
Variables (m minw : nat) (bigroom : N).

Fixpoint burst (n : nat) (q : Q) (ll : list Sym) (a : Sym) (rr : list Sym) {struct n} : option Cfg :=
  match n with
  | O => Some (q, ll, a, rr)
  | S n =>
    match q with
    | A =>
      match a with
      | S0 =>
        match ll with
        | [] => burst n B [] S0 (S1 :: rr)
        | S0 :: l' => burst n B l' S0 (S1 :: rr)
        | S1 :: l' =>
          match rr with
          | S0 :: rr1 =>
            match skip_core m minw bigroom l' rr1 with
            | Some (l2, r2) => burst n B l2 S1 (S1 :: S0 :: r2)
            | None => burst n B l' S1 (S1 :: rr)
            end
          | _ => burst n B l' S1 (S1 :: rr)
          end
        end
      | S1 => match rr with [] => None | b :: r' => burst n E (S1 :: ll) b r' end
      end
    | B =>
      match a with
      | S0 => match ll with [] => burst n C [] S0 (S0 :: rr) | b :: l' => burst n C l' b (S0 :: rr) end
      | S1 => match ll with [] => burst n A [] S0 (S1 :: rr) | b :: l' => burst n A l' b (S1 :: rr) end
      end
    | C =>
      match a with
      | S0 => match rr with [] => None | b :: r' => burst n D (S0 :: ll) b r' end
      | S1 => match ll with [] => burst n B [] S0 (S0 :: rr) | b :: l' => burst n B l' b (S0 :: rr) end
      end
    | D =>
      match a with
      | S0 => match rr with [] => None | b :: r' => burst n A (S1 :: ll) b r' end
      | S1 => match rr with [] => None | b :: r' => burst n F (S1 :: ll) b r' end
      end
    | E =>
      match a with
      | S0 => match rr with [] => None | b :: r' => burst n C (S0 :: ll) b r' end
      | S1 => match ll with [] => burst n F [] S0 (S1 :: rr) | b :: l' => burst n F l' b (S1 :: rr) end
      end
    | F =>
      match a with
      | S0 => None
      | S1 => match rr with [] => None | b :: r' => burst n A (S0 :: ll) b r' end
      end
    end
  end.

Lemma burst_ok : forall n q ll a rr c' X, burst n q ll a rr = Some c' ->
  lift (q, ll, a, rr) X -->* lift c' X.
Proof.
  induction n as [|n IH]; intros q ll a rr c' X H; cbn [burst] in H.
  - injection H as <-. apply evstep_refl.
  - destruct q, a;
    (* a move left *)
    try (destruct rr as [|b r']; [discriminate|];
         eapply cstep_then; [reflexivity|exact (IH _ _ _ _ _ _ H)]);
    (* a move right *)
    try (destruct ll as [|b l'];
         (eapply cstep_then; [reflexivity|exact (IH _ _ _ _ _ _ H)]));
    try discriminate.
    (* state A on 0 *)
    destruct ll as [|[|] l'];
      try (eapply cstep_then; [reflexivity|exact (IH _ _ _ _ _ _ H)]).
    destruct rr as [|[|] rr1];
      try (eapply cstep_then; [reflexivity|exact (IH _ _ _ _ _ _ H)]).
    destruct (skip_core m minw bigroom l' rr1) as [[l2 r2]|] eqn:Hs;
      try (eapply cstep_then; [reflexivity|exact (IH _ _ _ _ _ _ H)]).
    eapply evstep_trans; [exact (skip_core_ok _ _ _ _ _ _ _ _ Hs)|].
    eapply cstep_then; [reflexivity|exact (IH _ _ _ _ _ _ H)].
Qed.

End Burst.

(* When to skip: only to save time. The soundness lemmas do not depend on these three values, the run lengths in check_run do. *)
Definition maxchain : nat := 1000.
Definition minw : nat := 2.
Definition bigroom : N := 2 ^ 400.

Definition bcfg (n : nat) (c : Cfg) : option Cfg :=
  match c with (q, ll, a, rr) => burst maxchain minw bigroom n q ll a rr end.

Lemma bcfg_ok n c c' X : bcfg n c = Some c' -> lift c X -->* lift c' X.
Proof. destruct c as [[[q ll] a] rr]. apply burst_ok. Qed.

Definition bsize : nat := 4096.

Fixpoint runp (p : positive) (c : Cfg) : option Cfg :=
  match p with
  | xH => bcfg bsize c
  | xO p' =>
    match runp p' c with
    | Some c1 => runp p' c1
    | None => None
    end
  | xI p' =>
    match bcfg bsize c with
    | Some c0 =>
      match runp p' c0 with
      | Some c1 => runp p' c1
      | None => None
      end
    | None => None
    end
  end.

Lemma runp_ok : forall p c c' X, runp p c = Some c' -> lift c X -->* lift c' X.
Proof.
  induction p as [p IH|p IH|]; intros c c' X H; simpl in H.
  - destruct (bcfg bsize c) as [c0|] eqn:H0; [|discriminate].
    destruct (runp p c0) as [c1|] eqn:H1; [|discriminate].
    eapply evstep_trans; [exact (bcfg_ok _ _ _ _ H0)|].
    eapply evstep_trans; [exact (IH _ _ _ H1)|].
    exact (IH _ _ _ H).
  - destruct (runp p c) as [c1|] eqn:H1; [|discriminate].
    eapply evstep_trans; [exact (IH _ _ _ H1)|].
    exact (IH _ _ _ H).
  - exact (bcfg_ok _ _ _ _ H).
Qed.

(* Exactly F units of raw steps. *)
Definition runN (F : N) (c : Cfg) : option Cfg :=
  match (match (F / N.of_nat bsize)%N with N0 => Some c | Npos p => runp p c end) with
  | Some c2 => bcfg (N.to_nat (F mod N.of_nat bsize)) c2
  | None => None
  end.

Lemma runN_ok F c c' X : runN F c = Some c' -> lift c X -->* lift c' X.
Proof.
  unfold runN. intros H.
  destruct (F / N.of_nat bsize)%N as [|p].
  - exact (bcfg_ok _ _ _ _ H).
  - destruct (runp p c) as [c2|] eqn:H2; [|discriminate].
    eapply evstep_trans; [exact (runp_ok _ _ _ _ H2)|].
    exact (bcfg_ok _ _ _ _ H).
Qed.

Fixpoint strip (p rr : list Sym) : option (list Sym) :=
  match p with
  | [] => Some rr
  | S0 :: p' => match rr with S0 :: r' => strip p' r' | _ => None end
  | S1 :: p' => match rr with S1 :: r' => strip p' r' | _ => None end
  end.

Lemma strip_ok : forall p rr q, strip p rr = Some q -> rr = p ++ q.
Proof.
  induction p as [|[|] p IH]; intros rr q H; simpl in H.
  - injection H as <-. reflexivity.
  - destruct rr as [|[|] r']; try discriminate. simpl. rewrite (IH _ _ H). reflexivity.
  - destruct rr as [|[|] r']; try discriminate. simpl. rewrite (IH _ _ H). reflexivity.
Qed.

(* Run f1 from the start to a configuration (l1, r1) in state C reading 0. Keep the first plen cells p of r1, make the rest of r1 unreadable, take one step and run f2.
   If that returns to l1, up to blanks at its far end, and its list r2 starts with p, r2 = p ++ q, the machine repeats forever: X becomes q *> X. *)
Definition plen : nat := 195.

Definition check (start : Cfg) (f1 f2 : N) : bool :=
  match runN f1 start with
  | Some (C, l1, S0, r1) =>
    let p := firstn plen r1 in
    match cstep (C, l1, S0, p) with
    | Some c2 =>
      match runN f2 c2 with
      | Some (C, l2, S0, r2) =>
        andb (eqz l2 l1) (match strip p r2 with Some _ => true | None => false end)
      | _ => false
      end
    | None => false
    end
  | _ => false
  end.

Lemma check_ok : forall start f1 f2 X0, check start f1 f2 = true -> ~ halts tm (lift start X0).
Proof.
  intros start f1 f2 X0 H. unfold check in H.
  destruct (runN f1 start) as [[[[q1 l1] a1] r1]|] eqn:H1; [|discriminate].
  destruct q1; try discriminate. destruct a1; try discriminate.
  set (p := firstn plen r1) in H.
  destruct (cstep (C, l1, S0, p)) as [c2|] eqn:Hc; [|discriminate].
  destruct (runN f2 c2) as [[[[q2 l2] a2] r2]|] eqn:H2; [|discriminate].
  destruct q2; try discriminate. destruct a2; try discriminate.
  apply andb_prop in H as [Hz Hs].
  destruct (strip p r2) as [q|] eqn:Hq; [|discriminate].
  pose proof (strip_ok _ _ _ Hq) as Hr2.
  pose proof (eqz_ok _ _ Hz) as Hl2.
  apply multistep_nonhalt with (c' := lift (C, l1, S0, r1) X0).
  - exact (runN_ok _ _ _ _ H1).
  - apply progress_nonhalt with (P := fun c => exists X, c = lift (C, l1, S0, p) X).
    + intros c [X ->].
      exists (lift (C, l1, S0, p) (q *> X)). split.
      * exists (q *> X). reflexivity.
      * replace (lift (C, l1, S0, p) (q *> X)) with (lift (C, l2, S0, r2) X).
        -- eapply progress_intro; [exact (cstep_ok _ _ _ Hc)|].
           exact (runN_ok _ _ _ _ H2).
        -- simpl. rewrite Hl2, Hr2, Str_app_assoc. reflexivity.
    + exists (skipn plen r1 *> X0).
      simpl. rewrite <- Str_app_assoc. unfold p. rewrite firstn_skipn. reflexivity.
Qed.

(* 80 cells are enough: on the rr side the head stays within 76 cells of the start. *)
Definition start : Cfg := (A, [], S0, repeat S0 80).

Lemma start_c0 : lift start (const S0) = c0.
Proof.
  pose proof (allz_ok (repeat S0 80) eq_refl) as H.
  unfold lift, start, c0, tape0. rewrite H. reflexivity.
Qed.

Lemma check_run : check start 126519664%N 51236735%N = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  rewrite <- start_c0. exact (check_ok _ _ _ _ check_run).
Qed.

End TM1.

Print Assumptions TM1.nonhalt.
