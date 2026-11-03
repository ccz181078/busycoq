(* 1RB1LA_1LA1RC_1RD0RB_1LE1LD_---1LF_1RA0LF does not halt from the blank tape.

   At its main configurations the tape holds two binary counters, low digit next to the head ([A] marks the head, on the cell to its right):
     ... (1 x2) (1 x1) 1 1 [A] 0 0 0 (d1 d1 0 0 0) (d2 d2 0 0 0) ... 0^inf
   One tick ([tick]) adds 1 to both counters. It is proved for any digits and any tape outside the counters, so any number k of ticks
   that overflows neither counter can be taken at once ([skip_ticks]), also when k has thousands of digits.

   [check] runs a simulator inside the VM that takes raw machine steps and, at such a configuration with enough room, as many ticks as the digits it reads allow ([try_skip]).
   It runs from the blank tape to a configuration X D [A] 0 L 0^inf, then runs again from D [A] 0 L 0^inf with everything before D unreadable, and reaches W D [A] 0 L 0^inf.
   So for every X, X D [A] 0 L 0^inf -->+ X W D [A] 0 L 0^inf, and the machine never halts. The only data in this file are two run lengths and five small constants (thrn, thrv, slack, plen, the 40 cells of start);
   L, D and W are computed in the VM. Measured outside this file: |L| = 497, D = 1011111011, |W| = 156384; the run first reaches this configuration after about 4.0e1384 steps, one period is about 2.4e2695 steps. *)
From BusyCoq Require Import Individual62.
From Coq Require Import NArith Lia String.
From Coq Require Import Lists.List. Import ListNotations.
Set Default Goal Selector "!".

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB1LA_1LA1RC_1RD0RB_1LE1LD_---1LF_1RA0LF"%string).

Notation "c --> c'" := (c -[ tm ]-> c') (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(* Digits, low digit first. A digit d of the first counter is the 5 cells d d 0 0 0 read away from the head,
   a digit x of the second counter is the 2 cells x 1 read away from the head. *)
Definition d2s (d : bool) : Sym := if d then S1 else S0.

Fixpoint W5 (ds : list bool) : list Sym :=
  match ds with
  | [] => []
  | d :: t => d2s d :: d2s d :: S0 :: S0 :: S0 :: W5 t
  end.

Fixpoint W2 (xs : list bool) : list Sym :=
  match xs with
  | [] => []
  | x :: t => d2s x :: S1 :: W2 t
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

Lemma sweep2 : forall xs xs' l r, inc xs = Some xs' ->
  W2 xs *> r <{{A}} l -->* W2 xs' *> r {{B}}> l.
Proof.
  induction xs as [|x t IH]; intros xs' l r H; [discriminate|].
  destruct x; simpl in H.
  - destruct (inc t) as [t'|]; [|discriminate].
    injection H as <-. simpl.
    step. step.
    follow (IH t' (S1 >> S1 >> l) r eq_refl).
    execute.
  - injection H as <-. simpl.
    execute.
Qed.

Lemma zeros_shift : forall k l,
  repeat S0 k *> S0 >> l = S0 >> repeat S0 k *> l.
Proof.
  induction k as [|k IH]; intros l; [reflexivity|].
  simpl. rewrite IH. reflexivity.
Qed.

Lemma clearF : forall k l r,
  repeat S1 k *> r <{{F}} l -->* r <{{F}} repeat S0 k *> l.
Proof.
  induction k as [|k IH]; intros l r.
  - simpl. finish.
  - simpl. step.
    follow (IH (S0 >> l) r).
    rewrite zeros_shift. finish.
Qed.

Lemma walk5 : forall ds ds' k l r, inc ds = Some ds' ->
  repeat S1 k *> S0 >> r {{C}}> W5 ds *> l -->* S0 >> r <{{F}} repeat S0 k *> W5 ds' *> l.
Proof.
  induction ds as [|d t IH]; intros ds' k l r H; [discriminate|].
  destruct d; simpl in H.
  - destruct (inc t) as [t'|]; [|discriminate].
    injection H as <-. simpl.
    do 13 step.
    follow (IH t' (S (S (S (S (S k))))) l r eq_refl).
    simpl. rewrite !zeros_shift. finish.
  - injection H as <-. simpl.
    do 3 step.
    follow clearF.
    finish.
Qed.

(* One tick adds 1 to both counters. l and r are arbitrary. *)
Definition anchor (ds xs : list bool) (l r : side) : Q * tape :=
  S0 >> S1 >> S1 >> W2 xs *> r <{{A}} S0 >> S0 >> W5 ds *> l.

Lemma tick : forall ds ds' xs xs' l r,
  inc ds = Some ds' -> inc xs = Some xs' ->
  anchor ds xs l r -->+ anchor ds' xs' l r.
Proof.
  intros ds ds' xs xs' l r Hd Hx. unfold anchor.
  eapply progress_intro; [prove_step | simpl_tape].
  do 4 step.
  follow (sweep2 xs xs' (S1 >> S1 >> S1 >> S1 >> S0 >> W5 ds *> l) r Hx).
  do 7 step.
  follow (walk5 ds ds' 3 l (S1 >> W2 xs' *> r) Hd).
  simpl. step. finish.
Qed.

(* The counters as numbers: k ticks at once, for any k with no overflow. *)
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

Lemma skip_ticks : forall (k : N) wl wr a b l r,
  a + k < pw wl -> b + k < pw wr ->
  anchor (enc wl a) (enc wr b) l r -->* anchor (enc wl (a + k)) (enc wr (b + k)) l r.
Proof.
  induction k as [|k IH] using N.peano_ind; intros wl wr a b l r Ha Hb.
  - rewrite !N.add_0_r. apply evstep_refl.
  - assert (Ea : a + N.succ k = a + k + 1) by lia.
    assert (Eb : b + N.succ k = b + k + 1) by lia.
    rewrite Ea, Eb in *.
    eapply evstep_trans.
    + apply IH; lia.
    + apply progress_evstep. apply tick; apply inc_enc; lia.
Qed.

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

(* Reading the counters off the lists. Blanks past the end of ll count as digits 0. *)
Definition s2b (s : Sym) : bool := match s with S0 => false | S1 => true end.

Fixpoint parse2 (rr : list Sym) : list bool * list Sym :=
  match rr with
  | x :: S1 :: r' => let '(xs, r2) := parse2 r' in (s2b x :: xs, r2)
  | _ => ([], rr)
  end.

Lemma parse2_ok : forall rr xs r2, parse2 rr = (xs, r2) -> rr = W2 xs ++ r2.
Proof.
  fix IH 1. intros rr xs r2 H.
  destruct rr as [|x [|[|] r']]; simpl in H.
  - injection H as <- <-. reflexivity.
  - injection H as <- <-. reflexivity.
  - injection H as <- <-. reflexivity.
  - destruct (parse2 r') as [t r3] eqn:Hp. injection H as <- <-.
    simpl. rewrite (IH r' t r3 Hp) at 1. destruct x; reflexivity.
Qed.

Definition pad5 (ll : list Sym) : list Sym :=
  match ll with
  | _ :: _ :: _ :: _ :: _ :: _ => ll
  | _ => ll ++ [S0; S0; S0; S0; S0]
  end.

Lemma app_zeros : forall ll, (ll ++ [S0; S0; S0; S0; S0]) *> const S0 = ll *> const S0.
Proof.
  intros ll. rewrite Str_app_assoc. simpl. rewrite <- !const_unfold. reflexivity.
Qed.

Lemma pad5_ok ll : pad5 ll *> const S0 = ll *> const S0.
Proof.
  unfold pad5. destruct ll as [|a [|b [|c [|d [|e t]]]]]; try apply app_zeros; reflexivity.
Qed.

Fixpoint parse5 (n : nat) (ll : list Sym) : list bool * list Sym :=
  match n with
  | O => ([], ll)
  | S m =>
    match pad5 ll with
    | S0 :: S0 :: S0 :: S0 :: S0 :: l2 => let '(ds, l3) := parse5 m l2 in (false :: ds, l3)
    | S1 :: S1 :: S0 :: S0 :: S0 :: l2 => let '(ds, l3) := parse5 m l2 in (true :: ds, l3)
    | _ => ([], ll)
    end
  end.

Lemma parse5_ok : forall n ll ds l3, parse5 n ll = (ds, l3) ->
  ll *> const S0 = W5 ds *> l3 *> const S0.
Proof.
  induction n as [|m IH]; intros ll ds l3 H; simpl in H.
  - injection H as <- <-. reflexivity.
  - pose proof (pad5_ok ll) as Hp.
    destruct (pad5 ll) as [|[|] [|[|] [|[|] [|[|] [|[|] l2]]]]] eqn:Hl;
      try (injection H as <- <-; reflexivity).
    + destruct (parse5 m l2) as [t l4] eqn:Hm. injection H as <- <-.
      rewrite <- Hp. simpl. rewrite (IH l2 t l4 Hm). reflexivity.
    + destruct (parse5 m l2) as [t l4] eqn:Hm. injection H as <- <-.
      rewrite <- Hp. simpl. rewrite (IH l2 t l4 Hm). reflexivity.
Qed.

(* When to skip: only to save time. The soundness lemmas below do not depend on these three values, on ok5 or on top0; the run lengths in check_run do. *)
Definition thrn : nat := 5.
Definition thrv : N := 32.
Definition slack : nat := 2.

Fixpoint ok5 (n : nat) (ll : list Sym) : bool :=
  match n with
  | O => true
  | S m =>
    match pad5 ll with
    | S0 :: S0 :: S0 :: S0 :: S0 :: l2 => ok5 m l2
    | S1 :: S1 :: S0 :: S0 :: S0 :: l2 => ok5 m l2
    | _ => false
    end
  end.

(* Position of the highest digit 0, plus 1. *)
Fixpoint top0 (xs : list bool) : nat :=
  match xs with
  | [] => O
  | x :: t =>
    match top0 t with
    | O => if x then O else 1%nat
    | S n => S (S n)
    end
  end.

(* As many ticks as the digits read here allow. *)
Definition skip_core (ll rr : list Sym) : option (list Sym * list Sym) :=
  if ok5 thrn ll then
    let '(xs, r2) := parse2 rr in
    let bl := top0 xs in
    if Nat.leb bl thrn then None else
    let '(ds, l2) := parse5 (bl + slack) ll in
    let cl := val (map negb ds) in
    if N.ltb cl thrv then None else
    let k := N.min cl (val (map negb xs)) in
    Some (W5 (enc (length ds) (val ds + k)%N) ++ l2, W2 (enc (length xs) (val xs + k)%N) ++ r2)
  else None.

Lemma skip_core_ok : forall ll rr l2 r2 X, skip_core ll rr = Some (l2, r2) ->
  S0 >> S1 >> S1 >> rr *> X <{{A}} S0 >> S0 >> ll *> const S0 -->*
  S0 >> S1 >> S1 >> r2 *> X <{{A}} S0 >> S0 >> l2 *> const S0.
Proof.
  intros ll rr l2 r2 X H. unfold skip_core in H.
  destruct (ok5 thrn ll); [|discriminate].
  destruct (parse2 rr) as [xs r3] eqn:Hr.
  destruct (Nat.leb (top0 xs) thrn); [discriminate|].
  destruct (parse5 (top0 xs + slack) ll) as [ds l3] eqn:Hl.
  destruct (N.ltb (val (map negb ds)) thrv); [discriminate|].
  injection H as <- <-.
  rewrite (parse2_ok _ _ _ Hr), (parse5_ok _ _ _ _ Hl).
  set (k := N.min (val (map negb ds)) (val (map negb xs))).
  pose proof (val_comp ds) as Hd. pose proof (val_comp xs) as Hx.
  assert (Hk1 : (k <= val (map negb ds))%N) by apply N.le_min_l.
  assert (Hk2 : (k <= val (map negb xs))%N) by apply N.le_min_r.
  pose proof (skip_ticks k (length ds) (length xs) (val ds) (val xs) (l3 *> const S0) (r3 *> X)
                ltac:(lia) ltac:(lia)) as Hs.
  rewrite !enc_val in Hs. unfold anchor in Hs.
  rewrite !Str_app_assoc. exact Hs.
Qed.

Definition try_skip (c : Cfg) : Cfg :=
  match c with
  | (A, ll0, S0, S1 :: S1 :: rr) =>
    match pad5 ll0 with
    | S0 :: S0 :: ll =>
      match skip_core ll rr with
      | Some (l2, r2) => (A, S0 :: S0 :: l2, S0, S1 :: S1 :: r2)
      | None => c
      end
    | _ => c
    end
  | _ => c
  end.

Lemma try_skip_ok c X : lift c X -->* lift (try_skip c) X.
Proof.
  destruct c as [[[q ll0] a] rr]. unfold try_skip.
  destruct q; try apply evstep_refl.
  destruct a; try apply evstep_refl.
  destruct rr as [|[|] [|[|] rr]]; try apply evstep_refl.
  pose proof (pad5_ok ll0) as Hp.
  destruct (pad5 ll0) as [|[|] [|[|] ll]]; try apply evstep_refl.
  destruct (skip_core ll rr) as [[l2 r2]|] eqn:Hs; try apply evstep_refl.
  simpl lift. rewrite <- Hp. exact (skip_core_ok _ _ _ _ _ Hs).
Qed.

Definition astep (c : Cfg) : option Cfg := cstep (try_skip c).

Lemma astep_ok c c' X : astep c = Some c' -> lift c X -->+ lift c' X.
Proof.
  intros H. eapply evstep_progress_trans.
  - apply try_skip_ok.
  - apply progress_base. exact (cstep_ok _ _ _ H).
Qed.

Fixpoint runp (p : positive) (c : Cfg) : option Cfg :=
  match p with
  | xH => astep c
  | xO p' =>
    match runp p' c with
    | Some c1 => runp p' c1
    | None => None
    end
  | xI p' =>
    match astep c with
    | Some c0 =>
      match runp p' c0 with
      | Some c1 => runp p' c1
      | None => None
      end
    | None => None
    end
  end.

Lemma runp_ok : forall p c c' X, runp p c = Some c' -> lift c X -->+ lift c' X.
Proof.
  induction p as [p IH|p IH|]; intros c c' X H; simpl in H.
  - destruct (astep c) as [c0|] eqn:H0; [|discriminate].
    destruct (runp p c0) as [c1|] eqn:H1; [|discriminate].
    eapply progress_trans; [exact (astep_ok _ _ _ H0)|].
    eapply progress_trans; [exact (IH _ _ _ H1)|].
    exact (IH _ _ _ H).
  - destruct (runp p c) as [c1|] eqn:H1; [|discriminate].
    eapply progress_trans; [exact (IH _ _ _ H1)|].
    exact (IH _ _ _ H).
  - exact (astep_ok _ _ _ H).
Qed.

(* Equal up to blanks at the far end of ll. *)
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

(* Run f1 from the start to a configuration (l1, r1) in state A reading 0. Keep the first plen cells p of r1, make the rest of r1 unreadable, and run f2.
   If that returns to l1 and its list r2 starts with p, r2 = p ++ q, the machine repeats forever: X becomes q *> X. *)
Definition plen : nat := 10.

Definition check (start : Cfg) (f1 f2 : positive) : bool :=
  match runp f1 start with
  | Some (A, l1, S0, r1) =>
    let p := firstn plen r1 in
    match runp f2 (A, l1, S0, p) with
    | Some (A, l2, S0, r2) =>
      andb (eqz l2 l1) (match strip p r2 with Some _ => true | None => false end)
    | _ => false
    end
  | _ => false
  end.

Lemma check_ok : forall start f1 f2 X0, check start f1 f2 = true -> ~ halts tm (lift start X0).
Proof.
  intros start f1 f2 X0 H. unfold check in H.
  destruct (runp f1 start) as [[[[q1 l1] a1] r1]|] eqn:H1; [|discriminate].
  destruct q1; try discriminate. destruct a1; try discriminate.
  set (p := firstn plen r1) in H.
  destruct (runp f2 (A, l1, S0, p)) as [[[[q2 l2] a2] r2]|] eqn:H2; [|discriminate].
  destruct q2; try discriminate. destruct a2; try discriminate.
  apply andb_prop in H as [Hz Hs].
  destruct (strip p r2) as [q|] eqn:Hq; [|discriminate].
  pose proof (strip_ok _ _ _ Hq) as Hr2.
  pose proof (eqz_ok _ _ Hz) as Hl2.
  apply multistep_nonhalt with (c' := lift (A, l1, S0, r1) X0).
  - apply progress_evstep. exact (runp_ok _ _ _ _ H1).
  - apply progress_nonhalt with (P := fun c => exists X, c = lift (A, l1, S0, p) X).
    + intros c [X ->].
      exists (lift (A, l1, S0, p) (q *> X)). split.
      * exists (q *> X). reflexivity.
      * replace (lift (A, l1, S0, p) (q *> X)) with (lift (A, l2, S0, r2) X).
        -- exact (runp_ok _ _ _ _ H2).
        -- simpl. rewrite Hl2, Hr2, Str_app_assoc. reflexivity.
    + exists (skipn plen r1 *> X0).
      simpl. rewrite <- Str_app_assoc. unfold p. rewrite firstn_skipn. reflexivity.
Qed.

(* 40 cells are enough: the head never goes further on the rr side from the start. *)
Definition start : Cfg := (A, [], S0, repeat S0 40).

Lemma start_c0 : lift start (const S0) = c0.
Proof.
  pose proof (allz_ok (repeat S0 40) eq_refl) as H.
  unfold lift, start, c0, tape0. rewrite H. reflexivity.
Qed.

Lemma check_run : check start 1803709%positive 4366304%positive = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  rewrite <- start_c0. exact (check_ok _ _ _ _ check_run).
Qed.

End TM1.

Print Assumptions TM1.nonhalt.
