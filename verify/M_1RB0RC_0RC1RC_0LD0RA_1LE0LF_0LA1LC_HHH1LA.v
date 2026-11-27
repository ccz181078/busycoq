(** * 1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA (bbchallenge 65826) does not halt

    The machine goes from blank tape to [Cyc 16797709], and from [Cyc (65 + 2 x)] to
    [Cyc (65 + 2 (x + 160521464))] for every [x], where

      [Cyc r = E> 0 (1011001)^59 1011 00000 1101100110110 (011)^16 001101100110 (011)^r]

    (blank on both sides, the head on the first cell written).  Both facts are runs of the verified symbolic
    executor of Part 1 ([arrive_run]: 5,037,044 moves; [period_run]: 5,581,714 moves with the count of the
    last block [65 + 2 x], [x] free), evaluated by [vm_compute] and turned into statements about the machine by
    the soundness theorem of the executor.  The tables of the executor (31 shift rules, 12 cycle rules) are
    checked in Part 2: a shift rule by simulating the machine on its window, a cycle rule by a run of the
    executor without cycle rules. *)


From Coq Require Import Lists.List NArith Lia Bool. Import ListNotations.
From BusyCoq Require Export Individual62.
Set Default Goal Selector "!".
Require Coq.Strings.String. Import String.StringSyntax.

(** * Part 1: a verified symbolic executor with binary counts

    A configuration is two lists of tokens (nearest cell first on both sides, so the words of the left side are
    stored reversed) and a state; the head reads the first cell of the right side.  A token is a cell or a block:
    a word repeated [c + a0 x0 + a1 x1 + ...] times, the [xi] free; the numbers are binary ([N]).
    [den rho S] is the configuration of the Turing machine that [S] stands for when [xi = rho i].

    One move of the executor ([move]) is

    - a shift rule from a table ([crossWith]): a block next to the head is crossed in one go, with a carried
      word, [k] copies at a time (the count is divided, which must be possible for every value of the variables);
    - otherwise one machine step ([stepS]); a block is opened only when its count is surely at least 1;
    - and when that step brings the event state to the left end of the tape, the right side is re-bracketed
      ([norm]) and a table of cycle rules is tried ([tryRules]): a rule is a template of the whole tape with
      counts [b0 + M xi] that comes back as the same template with counts [b1 + M xi]; it is applied [n] times
      at once, [n] itself a count.

    Any step whose outcome would depend on a variable makes the executor return [None].

    The soundness theorem is [run_sound]: if [run T K S = Some S'] and the tables are valid ([TblOK]), then for
    every [rho] the machine goes from [den rho S] to [den rho S'].  The executor's strategy (which rule, how the
    tape is re-bracketed, how many times a rule is applied) is not trusted: every case of every function is
    covered by the proof.  Nothing here is specific to one machine: the machine, the event state and the two
    strategy parameters are section variables. *)


Close Scope sym.
Local Open Scope N_scope.

(** ** Equality tests *)

Definition symb (a b : sym) : bool :=
  match a, b with S0, S0 | S1, S1 => true | _, _ => false end.

Lemma symb_eq : forall a b, symb a b = true -> a = b.
Proof. destruct a, b; simpl; congruence. Qed.

Fixpoint weqb (u v : list sym) : bool :=
  match u, v with
  | [], [] => true
  | a :: u', b :: v' => symb a b && weqb u' v'
  | _, _ => false
  end.

Lemma weqb_eq : forall u v, weqb u v = true -> u = v.
Proof.
  induction u as [|a u IH]; destruct v as [|b v]; simpl; try congruence.
  intros H. apply andb_true_iff in H. destruct H as [H1 H2].
  apply symb_eq in H1. apply IH in H2. congruence.
Qed.

Definition qeqb (a b : state) : bool :=
  match a, b with A, A | B, B | C, C | D, D | E, E | F, F => true | _, _ => false end.

Lemma qeqb_eq : forall a b, qeqb a b = true -> a = b.
Proof. destruct a, b; simpl; congruence. Qed.

(** ** Counts *)

Record Cnt := mkC { cc : N; ca : list N }.

Fixpoint dot (a : list N) (rho : nat -> N) : N :=
  match a with
  | [] => 0
  | x :: a' => x * rho O + dot a' (fun i => rho (S i))
  end.

Definition ev (rho : nat -> N) (n : Cnt) : N := cc n + dot (ca n) rho.

Fixpoint addL (xs ys : list N) : list N :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x :: xs', y :: ys' => (x + y) :: addL xs' ys'
  end.

Lemma dot_addL : forall xs ys rho, dot (addL xs ys) rho = dot xs rho + dot ys rho.
Proof.
  induction xs as [|x xs IH]; intros ys rho; simpl.
  - reflexivity.
  - destruct ys as [|y ys]; simpl.
    + lia.
    + rewrite IH. lia.
Qed.

Definition cadd (m n : Cnt) : Cnt := mkC (cc m + cc n) (addL (ca m) (ca n)).

Lemma ev_add : forall rho m n, ev rho (cadd m n) = ev rho m + ev rho n.
Proof. intros. unfold ev, cadd. simpl. rewrite dot_addL. lia. Qed.

Definition all0 (a : list N) : bool := forallb (fun x => x =? 0) a.
Definition isConst (n : Cnt) : bool := all0 (ca n).

Lemma dot_all0 : forall a rho, all0 a = true -> dot a rho = 0.
Proof.
  induction a as [|x a IH]; intros rho H; simpl in *.
  - reflexivity.
  - apply andb_true_iff in H. destruct H as [H1 H2]. apply N.eqb_eq in H1. subst x.
    rewrite (IH _ H2). lia.
Qed.

Lemma ev_const : forall rho n, isConst n = true -> ev rho n = cc n.
Proof. intros rho n H. unfold ev. rewrite (dot_all0 _ _ H). lia. Qed.

Definition cmul (k : N) (n : Cnt) : Cnt := mkC (k * cc n) (List.map (N.mul k) (ca n)).

Lemma dot_map_mul : forall k a rho, dot (List.map (N.mul k) a) rho = k * dot a rho.
Proof.
  induction a as [|x a IH]; intros rho; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma ev_mul : forall rho k n, ev rho (cmul k n) = k * ev rho n.
Proof. intros. unfold ev, cmul. simpl. rewrite dot_map_mul. lia. Qed.

Definition allmod (k : N) (a : list N) : bool := forallb (fun x => x mod k =? 0) a.

(** [n = k * q + r] with [r] a number: possible when [k] divides every coefficient. *)
Definition cdiv (n : Cnt) (k : N) : option (Cnt * N) :=
  if allmod k (ca n) then Some (mkC (cc n / k) (List.map (fun x => x / k) (ca n)), cc n mod k) else None.

Lemma dot_map_div : forall k a rho, allmod k a = true -> dot a rho = k * dot (List.map (fun x => x / k) a) rho.
Proof.
  induction a as [|x a IH]; intros rho H; simpl in *.
  - lia.
  - apply andb_true_iff in H. destruct H as [H1 H2]. apply N.eqb_eq in H1.
    rewrite (IH _ H2). pose proof (N.div_mod' x k) as E. rewrite H1 in E.
    rewrite E at 1. lia.
Qed.

Lemma ev_div : forall rho n k m r, cdiv n k = Some (m, r) -> ev rho n = k * ev rho m + r.
Proof.
  intros rho n k m r H. unfold cdiv in H. destruct (allmod k (ca n)) eqn:Ha; [|discriminate].
  injection H as <- <-. unfold ev. simpl. rewrite (dot_map_div _ _ _ Ha).
  pose proof (N.div_mod' (cc n) k). lia.
Qed.

(** Without coefficients 0 at the end. *)
Fixpoint trimL (a : list N) : list N :=
  match a with
  | [] => []
  | x :: a' =>
    match trimL a' with
    | [] => if x =? 0 then [] else [x]
    | t => x :: t
    end
  end.

Lemma dot_trimL : forall a rho, dot (trimL a) rho = dot a rho.
Proof.
  induction a as [|x a IH]; intros rho; simpl.
  - reflexivity.
  - specialize (IH (fun i => rho (S i))). destruct (trimL a) as [|y t].
    + simpl in IH. destruct (x =? 0) eqn:Hx.
      * apply N.eqb_eq in Hx. subst x. simpl. lia.
      * simpl. lia.
    + change (dot (x :: y :: t) rho) with (x * rho O + dot (y :: t) (fun i => rho (S i))). lia.
Qed.

Definition ctrim (n : Cnt) : Cnt := mkC (cc n) (trimL (ca n)).

Lemma ev_trim : forall rho n, ev rho (ctrim n) = ev rho n.
Proof. intros. unfold ev, ctrim. simpl. rewrite dot_trimL. reflexivity. Qed.

(** Coefficient by coefficient; [None] if a coefficient would be negative. *)
Fixpoint subL (xs ys : list N) : option (list N) :=
  match ys with
  | [] => Some xs
  | y :: ys' =>
    match xs with
    | [] => if y =? 0 then match subL [] ys' with Some zs => Some (0 :: zs) | None => None end else None
    | x :: xs' => if y <=? x then match subL xs' ys' with Some zs => Some ((x - y) :: zs) | None => None end
                  else None
    end
  end.

Lemma subL_spec : forall ys xs zs rho, subL xs ys = Some zs -> dot xs rho = dot zs rho + dot ys rho.
Proof.
  induction ys as [|y ys IH]; intros xs zs rho H.
  - simpl in H. injection H as <-. simpl. lia.
  - destruct xs as [|x xs].
    + cbn [subL] in H. destruct (y =? 0) eqn:Hy; [|discriminate]. apply N.eqb_eq in Hy. subst y.
      destruct (subL [] ys) as [zs'|] eqn:Hz; [|discriminate]. injection H as <-.
      pose proof (IH _ _ (fun i => rho (S i)) Hz) as E. simpl in *. lia.
    + cbn [subL] in H. destruct (y <=? x) eqn:Hy; [|discriminate]. apply N.leb_le in Hy.
      destruct (subL xs ys) as [zs'|] eqn:Hz; [|discriminate]. injection H as <-.
      pose proof (IH _ _ (fun i => rho (S i)) Hz) as E. simpl. rewrite E. nia.
Qed.

(** [m - n] when that is a count for every value of the variables. *)
Definition csub (m n : Cnt) : option Cnt :=
  if cc n <=? cc m then
    match subL (ca m) (ca n) with
    | Some a => Some (mkC (cc m - cc n) (trimL a))
    | None => None
    end
  else None.

Lemma ev_sub : forall rho m n k, csub m n = Some k -> ev rho m = ev rho k + ev rho n.
Proof.
  intros rho m n k H. unfold csub in H. destruct (cc n <=? cc m) eqn:Hc; [|discriminate].
  apply N.leb_le in Hc. destruct (subL (ca m) (ca n)) as [a|] eqn:Ha; [|discriminate].
  injection H as <-. unfold ev. simpl. rewrite dot_trimL. rewrite (subL_spec _ _ _ rho Ha). lia.
Qed.

(** ** Tokens and their denotation *)

Inductive Tok := cell (b : sym) | blk (w : list sym) (n : Cnt).

(** [w] repeated [n] times in front of a stream. *)
Definition rep (n : N) (w : list sym) (s : Stream sym) : Stream sym := (w ^^ N.to_nat n) *> s.

(** The stream a token list stands for (nearest cell first; blank after the last token). *)
Fixpoint dn (rho : nat -> N) (t : list Tok) : Stream sym :=
  match t with
  | [] => const S0
  | cell b :: t' => b >> dn rho t'
  | blk w n :: t' => rep (ev rho n) w (dn rho t')
  end.

Lemma rep_0 : forall w s, rep 0 w s = s.
Proof. reflexivity. Qed.

Lemma rep_add : forall a b w s, rep (a + b) w s = rep a w (rep b w s).
Proof. intros. unfold rep. rewrite N2Nat.inj_add, lpow_add, Str_app_assoc. reflexivity. Qed.

Lemma rep_1 : forall w s, rep 1 w s = w *> s.
Proof. intros. unfold rep. simpl. rewrite app_nil_r. reflexivity. Qed.

Lemma rep_succ : forall n w s, rep (n + 1) w s = w *> rep n w s.
Proof. intros. rewrite N.add_comm, rep_add, rep_1. reflexivity. Qed.

Lemma rep_app_comm : forall n w s, rep n w (w *> s) = w *> rep n w s.
Proof. intros. unfold rep. apply lpow_shift'. Qed.

Lemma lpow_times : forall (a : list sym) b n, a ^^ (b * n) = (a ^^ n) ^^ b.
Proof.
  intros a b n. induction b as [|b IH]; simpl.
  - reflexivity.
  - rewrite lpow_add, IH. reflexivity.
Qed.

Lemma rep_pow : forall m k w s, rep m (w ^^ N.to_nat k) s = rep (k * m) w s.
Proof.
  intros. unfold rep. rewrite N2Nat.inj_mul, (PeanoNat.Nat.mul_comm (N.to_nat k)), lpow_times. reflexivity.
Qed.

Lemma rep_rotate : forall n d b s, b >> rep n (d ++ [b]) s = rep n (b :: d) (b >> s).
Proof.
  intros. unfold rep. generalize (N.to_nat n) as k. induction k as [|k IH]; simpl.
  - reflexivity.
  - rewrite !Str_app_assoc. simpl. rewrite IH. reflexivity.
Qed.

Lemma dn_cells : forall rho w t, dn rho (List.map cell w ++ t) = w *> dn rho t.
Proof. induction w as [|b w IH]; intros t; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(** ** Taking cells off a side, putting blocks on *)

(** The nearest cell of a side and the rest.  A block is opened only if its count is surely at least 1. *)
Definition popCell (t : list Tok) : option (sym * list Tok) :=
  match t with
  | [] => Some (S0, [])
  | cell b :: t' => Some (b, t')
  | blk w n :: t' =>
    match w with
    | [] => None
    | b :: w' =>
      if 1 <=? cc n then
        Some (b, List.map cell w' ++
                 (if andb (cc n =? 1) (isConst n) then t' else blk (b :: w') (mkC (cc n - 1) (ca n)) :: t'))
      else None
    end
  end.

Lemma popCell_spec : forall rho t b t', popCell t = Some (b, t') -> dn rho t = b >> dn rho t'.
Proof.
  intros rho t b t' H. destruct t as [|x t].
  - injection H as <- <-. simpl. apply const_unfold.
  - destruct x as [c|w n].
    + injection H as <- <-. reflexivity.
    + simpl in H. destruct w as [|c w']; [discriminate|].
      destruct (1 <=? cc n) eqn:Hc; [|discriminate]. apply N.leb_le in Hc.
      injection H as <- <-. rewrite dn_cells.
      destruct (andb (cc n =? 1) (isConst n)) eqn:H1.
      * apply andb_true_iff in H1. destruct H1 as [H1 H2]. apply N.eqb_eq in H1.
        simpl. rewrite (ev_const _ _ H2), H1, rep_1. reflexivity.
      * simpl. replace (ev rho n) with (ev rho (mkC (cc n - 1) (ca n)) + 1) by (unfold ev; simpl; lia).
        rewrite rep_succ. reflexivity.
Qed.

(** Take the word [u] off a side, cell by cell. *)
Fixpoint takeW (u : list sym) (t : list Tok) : option (list Tok) :=
  match u with
  | [] => Some t
  | b :: u' =>
    match popCell t with
    | Some (b', t') => if symb b b' then takeW u' t' else None
    | None => None
    end
  end.

Lemma takeW_spec : forall rho u t t', takeW u t = Some t' -> dn rho t = u *> dn rho t'.
Proof.
  induction u as [|b u IH]; intros t t' H; simpl in H.
  - injection H as <-. reflexivity.
  - destruct (popCell t) as [[b' t'']|] eqn:Hp; [|discriminate].
    destruct (symb b b') eqn:Hb; [|discriminate]. apply symb_eq in Hb. subst b'.
    rewrite (popCell_spec _ _ _ _ Hp), (IH _ _ H). reflexivity.
Qed.

(** Put a block on a side; it merges with a block of the same word. *)
Definition pushBlk (w : list sym) (n : Cnt) (t : list Tok) : list Tok :=
  match t with
  | blk w' m :: t' => if weqb w w' then blk w (cadd n m) :: t' else blk w n :: t
  | _ => blk w n :: t
  end.

Lemma pushBlk_spec : forall rho w n t, dn rho (pushBlk w n t) = rep (ev rho n) w (dn rho t).
Proof.
  intros rho w n t. destruct t as [|[c|w' m] t]; try reflexivity.
  simpl. destruct (weqb w w') eqn:Hw; [|reflexivity]. apply weqb_eq in Hw. subst w'.
  simpl. rewrite ev_add, rep_add. reflexivity.
Qed.

(** ** Cycle rules: templates *)

(** A token of a rule's template: a cell, a block with a fixed count, or a block whose count is [b0 + M x]
    before and [b1 + M x] after one application ([x] free, [M] the modulus of the rule). *)
Inductive TT := tcell (b : sym) | tfix (w : list sym) (n : N) | tvar (w : list sym) (b0 b1 : N).

(** A cycle rule: a modulus and a template of the right side of the tape. *)
Record CRule := mkR { rM : N; rt : list TT }.

(** The template as tokens, before ([sel = false]) or after; the variable of a block is its position. *)
Fixpoint symK (M : N) (sel : bool) (k : nat) (t : list TT) : list Tok :=
  match t with
  | [] => []
  | tcell b :: t' => cell b :: symK M sel (S k) t'
  | tfix w n :: t' => blk w (mkC n []) :: symK M sel (S k) t'
  | tvar w b0 b1 :: t' => blk w (mkC (if sel then b1 else b0) (repeat 0 k ++ [M])) :: symK M sel (S k) t'
  end.

(** Before and after are congruent modulo [M] in every block. *)
Fixpoint wfT (M : N) (t : list TT) : bool :=
  match t with
  | [] => true
  | tvar _ b0 b1 :: t' => andb (b0 mod M =? b1 mod M) (wfT M t')
  | _ :: t' => wfT M t'
  end.

Definition wfR (r : CRule) : bool := andb (0 <? rM r) (wfT (rM r) (rt r)).

(** The template with the count of the block at position [i] equal to [min b0 b1 + M * rho i]. *)
Fixpoint instV (M : N) (t : list TT) (rho : nat -> N) : Stream sym :=
  match t with
  | [] => const S0
  | tcell b :: t' => b >> instV M t' (fun i => rho (S i))
  | tfix w n :: t' => rep n w (instV M t' (fun i => rho (S i)))
  | tvar w b0 b1 :: t' => rep (N.min b0 b1 + M * rho O) w (instV M t' (fun i => rho (S i)))
  end.

Lemma instV_ext : forall M t rho rho', (forall i, rho i = rho' i) -> instV M t rho = instV M t rho'.
Proof.
  intros M. induction t as [|e t IH]; intros rho rho' H; [reflexivity|].
  assert (E : instV M t (fun i => rho (S i)) = instV M t (fun i => rho' (S i))) by (apply IH; intros; apply H).
  destruct e; simpl; rewrite E, ?H; reflexivity.
Qed.

(** By position: what a block's count before ([sel = false]) or after is above [min b0 b1], divided by [M]. *)
Fixpoint uvec (M : N) (sel : bool) (t : list TT) (i : nat) : N :=
  match t, i with
  | [], _ => 0
  | tvar _ b0 b1 :: _, O => ((if sel then b1 else b0) - N.min b0 b1) / M
  | _ :: _, O => 0
  | _ :: t', S i' => uvec M sel t' i'
  end.

Lemma dot_repeat : forall M k rho, dot (repeat 0 k ++ [M]) rho = M * rho k.
Proof.
  intros M. induction k as [|k IH]; intros rho; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma divsub : forall M a b, 0 < M -> a mod M = b mod M -> b <= a -> M * ((a - b) / M) = a - b.
Proof.
  intros M a b HM H Hle.
  pose proof (N.div_mod' a M) as Ea. pose proof (N.div_mod' b M) as Eb. rewrite H in Ea.
  assert (Hq : b / M <= a / M) by (apply N.Div0.div_le_mono; lia).
  assert (E : a - b = (a / M - b / M) * M) by nia.
  rewrite E, N.div_mul by lia. lia.
Qed.

Lemma min_facts : forall M b0 b1 (sel : bool), b0 mod M = b1 mod M ->
  N.min b0 b1 <= (if sel then b1 else b0) /\ (if sel then b1 else b0) mod M = N.min b0 b1 mod M.
Proof.
  intros M b0 b1 sel H. destruct (N.le_ge_cases b0 b1) as [Hle|Hle].
  - rewrite (N.min_l _ _ Hle). destruct sel; split; (lia || congruence).
  - rewrite (N.min_r _ _ Hle). destruct sel; split; (lia || congruence).
Qed.

Lemma sym_inst : forall M (sel : bool) t rho k, 0 < M -> wfT M t = true ->
  dn rho (symK M sel k t) = instV M t (fun i => rho (k + i)%nat + uvec M sel t i).
Proof.
  intros M sel. induction t as [|e t IH]; intros rho k HM Hw; [reflexivity|].
  assert (TL : forall e', wfT M t = true ->
      dn rho (symK M sel (S k) t) = instV M t (fun i => rho (k + S i)%nat + uvec M sel (e' :: t) (S i))).
  { intros e' Hw'. rewrite (IH rho (S k) HM Hw'). apply instV_ext. intros i.
    replace (S k + i)%nat with (k + S i)%nat by lia. destruct e'; reflexivity. }
  destruct e as [b|w n|w b0 b1].
  - simpl in Hw. cbn [symK dn instV]. rewrite (TL (tcell b) Hw). reflexivity.
  - simpl in Hw. cbn [symK dn instV]. rewrite (TL (tfix w n) Hw). unfold ev. simpl. rewrite N.add_0_r.
    reflexivity.
  - simpl in Hw. apply andb_true_iff in Hw. destruct Hw as [Hb Hw]. apply N.eqb_eq in Hb.
    cbn [symK dn instV]. rewrite (TL (tvar w b0 b1) Hw). f_equal.
    unfold ev. cbn [cc ca uvec]. rewrite dot_repeat, PeanoNat.Nat.add_0_r.
    destruct (min_facts M b0 b1 sel Hb) as [H1 H2].
    pose proof (divsub M _ _ HM H2 H1) as H3. rewrite N.mul_add_distr_l, H3. lia.
Qed.


Record SCfg := mkSC { sl : list Tok; sr : list Tok; sq : state }.

(** A shift rule: in state [q], with the word [u] carried on the side the head comes from, [k] copies of [w]
    are crossed, leaving [v] behind; [s] steps.  All words nearest cell first. *)
Record SRule := mkS { rq : state; rw : list sym; rk : N; ru : list sym; rv : list sym; rsteps : N }.

(** Blocks of fewer than [flatMax] copies written out as cells: see [canon]. *)
Definition flatMax : N := 1000.

Section Exec.

Variable tm : TM.
(** The event state: its arrival at the left end of the tape is where cycle rules are tried. *)
Variable evSt : state.
(** A block that [norm] finds with a number of copies below [thr] is written out as cells. *)
Variable thr : N.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(** The head in state [q] on the first cell of [r], with [l] on its left. *)
Definition conf (l r : Stream sym) (q : state) : Q * tape := l {{q}}> r.

Definition den (rho : nat -> N) (S : SCfg) : Q * tape := conf (dn rho (sl S)) (dn rho (sr S)) (sq S).

Lemma step_R : forall q s s' q' l r, tm (q, s) = Some (s', R, q') ->
  conf l (s >> r) q -[ tm ]-> conf (s' >> l) r q'.
Proof. intros. unfold conf. simpl. apply (@step_right tm q q' s s' l r). assumption. Qed.

Lemma step_L : forall q s s' q' a l r, tm (q, s) = Some (s', L, q') ->
  conf (a >> l) (s >> r) q -[ tm ]-> conf l (a >> s' >> r) q'.
Proof. intros. unfold conf. simpl. apply (@step_left tm q q' s s' (a >> l) r). assumption. Qed.

(** ** The machine on a finite window (to check the shift rules) *)

Definition wstep (c : list sym * list sym * state) : option (list sym * list sym * state) :=
  match c with
  | (l, r, q) =>
    match r with
    | [] => None
    | s :: r' =>
      match tm (q, s) with
      | Some (s', R, q') => Some (s' :: l, r', q')
      | Some (s', L, q') =>
        match l with
        | [] => None
        | a :: l' => Some (l', a :: s' :: r', q')
        end
      | None => None
      end
    end
  end.

Definition wconf (Lt Rt : Stream sym) (c : list sym * list sym * state) : Q * tape :=
  match c with (l, r, q) => conf (l *> Lt) (r *> Rt) q end.

Lemma wstep_ok : forall Lt Rt c c', wstep c = Some c' -> wconf Lt Rt c -[ tm ]-> wconf Lt Rt c'.
Proof.
  intros Lt Rt [[l r] q] c' H. unfold wstep in H. destruct r as [|s r']; [discriminate|].
  destruct (tm (q, s)) as [[[s' d] q']|] eqn:Ht; [|discriminate]. destruct d.
  - destruct l as [|a l']; [discriminate|]. injection H as <-. simpl. apply step_L. assumption.
  - injection H as <-. simpl. apply step_R. assumption.
Qed.

Fixpoint wrun (n : nat) (c : list sym * list sym * state) : option (list sym * list sym * state) :=
  match n with
  | O => Some c
  | S n' => match wstep c with Some c' => wrun n' c' | None => None end
  end.

Lemma wrun_ok : forall Lt Rt n c c', wrun n c = Some c' -> wconf Lt Rt c -->* wconf Lt Rt c'.
Proof.
  induction n as [|n IH]; intros c c' H; simpl in H.
  - injection H as <-. apply evstep_refl.
  - destruct (wstep c) as [c1|] eqn:H1; [|discriminate].
    eapply evstep_step; [apply (wstep_ok _ _ _ _ H1) | apply (IH _ _ H)].
Qed.

(** ** Shift rules *)

(* Both directions are the same check in the coordinates (near, far).
   A left scan swaps physical left and right, including their frames. *)
Definition orient {A : Type} (d : dir) (near far : A) : A * A :=
  match d with R => (near, far) | L => (far, near) end.

Definition scross (d : dir) (near far : Stream sym) (q : Q) :=
  let '(l, r) := orient d near far in conf l r q.

Definition wcross (d : dir) (near far : list sym) (q : Q) :=
  (orient d near far, q).

Lemma wconf_cross : forall d Lt Rt near far q,
  wconf (fst (orient d Lt Rt)) (snd (orient d Lt Rt)) (wcross d near far q) =
  scross d (near *> Lt) (far *> Rt) q.
Proof. intros [] Lt Rt near far q; reflexivity. Qed.

Definition window_eqb (x y : list sym * list sym * state) : bool :=
  let '(l, r, q) := x in let '(l', r', q') := y in
  andb (weqb l l') (andb (weqb r r') (qeqb q q')).

Lemma window_eqb_eq : forall x y, window_eqb x y = true -> x = y.
Proof.
  intros [[l r] q] [[l' r'] q'] H; cbn [window_eqb] in H.
  apply andb_true_iff in H as [Hl H]. apply andb_true_iff in H as [Hr Hq].
  apply weqb_eq in Hl, Hr. apply qeqb_eq in Hq. now subst.
Qed.

Definition OKCross (d : dir) (r : SRule) : Prop := forall Lt Rt,
  scross d (ru r *> Lt) (rw r ^^ N.to_nat (rk r) *> Rt) (rq r) -->*
  scross d (ru r *> rv r *> Lt) Rt (rq r).

Definition OKR := OKCross R.
Definition OKL := OKCross L.

Definition chkCross (d : dir) (r : SRule) : bool :=
  match wrun (N.to_nat (rsteps r)) (wcross d (ru r) (rw r ^^ N.to_nat (rk r)) (rq r)) with
  | Some c => window_eqb c (wcross d (ru r ++ rv r) [] (rq r))
  | None => false
  end.

Definition chkR := chkCross R.
Definition chkL := chkCross L.

Lemma chkCross_ok : forall d r, chkCross d r = true -> OKCross d r.
Proof.
  intros d r H Lt Rt. unfold chkCross in H.
  destruct wrun as [c|] eqn:Hr; [|discriminate].
  apply window_eqb_eq in H. subst c.
  pose proof (wrun_ok (fst (orient d Lt Rt)) (snd (orient d Lt Rt)) _ _ _ Hr) as E.
  rewrite !wconf_cross, Str_app_assoc in E. exact E.
Qed.

Lemma cross_repeat : forall d r, OKCross d r -> forall m Lt Rt,
  scross d (ru r *> Lt) ((rw r ^^ N.to_nat (rk r)) ^^ m *> Rt) (rq r) -->*
  scross d (ru r *> rv r ^^ m *> Lt) Rt (rq r).
Proof.
  intros d r H. induction m as [|m IH]; intros Lt Rt.
  - apply evstep_refl.
  - cbn [lpow]. rewrite Str_app_assoc. eapply evstep_trans; [apply H|].
    replace ((rv r ++ rv r ^^ m) *> Lt) with (rv r ^^ m *> rv r *> Lt).
    + apply IH.
    + rewrite lpow_shift', Str_app_assoc. reflexivity.
Qed.

(** Cross the block [w^n] (already taken off its side, [far] is what is behind it) with the first rule of the
    list that applies; [near] is the side the head comes from.  Returns the new [near] and [far]. *)
Fixpoint crossWith (st : state) (w : list sym) (n : Cnt) (near far : list Tok) (rs : list SRule) :
    option (list Tok * list Tok) :=
  match rs with
  | [] => None
  | r :: rs' =>
    if andb (qeqb (rq r) st) (weqb (rw r) w) then
      match cdiv n (rk r) with
      | Some (m, rem) =>
        if 1 <=? cc m then
          match takeW (ru r) near with
          | Some near' =>
            Some (List.map cell (ru r) ++ pushBlk (rv r) m near', if rem =? 0 then far else blk w (mkC rem []) :: far)
          | None => crossWith st w n near far rs'
          end
        else crossWith st w n near far rs'
      | None => crossWith st w n near far rs'
      end
    else crossWith st w n near far rs'
  end.

Lemma far_spec : forall rho w rem far,
  dn rho (if rem =? 0 then far else blk w (mkC rem []) :: far) = rep rem w (dn rho far).
Proof.
  intros. destruct (rem =? 0) eqn:H.
  - apply N.eqb_eq in H. subst rem. reflexivity.
  - simpl. unfold ev. simpl. rewrite N.add_0_r. reflexivity.
Qed.

Lemma split_rep : forall rho n k m rem w s, cdiv n k = Some (m, rem) ->
  rep (ev rho n) w s = (w ^^ N.to_nat k) ^^ N.to_nat (ev rho m) *> rep rem w s.
Proof.
  intros rho n k m rem w s H. rewrite (ev_div rho _ _ _ _ H), rep_add, <- rep_pow. reflexivity.
Qed.

Lemma crossWith_sound : forall d rho st w n near far near' far' rs,
  (forall r, In r rs -> OKCross d r) -> crossWith st w n near far rs = Some (near', far') ->
  scross d (dn rho near) (rep (ev rho n) w (dn rho far)) st -->*
  scross d (dn rho near') (dn rho far') st.
Proof.
  intros d rho st w n near far near' far'. induction rs as [|r rs IH]; intros Hrs H; [discriminate|].
  assert (IH' : crossWith st w n near far rs = Some (near', far') ->
    scross d (dn rho near) (rep (ev rho n) w (dn rho far)) st -->*
    scross d (dn rho near') (dn rho far') st).
  { apply IH. intros r' Hr'. apply Hrs. right. assumption. }
  simpl in H. destruct (andb (qeqb (rq r) st) (weqb (rw r) w)) eqn:Hq; [|auto].
  destruct (cdiv n (rk r)) as [[m rem]|] eqn:Hd; [|auto].
  destruct (1 <=? cc m); [|auto].
  destruct (takeW (ru r) near) as [nr|] eqn:Ht; [|auto].
  injection H as <- <-. apply andb_true_iff in Hq as [Hq Hw].
  apply qeqb_eq in Hq. apply weqb_eq in Hw. subst st w.
  rewrite (takeW_spec rho _ _ _ Ht), (split_rep rho _ _ _ _ _ _ Hd), far_spec, dn_cells, pushBlk_spec.
  apply cross_repeat. apply Hrs. left. reflexivity.
Qed.

(** The smallest count a block must surely have to be crossed by a shift rule (a matter of strategy only). *)
Definition minCross : N := 6.

(** Cross the block under the head (to the right), or else the block just left of the head (to the left). *)
Definition cross (shR shL : list SRule) (S : SCfg) : option SCfg :=
  let a : option SCfg :=
    match sr S with
    | blk w n :: far =>
      if minCross <=? cc n then
        match crossWith (sq S) w n (sl S) far shR with
        | Some (l, r) => Some (mkSC l r (sq S))
        | None => None
        end
      else None
    | _ => None
    end in
  match a with
  | Some S' => Some S'
  | None =>
    match sl S with
    | blk w n :: far =>
      if minCross <=? cc n then
        match crossWith (sq S) w n (sr S) far shL with
        | Some (r, l) => Some (mkSC l r (sq S))
        | None => None
        end
      else None
    | _ => None
    end
  end.

Lemma cross_sound : forall rho shR shL S S',
  (forall r, In r shR -> OKR r) -> (forall r, In r shL -> OKL r) ->
  cross shR shL S = Some S' -> den rho S -->* den rho S'.
Proof.
  intros rho shR shL [l r q] S' HR HL H. unfold cross in H. simpl in H.
  match type of H with match ?a with _ => _ end = _ => destruct a as [S1|] eqn:Ha end.
  - injection H as <-. destruct r as [|[c|w n] far]; try discriminate.
    destruct (minCross <=? cc n); [|discriminate].
    destruct (crossWith q w n l far shR) as [[l' r']|] eqn:Hc; [|discriminate].
    injection Ha as <-. exact (crossWith_sound R rho _ _ _ _ _ _ _ _ HR Hc).
  - clear Ha. destruct l as [|[c|w n] far]; try discriminate.
    destruct (minCross <=? cc n); [|discriminate].
    destruct (crossWith q w n r far shL) as [[r' l']|] eqn:Hc; [|discriminate].
    injection H as <-. exact (crossWith_sound L rho _ _ _ _ _ _ _ _ HL Hc).
Qed.

(** ** One machine step *)

Definition stepS (S : SCfg) : option SCfg :=
  match popCell (sr S) with
  | None => None
  | Some (b, r') =>
    match tm (sq S, b) with
    | None => None
    | Some (wr, R, q) => Some (mkSC (cell wr :: sl S) r' q)
    | Some (wr, L, q) =>
      match popCell (sl S) with
      | None => None
      | Some (a, l') => Some (mkSC l' (cell a :: cell wr :: r') q)
      end
    end
  end.

Lemma stepS_sound : forall rho S S', stepS S = Some S' -> den rho S -[ tm ]-> den rho S'.
Proof.
  intros rho [l r q] S' H. unfold stepS in H. simpl in H.
  destruct (popCell r) as [[b r']|] eqn:Hp; [|discriminate].
  destruct (tm (q, b)) as [[[wr d] q']|] eqn:Ht; [|discriminate].
  unfold den. simpl. rewrite (popCell_spec rho _ _ _ Hp). destruct d.
  - destruct (popCell l) as [[a l']|] eqn:Hl; [|discriminate]. injection H as <-.
    rewrite (popCell_spec rho _ _ _ Hl). simpl. apply step_L. assumption.
  - injection H as <-. simpl. apply step_R. assumption.
Qed.

(** ** Re-bracketing a side *)

(** The cells of [w], as cells, at the front of a token list. *)
Fixpoint stripCells (w : list sym) (t : list Tok) : option (list Tok) :=
  match w with
  | [] => Some t
  | b :: w' =>
    match t with
    | cell b' :: t' => if symb b b' then stripCells w' t' else None
    | _ => None
    end
  end.

Lemma stripCells_spec : forall rho w t t', stripCells w t = Some t' -> dn rho t = w *> dn rho t'.
Proof.
  induction w as [|b w IH]; intros t t' H; simpl in H.
  - injection H as <-. reflexivity.
  - destruct t as [|[b'|w' n] t]; try discriminate.
    destruct (symb b b') eqn:Hb; [|discriminate]. apply symb_eq in Hb. subst b'.
    simpl. rewrite (IH _ _ H). reflexivity.
Qed.

(** A block absorbs blocks of the same word and literal copies of its word that follow it. *)
Fixpoint absorb (f : nat) (w : list sym) (n : Cnt) (rest : list Tok) : Cnt * list Tok :=
  match f with
  | O => (n, rest)
  | S f' =>
    let a : option (Cnt * list Tok) :=
      match rest with
      | blk w' m :: rest' => if weqb w' w then Some (cadd n m, rest') else None
      | _ => None
      end in
    match a with
    | Some (n', r') => absorb f' w n' r'
    | None =>
      match stripCells w rest with
      | Some r' => absorb f' w (mkC (cc n + 1) (ca n)) r'
      | None => (n, rest)
      end
    end
  end.

Lemma absorb_spec : forall rho f w n rest,
  rep (ev rho (fst (absorb f w n rest))) w (dn rho (snd (absorb f w n rest))) = rep (ev rho n) w (dn rho rest).
Proof.
  induction f as [|f IH]; intros w n rest; [reflexivity|]. cbn [absorb].
  match goal with |- context [match ?a with Some _ => _ | None => _ end] => destruct a as [[n' r']|] eqn:Ha end.
  - rewrite IH. destruct rest as [|[c|w' m] rest']; try discriminate.
    destruct (weqb w' w) eqn:Hw; [|discriminate]. apply weqb_eq in Hw. subst w'.
    injection Ha as <- <-. simpl. rewrite ev_add, rep_add. reflexivity.
  - clear Ha. destruct (stripCells w rest) as [r'|] eqn:Hs; [|reflexivity].
    rewrite IH, (stripCells_spec rho _ _ _ Hs), rep_app_comm.
    replace (ev rho (mkC (cc n + 1) (ca n))) with (ev rho n + 1) by (unfold ev; simpl; lia).
    rewrite rep_succ. reflexivity.
Qed.

(** The shortest [d] with [w = d^j], found by trying every length (the answer is checked where it is used). *)
Fixpoint rootGo (w : list sym) (fuel d : nat) : list sym * nat :=
  match fuel with
  | O => (w, 1%nat)
  | S f =>
    if Nat.ltb d (length w) then
      if andb (Nat.eqb (Nat.modulo (length w) d) 0) (weqb (firstn d w ^^ Nat.div (length w) d) w)
      then (firstn d w, Nat.div (length w) d)
      else rootGo w f (S d)
    else (w, 1%nat)
  end.

Definition rootOf (w : list sym) : list sym * nat := rootGo w (length w) 1.

(** A block with its word reduced to its root. *)
Definition rootRed (w : list sym) (n : Cnt) : list sym * Cnt :=
  let dj := rootOf w in
  if andb (Nat.ltb 1 (snd dj)) (weqb (fst dj ^^ snd dj) w) then (fst dj, cmul (N.of_nat (snd dj)) n) else (w, n).

Lemma rootRed_spec : forall rho w n s,
  rep (ev rho (snd (rootRed w n))) (fst (rootRed w n)) s = rep (ev rho n) w s.
Proof.
  intros rho w n s. unfold rootRed.
  destruct (andb (Nat.ltb 1 (snd (rootOf w))) (weqb (fst (rootOf w) ^^ snd (rootOf w)) w)) eqn:H; [|reflexivity].
  apply andb_true_iff in H. destruct H as [_ H]. apply weqb_eq in H. simpl.
  rewrite ev_mul, <- rep_pow, Nat2N.id, H. reflexivity.
Qed.

(** A word as its last cell and what is before it. *)
Fixpoint unsnoc (w : list sym) : option (list sym * sym) :=
  match w with
  | [] => None
  | a :: t =>
    match unsnoc t with
    | None => Some ([], a)
    | Some (d, b) => Some (a :: d, b)
    end
  end.

Lemma unsnoc_spec : forall w d b, unsnoc w = Some (d, b) -> w = d ++ [b].
Proof.
  induction w as [|a t IH]; intros d b H; [discriminate|]. simpl in H.
  destruct (unsnoc t) as [[d' b']|] eqn:Hu.
  - injection H as <- <-. rewrite (IH _ _ eq_refl). reflexivity.
  - injection H as <- <-. destruct t as [|c t]; [reflexivity|]. simpl in Hu.
    destruct (unsnoc t) as [[? ?]|]; discriminate.
Qed.

(** [cellOnto]: put a cell in front of a token list: a block whose word ends in that cell is rotated to the left
    of it.  [blkOnto]: put a block in front of a token list: its word is reduced to its root, it absorbs what
    follows, and a block of fewer than [thr] copies is written out. *)
Fixpoint cellOnto (f : nat) (b : sym) (rest : list Tok) {struct f} : list Tok :=
  match f with
  | O => cell b :: rest
  | S f' =>
    match rest with
    | blk w n :: rest' =>
      match unsnoc w with
      | Some (d, b') => if symb b' b then blkOnto f' (b :: d) n (cellOnto f' b rest') else cell b :: rest
      | None => cell b :: rest
      end
    | _ => cell b :: rest
    end
  end
with blkOnto (f : nat) (w : list sym) (n : Cnt) (rest : list Tok) {struct f} : list Tok :=
  match f with
  | O => blk w n :: rest
  | S f' =>
    let wn := rootRed w n in
    let nr := absorb (S (length rest)) (fst wn) (snd wn) rest in
    if andb (isConst (fst nr)) (cc (fst nr) <? thr) then
      fold_right (fun b acc => cellOnto f' b acc) (snd nr) (fst wn ^^ N.to_nat (cc (fst nr)))
    else blk (fst wn) (fst nr) :: snd nr
  end.

Lemma onto_spec : forall rho f,
  (forall b rest, dn rho (cellOnto f b rest) = b >> dn rho rest) /\
  (forall w n rest, dn rho (blkOnto f w n rest) = rep (ev rho n) w (dn rho rest)).
Proof.
  intros rho. induction f as [|f [IHc IHb]]; [split; reflexivity|]. split.
  - intros b rest. cbn [cellOnto]. destruct rest as [|[c|w n] rest']; try reflexivity.
    destruct (unsnoc w) as [[d b']|] eqn:Hu; [|reflexivity].
    destruct (symb b' b) eqn:Hb; [|reflexivity]. apply symb_eq in Hb. subst b'.
    rewrite IHb, IHc. apply unsnoc_spec in Hu. subst w. simpl. rewrite rep_rotate. reflexivity.
  - intros w n rest. cbn [blkOnto]. cbv zeta.
    rewrite <- (rootRed_spec rho w n), <- (absorb_spec rho (S (length rest))).
    generalize (rootRed w n) as wn. intros wn.
    generalize (absorb (S (length rest)) (fst wn) (snd wn) rest) as nr. intros nr.
    destruct (andb (isConst (fst nr)) (cc (fst nr) <? thr)) eqn:Hs; [|reflexivity].
    apply andb_true_iff in Hs. destruct Hs as [Hs _]. rewrite (ev_const _ _ Hs). unfold rep.
    generalize (fst wn ^^ N.to_nat (cc (fst nr))) as cells. induction cells as [|c cells IHl]; [reflexivity|].
    simpl. rewrite IHc, IHl. reflexivity.
Qed.

Definition normFuel : nat := 2000.

(** One pass from the far end: every token is put in front of the normal form of what follows it. *)
Definition npass (t : list Tok) : list Tok :=
  fold_right (fun tok acc =>
    match tok with
    | cell b => cellOnto normFuel b acc
    | blk w n => blkOnto normFuel w n acc
    end) [] t.

Lemma npass_spec : forall rho t, dn rho (npass t) = dn rho t.
Proof.
  intros rho. induction t as [|x t IH]; [reflexivity|]. unfold npass in *. cbn [fold_right].
  destruct x as [b|w n].
  - rewrite (proj1 (onto_spec rho normFuel)), IH. reflexivity.
  - rewrite (proj2 (onto_spec rho normFuel)), IH. reflexivity.
Qed.

(** The cells at the front of a token list. *)
Fixpoint leadCells (t : list Tok) : list sym :=
  match t with
  | cell b :: t' => b :: leadCells t'
  | _ => []
  end.

Fixpoint isPrefix (w s : list sym) : bool :=
  match w, s with
  | [], _ => true
  | a :: w', b :: s' => andb (symb a b) (isPrefix w' s')
  | _, _ => false
  end.

(** How many times [w] is found at the front of [s], one copy after the other. *)
Fixpoint countCopies (w : list sym) (f : nat) (s : list sym) : N :=
  match f with
  | O => 0
  | S f' => if isPrefix w s then 1 + countCopies w f' (skipn (length w) s) else 0
  end.

(** A word of at most 14 cells of which at least four copies start [s], covering the most cells (strategy
    only). *)
Definition bestRepeat (s : list sym) : option (list sym * N) :=
  let len := length s in
  fold_left (fun best lw =>
    let w := firstn lw s in
    let c := 1 + countCopies w len (skipn lw s) in
    let better : bool :=
      match best with
      | None => true
      | Some (w', c') => c' * N.of_nat (length w') <? c * N.of_nat lw
      end in
    if andb (4 <=? c) better then Some (w, c) else best)
    [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14]%nat None.

(** Runs of four or more equal words among the cells become blocks. *)
Fixpoint form (f : nat) (t : list Tok) : list Tok :=
  match f with
  | O => t
  | S f' =>
    match t with
    | [] => []
    | blk w n :: t' => blk w n :: form f' t'
    | cell b :: t' =>
      match bestRepeat (b :: leadCells t') with
      | Some (w, c) =>
        match stripCells (w ^^ N.to_nat c) (cell b :: t') with
        | Some t'' => blk w (mkC c []) :: form f' t''
        | None => cell b :: form f' t'
        end
      | None => cell b :: form f' t'
      end
    end
  end.

Lemma form_spec : forall rho f t, dn rho (form f t) = dn rho t.
Proof.
  intros rho. induction f as [|f IH]; intros t; [reflexivity|]. cbn [form].
  destruct t as [|[b|w n] t]; [reflexivity | | simpl; rewrite IH; reflexivity].
  destruct (bestRepeat (b :: leadCells t)) as [[w c]|]; [|simpl; rewrite IH; reflexivity].
  destruct (stripCells (w ^^ N.to_nat c) (cell b :: t)) as [t''|] eqn:Hs; [|simpl; rewrite IH; reflexivity].
  rewrite (stripCells_spec rho _ _ _ Hs). cbn [dn]. rewrite IH. unfold ev, rep. simpl. rewrite N.add_0_r.
  reflexivity.
Qed.

Definition formT (t : list Tok) : list Tok := form (S (length t)) t.

(** The normal form of a side. *)
Definition norm (t : list Tok) : list Tok :=
  npass (formT (npass (formT (npass (formT (npass t)))))).

Lemma norm_spec : forall rho t, dn rho (norm t) = dn rho t.
Proof. intros. unfold norm, formT. rewrite !npass_spec, !form_spec, !npass_spec || idtac.
  repeat (rewrite ?npass_spec, ?form_spec). reflexivity. Qed.

Fixpoint flatT (t : list Tok) : list Tok :=
  match t with
  | [] => []
  | cell b :: t' => cell b :: flatT t'
  | blk w n :: t' =>
    if andb (isConst n) (cc n <? flatMax) then List.map cell (w ^^ N.to_nat (cc n)) ++ flatT t'
    else blk w n :: flatT t'
  end.

Lemma flatT_spec : forall rho t, dn rho (flatT t) = dn rho t.
Proof.
  intros rho. induction t as [|[b|w n] t IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
  - destruct (andb (isConst n) (cc n <? flatMax)) eqn:H.
    + apply andb_true_iff in H. destruct H as [H _]. rewrite dn_cells, IH, (ev_const _ _ H). reflexivity.
    + simpl. rewrite IH. reflexivity.
Qed.

(** Blank cells at the far end dropped. *)
Fixpoint stripZ (t : list Tok) : list Tok :=
  match t with
  | [] => []
  | x :: t' =>
    let s := stripZ t' in
    match x, s with
    | cell S0, [] => []
    | _, _ => x :: s
    end
  end.

Lemma stripZ_spec : forall rho t, dn rho (stripZ t) = dn rho t.
Proof.
  intros rho. induction t as [|x t IH]; [reflexivity|]. cbn [stripZ]. cbv zeta.
  destruct x as [[|]|w n].
  - destruct (stripZ t) as [|y s] eqn:Hs.
    + simpl. rewrite <- IH. simpl. apply const_unfold.
    + cbn [dn]. cbn [dn] in IH. rewrite IH. reflexivity.
  - cbn [dn]. rewrite IH. reflexivity.
  - cbn [dn]. rewrite IH. reflexivity.
Qed.

(** A form that depends only on the cells when at most one block is long or has a variable; used to compare the
    end of a run with a target. *)
Definition canon (t : list Tok) : list Tok := stripZ (npass (flatT t)).

Lemma canon_spec : forall rho t, dn rho (canon t) = dn rho t.
Proof. intros. unfold canon. rewrite stripZ_spec, npass_spec, flatT_spec. reflexivity. Qed.


(** ** Cycle rules: validity and application *)

(** A cycle rule, as a statement about the machine: from the template with counts [b0 + M xi] (event state at
    the left end, nothing to its left) the machine reaches the template with counts [b1 + M xi], for all values
    of the [xi]. *)
Definition RuleOK (r : CRule) : Prop := forall rho,
  conf (const S0) (dn rho (symK (rM r) false O (rt r))) evSt -->*
  conf (const S0) (dn rho (symK (rM r) true O (rt r))) evSt.

Lemma wfR_spec : forall r, wfR r = true -> 0 < rM r /\ wfT (rM r) (rt r) = true.
Proof. intros r H. apply andb_true_iff in H. destruct H as [H1 H2]. apply N.ltb_lt in H1. auto. Qed.

Lemma rule_inst : forall r, RuleOK r -> wfR r = true -> forall rho,
  conf (const S0) (instV (rM r) (rt r) (fun i => rho i + uvec (rM r) false (rt r) i)) evSt -->*
  conf (const S0) (instV (rM r) (rt r) (fun i => rho i + uvec (rM r) true (rt r) i)) evSt.
Proof.
  intros r H Hw rho. destruct (wfR_spec r Hw) as [HM Hw'].
  pose proof (H rho) as E. rewrite (sym_inst _ false _ rho O HM Hw'), (sym_inst _ true _ rho O HM Hw') in E.
  exact E.
Qed.

Lemma rule_instN : forall r, RuleOK r -> wfR r = true -> forall n rho,
  conf (const S0) (instV (rM r) (rt r) (fun i => rho i + n * uvec (rM r) false (rt r) i)) evSt -->*
  conf (const S0) (instV (rM r) (rt r) (fun i => rho i + n * uvec (rM r) true (rt r) i)) evSt.
Proof.
  intros r H Hw. induction n as [|n IH] using N.peano_ind; intros rho.
  - rewrite (instV_ext _ _ (fun i => rho i + 0 * uvec (rM r) false (rt r) i)
                           (fun i => rho i + 0 * uvec (rM r) true (rt r) i)) by (intros; lia).
    apply evstep_refl.
  - pose proof (rule_inst r H Hw (fun i => rho i + n * uvec (rM r) false (rt r) i)) as h1.
    pose proof (IH (fun i => rho i + uvec (rM r) true (rt r) i)) as h2.
    rewrite (instV_ext _ _ (fun i => rho i + N.succ n * uvec (rM r) false (rt r) i)
              (fun i => rho i + n * uvec (rM r) false (rt r) i + uvec (rM r) false (rt r) i)) by (intros; lia).
    eapply evstep_trans; [exact h1|].
    rewrite (instV_ext _ _ (fun i => rho i + n * uvec (rM r) false (rt r) i + uvec (rM r) true (rt r) i)
              (fun i => rho i + uvec (rM r) true (rt r) i + n * uvec (rM r) false (rt r) i)) by (intros; lia).
    eapply evstep_trans; [exact h2|].
    rewrite (instV_ext _ _ (fun i => rho i + uvec (rM r) true (rt r) i + n * uvec (rM r) true (rt r) i)
              (fun i => rho i + N.succ n * uvec (rM r) true (rt r) i)) by (intros; lia).
    apply evstep_refl.
Qed.

(** One token of the tape against one token of the template, for [n] applications at once ([n] a count: the
    number of applications may depend on the variables). *)
Definition appTok (M : N) (n : Cnt) (e : TT) (x : Tok) : option Tok :=
  match e, x with
  | tcell b, cell b' => if symb b b' then Some (cell b') else None
  | tfix w k, blk w' m => if andb (weqb w w') (andb (isConst m) (cc m =? k)) then Some (blk w' m) else None
  | tvar w b0 b1, blk w' m =>
    let lo := N.min b0 b1 in
    match csub m (cmul (M * ((b0 - lo) / M)) n) with
    | Some m1 =>
      if andb (weqb w w') (andb (lo <=? cc m1) (andb ((cc m1 - lo) mod M =? 0) (allmod M (ca m1))))
      then Some (blk w' (ctrim (cadd m1 (cmul (M * ((b1 - lo) / M)) n))))
      else None
    | None => None
    end
  | _, _ => None
  end.

Fixpoint appToks (M : N) (n : Cnt) (t : list TT) (s : list Tok) : option (list Tok) :=
  match t, s with
  | [], [] => Some []
  | e :: t', x :: s' =>
    match appTok M n e x, appToks M n t' s' with
    | Some x', Some s'' => Some (x' :: s'')
    | _, _ => None
    end
  | _, _ => None
  end.

Lemma app_inst : forall rho M n t toks toks', appToks M n t toks = Some toks' ->
  exists rho' : nat -> N,
    dn rho toks = instV M t (fun i => rho' i + ev rho n * uvec M false t i) /\
    dn rho toks' = instV M t (fun i => rho' i + ev rho n * uvec M true t i).
Proof.
  intros rho M n. induction t as [|e t IH]; intros toks toks' H.
  - destruct toks; [|discriminate]. injection H as <-. exists (fun _ : nat => 0). split; reflexivity.
  - destruct toks as [|x s]; [discriminate|]. cbn [appToks] in H.
    destruct (appTok M n e x) as [x'|] eqn:Hx; [|discriminate].
    destruct (appToks M n t s) as [s'|] eqn:Hs; [|discriminate]. injection H as <-.
    destruct (IH _ _ Hs) as [rt' [h1 h2]].
    destruct e as [b|w k|w b0 b1]; destruct x as [b'|w' m]; try discriminate.
    + simpl in Hx. destruct (symb b b') eqn:Hb; [|discriminate]. injection Hx as <-.
      apply symb_eq in Hb. subst b'.
      exists (fun i => match i with O => 0 | S i' => rt' i' end). cbn [dn instV uvec].
      rewrite h1, h2. split; reflexivity.
    + simpl in Hx. destruct (andb (weqb w w') (andb (isConst m) (cc m =? k))) eqn:Hc; [|discriminate].
      injection Hx as <-. apply andb_true_iff in Hc. destruct Hc as [Hw Hc].
      apply andb_true_iff in Hc. destruct Hc as [Hc Hk]. apply weqb_eq in Hw. apply N.eqb_eq in Hk. subst w'.
      exists (fun i => match i with O => 0 | S i' => rt' i' end). cbn [dn instV uvec].
      rewrite h1, h2, (ev_const _ _ Hc), Hk. split; reflexivity.
    + cbn [appTok] in Hx. cbv zeta in Hx.
      destruct (csub m (cmul (M * ((b0 - N.min b0 b1) / M)) n)) as [m1|] eqn:Hsub; [|discriminate].
      match type of Hx with (if ?c then _ else _) = _ => destruct c eqn:Hc end; [|discriminate].
      injection Hx as <-. apply andb_true_iff in Hc. destruct Hc as [Hw Hc].
      apply andb_true_iff in Hc. destruct Hc as [Hge Hc]. apply andb_true_iff in Hc. destruct Hc as [Hmod Hev].
      apply weqb_eq in Hw. apply N.leb_le in Hge. apply N.eqb_eq in Hmod. subst w'.
      pose proof (ev_sub rho _ _ _ Hsub) as hs. rewrite ev_mul in hs.
      pose proof (dot_map_div M (ca m1) rho Hev) as hd.
      pose proof (N.div_mod' (cc m1 - N.min b0 b1) M) as hq. rewrite Hmod in hq.
      assert (Hcc : cc m1 = N.min b0 b1 + M * ((cc m1 - N.min b0 b1) / M)).
      { clear -Hge hq. lia. }
      set (y := (cc m1 - N.min b0 b1) / M + dot (List.map (fun x => x / M) (ca m1)) rho).
      assert (hm1 : ev rho m1 = N.min b0 b1 + M * y).
      { unfold ev, y. rewrite hd. rewrite Hcc at 1. ring. }
      exists (fun i => match i with O => y | S i' => rt' i' end). cbn [dn instV uvec].
      rewrite h1, h2. split; f_equal.
      * rewrite hs, hm1. ring.
      * rewrite ev_trim, ev_add, ev_mul, hm1. ring.
Qed.

(** How many times to apply a rule (strategy only; [appToks] checks). *)
Variable strat : list TT -> list Tok -> option Cnt.

Definition tryRule (r : CRule) (toks : list Tok) : option (list Tok) :=
  match strat (rt r) toks with
  | Some n => if 1 <=? cc n then appToks (rM r) n (rt r) toks else None
  | None => None
  end.

Fixpoint tryRules (rs : list CRule) (toks : list Tok) : option (list Tok) :=
  match rs with
  | [] => None
  | r :: rs' =>
    match tryRule r toks with
    | Some t => Some t
    | None => tryRules rs' toks
    end
  end.

Lemma tryRule_sound : forall rho r toks toks', RuleOK r -> wfR r = true -> tryRule r toks = Some toks' ->
  conf (const S0) (dn rho toks) evSt -->* conf (const S0) (dn rho toks') evSt.
Proof.
  intros rho r toks toks' H Hw Ht. unfold tryRule in Ht.
  destruct (strat (rt r) toks) as [n|]; [|discriminate]. destruct (1 <=? cc n); [|discriminate].
  destruct (app_inst rho _ _ _ _ _ Ht) as [rho' [h1 h2]]. rewrite h1, h2.
  apply (rule_instN r H Hw (ev rho n) rho').
Qed.

Definition RulesOK (rs : list CRule) : Prop := Forall (fun r => RuleOK r /\ wfR r = true) rs.

Lemma tryRules_sound : forall rho rs toks toks', RulesOK rs -> tryRules rs toks = Some toks' ->
  conf (const S0) (dn rho toks) evSt -->* conf (const S0) (dn rho toks') evSt.
Proof.
  intros rho rs toks toks' Hrs. induction Hrs as [|r rs [H Hw] _ IH]; intros Ht; [discriminate|].
  simpl in Ht. destruct (tryRule r toks) as [t|] eqn:Hr.
  - injection Ht as <-. exact (tryRule_sound rho _ _ _ H Hw Hr).
  - exact (IH Ht).
Qed.

(** ** The executor *)

(** The tables: shift rules to the right and to the left, cycle rules. *)
Record Tbl := mkT { tR : list SRule; tL : list SRule; tC : list CRule }.

Definition TblOK (T : Tbl) : Prop :=
  (forall r, In r (tR T) -> OKR r) /\ (forall r, In r (tL T) -> OKL r) /\ RulesOK (tC T).

(** At an event (the event state at the left end): normal form, then the first cycle rule that applies. *)
Definition atEvent (T : Tbl) (S : SCfg) : SCfg :=
  let r := norm (sr S) in
  match tryRules (tC T) r with
  | Some r' => mkSC (sl S) r' (sq S)
  | None => mkSC (sl S) r (sq S)
  end.

Definition isNil (t : list Tok) : bool := match t with [] => true | _ => false end.

(** One machine step, and the event if there is one. *)
Definition moveS (T : Tbl) (S : SCfg) : option SCfg :=
  match stepS S with
  | None => None
  | Some S' => if andb (qeqb (sq S') evSt) (isNil (sl S')) then Some (atEvent T S') else Some S'
  end.

Definition move (T : Tbl) (S : SCfg) : option SCfg :=
  match cross (tR T) (tL T) S with
  | Some S' => Some S'
  | None => moveS T S
  end.

Lemma atEvent_sound : forall rho T S, TblOK T -> sq S = evSt -> sl S = [] ->
  den rho S -->* den rho (atEvent T S).
Proof.
  intros rho T [l r q] [_ [_ HC]] Hq Hl. simpl in Hq, Hl. subst q l. unfold atEvent. simpl.
  destruct (tryRules (tC T) (norm r)) as [r'|] eqn:Hr.
  - pose proof (tryRules_sound rho _ _ _ HC Hr) as E. rewrite norm_spec in E. exact E.
  - unfold den. simpl. rewrite norm_spec. apply evstep_refl.
Qed.

Lemma moveS_sound : forall rho T S S', TblOK T -> moveS T S = Some S' -> den rho S -->+ den rho S'.
Proof.
  intros rho T S S' HT H. unfold moveS in H. destruct (stepS S) as [S1|] eqn:Hs; [|discriminate].
  pose proof (stepS_sound rho _ _ Hs) as h1.
  destruct (andb (qeqb (sq S1) evSt) (isNil (sl S1))) eqn:He.
  - injection H as <-. apply andb_true_iff in He. destruct He as [Hq Hl]. apply qeqb_eq in Hq.
    assert (Hl' : sl S1 = []) by (destruct (sl S1); [reflexivity | discriminate]).
    eapply progress_evstep_trans; [apply progress_base; exact h1 | apply atEvent_sound; assumption].
  - injection H as <-. apply progress_base. exact h1.
Qed.

Lemma move_sound : forall rho T S S', TblOK T -> move T S = Some S' -> den rho S -->* den rho S'.
Proof.
  intros rho T S S' HT H. unfold move in H. destruct (cross (tR T) (tL T) S) as [S1|] eqn:Hc.
  - injection H as <-. destruct HT as [HR [HL _]]. exact (cross_sound rho _ _ _ _ HR HL Hc).
  - apply progress_evstep. exact (moveS_sound rho _ _ _ HT H).
Qed.

Definition obind (T : Tbl) (o : option SCfg) : option SCfg :=
  match o with Some X => move T X | None => None end.

(** [k] moves. *)
Definition run (T : Tbl) (k : N) (S : SCfg) : option SCfg := N.iter k (obind T) (Some S).

(** Soundness of the executor.  With valid tables, whatever the executor does in [k] moves the machine does in
    some number of steps, for every value of the variables. *)
Theorem run_sound : forall T, TblOK T -> forall k S S', run T k S = Some S' ->
  forall rho, den rho S -->* den rho S'.
Proof.
  intros T HT. unfold run. induction k as [|k IH] using N.peano_ind; intros S S' H rho.
  - injection H as <-. apply evstep_refl.
  - rewrite N.iter_succ in H. destruct (N.iter k (obind T) (Some S)) as [S1|] eqn:H1; [|discriminate].
    eapply evstep_trans; [exact (IH _ _ H1 rho) | exact (move_sound rho _ _ _ HT H)].
Qed.

(** ** Comparing configurations *)

Fixpoint lneqb (a b : list N) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => andb (x =? y) (lneqb a' b')
  | _, _ => false
  end.

Lemma lneqb_eq : forall a b, lneqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; destruct b as [|y b]; simpl; try congruence.
  intros H. apply andb_true_iff in H. destruct H as [H1 H2]. apply N.eqb_eq in H1. apply IH in H2. congruence.
Qed.

Definition tokeqb (x y : Tok) : bool :=
  match x, y with
  | cell a, cell b => symb a b
  | blk w n, blk w' n' => andb (weqb w w') (andb (cc n =? cc n') (lneqb (ca n) (ca n')))
  | _, _ => false
  end.

Lemma tokeqb_eq : forall x y, tokeqb x y = true -> x = y.
Proof.
  intros [a|w [c a]] [b|w' [c' a']]; simpl; try congruence.
  - intros H. apply symb_eq in H. congruence.
  - intros H. apply andb_true_iff in H. destruct H as [H1 H]. apply andb_true_iff in H. destruct H as [H2 H3].
    apply weqb_eq in H1. apply N.eqb_eq in H2. apply lneqb_eq in H3. congruence.
Qed.

Fixpoint tokseqb (s t : list Tok) : bool :=
  match s, t with
  | [], [] => true
  | x :: s', y :: t' => andb (tokeqb x y) (tokseqb s' t')
  | _, _ => false
  end.

Lemma tokseqb_eq : forall s t, tokseqb s t = true -> s = t.
Proof.
  induction s as [|x s IH]; destruct t as [|y t]; simpl; try congruence.
  intros H. apply andb_true_iff in H. destruct H as [H1 H2]. apply tokeqb_eq in H1. apply IH in H2. congruence.
Qed.

Definition cfgeqb (S S' : SCfg) : bool :=
  andb (tokseqb (sl S) (sl S')) (andb (tokseqb (sr S) (sr S')) (qeqb (sq S) (sq S'))).

Lemma cfgeqb_eq : forall S S', cfgeqb S S' = true -> S = S'.
Proof.
  intros [l r q] [l' r' q'] H. unfold cfgeqb in H. simpl in H.
  apply andb_true_iff in H. destruct H as [H1 H]. apply andb_true_iff in H. destruct H as [H2 H3].
  apply tokseqb_eq in H1. apply tokseqb_eq in H2. apply qeqb_eq in H3. congruence.
Qed.

(** [k] moves from [S] end exactly at [S']. *)
Definition runTo (T : Tbl) (k : N) (S S' : SCfg) : bool :=
  match run T k S with
  | Some X => cfgeqb X S'
  | None => false
  end.

Lemma runTo_sound : forall T, TblOK T -> forall k S S', runTo T k S S' = true ->
  forall rho, den rho S -->* den rho S'.
Proof.
  intros T HT k S S' H rho. unfold runTo in H. destruct (run T k S) as [X|] eqn:Hr; [|discriminate].
  apply cfgeqb_eq in H. subst X. exact (run_sound T HT _ _ _ Hr rho).
Qed.

(** One machine step first: at least one step of the machine. *)
Definition runTo1 (T : Tbl) (k : N) (S S' : SCfg) : bool :=
  match moveS T S with
  | Some X => runTo T k X S'
  | None => false
  end.

Lemma runTo1_sound : forall T, TblOK T -> forall k S S', runTo1 T k S S' = true ->
  forall rho, den rho S -->+ den rho S'.
Proof.
  intros T HT k S S' H rho. unfold runTo1 in H. destruct (moveS T S) as [S1|] eqn:Hm; [|discriminate].
  eapply progress_evstep_trans; [exact (moveS_sound rho _ _ _ HT Hm) | exact (runTo_sound T HT _ _ _ H rho)].
Qed.

(** A cycle rule proved by the executor: a run from the template before to the template after. *)
Definition chkRule (T : Tbl) (k : N) (r : CRule) : bool :=
  andb (wfR r) (runTo T k (mkSC [] (symK (rM r) false O (rt r)) evSt) (mkSC [] (symK (rM r) true O (rt r)) evSt)).

Lemma chkRule_ok : forall T, TblOK T -> forall k r, chkRule T k r = true -> RuleOK r /\ wfR r = true.
Proof.
  intros T HT k r H. apply andb_true_iff in H. destruct H as [Hw H]. split; [|exact Hw].
  intros rho. exact (runTo_sound T HT _ _ _ H rho).
Qed.

Lemma shifts_ok : forall shR shL, forallb chkR shR = true -> forallb chkL shL = true ->
  TblOK (mkT shR shL []).
Proof.
  intros shR shL HR HL. split; [|split].
  - intros r Hr. apply chkCross_ok. exact (proj1 (forallb_forall _ _) HR r Hr).
  - intros r Hr. apply chkCross_ok. exact (proj1 (forallb_forall _ _) HL r Hr).
  - constructor.
Qed.

Lemma tbl_ok : forall shR shL rs, TblOK (mkT shR shL []) -> RulesOK rs -> TblOK (mkT shR shL rs).
Proof. intros shR shL rs [HR [HL _]] H. split; [|split]; assumption. Qed.

End Exec.

(** ** The strategy for the number of applications of a cycle rule

    [appToks] validates the chosen count. *)

(** The smallest of what the shrinking blocks allow, by the numeric part of their counts. *)
Fixpoint ruleNmin (t : list TT) (s : list Tok) : option N :=
  match t, s with
  | tvar _ b0 b1 :: t', blk _ m :: s' =>
    let r := ruleNmin t' s' in
    if b1 <? b0 then
      let k := (cc m - b0) / (b0 - b1) + 1 in
      Some (match r with None => k | Some k' => N.min k k' end)
    else r
  | _ :: t', _ :: s' => ruleNmin t' s'
  | _, _ => None
  end.

Definition stratMin (t : list TT) (s : list Tok) : option Cnt :=
  match ruleNmin t s with Some n => Some (mkC n []) | None => None end.

(** * Part 2: the machine *)

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA").

(** The executor for this machine: events are state E at the left end of the tape; blocks of fewer than 3 copies
    are written out; a cycle rule is applied a number of times. *)
Definition thr : N := 3.
Notation TOK := (TblOK tm E).

(** The shift rules to the right: state, word, copies, carried word, word left behind, steps. *)
Definition shR : list SRule :=
  [mkS A [S0; S1; S1] 1 [] [S0; S1; S1] 3;
   mkS C [S1; S0; S1] 1 [] [S1; S1; S0] 3;
   mkS B [S1; S1; S0; S1; S1; S0] 1 [] [S1; S0; S1; S1; S0; S1] 6;
   mkS B [S1; S1; S0] 1 [] [S1; S0; S1] 3;
   mkS A [S1; S0; S1; S1; S0; S0; S1] 1 [S0; S0] [S1; S0; S1; S1; S0; S0; S1] 13;
   mkS A [S0; S1; S1; S0; S1; S1] 1 [] [S0; S1; S1; S0; S1; S1] 6;
   mkS C [S1; S0; S1; S1; S0; S1] 1 [] [S1; S1; S0; S1; S1; S0] 6;
   mkS C [S0; S1; S1; S0; S1; S1; S0; S1; S1; S0; S0; S1; S1] 1 [S0; S0; S0] [S1; S0; S1; S1; S0; S1; S1; S0; S1; S1; S0; S0; S1] 19;
   mkS B [S0; S1; S1; S0; S1; S1; S0; S1; S1; S0; S1; S1; S0] 1 [] [S1; S0; S1; S1; S0; S1; S1; S0; S1; S1; S0; S0; S1] 19;
   mkS A [S0; S1; S1; S0; S1; S1; S0; S0; S1; S1; S0; S1; S1] 1 [] [S0; S1; S1; S0; S0; S1; S1; S0; S1; S1; S0; S1; S1] 19;
   mkS A [S1; S0; S1; S1; S0; S1; S1; S0; S1; S1; S0; S0; S1] 1 [S0; S0] [S1; S0; S1; S1; S0; S1; S1; S0; S1; S1; S0; S0; S1] 19;
   mkS A [S0; S1; S1; S0; S0; S1; S1; S0; S1; S1; S0; S1; S1] 1 [] [S0; S1; S1; S0; S1; S1; S0; S0; S1; S1; S0; S1; S1] 19;
   mkS B [S1; S1; S0; S1; S1; S0; S0; S1; S1; S0; S1; S1; S0] 1 [] [S1; S0; S1; S1; S0; S0; S1; S1; S0; S1; S1; S0; S1] 19].

(** The shift rules to the left: state, word, copies, carried word, word left behind, steps. *)
Definition shL : list SRule :=
  [mkS F [S0; S1; S1] 2 [S1; S0; S0] [S1; S1; S0; S1; S1; S0] 18;
   mkS E [S0; S1; S1] 2 [S1] [S1; S0; S1; S1; S0; S1] 18;
   mkS C [S1; S1; S0] 2 [S0] [S1; S1; S0; S1; S1; S0] 18;
   mkS A [S1; S0; S1; S1; S0; S1] 1 [S1; S1; S0; S0; S0] [S1; S1; S0; S1; S1; S0] 18;
   mkS D [S1; S0; S1] 2 [S0] [S0; S1; S1; S0; S1; S1] 18;
   mkS A [S1; S0; S1; S1; S0; S0; S1] 1 [S1; S1; S0; S0; S0] [S0; S1; S1; S0; S1; S1; S0] 23;
   mkS E [S0; S1; S1; S0; S1; S1] 1 [S1] [S1; S0; S1; S1; S0; S1] 18;
   mkS C [S1; S1; S0; S1; S1; S0] 1 [S0] [S1; S1; S0; S1; S1; S0] 18;
   mkS D [S1; S0; S1; S1; S0; S1] 1 [S1; S0] [S1; S1; S0; S1; S1; S0] 18;
   mkS D [S1; S0; S1; S1; S0; S1] 1 [S0] [S0; S1; S1; S0; S1; S1] 18;
   mkS F [S0; S1; S1; S0; S1; S1] 1 [S1; S0; S0] [S1; S1; S0; S1; S1; S0] 18;
   mkS A [S1; S1; S0] 2 [S0; S1; S0; S0] [S1; S1; S0; S1; S1; S0] 18;
   mkS A [S1; S1; S0; S1; S1; S0] 1 [S0; S1; S0; S0] [S1; S1; S0; S1; S1; S0] 18;
   mkS A [S1; S0; S1; S1; S0; S1; S1; S0; S1; S1; S0; S0; S1] 1 [S1; S1; S0; S0; S0] [S0; S1; S1; S0; S1; S1; S0; S1; S1; S0; S1; S1; S0] 41;
   mkS E [S0; S1; S1; S0; S0; S1; S1; S0; S1; S1; S0; S1; S1] 1 [S1] [S1; S0; S1; S1; S0; S1; S1; S0; S1; S1; S0; S0; S1] 41;
   mkS D [S1; S0; S1; S1; S0; S1; S1; S0; S1; S1; S0; S0; S1] 1 [S0] [S0; S1; S1; S0; S0; S1; S1; S0; S1; S1; S0; S1; S1] 41;
   mkS F [S0; S1; S1; S0; S1; S1; S0; S0; S1; S1; S0; S1; S1] 1 [S1; S0; S0] [S1; S1; S0; S1; S1; S0; S0; S1; S1; S0; S1; S1; S0] 41;
   mkS A [S1; S0; S1; S1; S0; S0; S1; S1; S0; S1; S1; S0; S1] 1 [S1; S1; S0; S0; S0] [S1; S1; S0; S1; S1; S0; S0; S1; S1; S0; S1; S1; S0] 41].

Lemma shR_chk : forallb (chkR tm) shR = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma shL_chk : forallb (chkL tm) shL = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** The tables without cycle rules: what the cycle rules themselves are proved with. *)
Definition T0 : Tbl := mkT shR shL [].

Lemma T0_ok : TOK T0.
Proof. exact (shifts_ok tm E shR shL shR_chk shL_chk). Qed.

(** Cycle rule 0 (2 events a cycle): [E> 0 (1011001)^44+2*x1 (101)^5 10 (011)^6 (0110110110110)^7 0110110 (011)^45+2*x14 0 (011)^41+2*x16 0], the counts with a variable going 44 -> 46, 45 -> 43, 41 -> 41. *)
Definition rule0 : CRule := mkR 2
  [tcell S0; tvar [S1; S0; S1; S1; S0; S0; S1] 44 46; tfix [S1; S0; S1] 5; tcell S1; tcell S0; tfix [S0; S1; S1]
   6; tfix [S0; S1; S1; S0; S1; S1; S0; S1; S1; S0; S1; S1; S0] 7; tcell S0; tcell S1; tcell S1; tcell S0; tcell
   S1; tcell S1; tcell S0; tvar [S0; S1; S1] 45 43; tcell S0; tvar [S0; S1; S1] 41 41; tcell S0].

(** Cycle rule 1 (4 events a cycle): [E> 0 (1011001)^44+2*x1 1011 (0)^4 (0110110011011)^18 0110110 (011)^69+2*x15 000 (011)^41+2*x19 0], the counts with a variable going 44 -> 42, 69 -> 83, 41 -> 41. *)
Definition rule1 : CRule := mkR 2
  [tcell S0; tvar [S1; S0; S1; S1; S0; S0; S1] 44 42; tcell S1; tcell S0; tcell S1; tcell S1; tfix [S0] 4; tfix
   [S0; S1; S1; S0; S1; S1; S0; S0; S1; S1; S0; S1; S1] 18; tcell S0; tcell S1; tcell S1; tcell S0; tcell S1;
   tcell S1; tcell S0; tvar [S0; S1; S1] 69 83; tcell S0; tcell S0; tcell S0; tvar [S0; S1; S1] 41 41; tcell
   S0].

(** Cycle rule 2 (2 events a cycle): [E> 0 (1011001)^44+2*x1 (101)^5 10 (011)^6 (0110110110110)^49 0110110 (011)^45+2*x14 0 (011)^41+2*x16 0], the counts with a variable going 44 -> 46, 45 -> 43, 41 -> 41. *)
Definition rule2 : CRule := mkR 2
  [tcell S0; tvar [S1; S0; S1; S1; S0; S0; S1] 44 46; tfix [S1; S0; S1] 5; tcell S1; tcell S0; tfix [S0; S1; S1]
   6; tfix [S0; S1; S1; S0; S1; S1; S0; S1; S1; S0; S1; S1; S0] 49; tcell S0; tcell S1; tcell S1; tcell S0;
   tcell S1; tcell S1; tcell S0; tvar [S0; S1; S1] 45 43; tcell S0; tvar [S0; S1; S1] 41 41; tcell S0].

(** Cycle rule 3 (4 events a cycle): [E> 0 (1011001)^44+2*x1 1011 (0)^5 110110011010 (101)^68+2*x19 1000 (011)^41+2*x24 0], the counts with a variable going 44 -> 42, 68 -> 82, 41 -> 41. *)
Definition rule3 : CRule := mkR 2
  [tcell S0; tvar [S1; S0; S1; S1; S0; S0; S1] 44 42; tcell S1; tcell S0; tcell S1; tcell S1; tfix [S0] 5; tcell
   S1; tcell S1; tcell S0; tcell S1; tcell S1; tcell S0; tcell S0; tcell S1; tcell S1; tcell S0; tcell S1; tcell
   S0; tvar [S1; S0; S1] 68 82; tcell S1; tcell S0; tcell S0; tcell S0; tvar [S0; S1; S1] 41 41; tcell S0].

(** Cycle rule 4 (2 events a cycle): [E> 0 (1011001)^44+2*x1 (101)^5 10 (011)^45+2*x5 0 (011)^41+2*x7 0], the counts with a variable going 44 -> 46, 45 -> 43, 41 -> 41. *)
Definition rule4 : CRule := mkR 2
  [tcell S0; tvar [S1; S0; S1; S1; S0; S0; S1] 44 46; tfix [S1; S0; S1] 5; tcell S1; tcell S0; tvar [S0; S1; S1]
   45 43; tcell S0; tvar [S0; S1; S1] 41 41; tcell S0].

(** Cycle rule 5 (4 events a cycle): [E> 0 (1011001)^45+2*x1 1011 (0)^4 (0110110011011)^58 01101100 (101)^68+2*x16 1000 (011)^41+2*x21 0], the counts with a variable going 45 -> 43, 68 -> 82, 41 -> 41. *)
Definition rule5 : CRule := mkR 2
  [tcell S0; tvar [S1; S0; S1; S1; S0; S0; S1] 45 43; tcell S1; tcell S0; tcell S1; tcell S1; tfix [S0] 4; tfix
   [S0; S1; S1; S0; S1; S1; S0; S0; S1; S1; S0; S1; S1] 58; tcell S0; tcell S1; tcell S1; tcell S0; tcell S1;
   tcell S1; tcell S0; tcell S0; tvar [S1; S0; S1] 68 82; tcell S1; tcell S0; tcell S0; tcell S0; tvar [S0; S1;
   S1] 41 41; tcell S0].

(** Cycle rule 6 (2 events a cycle): [E> 0 (1011001)^44+2*x1 (101)^5 10 (011)^6 (0110110110110)^41+2*x6 0110110 (011)^45+2*x14 0 (011)^41+2*x16 0], the counts with a variable going 44 -> 46, 41 -> 41, 45 -> 43, 41 -> 41. *)
Definition rule6 : CRule := mkR 2
  [tcell S0; tvar [S1; S0; S1; S1; S0; S0; S1] 44 46; tfix [S1; S0; S1] 5; tcell S1; tcell S0; tfix [S0; S1; S1]
   6; tvar [S0; S1; S1; S0; S1; S1; S0; S1; S1; S0; S1; S1; S0] 41 41; tcell S0; tcell S1; tcell S1; tcell S0;
   tcell S1; tcell S1; tcell S0; tvar [S0; S1; S1] 45 43; tcell S0; tvar [S0; S1; S1] 41 41; tcell S0].

(** Cycle rule 7 (4 events a cycle): [E> 0 (1011001)^44+2*x1 1011 (0)^4 (0110110011011)^17 0110110 (011)^68+2*x15 0 (011)^41+2*x17 0], the counts with a variable going 44 -> 42, 68 -> 82, 41 -> 41. *)
Definition rule7 : CRule := mkR 2
  [tcell S0; tvar [S1; S0; S1; S1; S0; S0; S1] 44 42; tcell S1; tcell S0; tcell S1; tcell S1; tfix [S0] 4; tfix
   [S0; S1; S1; S0; S1; S1; S0; S0; S1; S1; S0; S1; S1] 17; tcell S0; tcell S1; tcell S1; tcell S0; tcell S1;
   tcell S1; tcell S0; tvar [S0; S1; S1] 68 82; tcell S0; tvar [S0; S1; S1] 41 41; tcell S0].

(** Cycle rule 8 (72 events a cycle): [E> 0 (1011001)^145+2*x1 1011 (0)^5 1101100110110 (011)^16 001101100110 (011)^869+2*x33 0], the counts with a variable going 145 -> 93, 869 -> 1283. *)
Definition rule8 : CRule := mkR 2
  [tcell S0; tvar [S1; S0; S1; S1; S0; S0; S1] 145 93; tcell S1; tcell S0; tcell S1; tcell S1; tfix [S0] 5;
   tcell S1; tcell S1; tcell S0; tcell S1; tcell S1; tcell S0; tcell S0; tcell S1; tcell S1; tcell S0; tcell S1;
   tcell S1; tcell S0; tfix [S0; S1; S1] 16; tcell S0; tcell S0; tcell S1; tcell S1; tcell S0; tcell S1; tcell
   S1; tcell S0; tcell S0; tcell S1; tcell S1; tcell S0; tvar [S0; S1; S1] 869 1283; tcell S0].

(** Cycle rule 9 (4 events a cycle): [E> 0 (1011001)^44+2*x1 1011 (0)^5 110110 (011)^4 0 (011)^4 0 (011)^69+2*x17 000 (011)^41+2*x21 0], the counts with a variable going 44 -> 42, 69 -> 83, 41 -> 41. *)
Definition rule9 : CRule := mkR 2
  [tcell S0; tvar [S1; S0; S1; S1; S0; S0; S1] 44 42; tcell S1; tcell S0; tcell S1; tcell S1; tfix [S0] 5; tcell
   S1; tcell S1; tcell S0; tcell S1; tcell S1; tcell S0; tfix [S0; S1; S1] 4; tcell S0; tfix [S0; S1; S1] 4;
   tcell S0; tvar [S0; S1; S1] 69 83; tcell S0; tcell S0; tcell S0; tvar [S0; S1; S1] 41 41; tcell S0].

(** Cycle rule 10 (2 events a cycle): [E> 0 (1011001)^44+2*x1 (101)^5 10 (011)^10 00110110 (011)^45+2*x14 0 (011)^41+2*x16 0], the counts with a variable going 44 -> 46, 45 -> 43, 41 -> 41. *)
Definition rule10 : CRule := mkR 2
  [tcell S0; tvar [S1; S0; S1; S1; S0; S0; S1] 44 46; tfix [S1; S0; S1] 5; tcell S1; tcell S0; tfix [S0; S1; S1]
   10; tcell S0; tcell S0; tcell S1; tcell S1; tcell S0; tcell S1; tcell S1; tcell S0; tvar [S0; S1; S1] 45 43;
   tcell S0; tvar [S0; S1; S1] 41 41; tcell S0].

(** Cycle rule 11 (4 events a cycle): [E> 0 (1011001)^45+2*x1 1011 (0)^5 (1101100110110)^4 1101100 (101)^68+2*x15 1000 (011)^41+2*x20 0], the counts with a variable going 45 -> 43, 68 -> 82, 41 -> 41. *)
Definition rule11 : CRule := mkR 2
  [tcell S0; tvar [S1; S0; S1; S1; S0; S0; S1] 45 43; tcell S1; tcell S0; tcell S1; tcell S1; tfix [S0] 5; tfix
   [S1; S1; S0; S1; S1; S0; S0; S1; S1; S0; S1; S1; S0] 4; tcell S1; tcell S1; tcell S0; tcell S1; tcell S1;
   tcell S0; tcell S0; tvar [S1; S0; S1] 68 82; tcell S1; tcell S0; tcell S0; tcell S0; tvar [S0; S1; S1] 41 41;
   tcell S0].

(** The cycle rules with the number of moves of the run that proves each. *)
Definition rules : list (N * CRule) :=
  [(762, rule0); (2235, rule1); (762, rule2); (2055, rule3); (422, rule4); (2389, rule5);
   (762, rule6); (2235, rule7); (201007, rule8); (2583, rule9); (570, rule10); (3255, rule11)].

Lemma rules_chk : forallb (fun p => chkRule tm E thr stratMin T0 (fst p) (snd p)) rules = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** The tables of the two long runs. *)
Definition T : Tbl := mkT shR shL (List.map snd rules).

Lemma T_ok : TOK T.
Proof.
  apply tbl_ok; [exact T0_ok|]. apply Forall_forall. intros r Hr.
  apply in_map_iff in Hr. destruct Hr as [p [<- Hp]].
  exact (chkRule_ok tm E thr stratMin T0 T0_ok _ _ (proj1 (forallb_forall _ _) rules_chk p Hp)).
Qed.

(** The right side of C(r) in normal form, as tokens; [n] is the count of the last block. *)
Definition cycToks (n : Cnt) : list Tok :=
  [cell S0; blk [S1; S0; S1; S1; S0; S0; S1] (mkC 59 []); cell S1; cell S0; cell S1; cell S1;
   blk [S0] (mkC 5 []); cell S1; cell S1; cell S0; cell S1; cell S1; cell S0; cell S0; cell S1; cell S1;
   cell S0; cell S1; cell S1; cell S0; blk [S0; S1; S1] (mkC 16 []); cell S0; cell S0; cell S1; cell S1;
   cell S0; cell S1; cell S1; cell S0; cell S0; cell S1; cell S1; cell S0; blk [S0; S1; S1] n; cell S0].

(** 5037044 moves of the executor from blank tape end at C(16797709). *)
Lemma arrive_run :
  runTo tm E thr stratMin T 5037044 (mkSC [] [] A) (mkSC [] (cycToks (mkC 16797709 [])) E) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** One machine step and 5581713 more moves of the executor from C(65 + 2 x), x free, end at C(321042993 + 2 x). *)
Lemma period_run :
  runTo1 tm E thr stratMin T 5581713 (mkSC [] (cycToks (mkC 65 [2])) E)
    (mkSC [] (cycToks (mkC 321042993 [2])) E) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(** [E> 0 (1011001)^59 1011 00000 1101100110110 (011)^16 001101100110 (011)^r] *)
Definition Cyc (r : N) : Q * tape :=
  const S0 {{E}}>
    [S0] *> [S1; S0; S1; S1; S0; S0; S1] ^^ 59 *> [S1; S0; S1; S1] *> [S0; S0; S0; S0; S0] *>
    [S1; S1; S0; S1; S1; S0; S0; S1; S1; S0; S1; S1; S0] *> [S0; S1; S1] ^^ 16 *>
    [S0; S0; S1; S1; S0; S1; S1; S0; S0; S1; S1; S0] *> [S0; S1; S1] ^^ N.to_nat r *> const S0.

(** The tokens of [cycToks n] stand for [Cyc], with [n] copies of 011 in the last block. *)
Lemma den_cyc : forall rho n, den rho (mkSC [] (cycToks n) E) = Cyc (ev rho n).
Proof.
  intros rho n. unfold den, conf, Cyc, cycToks. cbn [sl sr sq dn]. unfold rep.
  rewrite <- (const_unfold _ S0). reflexivity.
Qed.

Global Opaque Cyc.

(** The run from blank tape reaches [Cyc 16797709]. *)
Lemma reach : c0 -->* Cyc 16797709.
Proof.
  pose proof (runTo_sound tm E thr stratMin T T_ok _ _ _ arrive_run (fun _ => 0)) as H.
  rewrite den_cyc in H. change (ev (fun _ => 0) (mkC 16797709 [])) with (16797709 + 0) in H.
  rewrite N.add_0_r in H. exact H.
Qed.

(** One period of the growth cycle, for every value of the free count. *)
Lemma grow : forall x, Cyc (65 + 2 * x) -->+ Cyc (65 + 2 * (x + 160521464)).
Proof.
  intros x. pose proof (runTo1_sound tm E thr stratMin T T_ok _ _ _ period_run (fun _ => x)) as H.
  rewrite !den_cyc in H.
  replace (ev (fun _ => x) (mkC 65 [2])) with (65 + 2 * x) in H by (unfold ev; cbn [cc ca dot]; lia).
  replace (ev (fun _ => x) (mkC 321042993 [2])) with (65 + 2 * (x + 160521464)) in H
    by (unfold ev; cbn [cc ca dot]; lia).
  exact H.
Qed.

(** The machine does not halt from blank tape. *)
Theorem nonhalt : ~ halts tm c0.
Proof.
  apply (multistep_nonhalt _ _ _ reach).
  change 16797709 with (65 + 2 * 8398822).
  apply (progress_nonhalt_simple tm N (fun x => Cyc (65 + 2 * x))).
  intros x. exists (x + 160521464). apply grow.
Qed.

End TM1.

Print Assumptions TM1.nonhalt.
