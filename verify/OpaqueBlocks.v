From BusyCoq Require Import Individual62.
Require Import Lia List Bool PeanoNat.
Require Coq.Strings.String.
Import String.StringSyntax.
Import ListNotations.
Close Scope sym_scope.

(** * Opaque blocks: a checker for bouncers whose tape is [cells w^k cells w^j cells]

  The tape is written as a list of tokens.  A token is a cell or a block [w^n],
  where [n] is one of two unknowns [k], [j].  The checker runs the machine on such
  a list without ever looking inside a block:

  - if the head meets a block, it runs the machine on a window of one copy of [w]
    and up to 3 carried cells; if the head leaves the window on the far side in
    the same state with the carried cells restored, the same happens for every
    copy, so the whole block is crossed ([shiftR], [shiftL]);
  - otherwise it moves the block one cell aside, [(c w)^n c = c (w c)^n] ([rot]);
  - otherwise it makes one step of the machine ([pstep]).

  So every run of the checker is a run of the machine for all values of the
  unknowns ([sstep_spec], [round_spec]).

  A round goes from state [qe] at the left end of the tape to the next time [qe]
  steps onto a new cell there.  [nonhalt_of_cert] needs a list [TP] of token lists
  ("templates") with two blocks, and a number [N], such that for every template [t]

  - one round from [t] at [(k+1, j)] ends in a template at [(k, j')], [j' > j];
  - from [t] at [(0, j)], [j >= N], at most [N] rounds end in a template at
    [(k', j')] with [k' + j' >= j].  Here the second block becomes the first one,
    and a new second block of length 0 is put in on the way.

  If the machine reaches a template at [(k, j)] with [k + j >= N], it never halts:
  [k + j >= N] is kept, and it gives [j >= N] whenever [k = 0].

  All of this is checked by [vm_compute] on the boolean [ok].  The functions under
  "Hints" are not trusted: what they return is checked. *)

Inductive tok := Cl (s : Sym) | Bk (w : list Sym) (v : bool).

Definition tok_eq_dec (a b : tok) : {a = b} + {a <> b}.
Proof. repeat decide equality. Defined.
Definition teqb (a b : list tok) : bool := if list_eq_dec tok_eq_dec a b then true else false.
Definition seqb (a b : list Sym) : bool := if list_eq_dec eqb_sym a b then true else false.

Lemma teqb_spec a b : teqb a b = true -> a = b.
Proof. unfold teqb. destruct (list_eq_dec tok_eq_dec a b); congruence. Qed.
Lemma seqb_spec a b : seqb a b = true -> a = b.
Proof. unfold seqb. destruct (list_eq_dec eqb_sym a b); congruence. Qed.

Definition get (x : nat * nat) (v : bool) : nat := if v then snd x else fst x.

Fixpoint flat (x : nat * nat) (t : list tok) : list Sym :=
  match t with
  | [] => []
  | Cl s :: t => s :: flat x t
  | Bk w v :: t => w ^^ get x v ++ flat x t
  end.

Lemma flat_app x a b : flat x (a ++ b) = flat x a ++ flat x b.
Proof. induction a as [|[s|w v] a IH]; cbn; rewrite ?IH, ?app_assoc; reflexivity. Qed.
Lemma flat_cells x u : flat x (map Cl u) = u.
Proof. induction u; cbn; congruence. Qed.

Section Checker.
Variable tm : TM.
Variable qe : Q.

(** ** Running the machine on a finite window *)

Definition zip := (list Sym * Q * list Sym)%type.
Definition zc (l r : side) (z : zip) : Q * tape :=
  let '(u, q, w) := z in u *> l {{q}}> w *> r.

Definition zstep (z : zip) : option zip :=
  let '(u, q, w) := z in
  match w with
  | s :: w' =>
    match tm (q, s) with
    | Some (o, R, q') => Some (o :: u, q', w')
    | Some (o, L, q') => match u with a :: u' => Some (u', q', a :: o :: w') | [] => None end
    | None => None
    end
  | [] => None
  end.

Lemma zstep_spec z z' l r : zstep z = Some z' -> zc l r z -[ tm ]-> zc l r z'.
Proof.
  destruct z as [[u q] [|s w]]; cbn; [congruence|].
  destruct (tm (q, s)) as [[[o []] q']|] eqn:E; [destruct u as [|a u]| |]; intros H; inverts H.
  - exact (@step_left tm q q' s o ((a :: u) *> l) (w *> r) E).
  - exact (@step_right tm q q' s o (u *> l) (w *> r) E).
Qed.

(** Run until the head leaves the window on the left ([b = true]) or on the right. *)
Fixpoint wrun (b : bool) (f : nat) (z : zip) : option zip :=
  match f with
  | O => None
  | S f =>
    match z, b with
    | ([], _, _), true | (_, _, []), false => Some z
    | _, _ => match zstep z with Some z' => wrun b f z' | None => None end
    end
  end.

Lemma wrun_spec b f z z' l r : wrun b f z = Some z' -> zc l r z -[ tm ]->* zc l r z'.
Proof.
  revert z. induction f as [|f IH]; intros z; cbn; [congruence|].
  assert (X : match zstep z with Some z1 => wrun b f z1 | None => None end = Some z' ->
              zc l r z -[ tm ]->* zc l r z').
  { destruct (zstep z) as [z1|] eqn:E; [|congruence]. intros H.
    eapply evstep_step; [apply zstep_spec; eassumption | apply IH; assumption]. }
  destruct z as [[[|a u] q] [|s w]], b; try exact X; intros H; inverts H; apply evstep_refl.
Qed.

Lemma shiftR u q w w2 :
  (forall l r, zc l r (u, q, w) -[ tm ]->* zc l r (u ++ w2, q, [])) ->
  forall n l r, u *> l {{q}}> w ^^ n *> r -[ tm ]->* u *> w2 ^^ n *> l {{q}}> r.
Proof.
  intros H n. induction n as [|n IH]; intros l r; [apply evstep_refl|].
  cbn [lpow]. rewrite !Str_app_assoc.
  eapply evstep_trans; [apply (H l (w ^^ n *> r))|]. cbn [zc Str_app].
  rewrite !Str_app_assoc.
  eapply evstep_trans; [apply IH|].
  rewrite lpow_shift'. apply evstep_refl.
Qed.

Lemma shiftL u q w w2 :
  (forall l r, zc l r (w, q, u) -[ tm ]->* zc l r ([], q, u ++ w2)) ->
  forall n l r, w ^^ n *> l {{q}}> u *> r -[ tm ]->* l {{q}}> u *> w2 ^^ n *> r.
Proof.
  intros H n. induction n as [|n IH]; intros l r; [apply evstep_refl|].
  cbn [lpow]. rewrite !Str_app_assoc.
  eapply evstep_trans; [apply (H (w ^^ n *> l) r)|]. cbn [zc Str_app].
  rewrite !Str_app_assoc.
  eapply evstep_trans; [apply IH|].
  rewrite lpow_shift'. apply evstep_refl.
Qed.

(** ** Configurations with blocks *)

Definition conf := (list tok * Q * list tok)%type.
Definition den (x : nat * nat) (t : list tok) : side := flat x t *> const s0.
Definition cf (x : nat * nat) (c : conf) : Q * tape :=
  let '(lt, q, rt) := c in den x lt {{q}}> den x rt.

Definition sread (t : list tok) : option (Sym * list tok) :=
  match t with
  | [] => Some (s0, [])
  | Cl s :: t => Some (s, t)
  | Bk _ _ :: _ => None
  end.

Lemma sread_spec x t s t' : sread t = Some (s, t') -> den x t = s >> den x t'.
Proof.
  destruct t as [|[c|w v] t]; cbn; intros H; inverts H; [|reflexivity].
  unfold den. cbn. apply const_unfold.
Qed.

(** One step of the machine. *)
Definition pstep (c : conf) : option conf :=
  let '(lt, q, rt) := c in
  match sread rt with
  | Some (s, r) =>
    match tm (q, s) with
    | Some (o, R, q') => Some (Cl o :: lt, q', r)
    | Some (o, L, q') =>
      match sread lt with Some (a, l) => Some (l, q', Cl a :: Cl o :: r) | None => None end
    | None => None
    end
  | None => None
  end.

Lemma pstep_spec x c c' : pstep c = Some c' -> cf x c -[ tm ]-> cf x c'.
Proof.
  destruct c as [[lt q] rt]. cbn [pstep].
  destruct (sread rt) as [[s r]|] eqn:Er; [|congruence].
  cbn [cf]. rewrite (sread_spec x _ _ _ Er).
  destruct (tm (q, s)) as [[[o []] q']|] eqn:E; [| |congruence].
  - destruct (sread lt) as [[a l]|] eqn:El; intros H; inverts H.
    cbn [cf]. rewrite (sread_spec x _ _ _ El).
    exact (@step_left tm q q' s o (a >> den x l) (den x r) E).
  - intros H; inverts H. exact (@step_right tm q q' s o (den x lt) (den x r) E).
Qed.

Fixpoint takeC (m : nat) (t : list tok) : option (list Sym * list tok) :=
  match m, t with
  | O, _ => Some ([], t)
  | S m, Cl s :: t => match takeC m t with Some (u, r) => Some (s :: u, r) | None => None end
  | _, _ => None
  end.

Lemma takeC_spec x m t u r : takeC m t = Some (u, r) -> flat x t = u ++ flat x r.
Proof.
  revert t u. induction m as [|m IH]; intros t u; cbn.
  - intros H; inverts H. reflexivity.
  - destruct t as [|[s|w v] t]; try congruence.
    destruct (takeC m t) as [[u' r']|] eqn:E; intros H; inverts H.
    cbn. erewrite IH by eassumption. reflexivity.
Qed.

(** Crossing a block to the right with the [m] cells behind the head carried along,
    and to the left with the [m] cells at the head carried along. *)
Definition tryR (lt : list tok) (q : Q) (w : list Sym) (v : bool) (r : list tok) (m : nat) : option conf :=
  match takeC m lt with
  | Some (u, lt') =>
    match wrun false 50 (u, q, w) with
    | Some (u', q', []) =>
      if q_eqb q q' && seqb u' (u ++ skipn m u') then Some (map Cl u ++ Bk (skipn m u') v :: lt', q, r)
      else None
    | _ => None
    end
  | None => None
  end.

Definition tryL (lt : list tok) (q : Q) (w : list Sym) (v : bool) (rt : list tok) (m : nat) : option conf :=
  match takeC m rt with
  | Some (u, r) =>
    match wrun true 50 (w, q, u) with
    | Some ([], q', u') =>
      if q_eqb q q' && seqb u' (u ++ skipn m u') then Some (lt, q, map Cl u ++ Bk (skipn m u') v :: r)
      else None
    | _ => None
    end
  | None => None
  end.

Lemma tryR_spec x lt q w v r m c' :
  tryR lt q w v r m = Some c' -> cf x (lt, q, Bk w v :: r) -[ tm ]->* cf x c'.
Proof.
  unfold tryR. destruct (takeC m lt) as [[u lt']|] eqn:Et; [|congruence].
  destruct (wrun false 50 (u, q, w)) as [[[u' q'] [|]]|] eqn:Ew; try congruence.
  destruct (q_eqb_spec q q'); [subst q'|cbn; congruence].
  destruct (seqb u' (u ++ skipn m u')) eqn:Es; cbn; [|congruence].
  apply seqb_spec in Es. intros H; inverts H.
  cbn [cf]. unfold den. rewrite (takeC_spec x _ _ _ _ Et). cbn [flat].
  rewrite flat_app, flat_cells. cbn [flat]. rewrite !Str_app_assoc.
  apply shiftR. intros l0 r0. rewrite <- Es. eapply wrun_spec; eassumption.
Qed.

Lemma tryL_spec x lt q w v rt m c' :
  tryL lt q w v rt m = Some c' -> cf x (Bk w v :: lt, q, rt) -[ tm ]->* cf x c'.
Proof.
  unfold tryL. destruct (takeC m rt) as [[u r]|] eqn:Et; [|congruence].
  destruct (wrun true 50 (w, q, u)) as [[[[|] q'] u']|] eqn:Ew; try congruence.
  destruct (q_eqb_spec q q'); [subst q'|cbn; congruence].
  destruct (seqb u' (u ++ skipn m u')) eqn:Es; cbn; [|congruence].
  apply seqb_spec in Es. intros H; inverts H.
  cbn [cf]. unfold den. rewrite (takeC_spec x _ _ _ _ Et). cbn [flat].
  rewrite flat_app, flat_cells. cbn [flat]. rewrite !Str_app_assoc.
  apply shiftL. intros l0 r0. rewrite <- Es. eapply wrun_spec; eassumption.
Qed.

Fixpoint first {X} (f : nat -> option X) (ms : list nat) : option X :=
  match ms with
  | [] => None
  | m :: ms => match f m with Some a => Some a | None => first f ms end
  end.

Lemma first_spec {X} (f : nat -> option X) ms a : first f ms = Some a -> exists m, f m = Some a.
Proof. induction ms as [|m ms IH]; cbn; [congruence|]. destruct (f m) eqn:E; eauto. intros H; inverts H; eauto. Qed.

(** Moving a block one cell away from the head: [(c w)^n c = c (w c)^n]. *)
Definition rot (t : list tok) : option (list tok) :=
  match t with
  | Bk (c :: w) v :: Cl c' :: r => if sym_eqb c c' then Some (Cl c :: Bk (w ++ [c]) v :: r) else None
  | _ => None
  end.

Lemma rot_spec x t t' : rot t = Some t' -> flat x t = flat x t'.
Proof.
  destruct t as [|[|[|c w] v] [|[c'|] r]]; cbn; try congruence.
  destruct (sym_eqb_spec c c'); [subst c'|congruence]. intros H; inverts H.
  cbn. apply lpow_rotate_list.
Qed.

Definition ms := [0; 1; 2; 3].

Definition sstep (c : conf) : option conf :=
  let '(lt, q, rt) := c in
  match rt, lt with
  | Bk w v :: r, _ =>
    match first (tryR lt q w v r) ms with
    | Some c' => Some c'
    | None => match rot rt with Some rt' => Some (lt, q, rt') | None => None end
    end
  | _, Bk w v :: l =>
    match first (tryL l q w v rt) ms with
    | Some c' => Some c'
    | None =>
      match pstep c with
      | Some c' => Some c'
      | None => match rot lt with Some lt' => Some (lt', q, rt) | None => None end
      end
    end
  | _, _ => pstep c
  end.

Lemma sstep_spec x c c' : sstep c = Some c' -> cf x c -[ tm ]->* cf x c'.
Proof.
  assert (PS : pstep c = Some c' -> cf x c -[ tm ]->* cf x c').
  { intros H. apply evstep_one. apply pstep_spec. assumption. }
  destruct c as [[lt q] rt]. unfold sstep.
  assert (LB : forall w v l, lt = Bk w v :: l ->
    match first (tryL l q w v rt) ms with
    | Some c' => Some c'
    | None => match pstep (lt, q, rt) with
              | Some c' => Some c'
              | None => match rot lt with Some lt' => Some (lt', q, rt) | None => None end
              end
    end = Some c' -> cf x (lt, q, rt) -[ tm ]->* cf x c').
  { intros w v l ->. destruct (first (tryL l q w v rt) ms) as [c1|] eqn:E.
    - intros H; inverts H. apply first_spec in E as [m E]. eapply tryL_spec; eassumption.
    - destruct (pstep (Bk w v :: l, q, rt)) as [c1|] eqn:E1; [intros H; inverts H; auto|].
      destruct (rot (Bk w v :: l)) as [lt'|] eqn:E2; intros H; inverts H.
      cbn [cf]. unfold den. rewrite (rot_spec x _ _ E2). apply evstep_refl. }
  destruct rt as [|[s|w v] r].
  - destruct lt as [|[s|w v] l]; auto. apply (LB w v l eq_refl).
  - destruct lt as [|[s'|w v] l]; auto. apply (LB w v l eq_refl).
  - destruct (first (tryR lt q w v r) ms) as [c1|] eqn:E.
    + intros H; inverts H. apply first_spec in E as [m E]. eapply tryR_spec; eassumption.
    + destruct (rot (Bk w v :: r)) as [rt'|] eqn:E2; intros H; inverts H.
      cbn [cf]. unfold den. rewrite (rot_spec x _ _ E2). apply evstep_refl.
Qed.

(** A round: from state [qe] at the left end of the tape until [qe] steps onto a new
    cell at the left end again. *)
Definition D (x : nat * nat) (t : list tok) : Q * tape := cf x ([], qe, t).

Fixpoint run (f : nat) (c : conf) : option (list tok) :=
  match f with
  | O => None
  | S f =>
    match sstep c with
    | Some (lt', q', rt') =>
      match c with
      | ([], _, _) => if q_eqb q' qe && teqb lt' [] then Some rt' else run f (lt', q', rt')
      | _ => run f (lt', q', rt')
      end
    | None => None
    end
  end.

Lemma run_spec x f c rt : run f c = Some rt -> cf x c -[ tm ]->* D x rt.
Proof.
  revert c. induction f as [|f IH]; intros c; cbn [run]; [congruence|].
  destruct (sstep c) as [[[lt' q'] rt']|] eqn:E; [|congruence].
  apply (sstep_spec x) in E.
  assert (X : run f (lt', q', rt') = Some rt -> cf x c -[ tm ]->* D x rt).
  { intros H. eapply evstep_trans; [exact E | apply IH; assumption]. }
  destruct c as [[[|] q] r]; auto.
  destruct (q_eqb_spec q' qe); cbn; auto.
  destruct (teqb lt' []) eqn:El; auto.
  apply teqb_spec in El. subst. intros H; inverts H. exact E.
Qed.

Definition round (t : list tok) : option (list tok) :=
  match pstep ([], qe, t) with Some c => run (10 ^ 5) c | None => None end.

Lemma round_spec x t rt : round t = Some rt -> D x t -[ tm ]->+ D x rt.
Proof.
  unfold round. destruct (pstep ([], qe, t)) as [c|] eqn:E; [|congruence]. intros H.
  eapply progress_intro; [apply pstep_spec; eassumption | eapply run_spec; eassumption].
Qed.

End Checker.

(** ** Rewriting a token list without changing the tape *)

(** Trailing zeros. *)
Definition strip0 (t : list tok) : list tok :=
  fold_right (fun a acc => match a, acc with Cl S0, [] => [] | _, _ => a :: acc end) [] t.

Lemma strip0_spec x t : den x (strip0 t) = den x t.
Proof.
  unfold den. induction t as [|a t IH]; [reflexivity|].
  cbn [strip0 fold_right]. fold (strip0 t).
  assert (X : flat x (a :: strip0 t) *> const s0 = flat x (a :: t) *> const s0).
  { destruct a as [s|w v]; cbn [flat]; [cbn; congruence|]. rewrite !Str_app_assoc. congruence. }
  destruct a as [[|]|w v]; try exact X.
  destruct (strip0 t); [|exact X].
  cbn in *. rewrite <- IH. apply const_unfold.
Qed.

(** Blocks as far to the left as they go: the list is reversed, every block is moved
    away from the front with [c (w c)^n = (c w)^n c], and the list is reversed back. *)
Definition flip (t : list tok) : list tok :=
  rev (map (fun a => match a with Bk w v => Bk (rev w) v | _ => a end) t).

Lemma lpow_rev {X} (w : list X) n : rev (w ^^ n) = rev w ^^ n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [lpow]. rewrite rev_app_distr, IH, lpow_shift. reflexivity.
Qed.

Lemma flat_flip x t : flat x (flip t) = rev (flat x t).
Proof.
  unfold flip. induction t as [|[s|w v] t IH]; cbn; [reflexivity| |];
    rewrite flat_app, IH; cbn; rewrite ?rev_app_distr, ?lpow_rev, ?app_nil_r; reflexivity.
Qed.

Fixpoint push (w : list Sym) (v : bool) (r : list tok) : list tok :=
  match w, r with
  | c :: w', Cl c' :: r' => if sym_eqb c c' then Cl c :: push (w' ++ [c]) v r' else Bk w v :: r
  | _, _ => Bk w v :: r
  end.

Lemma push_spec x w v r : flat x (push w v r) = flat x (Bk w v :: r).
Proof.
  revert w. induction r as [|[c'|w' v'] r IH]; intros [|c w]; try reflexivity.
  cbn [push]. destruct (sym_eqb_spec c c'); [subst c'|reflexivity].
  cbn [flat]. rewrite IH. cbn [flat]. symmetry. apply lpow_rotate_list.
Qed.

Fixpoint rotall (t : list tok) : list tok :=
  match t with
  | [] => []
  | Cl c :: r => Cl c :: rotall r
  | Bk w v :: r => push w v (rotall r)
  end.

Lemma rotall_spec x t : flat x (rotall t) = flat x t.
Proof. induction t as [|[c|w v] t IH]; cbn [rotall]; rewrite ?push_spec; cbn; congruence. Qed.

Definition leftmost (t : list tok) : list tok := flip (rotall (flip t)).

Lemma leftmost_spec x t : flat x (leftmost t) = flat x t.
Proof. unfold leftmost. rewrite flat_flip, rotall_spec, flat_flip. apply rev_involutive. Qed.

(** [d] more copies of the word in front of every block. *)
Fixpoint expand (d : nat * nat) (t : list tok) : list tok :=
  match t with
  | [] => []
  | Cl c :: r => Cl c :: expand d r
  | Bk w v :: r => map Cl (w ^^ get d v) ++ Bk w v :: expand d r
  end.

Lemma expand_spec d x t : flat x (expand d t) = flat (fst d + fst x, snd d + snd x) t.
Proof.
  induction t as [|[c|w v] t IH]; cbn [expand flat]; [reflexivity|rewrite IH; reflexivity|].
  rewrite flat_app, flat_cells. cbn [flat]. rewrite IH, app_assoc, <- lpow_add.
  destruct v; reflexivity.
Qed.

(** Blocks of an unknown that is 0, and the two unknowns exchanged. *)
Definition dropv (v : bool) (t : list tok) : list tok :=
  filter (fun a => match a with Bk _ v' => negb (Bool.eqb v v') | _ => true end) t.
Definition swap (t : list tok) : list tok :=
  map (fun a => match a with Bk w v => Bk w (negb v) | _ => a end) t.

Lemma dropv_spec v x t : get x v = 0 -> flat x (dropv v t) = flat x t.
Proof.
  intros H. unfold dropv in *. induction t as [|[c|w v'] t IH]; cbn [filter flat]; [reflexivity|rewrite IH; reflexivity|].
  destruct (Bool.eqb_spec v v'); cbn [negb flat]; [subst; rewrite H; assumption|rewrite IH; reflexivity].
Qed.

Lemma swap_spec x t : flat x (swap t) = flat (snd x, fst x) t.
Proof. unfold swap. induction t as [|[c|w []] t IH]; cbn [map flat get negb fst snd]; rewrite ?IH; reflexivity. Qed.

(** ** Hints: not trusted, their results are checked *)

Fixpoint drop (w : list Sym) (t : list tok) : option (list tok) :=
  match w, t with
  | [], _ => Some t
  | c :: w, Cl c' :: t => if sym_eqb c c' then drop w t else None
  | _, _ => None
  end.

Definition inc (v : bool) (d : nat * nat) := if v then (fst d, S (snd d)) else (S (fst d), snd d).

(** Copies of the word after a block, all but one, counted into the block. *)
Fixpoint absorb (f : nat) (t : list tok) : list tok * (nat * nat) :=
  match f, t with
  | S f, Cl c :: r => let '(r', d) := absorb f r in (Cl c :: r', d)
  | S f, Bk w v :: r =>
    match drop w r with
    | Some r1 =>
      match drop w r1 with
      | Some _ => let '(t', d) := absorb f (Bk w v :: r1) in (t', inc v d)
      | None => let '(r', d) := absorb f r in (Bk w v :: r', d)
      end
    | None => let '(r', d) := absorb f r in (Bk w v :: r', d)
    end
  | _, _ => (t, (0, 0))
  end.

Definition W := [S0; S1; S0; S1; S0; S1].

Fixpoint skip01 (t : list tok) : list tok * list tok :=
  match t with
  | Cl S0 :: Cl S1 :: r => let '(a, b) := skip01 r in (Cl S0 :: Cl S1 :: a, b)
  | _ => ([], t)
  end.

(** A second block, at the start of the run of [01] after the first [000]. *)
Fixpoint ins (t : list tok) : option (list tok) :=
  match t with
  | [] => None
  | Cl c :: r => option_map (cons (Cl c)) (ins r)
  | Bk w v :: r =>
    let '(a, b) := skip01 r in
    match b with
    | Cl S0 :: Cl S0 :: Cl S0 :: b' =>
      match drop (W ++ W) b' with
      | Some _ => Some (Bk w v :: a ++ Cl S0 :: Cl S0 :: Cl S0 :: Bk W true :: b')
      | None => None
      end
    | _ => None
    end
  end.

(** ** The certificate *)

Section Cert.
Variable tm : TM.
Variable qe : Q.
Variable TP : list (list tok).
Variable N : nat.

Notation D := (D qe).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(** One round with one copy of the first block's word written out in front of it. *)
Definition next (t : list tok) : option (list tok * (nat * nat)) :=
  match round tm qe (expand (1, 0) t) with
  | Some rt =>
    let n := strip0 (leftmost rt) in
    let '(t', d) := absorb (S (length n)) n in
    if teqb (leftmost (expand d t')) n then Some (t', d) else None
  | None => None
  end.

Lemma D_ext x x' t t' : den x t = den x' t' -> D x t = D x' t'.
Proof. unfold D, D, cf. intros ->. reflexivity. Qed.

Lemma next_spec t t' d k j :
  next t = Some (t', d) -> D (S k, j) t -->+ D (fst d + k, snd d + j) t'.
Proof.
  unfold next. destruct (round tm qe (expand (1, 0) t)) as [rt|] eqn:E; [|congruence].
  destruct (absorb _ _) as [t1 d1]. destruct (teqb _ _) eqn:Et; intros H; inverts H.
  apply teqb_spec in Et. apply (round_spec tm qe (k, j)) in E.
  replace (D (S k, j) t) with (D (k, j) (expand (1, 0) t)).
  2: { apply D_ext. unfold den. rewrite expand_spec. reflexivity. }
  replace (D (fst d + k, snd d + j) t') with (D (k, j) rt); [exact E|].
  apply D_ext. transitivity (den (k, j) (strip0 (leftmost rt))).
  - rewrite strip0_spec. unfold den. rewrite leftmost_spec. reflexivity.
  - rewrite <- Et. unfold den. rewrite leftmost_spec, expand_spec. reflexivity.
Qed.

(** [p] rounds from a seed. *)
Fixpoint orbit (p : nat) (t : list tok) : list (list tok) :=
  match p with
  | O => []
  | S p => t :: match next t with Some (t', _) => orbit p t' | None => [] end
  end.

Definition mem (t : list tok) : bool := existsb (teqb t) TP.

Lemma mem_spec t : mem t = true -> In t TP.
Proof.
  unfold mem. intros H. apply existsb_exists in H as [t' [H1 H2]].
  apply teqb_spec in H2. congruence.
Qed.

(** Rounds until a template is reached.  While the second unknown is 0, a block of
    that unknown is put where the second block of a template is. *)
Fixpoint trans (f : nat) (t : list tok) (J : nat) : option (list tok * nat * nat * nat) :=
  match f with
  | O => None
  | S f =>
    if mem t then Some (t, 0, 0, J) else
    let t1 := match J, ins t with
              | 0, Some t2 => if teqb (dropv true t2) t then t2 else t
              | _, _ => t
              end in
    match next t1 with
    | Some (t', (d0, d1)) =>
      match trans f t' (d1 + J) with
      | Some (r, n, a, J') => Some (r, S n, d0 + a, J')
      | None => None
      end
    | None => None
    end
  end.

Lemma trans_spec f t J r n a J' :
  trans f t J = Some (r, n, a, J') ->
  In r TP /\ forall k, D (n + k, J) t -->* D (a + k, J') r /\ (0 < n -> D (n + k, J) t -->+ D (a + k, J') r).
Proof.
  revert t J r n a J'. induction f as [|f IH]; intros t J r n a J'; cbn [trans]; [congruence|].
  destruct (mem t) eqn:Em.
  { intros H; inverts H. split; [apply mem_spec; assumption|].
    intros k. split; [apply evstep_refl | lia]. }
  set (t1 := match J, ins t with
             | 0, Some t2 => if teqb (dropv true t2) t then t2 else t
             | _, _ => t
             end).
  assert (E1 : forall k, D (k, J) t = D (k, J) t1).
  { intros k. subst t1. destruct J; [|reflexivity]. destruct (ins t) as [t2|]; [|reflexivity].
    destruct (teqb (dropv true t2) t) eqn:Et; [|reflexivity]. apply teqb_spec in Et.
    apply D_ext. unfold den. rewrite <- Et, dropv_spec; reflexivity. }
  destruct (next t1) as [[t' [d0 d1]]|] eqn:En; [|congruence].
  destruct (trans f t' (d1 + J)) as [[[[r0 n0] a0] J0]|] eqn:Et; intros H; inverts H.
  destruct (IH _ _ _ _ _ _ Et) as [I1 I2]. split; [assumption|].
  intros k.
  assert (X : D (S n0 + k, J) t -->+ D (d0 + a0 + k, J') r).
  { pose proof (next_spec _ _ _ (n0 + k) J En) as X1. cbn [fst snd] in X1.
    destruct (I2 (d0 + k)) as [I3 _].
    replace (d0 + (n0 + k)) with (n0 + (d0 + k)) in X1 by lia.
    replace (d0 + a0 + k) with (a0 + (d0 + k)) by lia.
    rewrite E1. eapply progress_evstep_trans; [exact X1 | exact I3]. }
  split; [apply progress_evstep|]; auto.
Qed.

(** What is checked for every template [t]: a round at [k + 1] leads to a template with
    the second unknown larger, and at [k = 0] at most [N] rounds lead to a template
    without lowering the sum of the unknowns. *)
Definition ok (t : list tok) : bool :=
  match next t with
  | Some (t', (0, S _)) => mem t'
  | _ => false
  end &&
  match trans (S N) (dropv true (swap t)) 0 with
  | Some (_, S n, a, J') => (S n <=? a + J') && (S n <=? N)
  | _ => false
  end.

Definition Good (c : Q * tape) : Prop :=
  exists t k j, In t TP /\ c = D (k, j) t /\ N <= k + j.

Lemma Good_step : forallb ok TP = true -> forall c, Good c -> exists c', Good c' /\ c -->+ c'.
Proof.
  intros H c [t [k [j [Ht [-> Hk]]]]].
  rewrite forallb_forall in H. apply H in Ht. apply andb_prop in Ht as [H1 H2].
  destruct k as [|k].
  - destruct (trans (S N) (dropv true (swap t)) 0) as [[[[r [|n]] a] J']|] eqn:Et; try congruence.
    apply andb_prop in H2 as [H3 H4]. apply Nat.leb_le in H3, H4.
    destruct (trans_spec _ _ _ _ _ _ _ Et) as [I1 I2].
    destruct (I2 (j - S n)) as [_ I3].
    exists (D (a + (j - S n), J') r). split; [exists r, (a + (j - S n)), J'; repeat split; [assumption|lia]|].
    replace (D (0, j) t) with (D (S n + (j - S n), 0) (dropv true (swap t))); [apply I3; lia|].
    apply D_ext. unfold den. rewrite dropv_spec by reflexivity. rewrite swap_spec. cbn [fst snd].
    replace (S n + (j - S n)) with j by lia. reflexivity.
  - destruct (next t) as [[t' [[|] [|d]]]|] eqn:En; try congruence.
    exists (D (k, S d + j) t'). split; [exists t', k, (S d + j); repeat split; [apply mem_spec; assumption|lia]|].
    apply (next_spec _ _ _ _ _ En).
Qed.

Theorem nonhalt_of_cert k j t :
  forallb ok TP = true -> mem t = true -> N <=? k + j = true -> c0 -->* D (k, j) t -> ~ halts tm c0.
Proof.
  intros H Ht Hk Hs. apply multistep_nonhalt with (c' := D (k, j) t).
  - exact Hs.
  - apply progress_nonhalt with (P := Good); [apply Good_step; assumption|].
    exists t, k, j. repeat split; [apply mem_spec; assumption | apply Nat.leb_le; assumption].
Qed.

End Cert.

(** The run from blank tape, by plain simulation. *)
Lemma start_spec tm qe x t n :
  cconfig_evstep_dec tm ([], [], s0, q0) ([], tl (flat x t), hd s0 (flat x t), qe) n = true ->
  c0 -[ tm ]->* D qe x t.
Proof.
  intros H. apply cconfig_evstep_dec_spec in H.
  unfold D, cf, den. destruct (flat x t); exact H.
Qed.
