Require Import List Bool Lia String.
From BusyCoq Require Import Individual62.
Open Scope string.
Import ListNotations.

(** * Two machines that differ by one word at the right end of the tape

    tm  = 1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE
    tm' = 1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC

    tm' is tm read in a mirror with the states renamed by [g], so a run of tm'
    is a mirrored run of the table of tm.  From blank tape the two runs reach,
    after 2 and 49 steps, the same tape except that the run of tm' has the
    word W8 = 10001101 once more at the far end.  From then on the two runs go
    in lockstep: the extra word is never read, except when the head leaves the
    rightmost cell q it has visited.  That happens only in state B on a 1, and
    then both runs cross the far end (5 steps without the word, 49 with it) and
    come back with the same cells left of q, q having moved two cells right.

    The model [Cfg] is a configuration of tm with the head inside the last four
    cells up to q ([Inn]) or further left ([Out]).  [to_config false] reads it
    as a configuration of tm, [to_config true] as the mirrored configuration of
    tm' with W8 placed after q.  One model step [f] is one step of both
    machines, or the far-end crossing ([far0], [far1]).  The invariant [P] says
    that the abstraction of the model configuration (the last four cells, and
    the state and head position when the head is among them) is one of the 28
    entries of [S0].  None of them moves right from q except in state B on a 1,
    and [S0] is closed under the abstract step [anext] ([check_S0]).

    [eqv] is the whole result: tm halts from blank tape iff tm' does.  It does
    not decide either machine. *)

Module TailWord.
Open Scope sym.

Definition tm := Eval compute in (TM_from_str "1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE").
Definition tm' := Eval compute in (TM_from_str "1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC").
Close Scope string.
Definition machine (b:bool) := if b then tm' else tm.

(** The renaming of states from tm to tm'. *)
Definition g q := match q with A=>D | B=>E | C=>A | D=>B | E=>C | F=>F end.

Definition flipd d := match d with L => R | R => L end.

Lemma tm'_none q a: tm (q, a) = None -> tm' (g q, a) = None.
Proof. intros H; destruct q, a; cbn in H |- *; congruence. Qed.

Lemma tm'_some q a a' d q': tm (q, a) = Some (a', d, q') ->
  tm' (g q, a) = Some (a', flipd d, g q').
Proof. intros H; destruct q, a; cbn in H |- *; inversion H; subst; reflexivity. Qed.

(** The extra word, as tm reads it from left to right. *)
Definition W8 : list Sym := [1;0;0;0;1;1;0;1].

(** [Inn q X wl a u]: the head reads [a] in state [q], [wl] is the part of the
    window left of the head (nearest first) and [X] the tape beyond it, and [u]
    the cells right of the head up to q.  [Out q l a v w]: the head reads [a],
    [l] is the whole tape on its left, then come [v] and the window [w], whose
    last cell is q. *)
Inductive Cfg :=
| Inn (q:Q) (X:side) (wl:list Sym) (a:Sym) (u:list Sym)
| Out (q:Q) (l:side) (a:Sym) (v w:list Sym).

Definition to_config (b:bool) (c:Cfg) : Q * tape :=
  match c with
  | Inn q X wl a u =>
    if b then (g q, (u *> W8 *> 0inf, a, wl *> X))
         else (q, (wl *> X, a, u *> 0inf))
  | Out q l a v w =>
    if b then (g q, ((v ++ w) *> W8 *> 0inf, a, l))
         else (q, (l, a, (v ++ w) *> 0inf))
  end.

(** One step of the model. *)
Definition f (c:Cfg) : option Cfg :=
  match c with
  | Inn q X wl a u =>
    match tm (q, a) with
    | None => None
    | Some (a', L, q') =>
      match wl with
      | x :: wl' => Some (Inn q' X wl' x (a' :: u))
      | [] => Some (Out q' (Streams.tl X) (Streams.hd X) [] (a' :: u))
      end
    | Some (a', R, q') =>
      match u with
      | b :: u' => Some (Inn q' X (a' :: wl) b u')
      | [] => (* B on q: cross the far end and come back in D *)
        match wl with
        | x :: wl' => Some (Inn D (wl' *> X) [] x [1;0;1])
        | [] => Some (Inn D (Streams.tl X) [] (Streams.hd X) [1;0;1])
        end
      end
    end
  | Out q l a v w =>
    match tm (q, a) with
    | None => None
    | Some (a', L, q') => Some (Out q' (Streams.tl l) (Streams.hd l) (a' :: v) w)
    | Some (a', R, q') =>
      match v with
      | b :: v' => Some (Out q' (a' >> l) b v' w)
      | [] =>
        match w with
        | b :: w' => Some (Inn q' (a' >> l) [] b w')
        | [] => None
        end
      end
    end
  end.

Definition cfg0 := Inn C 0inf [0;0] 1 [1].

(** ** The abstraction *)

Inductive Ab :=
| inn (q:Q) (wl:list Sym) (a:Sym) (u:list Sym)
| out (w:list Sym).

Definition abs c :=
  match c with
  | Inn q _ wl a u => inn q wl a u
  | Out _ _ _ _ w => out w
  end.

Definition Ab_eq_dec (x y:Ab) : {x = y} + {x <> y}.
Proof.
  pose proof (list_eq_dec eqb_sym) as Hl.
  decide equality; solve [apply Hl | apply eqb_sym | apply eqb_q].
Defined.

(** The states a move to the right can lead to. *)
Definition rTargets := [B;D;E;F].

Definition anext (s:Ab) : list Ab :=
  match s with
  | inn q wl a u =>
    match tm (q, a) with
    | None => []
    | Some (a', L, q') =>
      match wl with
      | x :: wl' => [inn q' wl' x (a' :: u)]
      | [] => [out (a' :: u)]
      end
    | Some (a', R, q') =>
      match u with
      | b :: u' => [inn q' (a' :: wl) b u']
      | [] =>
        match wl with
        | x :: _ => [inn D [] x [1;0;1]]
        | [] => [inn D [] 0 [1;0;1]; inn D [] 1 [1;0;1]]
        end
      end
    end
  | out w =>
    out w ::
    match w with
    | b :: w' => List.map (fun q' => inn q' [] b w') rTargets
    | [] => []
    end
  end.

(** No move right from q except in state B on a 1; the window is never empty. *)
Definition okb (s:Ab) : bool :=
  match s with
  | inn B _ 1 [] => true
  | inn q _ a [] =>
    match tm (q, a) with
    | Some (_, R, _) => false
    | _ => true
    end
  | inn _ _ _ _ => true
  | out [] => false
  | out _ => true
  end.

Definition mem s xs := if in_dec Ab_eq_dec s xs then true else false.

(** The 28 abstract configurations reached from [cfg0]: 26 with the head in
    the window, 2 with the head further left.  [check_S0] verifies that the
    list is closed under [anext] and passes [okb]; it does not have to be
    complete. *)
Definition S0 : list Ab := [
  inn A [] 0 [1;0;1];
  inn B [] 0 [1;0;1];
  inn B [] 1 [1;0;1];
  inn B [1] 0 [0;1];
  inn B [1] 1 [0;1];
  inn B [1;0;0] 0 [];
  inn B [1;0;1] 1 [];
  inn C [] 1 [1;0;1];
  inn C [0] 0 [0;1];
  inn C [0;0] 1 [1];
  inn D [] 0 [1;0;1];
  inn D [] 1 [1;0;1];
  inn D [0] 0 [0;1];
  inn D [0] 1 [0;1];
  inn D [0;0;0] 1 [];
  inn E [] 0 [0;0;1];
  inn E [] 0 [1;0;1];
  inn E [] 1 [1;0;1];
  inn E [0] 1 [0;1];
  inn E [0;0] 0 [1];
  inn F [] 0 [0;0;1];
  inn F [] 0 [1;0;1];
  inn F [] 1 [1;0;1];
  inn F [0] 1 [0;1];
  inn F [0;0] 0 [0];
  inn F [0;1] 0 [1];
  out [0;1;0;1];
  out [1;1;0;1]].

Definition check (xs:list Ab) :=
  forallb (fun s => andb (okb s) (forallb (fun t => mem t xs) (anext s))) xs.

Lemma check_S0 : check S0 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma mem_spec s xs: mem s xs = true -> In s xs.
Proof. unfold mem. destruct (in_dec Ab_eq_dec s xs); congruence. Qed.

Lemma closed s: In s S0 -> okb s = true /\ forall t, In t (anext s) -> In t S0.
Proof.
  intros H.
  pose proof check_S0 as Hc. unfold check in Hc.
  rewrite forallb_forall in Hc.
  specialize (Hc s H). apply andb_prop in Hc. destruct Hc as [H1 H2].
  split; [exact H1 |].
  intros t Ht. rewrite forallb_forall in H2. apply mem_spec, H2, Ht.
Qed.

Definition P c := In (abs c) S0.

Lemma anext_spec c c': f c = Some c' -> In (abs c') (anext (abs c)).
Proof.
  destruct c as [q X wl a u|q l a v w]; cbn [f abs anext];
  destruct (tm (q, a)) as [[[a' []] q']|] eqn:Ht; try discriminate.
  - destruct wl; intros H; inversion H; subst; cbn; auto.
  - destruct u as [|b u'].
    + destruct wl; intros H; inversion H; subst; cbn [abs]; [| left; reflexivity].
      destruct (Streams.hd X); cbn; auto.
    + intros H; inversion H; subst; cbn; auto.
  - intros H; inversion H; subst; cbn; auto.
  - destruct v as [|b v'].
    + destruct w as [|b w']; intros H; inversion H; subst.
      right. cbn [abs]. apply (List.in_map (fun t => inn t [] b w')).
      destruct q, a; cbn in Ht; inversion Ht; subst; cbn; tauto.
    + intros H; inversion H; subst; cbn; auto.
Qed.

Lemma P_step c c': P c -> f c = Some c' -> P c'.
Proof.
  intros HP E. apply (closed _ HP). apply anext_spec, E.
Qed.

(** ** The steps of the two machines *)

Lemma stream_eta (X:side): X = Streams.hd X >> Streams.tl X.
Proof. destruct X; reflexivity. Qed.

(** The far end, without the word (tm) and with it (tm'). *)
Lemma far0 x Y:
  B;; x >> Y {{1}} 0inf -[tm]->+ D;; Y {{x}} [1;0;1] *> 0inf.
Proof. destruct x; execute. Qed.

Lemma far1 x Y:
  E;; W8 *> 0inf {{1}} x >> Y -[tm']->+ B;; [1;0;1] *> W8 *> 0inf {{x}} Y.
Proof. destruct x; unfold W8; execute. Qed.

Lemma halted_halts' tm0 c: halted tm0 c -> halts tm0 c.
Proof. intros H. exists 0%nat. exists c. split; [constructor | exact H]. Qed.

Lemma step_left' (tm0:TM) q q' l s s' r c':
  tm0 (q, s) = Some (s', L, q') -> c' = (q', move_left (l, s', r)) ->
  (q, (l, s, r)) -[ tm0 ]->+ c'.
Proof. intros H ->. apply progress_base, step_left, H. Qed.

Lemma step_right' (tm0:TM) q q' l s s' r c':
  tm0 (q, s) = Some (s', R, q') -> c' = (q', move_right (l, s', r)) ->
  (q, (l, s, r)) -[ tm0 ]->+ c'.
Proof. intros H ->. apply progress_base, step_right, H. Qed.

Lemma f_spec b c: P c ->
  match f c with
  | Some c' => to_config b c -[ machine b ]->+ to_config b c' /\ P c'
  | None => halts (machine b) (to_config b c)
  end.
Proof.
  intros HP.
  destruct (closed _ HP) as [Hok _].
  destruct (f c) as [c'|] eqn:E.
  2: {
    destruct c as [q X wl a u|q l a v w]; cbn [f] in E;
    destruct (tm (q, a)) as [[[a' []] q']|] eqn:Ht.
    all: try (destruct wl; discriminate E).
    all: try (destruct u; [destruct wl|]; discriminate E).
    all: try (apply halted_halts'; destruct b; cbn [halted to_config machine];
              [exact (tm'_none _ _ Ht) | exact Ht]).
    (* an empty window, excluded by [okb] *)
    all: try (apply halted_halts'; destruct b; cbn [halted to_config machine]; [exact (tm'_none _ _ Ht) | exact Ht]).
    all: destruct v; [destruct w; [discriminate Hok | discriminate E] | discriminate E].
  }
  split; [| exact (P_step _ _ HP E)].
  destruct c as [q X wl a u|q l a v w]; cbn [f] in E;
  destruct (tm (q, a)) as [[[a' []] q']|] eqn:Ht; try discriminate.
  - (* left *)
    destruct wl as [|x wl']; inversion E; subst; clear E;
    destruct b; cbn [to_config machine];
    [ eapply step_right'; [exact (tm'_some _ _ _ _ _ Ht) | reflexivity]
    | eapply step_left'; [exact Ht | reflexivity]
    | eapply step_right'; [exact (tm'_some _ _ _ _ _ Ht) | reflexivity]
    | eapply step_left'; [exact Ht | reflexivity] ].
  - (* right *)
    destruct u as [|b' u'].
    + (* from q: only B on a 1 *)
      assert (q = B /\ a = 1) as [-> ->].
      { destruct q, a; cbn in Ht; inversion Ht; subst; cbn in Hok;
        solve [split; reflexivity | discriminate Hok]. }
      cbn in Ht. inversion Ht; subst; clear Ht.
      destruct wl as [|x wl']; inversion E; subst; clear E.
      * rewrite (stream_eta X) at 1 2.
        destruct b; cbn [to_config machine Str_app g]; [apply far1 | apply far0].
      * destruct b; cbn [to_config machine Str_app g]; [apply far1 | apply far0].
    + inversion E; subst; clear E.
      destruct b; cbn [to_config machine];
      [ eapply step_left'; [exact (tm'_some _ _ _ _ _ Ht) | reflexivity]
      | eapply step_right'; [exact Ht | reflexivity] ].
  - (* left *)
    inversion E; subst; clear E.
    destruct b; cbn [to_config machine];
    [ eapply step_right'; [exact (tm'_some _ _ _ _ _ Ht) | reflexivity]
    | eapply step_left'; [exact Ht | reflexivity] ].
  - (* right *)
    destruct v as [|b' v'].
    + destruct w as [|b' w']; inversion E; subst; clear E.
      destruct b; cbn [to_config machine];
      [ eapply step_left'; [exact (tm'_some _ _ _ _ _ Ht) | reflexivity]
      | eapply step_right'; [exact Ht | reflexivity] ].
    + inversion E; subst; clear E.
      destruct b; cbn [to_config machine];
      [ eapply step_left'; [exact (tm'_some _ _ _ _ _ Ht) | reflexivity]
      | eapply step_right'; [exact Ht | reflexivity] ].
Qed.

(** ** The runs from blank tape *)

Lemma init0: c0 -[tm]->* to_config false cfg0.
Proof.
  cbn. rewrite <-!const_unfold. execute.
Qed.

Lemma init1: c0 -[tm']->* to_config true cfg0.
Proof.
  cbn. rewrite <-!const_unfold. unfold W8. execute.
Qed.

Lemma eqv_model b: halts (machine b) c0 <-> iter_halts f cfg0.
Proof.
  rewrite (halts_evstep_iff _ _ (to_config b cfg0)).
  2: destruct b; [apply init1 | apply init0].
  apply (halts_iff _ _ cfg0 f (to_config b) P).
  - intros c Hc. apply f_spec, Hc.
  - unfold P. vm_compute. tauto.
Qed.

Theorem eqv: halts tm c0 <-> halts tm' c0.
Proof. rewrite (eqv_model false), (eqv_model true). tauto. Qed.

End TailWord.

Print Assumptions TailWord.eqv.
