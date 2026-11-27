Require Import List Bool String.
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
    the state and head position when the head is among them) belongs to the
    computed set [S0].  The checker [check_S0] establishes closure and rules
    out any move right from q except in state B on a 1.

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

Definition orient (b:bool) (q:Q) (l:side) (a:Sym) (r:side) : Q * tape :=
  if b then (g q, (r, a, l)) else (q, (l, a, r)).

Definition tail (b:bool) := if b then W8 *> 0inf else 0inf.

Definition to_config (b:bool) (c:Cfg) : Q * tape :=
  match c with
  | Inn q X wl a u => orient b q (wl *> X) a (u *> tail b)
  | Out q l a v w => orient b q l a ((v ++ w) *> tail b)
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

(** [f] reads only the symbol at the head of [X] while in the window.
    Outside, the only observable event is crossing back into the window;
    this depends on the state, read symbol, and whether [v] is empty.
    Use a representative for each of these cases and run [f] itself. *)
Definition symbols : list Sym := [0;1].
Definition states : list Q := [A;B;C;D;E;F].

Definition representatives (s:Ab) : list Cfg :=
  match s with
  | inn q wl a u => List.map (fun x => Inn q (const x) wl a u) symbols
  | out w =>
    flat_map (fun q => flat_map (fun a => [Out q 0inf a [] w; Out q 0inf a [0] w])
                                symbols) states
  end.

Definition abstract_step c := option_map abs (f c).
Definition anext s :=
  flat_map (fun c => match abstract_step c with
                    | Some t => [t] | None => [] end) (representatives s).

Lemma representatives_cover c :
  exists rep, In rep (representatives (abs c)) /\ abstract_step rep = abstract_step c.
Proof.
  destruct c as [q X wl a u | q l a [|x v] w].
  - exists (Inn q (const (Streams.hd X)) wl a u).
    split; [simpl; destruct (Streams.hd X); auto |].
    unfold abstract_step; cbn [f].
    destruct (tm (q, a)) as [[[a' []] q']|]; [destruct wl|destruct u, wl|];
      reflexivity.
  - exists (Out q 0inf a [] w).
    split.
    + cbn [abs representatives]. apply in_flat_map. exists q.
      split; [destruct q; simpl; tauto |].
      apply in_flat_map. exists a. destruct a; simpl; auto.
    + unfold abstract_step; cbn [f].
      destruct (tm (q, a)) as [[[a' []] q']|]; [|destruct w|]; reflexivity.
  - exists (Out q 0inf a [0] w).
    split.
    + cbn [abs representatives]. apply in_flat_map. exists q.
      split; [destruct q; simpl; tauto |].
      apply in_flat_map. exists a. destruct a; simpl; auto.
    + unfold abstract_step; cbn [f].
      destruct (tm (q, a)) as [[[a' []] q']|]; reflexivity.
Qed.

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

(** Discover a candidate set by bounded worklist search.  The fuel is only
    a computation budget: closure and initial membership are checked below,
    independently of how the candidate was generated. *)
Fixpoint discover (fuel:nat) (todo seen:list Ab) : list Ab :=
  match fuel, todo with
  | S n, s :: rest =>
    if mem s seen then discover n rest seen
    else discover n (anext s ++ rest) (s :: seen)
  | _, _ => seen
  end.

Definition S0 := Eval vm_compute in discover 128 [abs cfg0] [].

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
  intros H. destruct (representatives_cover c) as [rep [Hin Hrep]].
  unfold anext. apply in_flat_map. exists rep. split; [exact Hin|].
  rewrite Hrep. unfold abstract_step. rewrite H. simpl; auto.
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

Lemma orient_halt b q l a r :
  tm (q, a) = None -> halts (machine b) (orient b q l a r).
Proof.
  intros H. apply halted_halts. destruct b; [apply tm'_none|]; exact H.
Qed.

Lemma orient_step b q l a r a' d q' c' :
  tm (q, a) = Some (a', d, q') ->
  c' = (match d with
        | L => orient b q' (Streams.tl l) (Streams.hd l) (a' >> r)
        | R => orient b q' (a' >> l) (Streams.hd r) (Streams.tl r)
        end) ->
  orient b q l a r -[machine b]->+ c'.
Proof.
  intros H ->. destruct b, d; apply progress_base;
    first [apply step_left | apply step_right];
    first [exact H | exact (tm'_some _ _ _ _ _ H)].
Qed.

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
    all: try (cbn [to_config]; apply orient_halt; exact Ht).
    (* an empty window, excluded by [okb] *)
    all: destruct v; [destruct w; [discriminate Hok | discriminate E] | discriminate E].
  }
  split; [| exact (P_step _ _ HP E)].
  destruct c as [q X wl a u|q l a v w]; cbn [f] in E;
  destruct (tm (q, a)) as [[[a' []] q']|] eqn:Ht; try discriminate.
  - destruct wl; inversion E; subst; cbn [to_config];
      (eapply orient_step; [exact Ht | reflexivity]).
  - destruct u as [|x u'].
    2: { inversion E; subst; cbn [to_config].
         eapply orient_step; [exact Ht | reflexivity]. }
    (* The exceptional right move is possible only in B on 1. *)
    assert (q = B /\ a = 1) as [-> ->].
    { destruct q, a; cbn in Ht; inversion Ht; subst; cbn in Hok;
      solve [split; reflexivity | discriminate Hok]. }
    destruct wl as [|x wl']; inversion E; subst; clear E.
    + rewrite (stream_eta X) at 1 2. destruct b; [apply far1 | apply far0].
    + destruct b; [apply far1 | apply far0].
  - inversion E; subst; cbn [to_config].
    eapply orient_step; [exact Ht | reflexivity].
  - destruct v as [|x v']; [destruct w|]; inversion E; subst; cbn [to_config];
      (eapply orient_step; [exact Ht | reflexivity]).
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
