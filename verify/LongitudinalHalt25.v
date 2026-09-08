From BusyCoq Require Import Individual25.

(** [sideRLs] only describes calls in which every signal returns.  This
    companion predicate describes a finite signal stream whose execution
    halts while processing one of its signals; the unused suffix is retained
    in the index but is deliberately unconstrained. *)
Inductive sideRLs_halt (tm : TM) : list (DH0 * DH0) -> side -> Prop :=
| sideRLs_halt_here hR hL hs r :
    (forall l, halts tm (l {{{ (hR,R) }}} r)) ->
    sideRLs_halt tm ((hR,hL)::hs) r
| sideRLs_halt_next hR hL hs r r' :
    sideRL tm hR hL r r' ->
    sideRLs_halt tm hs r' ->
    sideRLs_halt tm ((hR,hL)::hs) r.

#[export] Hint Constructors sideRLs_halt : core.

Lemma sideRLs_halt_app_left tm hs1 hs2 r :
  sideRLs_halt tm hs1 r ->
  sideRLs_halt tm (hs1 ++ hs2) r.
Proof.
  intros H.
  induction H; cbn; eauto.
Qed.

Lemma sideRLs_halt_app_right tm hs1 hs2 r r' :
  sideRLs tm hs1 r r' ->
  sideRLs_halt tm hs2 r' ->
  sideRLs_halt tm (hs1 ++ hs2) r.
Proof.
  intros H.
  induction H; cbn; eauto.
Qed.

Lemma sideRLs_halt_split tm hs1 hs2 r :
  sideRLs_halt tm (hs1 ++ hs2) r ->
  sideRLs_halt tm hs1 r \/
  exists r', sideRLs tm hs1 r r' /\ sideRLs_halt tm hs2 r'.
Proof.
  gen r.
  induction hs1 as [|[hR hL] hs1 IH]; cbn; intros r H.
  - right. exists r. split; [constructor|exact H].
  - inverts H.
    + left. constructor. exact H4.
    + specialize (IH _ H5).
      destruct IH as [IH|[r'' [IH1 IH2]]].
      * left. econstructor 2; eauto.
      * right. exists r''. split; [econstructor; eauto|exact IH2].
Qed.

(** A halting version of [sideRLs_segLRs_concat].  It is the extra case
    needed by the [segRLs_lrcons] constructor: after each returned right-side
    call, [segLRs] carries the head through the finite word to the next call. *)
Lemma sideRLs_halt_segLRs_concat tm hs h1 h2 w1 w2 r :
  segLRs tm hs w1 w2 ->
  sideRLs_halt tm (lrcons h1 hs h2) r ->
  forall l, halts tm (l <* w1 {{{ (h1,R) }}} r).
Proof.
  intros Hseg.
  gen h1 h2 r.
  induction Hseg; intros h1' h2' r Hhalt l.
  - cbn in Hhalt.
    inverts Hhalt; eauto.
    match goal with
    | Hnone : sideRLs_halt _ [] _ |- _ => inverts Hnone
    end.
  - cbn in Hhalt.
    inverts Hhalt.
    + eauto.
    + eapply halts_evstep.
      1: eapply IHHseg; eassumption.
      eapply progress_evstep.
      eapply progress_evstep_trans with
        (c' := (w1 *> l) {{{ (h1,L) }}} r').
      * apply H4.
      * apply H.
Qed.

(** If a segment emits a signal stream which later halts, then the input
    stream halts as well.  Unlike the extensional experiment in the old
    backup file, this theorem is proved by induction over the actual
    [segRLs] derivation, so the halting case cannot hold vacuously. *)
Lemma segRLs_sideRLs_halt_concat tm hs1 hs2 w1 w2 r :
  segRLs tm hs1 hs2 w1 w2 ->
  sideRLs_halt tm hs2 r ->
  sideRLs_halt tm hs1 (w1 *> r).
Proof.
  intros Hseg.
  gen r.
  induction Hseg; intros r Hhalt.
  - inverts Hhalt.
  - econstructor 2.
    + intros l. apply H.
    + eapply IHHseg. exact Hhalt.
  - apply sideRLs_halt_split in Hhalt.
    destruct Hhalt as [Hprefix|[r' [Hprefix Hsuffix]]].
    + constructor 1. intros l.
      eapply halts_evstep.
      1: eapply sideRLs_halt_segLRs_concat; eauto.
      apply H.
    + econstructor 2.
      * intros l.
        follow H.
        eapply progress_evstep_trans.
        2: apply H0.
        eapply sideRLs_segLRs_concat; eauto.
      * eapply IHHseg. exact Hsuffix.
Qed.

Lemma sideRLs_halt_single tm hR hL r :
  sideRLs_halt tm [(hR,hL)] r ->
  forall l, halts tm (l {{{ (hR,R) }}} r).
Proof.
  intros H l. inverts H; eauto.
  match goal with
  | Hnone : sideRLs_halt _ [] _ |- _ => inverts Hnone
  end.
Qed.

(* Unlike sideRL_rec, keep fuel exhaustion distinct from halting. *)
Inductive SideResult :=
| OutOfFuel
| Returned (q:Q) (r:side)
| Halted.

Definition result_spec tm l0 c result := match result with
| OutOfFuel => True
| Returned q r => c -[tm]->+ l0 <{{q}} r
| Halted => halts tm c end.

Lemma result_step tm l0 c c' result :
  c -[tm]-> c' -> result_spec tm l0 c' result -> result_spec tm l0 c result.
Proof. destruct result; cbn; intros; eauto using progress_step,halts_step. Qed.

Fixpoint sideRL_halt_rec (tm:TM) (l:list Sym) (r:side) (q:Q) (T:nat) :=
match T with
| O => OutOfFuel
| S T => match r with m>>r => match tm(q,m) with
  | None => Halted
  | Some(m,L,q) => match l with
    | [] => Returned q (m>>r)
    | m'::l => sideRL_halt_rec tm l (m'>>m>>r) q T end
  | Some(m,R,q) => sideRL_halt_rec tm (m::l) r q T
  end end
end.

Lemma sideRL_halt_rec_spec tm T : forall l r q l0,
  result_spec tm l0 (l0 <* l {{q}}> r) (sideRL_halt_rec tm l r q T).
Proof.
  induction T; intros l [m r] q l0; cbn[sideRL_halt_rec result_spec]; [trivial|].
  destruct (tm(q,m)) as [[[m' []] q']|] eqn:E.
  - destruct l as [|x l].
    + cbn[result_spec]; do 2 econstructor; exact E.
    + eapply result_step; [eapply step_left; exact E|exact (IHT l (x>>m'>>r) q' l0)].
  - eapply result_step; [eapply step_right; exact E|exact (IHT (m'::l) r q' l0)].
  - apply halted_halts; exact E.
Qed.

Fixpoint signals_halt_c tm (qs:list Q) r T := match qs with
| [] => false
| q::qs => match sideRL_halt_rec tm [] r q T with
  | Halted => true
  | Returned A r => signals_halt_c tm qs r T
  | _ => false end
end.
Definition calls (qs:list Q) : list (DH0*DH0) :=
  List.map (fun q=>((q,[]),(A,[]))) qs.

Lemma signals_halt_c_spec tm qs r T : signals_halt_c tm qs r T=true ->
  sideRLs_halt tm (calls qs) r.
Proof.
  revert r; induction qs as [|q qs IH]; intro r; cbn[signals_halt_c calls]; [discriminate|].
  pose proof (sideRL_halt_rec_spec tm T [] r q) as H.
  destruct (sideRL_halt_rec tm [] r q T) as [|q' r'|]; cbn[result_spec] in H;
    try discriminate.
  - destruct q'; [|discriminate]; intro E; econstructor 2; [exact H|apply IH; exact E].
  - intro E; constructor 1; exact H.
Qed.

(* A suspended right call: either it halts, or it returns and a later call
   in the finite continuation halts. The external left side is untouched. *)
Definition PendingHalts tm hs l r q :=
  (forall l0, halts tm (l0 <* l {{q}}> r)) \/
  exists r', (forall l0, l0 <* l {{q}}> r -[tm]->+ l0 <{{A}} r') /\
    sideRLs_halt tm hs r'.

Lemma pending_step tm hs l r q l' r' q' :
  (forall l0, l0 <* l {{q}}> r -[tm]-> l0 <* l' {{q'}}> r') ->
  PendingHalts tm hs l' r' q' -> PendingHalts tm hs l r q.
Proof.
  intros HS [HH|[last [HR HH]]].
  - left; intro l0; eapply halts_step; eauto.
  - right; exists last; split; [intro l0; eapply progress_step; eauto|assumption].
Qed.
Lemma pending_calls tm qs r q : PendingHalts tm (calls qs) [] r q ->
  sideRLs_halt tm (calls (q::qs)) r.
Proof. intros [H|[r' [HR HH]]]; [constructor 1; exact H|econstructor 2; eauto]. Qed.

Record RightConfig := right_config {
  rc_q:Q; rc_l:list Sym; rc_r:side; rc_todo:list Q }.

Definition right_step tm (period:list Q) '(right_config q l r todo) : RightConfig+bool :=
match r with m>>r => match tm(q,m) with
| None => inr true
| Some(m,R,q) => inl (right_config q (m::l) r todo)
| Some(m,L,q) => match l with
  | x::l => inl (right_config q l (x>>m>>r) todo)
  | [] => match q with
    | B => inr false
    | A => match (match todo with []=>period | _=>todo end) with
      | [] => inr false
      | q::todo => inl (right_config q [] (m>>r) todo)
      end end end
end end.

Definition FutureHalts tm period '(right_config q l r todo) :=
  exists n, PendingHalts tm (calls (todo++period^^n)) l r q.

Lemma right_step_spec tm period x :
  (match right_step tm period x with
   | inl y => FutureHalts tm period y | inr b => b=true end) ->
  FutureHalts tm period x.
Proof.
  destruct x as [q l [m r] todo]; cbn[right_step FutureHalts].
  destruct (tm(q,m)) as [[[m' []] q']|] eqn:E.
  - destruct l as [|s l].
    + destruct q'; [|discriminate]; destruct todo as [|q0 todo].
      * destruct period as [|q0 period]; [discriminate|].
        intros [n H]; exists (S n); right; exists (m'>>r); split.
        -- intro l0; do 2 econstructor; exact E.
        -- apply pending_calls in H; exact H.
      * intros [n H]; exists n; right; exists (m'>>r); split.
        -- intro l0; do 2 econstructor; exact E.
        -- apply pending_calls in H; exact H.
    + intros [n H]; exists n; eapply pending_step; [|exact H].
      intro l0; exact (@step_left tm q q' m m' ((s::l)*>l0) r E).
  - intros [n H]; exists n; eapply pending_step; [|exact H].
    intro l0; exact (@step_right tm q q' m m' (l*>l0) r E).
  - intro H; exists 0%nat; left; intro l0; apply halted_halts; exact E.
Qed.

(* Keep the fields in tail-recursive arguments; allocate a suspension only
   at a chunk boundary, not on every simulated transition. *)
Fixpoint right_chunk tm period fuel q l r todo : RightConfig+bool := match fuel with
| O=>inl (right_config q l r todo)
| S fuel=>match r with m>>r=>match tm(q,m) with
  | None=>inr true
  | Some(m',R,q')=>right_chunk tm period fuel q' (m'::l) r todo
  | Some(m',L,q')=>match l with
    | s::l=>right_chunk tm period fuel q' l (s>>m'>>r) todo
    | []=>match q' with
      | B=>inr false
      | A=>match (match todo with []=>period | _=>todo end) with
        | []=>inr false
        | q::todo=>right_chunk tm period fuel q [] (m'>>r) todo end end end
  end end end.
Definition right_batch tm period x :=
  let '(right_config q l r todo):=x in right_chunk tm period 1000 q l r todo.
Lemma right_chunk_spec tm period fuel : forall q l r todo,
  (match right_chunk tm period fuel q l r todo with
  | inl y=>FutureHalts tm period y | inr b=>b=true end) ->
  FutureHalts tm period (right_config q l r todo).
Proof.
  induction fuel; intros q l [m r] todo; cbn[right_chunk]; [auto|]; intro H.
  apply (right_step_spec tm period (right_config q l (m>>r) todo)).
  cbn[right_step]; destruct (tm(q,m)) as [[[m' []] q']|]; try apply IHfuel; try exact H.
  destruct l; [destruct q'; [destruct todo; [destruct period|]; eauto|exact H]|eauto].
Qed.
Definition right_run tm period x fuel :=
  Eqb.N_iter_until (right_batch tm period) (inl x) fuel.
Lemma right_run_spec tm period x fuel : right_run tm period x fuel=inr true ->
  FutureHalts tm period x.
Proof.
  pose proof (@Eqb.N_iter_until_spec RightConfig bool (right_batch tm period) (inl x) fuel
    (fun y=>FutureHalts tm period y -> FutureHalts tm period x)
    (fun b=>b=true -> FutureHalts tm period x)) as H.
  unfold right_run; intro E; rewrite E in H; apply H; [|auto|reflexivity].
  intros [q l r todo] HY; pose proof (right_chunk_spec tm period 1000 q l r todo) as HS.
  cbn[right_batch]; destruct (right_chunk tm period 1000 q l r todo); auto.
Qed.

Definition FlowHalts tm pre period r :=
  exists n, sideRLs_halt tm (calls (pre++period^^n)) r.
Definition flow_halt_c tm pre period r fuel :=
  match (match pre with []=>period | _=>pre end) with
  | [] => false
  | q::todo => match right_run tm period (right_config q [] r todo) fuel with
    | inr b => b | _=>false end end.
Lemma flow_halt_c_spec tm pre period r fuel : flow_halt_c tm pre period r fuel=true ->
  FlowHalts tm pre period r.
Proof.
  unfold flow_halt_c; destruct pre as [|q pre].
  - destruct period as [|q period]; [discriminate|].
    remember (right_config q [] r period) as x.
    destruct (right_run tm (q::period) x fuel) as [y|b] eqn:E; [discriminate|].
    intro EB; subst b x; apply right_run_spec in E; destruct E as [n H].
    exists (S n); apply pending_calls in H; exact H.
  - remember (right_config q [] r pre) as x.
    destruct (right_run tm period x fuel) as [y|b] eqn:E; [discriminate|].
    intro EB; subst b x; apply right_run_spec in E; destruct E as [n H].
    exists n; apply pending_calls in H; exact H.
Qed.

Inductive LeftRun tm : list Q -> side -> side -> Prop :=
| left_run_nil l : LeftRun tm [] l l
| left_run_cons q qs l l' l'' :
    (forall r, l <{{A}} r -[tm]->+ l' {{q}}> r) ->
    LeftRun tm qs l' l'' -> LeftRun tm (q::qs) l l''.
Lemma left_run_app tm qs l l' : LeftRun tm qs l l' -> forall qs' l'',
  LeftRun tm qs' l' l'' -> LeftRun tm (qs++qs') l l''.
Proof. intro H; induction H; cbn; intros; eauto using left_run_nil,left_run_cons. Qed.

Lemma left_run_halt tm qs l l' : LeftRun tm qs l l' -> forall q r,
  sideRLs_halt tm (calls (q::qs)) r -> halts tm (l {{q}}> r).
Proof.
  intro H; induction H; intros q0 r HH; cbn[calls] in HH;
    inversion HH as [hR hL hs r0 HH0|hR hL hs r0 r' HR HH']; subst.
  - apply HH0.
  - inversion HH'.
  - apply HH0.
  - eapply halts_evstep; [apply IHLeftRun; exact HH'|].
    follow100 (HR l); apply progress_evstep,H.
Qed.
Lemma rotate_pow {X} (q:X) qs n : q::(qs++[q])^^n=(q::qs)^^n++[q].
Proof.
  induction n; cbn[lpow app]; [reflexivity|].
  rewrite <-List.app_assoc; cbn[app]; rewrite IHn; rewrite List.app_assoc; reflexivity.
Qed.
Lemma left_cycles tm qs (L:nat->side) :
  (forall n, LeftRun tm qs (L n) (L (1+n))) ->
  forall k n, LeftRun tm (qs^^k) (L n) (L (k+n)).
Proof.
  intro H; induction k; intro n; cbn[lpow]; [constructor|].
  eapply left_run_app; [apply H|applys_eq (IHk (1+n)); flia].
Qed.
Lemma left_period_halt tm q qs (L:nat->side) r :
  (forall n, LeftRun tm (qs++[q]) (L n) (L (1+n))) ->
  FlowHalts tm [] (q::qs) r -> halts tm (L 0%nat {{q}}> r).
Proof.
  intros HL [n HH].
  eapply left_run_halt with (qs:=(qs++[q])^^n).
  - eapply left_cycles; exact HL.
  - rewrite rotate_pow; unfold calls; rewrite List.map_app.
    apply sideRLs_halt_app_left; exact HH.
Qed.
