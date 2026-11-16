(* SOC_ex rows 9, 8, 11. A single shared, conservative checker;
   finite shift data only, with primitive fallback at every unmatched edge. *)
From BusyCoq Require Import Individual62 BinaryCounter BinaryCounterFull Eqb SimplTape ES_v2.
Require Import NArith Lia ZifyNat List String.

Module Core.
Section Core.
Variable tm : TM.
Variables (QL QR : Q).
Notation ld0 := <[1;1;1;0].
Notation ld1 := <[1;1;1;1].
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation "l |> r" := (l <* [1;0;1;1;1] {{QR}}> r) (at level 30).
Notation "l <| r" := (l <{{QL}} [0;1;0;1;0] *> r) (at level 30).
Hypothesis LInc: forall l r n,
  l <* ld0 <* ld1^^n <| r -[tm]->+ l <* ld1 <* ld0^^n |> r.

Hypothesis RInc: forall l r n,
  l |> rd1^^n *> [0] *> r -[tm]->+ l <| rd0^^n *> [1] *> r.

Notation "c -->* c'" := (c -[tm]->* c') (at level 40).

Definition addN p k := match k with N0=>p | Npos k=>Pos.add p k end.
Lemma addN_succ p k: addN p (N.succ k) = addN (Pos.succ p) k.
Proof. destruct k; cbn [addN N.succ]; lia. Qed.

Lemma paired k p q l r:
  (k<=rest p)%N -> (k<=rest q)%N ->
  BinaryCounter ld0 ld1 l p |> BinaryCounter rd0 rd1 r q -->*
  BinaryCounter ld0 ld1 l (addN p k) |> BinaryCounter rd0 rd1 r (addN q k).
Proof.
  revert p q; induction k using N.peano_ind; intros p q Hp Hq.
  - apply evstep_refl.
  - assert (Hp0: rest p<>0%N) by lia.
    assert (Hq0: rest q<>0%N) by lia.
    pose proof (rest_S p Hp0); pose proof (rest_S q Hq0).
    rewrite !addN_succ.
    eapply evstep_trans.
    + apply progress_evstep; apply BinaryCounter.RInc.
      * intros; change (rd0^^n *> rd1 *> r0) with (rd0^^n *> [1] *> [0;0] *> r0).
        apply RInc.
      * apply not_full_iff_rest; exact Hq0.
    + eapply evstep_trans.
      * apply progress_evstep; apply BinaryCounter.LInc; [apply LInc|].
        apply not_full_iff_rest; exact Hp0.
      * apply IHk; lia.
Qed.

(* Binary words have a leading sentinel in their positive representation;
   it is not a tape digit.  No unary large integer is computed. *)
Fixpoint word (d0 d1:list Sym) p := match p with
  | xH=>nil | xO p=>d0++word d0 d1 p | xI p=>d1++word d0 d1 p end.
Fixpoint word_tail (d0 d1:list Sym) p t := match p with
  | xH=>t | xO p=>d0++word_tail d0 d1 p t | xI p=>d1++word_tail d0 d1 p t end.
Lemma word_tail_spec d0 d1 p t: word_tail d0 d1 p t = word d0 d1 p ++ t.
Proof. induction p; cbn; rewrite ?IHp, ?app_assoc; reflexivity. Qed.
Lemma word_spec d0 d1 p r:
  word d0 d1 p *> r = BinaryCounter d0 d1 r p.
Proof. induction p; cbn; rewrite ?Str_app_assoc, ?IHp; reflexivity. Qed.

(* This check permits omitted trailing blanks, but never treats a failed
   match as a halt.  Proposal parsers need no soundness assumptions. *)
Fixpoint peel (w s:list Sym) : option (list Sym) := match w with
  | nil=>Some s
  | b::w=>match s with
    | nil=>if sym_eqb b 0 then peel w nil else None
    | c::s=>if sym_eqb b c then peel w s else None end end.
Lemma peel_spec w s r: peel w s=Some r -> s *> 0inf = w *> r *> 0inf.
Proof.
  revert s; induction w as [|b w IH]; intros s H; cbn in H.
  - injection H as <-; reflexivity.
  - destruct s as [|c s].
    + destruct (sym_eqb_spec b 0); try discriminate; subst.
      specialize (IH _ H); cbn; rewrite <-IH; apply const_unfold.
    + destruct (sym_eqb_spec b c); try discriminate; subst.
      specialize (IH _ H); cbn; rewrite <-IH; reflexivity.
Qed.

Definition State := (Q * list Sym * list Sym)%type.
Definition denote (s:State) := let '(q,l,r):=s in l *> 0inf {{q}}> r *> 0inf.
Fixpoint room p : N := match p with
  | xH=>N0 | xI p=>N.double (room p) | xO p=>N.succ_double (room p) end.
Lemma room_spec p: room p=rest p.
Proof.
  induction p; cbn [room]; rewrite ?IHp.
  - unfold rest; cbn [log2 pow2']; pose proof (pow2'_log2_ge p).
    rewrite N.double_spec; lia.
  - rewrite N.succ_double_spec,rest_mul2; lia.
  - reflexivity.
Qed.

Fixpoint decode_left (l:list Sym) : positive * list Sym := match l with
  | S0::S1::S1::S1::l=>let '(p,r):=decode_left l in (xO p,r)
  | S1::S1::S1::S1::l=>let '(p,r):=decode_left l in (xI p,r)
  | _=>(xH,l) end.
Lemma decode_left_spec l p r: decode_left l=(p,r) ->
  l *> 0inf=BinaryCounter ld0 ld1 (r *> 0inf) p.
Proof.
  revert l p r; fix IH 1; intros [|[] [|[] [|[] [|[] l]]]] p r H;
    cbn [decode_left] in H; try (injection H as <- <-; reflexivity).
  all: destruct (decode_left l) as [p' r'] eqn:E; injection H as <- <-;
    cbn [BinaryCounter Str_app]; rewrite (IH _ _ _ E); reflexivity.
Qed.
Definition put b (v:positive * list Sym) :=
  let '(p,r):=v in (match b with S0=>xO p | S1=>xI p end,r).
Fixpoint decode_right n (r:list Sym) : positive * list Sym := match n with
  | O=>(xH,r)
  | S n=>match r with
    | b::S0::S0::r=>put b (decode_right n r)
    | nil=>put S0 (decode_right n nil)
    | b::nil | b::S0::nil=>put b (decode_right n nil)
    | _=>(xH,r) end end.
Lemma decode_right_spec n r p t: decode_right n r=(p,t) ->
  r *> 0inf=BinaryCounter rd0 rd1 (t *> 0inf) p.
Proof.
  revert r p t; induction n as [|n IHn]; intros r p t H.
  - injection H as <- <-; reflexivity.
  - destruct r as [|[] [|[] [|[] r]]]; cbn [decode_right] in H;
      try (injection H as <- <-; reflexivity).
    all: match type of H with context[decode_right ?n ?r] =>
      destruct (decode_right n r) as [p' t'] eqn:E;
      cbn [put] in H; injection H as <- <-;
      cbn [BinaryCounter Str_app]; rewrite <- (IHn _ _ _ E);
      repeat rewrite <-const_unfold; reflexivity end.
Qed.
Definition right_start (r:list Sym) := match r with
  | _::S1::_ | _::_::S1::_=>false | _=>true end.
Definition accelerate (s:State) := let '(state,l,r):=s in
  if q_eqb state QR then match l with
  | S1::S0::S1::S1::S1::l=>if right_start r then
    let '(p,l'):=decode_left l in
    match room p with
    | N0=>None
    | k=>let '(q,r'):=decode_right (S (log2 p)) r in
      match N.min k (room q) with
      | N0=>None
      | k=>Some (QR,[1;0;1;1;1]++word_tail ld0 ld1 (addN p k) l',
                       word_tail rd0 rd1 (addN q k) r') end end else None
  | _=>None end else None.
Lemma accelerate_spec s t: accelerate s=Some t -> denote s -[tm]->* denote t.
Proof.
  unfold accelerate; destruct s as [[state l] r].
  destruct (q_eqb_spec state QR); try discriminate; subst state.
  do 5 (destruct l as [|[] l]; try discriminate).
  destruct (right_start r); try discriminate.
  destruct (decode_left l) as [p l'] eqn:Hl.
  destruct (room p) eqn:Hp; try discriminate.
  destruct (decode_right (S (log2 p)) r) as [q r'] eqn:Hr.
  destruct (N.min (N.pos p0) (room q)) eqn:Hk; try discriminate.
  intros H; injection H as <-; rewrite !word_tail_spec.
  change (l *> 0inf |> r *> 0inf -[tm]->*
    (word ld0 ld1 (addN p (N.pos p1))++l') *> 0inf |>
    (word rd0 rd1 (addN q (N.pos p1))++r') *> 0inf).
  apply decode_left_spec in Hl; apply decode_right_spec in Hr.
  rewrite Hl,Hr,!Str_app_assoc,!word_spec.
  apply paired; rewrite <-!room_spec,<-Hk; [rewrite Hp; apply N.le_min_l|apply N.le_min_r].
Qed.

Definition make_left q (l r:list Sym) : State := match l with
  | nil=>(q,nil,S0::r) | b::l=>(q,l,b::r) end.
Lemma make_left_spec q l r:
  denote (make_left q l r)=l *> 0inf <{{q}} r *> 0inf.
Proof. destruct l; reflexivity. Qed.

Fixpoint prepend (w:list Sym) n t := match n with
  | O=>t | S n=>w++prepend w n t end.
Lemma prepend_spec w n t: prepend w n t=w^^n++t.
Proof. induction n; cbn; rewrite ?IHn, ?app_assoc; reflexivity. Qed.

(* A fixed bound avoids traversing the entire tape merely to obtain fuel.
   Partial shifts are sound too; a failed proposal falls back to one TM step. *)
Fixpoint scan_count fuel w s : nat * list Sym := match fuel with
  | O=>(O,s)
  | S fuel=>match peel w s with
    | None=>(O,s)
    | Some t=>let '(n,u):=scan_count fuel w t in (S n,u) end end.
Lemma scan_count_spec fuel w s n u: scan_count fuel w s=(n,u) ->
  s *> 0inf = w^^n *> u *> 0inf.
Proof.
  revert s n u; induction fuel as [|fuel IH]; intros s n u H; cbn [scan_count] in H.
  - injection H as <- <-; reflexivity.
  - destruct (peel w s) as [t|] eqn:E.
    + destruct (scan_count fuel w t) as [k v] eqn:G; injection H as <- <-.
      apply peel_spec in E; rewrite E,(IH _ _ _ G).
      cbn [lpow]; rewrite Str_app_assoc; reflexivity.
    + injection H as <- <-; reflexivity.
Qed.

(* Words are stored in stack order: input on the scanned stack, output on
   the opposite stack. This removes every runtime reversal. *)
Record Shift := Sh { sq:Q; sd:dir; sw:list Sym; sv:list Sym }.
Definition valid h := forall n l r, match sd h with
  | R=>l {{sq h}}> sw h^^n *> r -->* l <* sv h^^n {{sq h}}> r
  | L=>l <* sw h^^n <{{sq h}} r -->* l <{{sq h}} sv h^^n *> r end.
Variable scan_budget:nat.
Definition try_shift h (s:State) : option State :=
  let '(q,l,r):=s in
  if q_eqb q (sq h) then match sd h with
  | R=>let '(n,t):=scan_count scan_budget (sw h) r in
    match n with S (S _)=>Some(q,prepend (sv h) n l,t) | _=>None end
  | L=>let '(b,r):=match r with nil=>(S0,nil) | b::r=>(b,r) end in
    let '(n,t):=scan_count scan_budget (sw h) (b::l) in
    match n with S (S _)=>Some(make_left q t (prepend (sv h) n r)) | _=>None end
  end else None.
Lemma try_shift_spec h s t: valid h -> try_shift h s=Some t -> denote s -->* denote t.
Proof.
  intros Hvalid; destruct h as [q d w v], s as [[q' l] r].
  unfold try_shift; cbn [sq sd sw sv] in *.
  destruct (q_eqb_spec q' q); try discriminate; subst q'.
  destruct d.
  - destruct r as [|b r]; cbn beta iota zeta;
      match goal with |- context[scan_count ?f ?w ?s]=>
        destruct (scan_count f w s) as [n u] eqn:E end;
      destruct n as [|[|n]]; try discriminate; intros H; injection H as <-;
      rewrite make_left_spec,prepend_spec;
      apply scan_count_spec in E.
    + change (denote (q,l,nil)) with ((0::l) *> 0inf <{{q}} 0inf).
      eapply evstep_trans; [apply evstep_refl'; exact (f_equal (fun z=>z <{{q}} 0inf) E)|].
      eapply evstep_trans; [apply Hvalid|].
      apply evstep_refl'; simpl_tape; reflexivity.
    + change (denote (q,l,b::r)) with ((b::l) *> 0inf <{{q}} r *> 0inf).
      eapply evstep_trans; [apply evstep_refl'; exact (f_equal (fun z=>z <{{q}} r *> 0inf) E)|].
      eapply evstep_trans; [apply Hvalid|].
      apply evstep_refl'; simpl_tape; reflexivity.
  - destruct (scan_count scan_budget w r) as [n u] eqn:E;
      destruct n as [|[|n]]; try discriminate; intros H; injection H as <-.
    unfold denote; rewrite prepend_spec.
    apply scan_count_spec in E; rewrite E.
    eapply evstep_trans; [apply Hvalid|].
    apply evstep_refl'; simpl_tape; reflexivity.
Qed.
Variable shifts:list Shift.
Hypothesis shifts_valid: Forall valid shifts.
Fixpoint scan_rules hs s := match hs with
  | nil=>None | h::hs=>match try_shift h s with Some t=>Some t | None=>scan_rules hs s end end.
Lemma scan_rules_spec hs s t: Forall valid hs -> scan_rules hs s=Some t -> denote s -->* denote t.
Proof.
  intros H; induction H; cbn [scan_rules]; [discriminate|].
  destruct (try_shift x s) as [u|] eqn:E.
  - intros G; injection G as <-; eapply try_shift_spec; eassumption.
  - apply IHForall.
Qed.
Definition scan := scan_rules shifts.
Lemma scan_spec s t: scan s=Some t -> denote s -->* denote t.
Proof. apply scan_rules_spec,shifts_valid. Qed.
Definition primitive (s:State) : option State :=
  let '(q,l,r):=s in let '(b,r):=match r with nil=>(S0,nil) | b::r=>(b,r) end in
  match tm (q,b) with
  | None=>None
  | Some (b,R,q)=>Some (q,b::l,r)
  | Some (b,L,q)=>match l with nil=>Some (q,nil,S0::b::r) | a::l=>Some (q,l,a::b::r) end
  end.
Lemma primitive_spec s t: primitive s=Some t -> denote s -->* denote t.
Proof.
  destruct s as [[q l] r]; destruct r as [|b r]; unfold primitive;
    match goal with |- context[tm ?x] => destruct (tm x) as [[[a d] q']|] eqn:E end; try discriminate;
    destruct d; try destruct l as [|b' l]; intros H; injection H as <-.
  all: eapply evstep_step; [apply step_c_spec;
      cbn [step_c denote Str_app move_left move_right Streams.hd Streams.tl const];
      fold Q Sym in E; rewrite E; reflexivity|apply evstep_refl].
Qed.
Lemma primitive_halt s: primitive s=None -> halts tm (denote s).
Proof.
  destruct s as [[q l] r]; destruct r as [|b r]; unfold primitive;
    match goal with |- context[tm ?x] => destruct (tm x) as [[[a d] q']|] eqn:E end.
  all: try (destruct d; try destruct l; discriminate).
  all: intros _; apply halted_halts; exact E.
Qed.


Definition next (s:State) : State+unit := match accelerate s with
  | Some t=>inl t
  | None=>match scan s with
    | Some t=>inl t
    | None=>match primitive s with Some t=>inl t | None=>inr tt end end end.
Lemma next_spec s:
  match next s with inl t=>denote s -->* denote t | inr _=>halts tm (denote s) end.
Proof.
  unfold next; destruct (accelerate s) as [t|] eqn:E.
  - eapply accelerate_spec; exact E.
  - destruct (scan s) as [t|] eqn:G.
    + eapply scan_spec; exact G.
    + destruct (primitive s) as [t|] eqn:H.
      * eapply primitive_spec; exact H.
      * apply primitive_halt; exact H.
Qed.
Definition check_from (initial:State) fuel := match N_iter_until next (inl initial) fuel with
  | inr _=>true | inl _=>false end.
Lemma check_from_spec initial fuel: check_from initial fuel=true -> halts tm (denote initial).
Proof.
  pose proof (@N_iter_until_spec State unit next (inl initial) fuel
    (fun s=>denote initial -->* denote s) (fun _=>halts tm (denote initial))) as H.
  assert (K: forall s, denote initial -->* denote s ->
    match next s with inl t=>denote initial -->* denote t | inr _=>halts tm (denote initial) end).
  { intros s Hs; pose proof (next_spec s) as Hn; destruct (next s).
    - eapply evstep_trans; eassumption.
    - eapply halts_evstep; eassumption. }
  specialize (H K (evstep_refl _ _)); unfold check_from.
  destruct (N_iter_until next (inl initial) fuel); cbn in H |- *;
    intros Hc; try discriminate; exact H.
Qed.
End Core.
End Core.

Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC0LE_1RD0RC_1LA1RE_1RC0RF_0LA---").
Notation "l <| r" := (l <{{E}} [0;1;0;1;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1;1] {{D}}> r) (at level 30).
Lemma LInc l r n:
  l <* <[1;1;1;0] <* <[1;1;1;1]^^n <| r -[tm]->+
  l <* <[1;1;1;1] <* <[1;1;1;0]^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> [1;0;0]^^n *> [0] *> r -[tm]->+ l <| [0;0;0]^^n *> [1] *> r.
Proof. es. Qed.
Definition shifts := [
  Core.Sh A L [1] [0];
  Core.Sh A L [1;1;1;0;1;0] [0;0;0;0;0;1];
  Core.Sh B L [1;1] [1;0];
  Core.Sh C R [1] [0];
  Core.Sh C R [0;1;0] [1;1;1];
  Core.Sh C R [0;1;0;1] [0;1;1;1];
  Core.Sh C R [1;0;1;0] [1;1;1;0];
  Core.Sh C R [0;1;0;1;1] [0;0;1;1;1];
  Core.Sh C R [1;0;1;0;1] [0;1;1;1;0];
  Core.Sh C R [1;0;1;1;0] [1;1;1;0;1];
  Core.Sh C R [1;1;0;0;0] [1;1;1;0;1];
  Core.Sh C R [1;1;0;1;0] [1;1;1;0;0];
  Core.Sh C R [0;1;0;1;1;1] [0;0;0;1;1;1];
  Core.Sh C R [1;0;1;0;1;1] [0;0;1;1;1;0];
  Core.Sh C R [1;0;1;1;0;1] [0;1;1;1;0;1];
  Core.Sh C R [1;1;0;0;0;1] [0;1;1;1;0;1];
  Core.Sh C R [1;1;0;0;1;0] [1;1;1;0;1;1];
  Core.Sh C R [1;1;0;1;0;1] [0;1;1;1;0;0];
  Core.Sh C R [1;1;0;1;1;0] [1;1;1;0;1;0];
  Core.Sh C R [1;1;1;0;0;0] [1;1;1;0;1;0];
  Core.Sh C R [1;1;1;0;1;0] [1;1;1;0;0;0];
  Core.Sh D R [1;0;0] [1;1;1];
  Core.Sh D R [1;0;1;0] [1;0;1;1];
  Core.Sh D R [1;0;1;1;0] [1;0;0;1;1];
  Core.Sh D R [1;0;1;1;1;0] [1;0;0;0;1;1];
  Core.Sh E R [0;0;1] [1;1;1];
  Core.Sh E R [0;1;0;1] [1;1;0;1];
  Core.Sh E R [0;1;1;0;0] [1;1;0;1;1];
  Core.Sh E R [0;1;1;0;1] [1;1;0;0;1];
  Core.Sh E R [0;1;1;1;0;0] [1;1;0;1;0;1];
  Core.Sh E R [0;1;1;1;0;1] [1;1;0;0;0;1]].
Lemma shifts_spec: Forall (Core.valid tm) shifts.
Proof.
  repeat (constructor; [unfold Core.valid; cbn [Core.sd Core.sq Core.sw Core.sv];
    intros; shift_rule; es|]).
  constructor.
Qed.
Definition check fuel := Core.check_from tm D 1024 shifts (A,nil,nil) fuel.
Lemma check_spec fuel: check fuel=true -> halts tm c0.
Proof. unfold check; apply Core.check_from_spec with (QL:=E); [apply LInc|apply RInc|apply shifts_spec]. Qed.
Theorem halt: halts tm c0.
Proof. apply (check_spec 8388608%N). native_check_eq. Time Qed.
End TM2.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1RC0RB_1LD1RA_1LE0LD_1RB0LA_0LD---").
Notation "l <| r" := (l <{{A}} [0;1;0;1;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1;1] {{C}}> r) (at level 30).
Lemma LInc l r n:
  l <* <[1;1;1;0] <* <[1;1;1;1]^^n <| r -[tm]->+
  l <* <[1;1;1;1] <* <[1;1;1;0]^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> [1;0;0]^^n *> [0] *> r -[tm]->+ l <| [0;0;0]^^n *> [1] *> r.
Proof. es. Qed.
Definition shifts := [
  Core.Sh A R [0;0;1] [1;1;1];
  Core.Sh A R [0;1;0;1] [1;1;0;1];
  Core.Sh A R [0;1;1;0;0] [1;1;0;1;1];
  Core.Sh A R [0;1;1;0;1] [1;1;0;0;1];
  Core.Sh A R [0;1;1;1;0;0] [1;1;0;1;0;1];
  Core.Sh A R [0;1;1;1;0;1] [1;1;0;0;0;1];
  Core.Sh B R [1] [0];
  Core.Sh B R [0;1;0] [1;1;1];
  Core.Sh B R [0;1;0;1] [0;1;1;1];
  Core.Sh B R [1;0;1;0] [1;1;1;0];
  Core.Sh B R [0;1;0;1;1] [0;0;1;1;1];
  Core.Sh B R [1;0;1;0;1] [0;1;1;1;0];
  Core.Sh B R [1;0;1;1;0] [1;1;1;0;1];
  Core.Sh B R [1;1;0;0;0] [1;1;1;0;1];
  Core.Sh B R [1;1;0;1;0] [1;1;1;0;0];
  Core.Sh B R [0;1;0;1;1;1] [0;0;0;1;1;1];
  Core.Sh B R [1;0;1;0;1;1] [0;0;1;1;1;0];
  Core.Sh B R [1;0;1;1;0;1] [0;1;1;1;0;1];
  Core.Sh B R [1;1;0;0;0;1] [0;1;1;1;0;1];
  Core.Sh B R [1;1;0;0;1;0] [1;1;1;0;1;1];
  Core.Sh B R [1;1;0;1;0;1] [0;1;1;1;0;0];
  Core.Sh B R [1;1;0;1;1;0] [1;1;1;0;1;0];
  Core.Sh B R [1;1;1;0;0;0] [1;1;1;0;1;0];
  Core.Sh B R [1;1;1;0;1;0] [1;1;1;0;0;0];
  Core.Sh C R [1;0;0] [1;1;1];
  Core.Sh C R [1;0;1;0] [1;0;1;1];
  Core.Sh C R [1;0;1;1;0] [1;0;0;1;1];
  Core.Sh C R [1;0;1;1;1;0] [1;0;0;0;1;1];
  Core.Sh D L [1] [0];
  Core.Sh D L [1;1;1;0;1;0] [0;0;0;0;0;1];
  Core.Sh E L [1;1] [1;0]].
Lemma shifts_spec: Forall (Core.valid tm) shifts.
Proof.
  repeat (constructor; [unfold Core.valid; cbn [Core.sd Core.sq Core.sw Core.sv];
    intros; shift_rule; es|]).
  constructor.
Qed.
Definition check fuel := Core.check_from tm C (Nat.pow 2 14) shifts (A,nil,nil) fuel.
Lemma check_spec fuel: check fuel=true -> halts tm c0.
Proof. unfold check; apply Core.check_from_spec with (QL:=A); [apply LInc|apply RInc|apply shifts_spec]. Qed.
Theorem halt: halts tm c0.
Proof. apply (check_spec 67108864%N). native_check_eq. Time Qed.
End TM1.

(* SOC_ex row 11; TM14 extends the legacy test_SOC_4_3 numbering (1..13). *)
Module TM14.
Definition tm := Eval compute in (TM_from_str "1RB0RA_1LC1RE_1LD0LC_1RA0LE_1RA0RF_0LC---").
Notation "l <| r" := (l <{{E}} [0;1;0;1;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1;1] {{B}}> r) (at level 30).
Lemma LInc l r n:
  l <* <[1;1;1;0] <* <[1;1;1;1]^^n <| r -[tm]->+
  l <* <[1;1;1;1] <* <[1;1;1;0]^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> [1;0;0]^^n *> [0] *> r -[tm]->+ l <| [0;0;0]^^n *> [1] *> r.
Proof. es. Qed.
Definition shifts := [
  Core.Sh A R [1] [0];
  Core.Sh A R [0;1;0] [1;1;1];
  Core.Sh A R [0;1;0;1] [0;1;1;1];
  Core.Sh A R [1;0;1;0] [1;1;1;0];
  Core.Sh A R [0;1;0;1;1] [0;0;1;1;1];
  Core.Sh A R [1;0;1;0;1] [0;1;1;1;0];
  Core.Sh A R [1;0;1;1;0] [1;1;1;0;1];
  Core.Sh A R [1;1;0;0;0] [1;1;1;0;1];
  Core.Sh A R [1;1;0;1;0] [1;1;1;0;0];
  Core.Sh A R [0;1;0;1;1;1] [0;0;0;1;1;1];
  Core.Sh A R [1;0;1;0;1;1] [0;0;1;1;1;0];
  Core.Sh A R [1;0;1;1;0;1] [0;1;1;1;0;1];
  Core.Sh A R [1;1;0;0;0;1] [0;1;1;1;0;1];
  Core.Sh A R [1;1;0;0;1;0] [1;1;1;0;1;1];
  Core.Sh A R [1;1;0;1;0;1] [0;1;1;1;0;0];
  Core.Sh A R [1;1;0;1;1;0] [1;1;1;0;1;0];
  Core.Sh A R [1;1;1;0;0;0] [1;1;1;0;1;0];
  Core.Sh A R [1;1;1;0;1;0] [1;1;1;0;0;0];
  Core.Sh B R [1;0;0] [1;1;1];
  Core.Sh B R [1;0;1;0] [1;0;1;1];
  Core.Sh B R [1;0;1;1;0] [1;0;0;1;1];
  Core.Sh B R [1;0;1;1;1;0] [1;0;0;0;1;1];
  Core.Sh C L [1] [0];
  Core.Sh C L [1;1;1;0;1;0] [0;0;0;0;0;1];
  Core.Sh D L [1;1] [1;0];
  Core.Sh E R [0;0;1] [1;1;1];
  Core.Sh E R [0;1;0;1] [1;1;0;1];
  Core.Sh E R [0;1;1;0;0] [1;1;0;1;1];
  Core.Sh E R [0;1;1;0;1] [1;1;0;0;1];
  Core.Sh E R [0;1;1;1;0;0] [1;1;0;1;0;1];
  Core.Sh E R [0;1;1;1;0;1] [1;1;0;0;0;1]].
Lemma shifts_spec: Forall (Core.valid tm) shifts.
Proof.
  repeat (constructor; [unfold Core.valid; cbn [Core.sd Core.sq Core.sw Core.sv];
    intros; shift_rule; es|]).
  constructor.
Qed.
Definition check fuel := Core.check_from tm B (Nat.pow 2 14) shifts (A,nil,nil) fuel.
Lemma check_spec fuel: check fuel=true -> halts tm c0.
Proof. unfold check; apply Core.check_from_spec with (QL:=E); [apply LInc|apply RInc|apply shifts_spec]. Qed.
Theorem halt: halts tm c0.
Proof. apply (check_spec 134217728%N). native_check_eq. Time Qed.
End TM14.
