(* Checked fixed-width counter pairs, with primitive execution everywhere else. *)
From BusyCoq Require Import Individual62 BinaryCounter BinaryCounterFull Eqb SimplTape ES_v2.
Require Import NArith Lia ZifyNat List String.

Module TM67.
Definition tm := Eval compute in (TM_from_str "1LB1RF_1RC0RD_1RD1LC_1LE1RB_0RA0LE_0RA---").
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation "l |> r" := (l <* <[1;0;1;1;1] {{D}}> r) (at level 30).
Notation "l <| r" := (l <{{C}} [1;1;1;0;0] *> r) (at level 30).
Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -[tm]->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -[tm]->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
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
  | S0::S1::l=>let '(p,r):=decode_left l in (xO p,r)
  | S1::S1::l=>let '(p,r):=decode_left l in (xI p,r)
  | _=>(xH,l) end.
Lemma decode_left_spec l p r: decode_left l=(p,r) ->
  l *> 0inf=BinaryCounter ld0 ld1 (r *> 0inf) p.
Proof.
  revert l p r; fix IH 1; intros [|[] [|[] l]] p r H;
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
Definition accelerate (s:State) := match s with
  | (D,S1::S1::S1::S0::S1::l,r)=>if right_start r then
    let '(p,l'):=decode_left l in
    match room p with
    | N0=>None
    | k=>let '(q,r'):=decode_right (S (log2 p)) r in
      match N.min k (room q) with
      | N0=>None
      | k=>Some (D,[1;1;1;0;1]++word ld0 ld1 (addN p k)++l',
                       word rd0 rd1 (addN q k)++r') end end else None
  | _=>None end.
Lemma accelerate_spec s t: accelerate s=Some t -> denote s -[tm]->* denote t.
Proof.
  unfold accelerate; destruct s as [[state l] r]; destruct state; try discriminate.
  do 5 (destruct l as [|[] l]; try discriminate).
  destruct (right_start r); try discriminate.
  destruct (decode_left l) as [p l'] eqn:Hl.
  destruct (room p) eqn:Hp; try discriminate.
  destruct (decode_right (S (log2 p)) r) as [q r'] eqn:Hr.
  destruct (N.min (N.pos p0) (room q)) eqn:Hk; try discriminate.
  intros H; injection H as <-.
  change (l *> 0inf |> r *> 0inf -[tm]->*
    (word ld0 ld1 (addN p (N.pos p1))++l') *> 0inf |>
    (word rd0 rd1 (addN q (N.pos p1))++r') *> 0inf).
  apply decode_left_spec in Hl; apply decode_right_spec in Hr.
  rewrite Hl,Hr,!Str_app_assoc,!word_spec.
  apply paired; rewrite <-!room_spec,<-Hk; [rewrite Hp; apply N.le_min_l|apply N.le_min_r].
Qed.

(* Left overflow consumes the complete left counter and a right prefix. *)
Definition edge_left (odd:bool) n m := [1;1;1;0;1] ++
  if odd then ld1 ++ (ld1<+ld0<+ld0)^^m ++ ld0^^(n+2) ++ [1]
  else ld1 ++ ld0 ++ (ld0<+ld0<+ld1)^^m ++ ld0^^n ++ [1].
Definition edge_right (odd:bool) := if odd then [0] else nil.
Definition edge_input (odd:bool) m :=
  [1;1;1;1;0;0] ++ rd1^^(m*2+if odd then 1 else 0) ++ rd0.
Lemma edge_rule odd n m r:
  ld1^^n *> 0inf {{C}}> edge_input odd m *> r -->*
  edge_left odd n m *> 0inf {{D}}> edge_right odd *> r.
Proof. destruct odd; unfold edge_input,edge_left,edge_right; es. Qed.

Fixpoint blank (l:list Sym) := match l with nil=>true | S0::l=>blank l | _=>false end.
Lemma blank_spec l: blank l=true -> l *> 0inf=0inf.
Proof. induction l as [|[] l IH]; cbn; try discriminate; auto.
  intros H; rewrite (IH H); symmetry; apply const_unfold. Qed.

Definition checked_edge odd n m (s:State) : option State :=
  let '(q,l,r):=s in
  if q_eqb q C then match peel (ld1^^n) l, peel (edge_input odd m) r with
  | Some l,Some r=>if blank l then Some (D,edge_left odd n m,edge_right odd++r) else None
  | _,_=>None end else None.
Lemma checked_edge_spec odd n m s t:
  checked_edge odd n m s=Some t -> denote s -->* denote t.
Proof.
  destruct s as [[q l] r]; unfold checked_edge.
  destruct (q_eqb_spec q C); try discriminate; subst.
  destruct (peel (ld1^^n) l) as [l'|] eqn:Hl; try discriminate.
  destruct (peel (edge_input odd m) r) as [r'|] eqn:Hr; try discriminate.
  destruct (blank l') eqn:Hb; try discriminate.
  intros H; injection H as <-; unfold denote.
  apply peel_spec in Hl; apply peel_spec in Hr; apply blank_spec in Hb.
  rewrite Hl,Hr,Hb,Str_app_assoc; apply edge_rule.
Qed.
Fixpoint left_zeros (l:list Sym) := match l with
  | S1::S1::l=>S (left_zeros l) | _=>O end.
Fixpoint right_ones (r:list Sym) := match r with
  | S1::S0::S0::r=>S (right_ones r) | _=>O end.
Definition overflow (s:State) := match s with
  | (C,l,S1::S1::S1::S1::S0::S0::r)=>
    let n:=left_zeros l in let j:=right_ones r in
    checked_edge (Nat.odd j) n (Nat.div j 2) s
  | _=>None end.
Lemma overflow_spec s t: overflow s=Some t -> denote s -->* denote t.
Proof.
  destruct s as [[q l] r]; unfold overflow; destruct q; try discriminate.
  do 6 (destruct r as [|[] r]; try discriminate).
  apply checked_edge_spec.
Qed.


(* Elementary scans: one C/E transition, a three-transition D cycle,
   and two-transition F/D cycles per block. *)
Definition make_left q (l r:list Sym) : State := match l with
  | nil=>(q,nil,S0::r) | b::l=>(q,l,b::r) end.
Lemma make_left_spec q l r:
  denote (make_left q l r)=l *> 0inf <{{q}} r *> 0inf.
Proof. destruct l; reflexivity. Qed.
Inductive Shift := Keep | Erase | Digits | Alternating | Twins.
Definition shift_q tag := match tag with
  | Keep=>C | Erase=>E | Digits | Twins=>D | Alternating=>F end.
Definition shift_left tag n : list Sym := match tag with
  | Keep | Erase=>[1]^^n | _=>nil end.
Definition shift_right tag n : list Sym := match tag with
  | Keep | Erase=>[1] | Digits=>rd1^^(1+n) | Alternating=>[0;1]^^(1+n)
  | Twins=>[1;1]^^(1+n) end.
Definition shift_target tag n (l r:list Sym) : State := match tag with
  | Keep=>make_left C l ([1]^^(1+n)++r)
  | Erase=>make_left E l ([0]^^(1+n)++r)
  | Digits=>(D,[1;1;1]^^(1+n)++l,r)
  | Alternating=>(F,[1;0]^^(1+n)++l,r)
  | Twins=>(D,[0;1]^^(1+n)++l,r) end.
Lemma shift_rule tag n (l r:list Sym):
  denote (shift_q tag,shift_left tag n++l,shift_right tag n++r) -->*
  denote (shift_target tag n l r).
Proof.
  destruct tag; cbn [shift_q shift_left shift_right shift_target];
    rewrite ?make_left_spec; unfold denote; rewrite !Str_app_assoc;
    generalize (l *> 0inf), (r *> 0inf); intros l' r'; clear l r.
  all: es.
Qed.
Definition checked_shift tag n (s:State) : option State :=
  let '(q,l,r):=s in
  if q_eqb q (shift_q tag) then
    match peel (shift_left tag n) l,peel (shift_right tag n) r with
    | Some l,Some r=>Some (shift_target tag n l r) | _,_=>None end
  else None.
Lemma checked_shift_spec tag n s t:
  checked_shift tag n s=Some t -> denote s -->* denote t.
Proof.
  destruct s as [[q l] r]; unfold checked_shift.
  destruct (q_eqb_spec q (shift_q tag)); try discriminate; subst.
  destruct (peel (shift_left tag n) l) as [l'|] eqn:Hl; try discriminate.
  destruct (peel (shift_right tag n) r) as [r'|] eqn:Hr; try discriminate.
  intros H; injection H as <-.
  change (l *> 0inf {{shift_q tag}}> r *> 0inf -->* denote (shift_target tag n l' r')).
  apply peel_spec in Hl; apply peel_spec in Hr.
  rewrite Hl,Hr,<-!Str_app_assoc; apply shift_rule.
Qed.
Fixpoint ones (l:list Sym) := match l with S1::l=>S (ones l) | _=>O end.
Fixpoint alternating (r:list Sym) := match r with
  | S0::S1::r=>S (alternating r) | _=>O end.
(* Stop a C scan before any possible left-overflow opportunity.
   This affects speed only: checked_shift verifies the complete prefix. *)
Fixpoint bounded_ones k (l:list Sym) := match k,l with
  | S k,S1::l=>S (bounded_ones k l) | _,_=>O end.
Definition cap_C (r l:list Sym) := match r with
  | S1::S0::S0::_=>bounded_ones 2 l
  | S1::S1::S0::S0::_=>bounded_ones 1 l
  | S1::S1::S1::S0::S0::_=>O
  | _=>ones l end.
Definition scan_proposal (s:State) : option (Shift*nat) := match s with
  | (C,l,S1::r)=>Some (Keep,cap_C (S1::r) l)
  | (E,l,S1::_)=>Some (Erase,ones l)
  | (D,_,S1::S1::r)=>Some (Twins,left_zeros r)
  | (D,_,r)=>match right_ones r with S n=>Some (Digits,n) | _=>None end
  | (F,_,r)=>match alternating r with S n=>Some (Alternating,n) | _=>None end
  | _=>None end.
Definition scan (s:State) := match scan_proposal s with
  | Some (tag,n)=>checked_shift tag n s | None=>None end.
Lemma scan_spec s t: scan s=Some t -> denote s -->* denote t.
Proof.
  unfold scan; destruct (scan_proposal s) as [[tag n]|]; try discriminate.
  apply checked_shift_spec.
Qed.

Definition primitive (s:State) : option State :=
  let '(q,l,r):=s in let '(b,r):=match r with nil=>(S0,nil) | b::r=>(b,r) end in
  match tm (q,b) with
  | None=>None
  | Some (b,R,q)=>Some (q,b::l,r)
  | Some (b,L,q)=>match l with nil=>Some (q,nil,S0::b::r) | a::l=>Some (q,l,a::b::r) end
  end.
Local Opaque tm.
Lemma primitive_spec s t: primitive s=Some t -> denote s -->* denote t.
Proof.
  destruct s as [[q l] r]; destruct r as [|b r]; unfold primitive;
    destruct (tm (q,_)) as [[[a d] q']|] eqn:E; try discriminate;
    destruct d; try destruct l as [|b' l]; intros H; injection H as <-.
  all: eapply evstep_step; [apply step_c_spec;
      cbn [step_c denote Str_app move_left move_right Streams.hd Streams.tl const];
      fold Q Sym in E; rewrite E; reflexivity|apply evstep_refl].
Qed.
Lemma primitive_halt s: primitive s=None -> halts tm (denote s).
Proof.
  destruct s as [[q l] r]; destruct r as [|b r]; unfold primitive;
    destruct (tm (q,_)) as [[[a d] q']|] eqn:E.
  all: try (destruct d; try destruct l; discriminate).
  all: intros _; apply halted_halts; exact E.
Qed.
Local Transparent tm.

Definition next (s:State) : State+unit := match accelerate s with
  | Some t=>inl t
  | None=>match overflow s with
    | Some t=>inl t
    | None=>match scan s with
      | Some t=>inl t
      | None=>match primitive s with Some t=>inl t | None=>inr tt end end end end.
Lemma next_spec s:
  match next s with inl t=>denote s -->* denote t | inr _=>halts tm (denote s) end.
Proof.
  unfold next; destruct (accelerate s) as [t|] eqn:E.
  - eapply accelerate_spec; exact E.
  - destruct (overflow s) as [t|] eqn:F.
    + eapply overflow_spec; exact F.
    + destruct (scan s) as [t|] eqn:G.
      * eapply scan_spec; exact G.
      * destruct (primitive s) as [t|] eqn:H.
        -- eapply primitive_spec; exact H.
        -- apply primitive_halt; exact H.
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
Definition initial:State := (A,nil,nil).
Definition check := check_from initial.
Lemma check_spec fuel: check fuel=true -> halts tm c0.
Proof. apply check_from_spec. Qed.
Theorem halt: halts tm c0.
Proof. apply check_spec with (fuel:=200000%N); native_check_eq. Qed.
End TM67.

Module TM68.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RE_0RD0LC_1LE1RF_1RA0RB_0RD---").
Definition rename q := match q with A=>D | B=>E | C=>A | D=>B | E=>C | F=>F end.
Lemma same_rules: Perm TM67.tm tm rename.
Proof. split; intros [] []; cbn; intros; try congruence; inversion H; reflexivity. Qed.
Theorem halt: halts tm c0.
Proof.
  eapply (perm_halts _ _ _ C tape0 same_rules).
  apply TM67.check_from_spec with (initial:=(C,nil,nil)) (fuel:=600000%N).
  native_check_eq.
Qed.
End TM68.

(* Checked fixed-width counter pairs, with primitive execution everywhere else. *)
From BusyCoq Require Import Individual62 BinaryCounter BinaryCounterFull Eqb SimplTape ES_v2.
Require Import NArith Lia ZifyNat List String.

(* TM81 is omitted: Eqv_Misc_New.TM70.eqv identifies it with TM67.
   Keep the shared checker for TM82, now in TM82's own state names. *)
Module TM82.
Definition tm := Eval compute in (TM_from_str "1RB0RC_1RC1LB_1LD1RA_0LE0LD_1LA1RF_0RE---").
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation "l |> r" := (l <* <[1;0;1;1;1] {{C}}> r) (at level 30).
Notation "l <| r" := (l <{{B}} [1;1;1;0;0] *> r) (at level 30).
Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -[tm]->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -[tm]->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
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
  | S0::S1::l=>let '(p,r):=decode_left l in (xO p,r)
  | S1::S1::l=>let '(p,r):=decode_left l in (xI p,r)
  | _=>(xH,l) end.
Lemma decode_left_spec l p r: decode_left l=(p,r) ->
  l *> 0inf=BinaryCounter ld0 ld1 (r *> 0inf) p.
Proof.
  revert l p r; fix IH 1; intros [|[] [|[] l]] p r H;
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
Definition accelerate (s:State) := match s with
  | (C,S1::S1::S1::S0::S1::l,r)=>
    let '(p,l'):=decode_left l in
    match room p with
    | N0=>None
    | k=>let '(q,r'):=decode_right (S (log2 p)) r in
      match N.min k (room q) with
      | N0=>None
      | k=>Some (C,[1;1;1;0;1]++word ld0 ld1 (addN p k)++l',
                       word rd0 rd1 (addN q k)++r') end end
  | _=>None end.
Lemma accelerate_spec s t: accelerate s=Some t -> denote s -[tm]->* denote t.
Proof.
  unfold accelerate; destruct s as [[state l] r]; destruct state; try discriminate.
  do 5 (destruct l as [|[] l]; try discriminate).
  destruct (decode_left l) as [p l'] eqn:Hl.
  destruct (room p) eqn:Hp; try discriminate.
  destruct (decode_right (S (log2 p)) r) as [q r'] eqn:Hr.
  destruct (N.min (N.pos p0) (room q)) eqn:Hk; try discriminate.
  intros H; injection H as <-.
  change (l *> 0inf |> r *> 0inf -[tm]->*
    (word ld0 ld1 (addN p (N.pos p1))++l') *> 0inf |>
    (word rd0 rd1 (addN q (N.pos p1))++r') *> 0inf).
  apply decode_left_spec in Hl; apply decode_right_spec in Hr.
  rewrite Hl,Hr,!Str_app_assoc,!word_spec.
  apply paired; rewrite <-!room_spec,<-Hk; [rewrite Hp; apply N.le_min_l|apply N.le_min_r].
Qed.

(* The two left-overflow rules are needed for the larger TM82 trajectory.
   They consume the complete left counter, but only a prefix on the right. *)
Definition edge_left (odd:bool) n m := [1;1;1;0;1] ++
  if odd then ld1 ++ (ld1<+ld0<+ld0)^^m ++ ld0^^(n+2) ++ [1]
  else ld1 ++ ld0 ++ (ld0<+ld0<+ld1)^^m ++ ld0^^n ++ [1].
Definition edge_right (odd:bool) := if odd then [0] else nil.
Definition edge_input (odd:bool) m :=
  [1;1;1;1;0;0] ++ rd1^^(m*2+if odd then 1 else 0) ++ rd0.
Lemma edge_rule odd n m r:
  ld1^^n *> 0inf {{B}}> edge_input odd m *> r -->*
  edge_left odd n m *> 0inf {{C}}> edge_right odd *> r.
Proof. destruct odd; unfold edge_input,edge_left,edge_right; es. Qed.

Fixpoint blank (l:list Sym) := match l with nil=>true | S0::l=>blank l | _=>false end.
Lemma blank_spec l: blank l=true -> l *> 0inf=0inf.
Proof. induction l as [|[] l IH]; cbn; try discriminate; auto.
  intros H; rewrite (IH H); symmetry; apply const_unfold. Qed.

Definition checked_edge odd n m (s:State) : option State :=
  let '(q,l,r):=s in
  if q_eqb q B then match peel (ld1^^n) l, peel (edge_input odd m) r with
  | Some l,Some r=>if blank l then Some (C,edge_left odd n m,edge_right odd++r) else None
  | _,_=>None end else None.
Lemma checked_edge_spec odd n m s t:
  checked_edge odd n m s=Some t -> denote s -->* denote t.
Proof.
  destruct s as [[q l] r]; unfold checked_edge.
  destruct (q_eqb_spec q B); try discriminate; subst.
  destruct (peel (ld1^^n) l) as [l'|] eqn:Hl; try discriminate.
  destruct (peel (edge_input odd m) r) as [r'|] eqn:Hr; try discriminate.
  destruct (blank l') eqn:Hb; try discriminate.
  intros H; injection H as <-; unfold denote.
  apply peel_spec in Hl; apply peel_spec in Hr; apply blank_spec in Hb.
  rewrite Hl,Hr,Hb,Str_app_assoc; apply edge_rule.
Qed.
Fixpoint left_zeros (l:list Sym) := match l with
  | S1::S1::l=>S (left_zeros l) | _=>O end.
Fixpoint right_ones (r:list Sym) := match r with
  | S1::S0::S0::r=>S (right_ones r) | _=>O end.
Definition overflow (s:State) := match s with
  | (B,l,S1::S1::S1::S1::S0::S0::r)=>
    let n:=left_zeros l in let j:=right_ones r in
    checked_edge (Nat.odd j) n (Nat.div j 2) s
  | _=>None end.
Lemma overflow_spec s t: overflow s=Some t -> denote s -->* denote t.
Proof.
  destruct s as [[q l] r]; unfold overflow; destruct q; try discriminate.
  do 6 (destruct r as [|[] r]; try discriminate).
  apply checked_edge_spec.
Qed.

Definition primitive (s:State) : option State :=
  let '(q,l,r):=s in let '(b,r):=match r with nil=>(S0,nil) | b::r=>(b,r) end in
  match tm (q,b) with
  | None=>None
  | Some (b,R,q)=>Some (q,b::l,r)
  | Some (b,L,q)=>match l with nil=>Some (q,nil,S0::b::r) | a::l=>Some (q,l,a::b::r) end
  end.
Local Opaque tm.
Lemma primitive_spec s t: primitive s=Some t -> denote s -->* denote t.
Proof.
  destruct s as [[q l] r]; destruct r as [|b r]; unfold primitive;
    destruct (tm (q,_)) as [[[a d] q']|] eqn:E; try discriminate;
    destruct d; try destruct l as [|b' l]; intros H; injection H as <-.
  all: eapply evstep_step; [apply step_c_spec;
      cbn [step_c denote Str_app move_left move_right Streams.hd Streams.tl const];
      fold Q Sym in E; rewrite E; reflexivity|apply evstep_refl].
Qed.
Lemma primitive_halt s: primitive s=None -> halts tm (denote s).
Proof.
  destruct s as [[q l] r]; destruct r as [|b r]; unfold primitive;
    destruct (tm (q,_)) as [[[a d] q']|] eqn:E.
  all: try (destruct d; try destruct l; discriminate).
  all: intros _; apply halted_halts; exact E.
Qed.
Local Transparent tm.

Definition next (s:State) : State+unit := match accelerate s with
  | Some t=>inl t
  | None=>match overflow s with
    | Some t=>inl t
    | None=>match primitive s with Some t=>inl t | None=>inr tt end end end.
Lemma next_spec s:
  match next s with inl t=>denote s -->* denote t | inr _=>halts tm (denote s) end.
Proof.
  unfold next; destruct (accelerate s) as [t|] eqn:E.
  - eapply accelerate_spec; exact E.
  - destruct (overflow s) as [t|] eqn:F.
    + eapply overflow_spec; exact F.
    + destruct (primitive s) as [t|] eqn:G.
      * eapply primitive_spec; exact G.
      * apply primitive_halt; exact G.
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
Definition initial:State := (A,nil,nil).
Definition check := check_from initial.
Lemma check_spec fuel: check fuel=true -> halts tm c0.
Proof. apply check_from_spec. Qed.
Theorem halt: halts tm c0.
Proof. apply check_spec with (fuel:=5000000%N); native_check_eq. Qed.
End TM82.

(* Checked fixed-width counter pairs, with primitive execution everywhere else. *)
From BusyCoq Require Import Individual62 BinaryCounter BinaryCounterFull Eqb SimplTape ES_v2.
Require Import NArith Lia ZifyNat List String.

Module TM117.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RC0RA_0RF1LB_0RA---").
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -[tm]->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -[tm]->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
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
  | S0::S1::l=>let '(p,r):=decode_left l in (xO p,r)
  | S1::S1::l=>let '(p,r):=decode_left l in (xI p,r)
  | _=>(xH,l) end.
Lemma decode_left_spec l p r: decode_left l=(p,r) ->
  l *> 0inf=BinaryCounter ld0 ld1 (r *> 0inf) p.
Proof.
  revert l p r; fix IH 1; intros [|[] [|[] l]] p r H;
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
Definition accelerate (s:State) := match s with
  | (A,S0::S1::l,r)=>
    if right_start r then
    let '(p,l'):=decode_left l in
    match room p with
    | N0=>None
    | k=>let '(q,r'):=decode_right (S (log2 p)) r in
      match N.min k (room q) with
      | N0=>None
      | k=>Some (A,[0;1]++word ld0 ld1 (addN p k)++l',
                       word rd0 rd1 (addN q k)++r') end end else None
  | _=>None end.
Lemma accelerate_spec s t: accelerate s=Some t -> denote s -[tm]->* denote t.
Proof.
  unfold accelerate; destruct s as [[state l] r]; destruct state; try discriminate.
  do 2 (destruct l as [|[] l]; try discriminate).
  destruct (right_start r); try discriminate.
  destruct (decode_left l) as [p l'] eqn:Hl.
  destruct (room p) eqn:Hp; try discriminate.
  destruct (decode_right (S (log2 p)) r) as [q r'] eqn:Hr.
  destruct (N.min (N.pos p0) (room q)) eqn:Hk; try discriminate.
  intros H; injection H as <-.
  change (l *> 0inf |> r *> 0inf -[tm]->*
    (word ld0 ld1 (addN p (N.pos p1))++l') *> 0inf |>
    (word rd0 rd1 (addN q (N.pos p1))++r') *> 0inf).
  apply decode_left_spec in Hl; apply decode_right_spec in Hr.
  rewrite Hl,Hr,!Str_app_assoc,!word_spec.
  apply paired; rewrite <-!room_spec,<-Hk; [rewrite Hp; apply N.le_min_l|apply N.le_min_r].
Qed.

(* Only the complete left overflow is accelerated here. *)
Definition edge_left n := [0;1]++ld0^^n++[1].
Lemma edge_rule n r:
  ld1^^n *> 0inf {{C}}> [1;1;1] *> r -->*
  edge_left n *> 0inf {{A}}> [1] *> r.
Proof. unfold edge_left; es. Qed.

Fixpoint blank (l:list Sym) := match l with nil=>true | S0::l=>blank l | _=>false end.
Lemma blank_spec l: blank l=true -> l *> 0inf=0inf.
Proof. induction l as [|[] l IH]; cbn; try discriminate; auto.
  intros H; rewrite (IH H); symmetry; apply const_unfold. Qed.

Definition checked_edge n (s:State) : option State :=
  let '(q,l,r):=s in
  if q_eqb q C then match peel (ld1^^n) l, peel [1;1;1] r with
  | Some l,Some r=>if blank l then Some (A,edge_left n,S1::r) else None
  | _,_=>None end else None.
Lemma checked_edge_spec n s t:
  checked_edge n s=Some t -> denote s -->* denote t.
Proof.
  destruct s as [[q l] r]; unfold checked_edge.
  destruct (q_eqb_spec q C); try discriminate; subst.
  destruct (peel (ld1^^n) l) as [l'|] eqn:Hl; try discriminate.
  destruct (peel [1;1;1] r) as [r'|] eqn:Hr; try discriminate.
  destruct (blank l') eqn:Hb; try discriminate.
  intros H; injection H as <-; unfold denote.
  apply peel_spec in Hl; apply peel_spec in Hr; apply blank_spec in Hb.
  rewrite Hl,Hr,Hb; apply edge_rule.
Qed.
Fixpoint left_zeros (l:list Sym) := match l with
  | S1::S1::l=>S (left_zeros l) | _=>O end.
Definition overflow (s:State) := match s with
  | (C,l,S1::S1::S1::r)=>checked_edge (left_zeros l) s
  | _=>None end.
Lemma overflow_spec s t: overflow s=Some t -> denote s -->* denote t.
Proof.
  destruct s as [[q l] r]; unfold overflow; destruct q; try discriminate.
  do 3 (destruct r as [|[] r]; try discriminate).
  apply checked_edge_spec.
Qed.

Definition primitive (s:State) : option State :=
  let '(q,l,r):=s in let '(b,r):=match r with nil=>(S0,nil) | b::r=>(b,r) end in
  match tm (q,b) with
  | None=>None
  | Some (b,R,q)=>Some (q,b::l,r)
  | Some (b,L,q)=>match l with nil=>Some (q,nil,S0::b::r) | a::l=>Some (q,l,a::b::r) end
  end.
Local Opaque tm.
Lemma primitive_spec s t: primitive s=Some t -> denote s -->* denote t.
Proof.
  destruct s as [[q l] r]; destruct r as [|b r]; unfold primitive;
    destruct (tm (q,_)) as [[[a d] q']|] eqn:E; try discriminate;
    destruct d; try destruct l as [|b' l]; intros H; injection H as <-.
  all: eapply evstep_step; [apply step_c_spec;
      cbn [step_c denote Str_app move_left move_right Streams.hd Streams.tl const];
      fold Q Sym in E; rewrite E; reflexivity|apply evstep_refl].
Qed.
Lemma primitive_halt s: primitive s=None -> halts tm (denote s).
Proof.
  destruct s as [[q l] r]; destruct r as [|b r]; unfold primitive;
    destruct (tm (q,_)) as [[[a d] q']|] eqn:E.
  all: try (destruct d; try destruct l; discriminate).
  all: intros _; apply halted_halts; exact E.
Qed.
Local Transparent tm.

Definition next (s:State) : State+unit := match accelerate s with
  | Some t=>inl t
  | None=>match overflow s with
    | Some t=>inl t
    | None=>match primitive s with Some t=>inl t | None=>inr tt end end end.
Lemma next_spec s:
  match next s with inl t=>denote s -->* denote t | inr _=>halts tm (denote s) end.
Proof.
  unfold next; destruct (accelerate s) as [t|] eqn:E.
  - eapply accelerate_spec; exact E.
  - destruct (overflow s) as [t|] eqn:F.
    + eapply overflow_spec; exact F.
    + destruct (primitive s) as [t|] eqn:G.
      * eapply primitive_spec; exact G.
      * apply primitive_halt; exact G.
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
Definition initial:State := (A,nil,nil).
Definition check := check_from initial.
Lemma check_spec fuel: check fuel=true -> halts tm c0.
Proof. apply check_from_spec. Qed.
Theorem halt: halts tm c0.
Proof. apply check_spec with (fuel:=2000000%N); native_check_eq. Qed.
End TM117.

Module TM118.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_0RF1LC_0RB---").
Definition rename q := match q with A=>B | B=>C | C=>A | q=>q end.
Lemma same_rules: Perm TM117.tm tm rename.
Proof. split; intros [] []; cbn; intros; try congruence; inversion H; reflexivity. Qed.
Definition seed:TM117.State := (C,nil,nil).
Lemma seed_spec: halts TM117.tm (TM117.denote seed) -> halts tm c0.
Proof. apply (perm_halts _ _ _ C tape0 same_rules). Qed.
Theorem halt: halts tm c0.
Proof.
  apply seed_spec, (TM117.check_from_spec seed 1000000%N).
  native_check_eq.
Qed.
End TM118.

(* Checked fixed-width counter pairs, with primitive execution everywhere else. *)
From BusyCoq Require Import Individual62 BinaryCounter BinaryCounterFull Eqb SimplTape ES_v2.
Require Import NArith Lia ZifyNat List String.

Module TM179.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RC0RA_1RF0LD_0RD---").
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -[tm]->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -[tm]->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
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
  | S0::S1::l=>let '(p,r):=decode_left l in (xO p,r)
  | S1::S1::l=>let '(p,r):=decode_left l in (xI p,r)
  | _=>(xH,l) end.
Lemma decode_left_spec l p r: decode_left l=(p,r) ->
  l *> 0inf=BinaryCounter ld0 ld1 (r *> 0inf) p.
Proof.
  revert l p r; fix IH 1; intros [|[] [|[] l]] p r H;
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
Definition accelerate (s:State) := match s with
  | (A,S0::S1::l,r)=>
    if right_start r then
    let '(p,l'):=decode_left l in
    match room p with
    | N0=>None
    | k=>let '(q,r'):=decode_right (S (log2 p)) r in
      match N.min k (room q) with
      | N0=>None
      | k=>Some (A,[0;1]++word ld0 ld1 (addN p k)++l',
                       word rd0 rd1 (addN q k)++r') end end else None
  | _=>None end.
Lemma accelerate_spec s t: accelerate s=Some t -> denote s -[tm]->* denote t.
Proof.
  unfold accelerate; destruct s as [[state l] r]; destruct state; try discriminate.
  do 2 (destruct l as [|[] l]; try discriminate).
  destruct (right_start r); try discriminate.
  destruct (decode_left l) as [p l'] eqn:Hl.
  destruct (room p) eqn:Hp; try discriminate.
  destruct (decode_right (S (log2 p)) r) as [q r'] eqn:Hr.
  destruct (N.min (N.pos p0) (room q)) eqn:Hk; try discriminate.
  intros H; injection H as <-.
  change (l *> 0inf |> r *> 0inf -[tm]->*
    (word ld0 ld1 (addN p (N.pos p1))++l') *> 0inf |>
    (word rd0 rd1 (addN q (N.pos p1))++r') *> 0inf).
  apply decode_left_spec in Hl; apply decode_right_spec in Hr.
  rewrite Hl,Hr,!Str_app_assoc,!word_spec.
  apply paired; rewrite <-!room_spec,<-Hk; [rewrite Hp; apply N.le_min_l|apply N.le_min_r].
Qed.

(* A finite zero boundary also covers the infinite blank boundary. *)
Definition edge_left n := [0;1]++ld0^^n++[1].
Lemma edge_rule n l r:
  (ld1^^n++[0]) *> l {{C}}> [1;1;1] *> r -->*
  edge_left n *> l {{A}}> [1] *> r.
Proof. unfold edge_left; es. Qed.

Definition checked_edge n (s:State) : option State :=
  let '(q,l,r):=s in
  if q_eqb q C then match peel (ld1^^n++[0]) l, peel [1;1;1] r with
  | Some l,Some r=>Some (A,edge_left n++l,S1::r)
  | _,_=>None end else None.
Lemma checked_edge_spec n s t:
  checked_edge n s=Some t -> denote s -->* denote t.
Proof.
  destruct s as [[q l] r]; unfold checked_edge.
  destruct (q_eqb_spec q C); try discriminate; subst.
  destruct (peel (ld1^^n++[0]) l) as [l'|] eqn:Hl; try discriminate.
  destruct (peel [1;1;1] r) as [r'|] eqn:Hr; try discriminate.
  intros H; injection H as <-; unfold denote.
  apply peel_spec in Hl; apply peel_spec in Hr.
  rewrite Hl,Hr.
  change ((ld1^^n++[0]) *> l' *> 0inf {{C}}> [1;1;1] *> r' *> 0inf -->*
    (edge_left n++l') *> 0inf {{A}}> [1] *> r' *> 0inf).
  rewrite (Str_app_assoc (edge_left n)); apply edge_rule.
Qed.
Fixpoint left_zeros (l:list Sym) := match l with
  | S1::S1::l=>S (left_zeros l) | _=>O end.
Definition overflow (s:State) := match s with
  | (C,l,S1::S1::S1::r)=>checked_edge (left_zeros l) s
  | _=>None end.
Lemma overflow_spec s t: overflow s=Some t -> denote s -->* denote t.
Proof.
  destruct s as [[q l] r]; unfold overflow; destruct q; try discriminate.
  do 3 (destruct r as [|[] r]; try discriminate).
  apply checked_edge_spec.
Qed.

(* Each proposal is checked against an independently proved word rule. *)
Inductive Extra := R1Even | R1Odd | R2Even0 | R2Even1 | R2Odd0 | R2Odd1 | R31.
Definition extra_input tag n : list Sym := match tag with
  | R1Even=>rd1^^(n*2)++[1;1;0;0]
  | R1Odd=>rd1^^(n*2+1)++[1;1;0;0]
  | R2Even0=>rd1^^(n*2)++[1;0;1;0;0]++rd0
  | R2Even1=>rd1^^(n*2)++[1;0;1;0;0]++rd1
  | R2Odd0=>rd1^^(n*2+1)++[1;0;1;0;0]++rd0
  | R2Odd1=>rd1^^(n*2+1)++[1;0;1;0;0]++rd1
  | R31=>[1;0;1]++rd1 end.
Definition extra_target tag n (l r:list Sym) : State := match tag with
  | R1Even=>(A,[0;1]++ld0^^(n*3)++ld1++l,[1;0]++r)
  | R1Odd=>(A,[0;1]++ld0^^(n*3+2)++ld1++l,[0]++r)
  | R2Even0=>(A,[0;1]++ld0^^(n*3+1)++ld1++l,rd1++[1]++r)
  | R2Even1=>(A,[0;1]++ld0^^(n*3+3)++ld1++l,r)
  | R2Odd0=>(A,[0;1]++ld0^^(n*3+3)++ld1++l,[0;0;1]++r)
  | R2Odd1=>(A,[0;1]++ld0^^(n*3+4)++ld1++l,[1]++r)
  | R31=>(A,[0;1]++ld0++ld1++l,[0;0]++r) end.
Lemma extra_rule tag n (l r:list Sym):
  denote (A,[0;1]++l,extra_input tag n++r) -->* denote (extra_target tag n l r).
Proof.
  destruct tag; cbn [extra_input extra_target]; unfold denote;
    cbn [Str_app app]; repeat (rewrite Str_app_assoc; cbn [Str_app app]);
    generalize (l *> 0inf), (r *> 0inf); intros l' r'; clear l r.
  all: es.
Qed.
Definition checked_extra tag n (s:State) : option State :=
  let '(q,l,r):=s in
  if q_eqb q A then match peel [0;1] l, peel (extra_input tag n) r with
  | Some l,Some r=>Some (extra_target tag n l r) | _,_=>None end else None.
Lemma checked_extra_spec tag n s t:
  checked_extra tag n s=Some t -> denote s -->* denote t.
Proof.
  destruct s as [[q l] r]; unfold checked_extra.
  destruct (q_eqb_spec q A); try discriminate; subst.
  destruct (peel [0;1] l) as [l'|] eqn:Hl; try discriminate.
  destruct (peel (extra_input tag n) r) as [r'|] eqn:Hr; try discriminate.
  intros H; injection H as <-.
  change (l *> 0inf {{A}}> r *> 0inf -->* denote (extra_target tag n l' r')).
  apply peel_spec in Hl; apply peel_spec in Hr.
  rewrite Hl,Hr,<-!Str_app_assoc; apply extra_rule.
Qed.
Fixpoint right_ones (r:list Sym) : nat * list Sym := match r with
  | S1::S0::S0::r=>let '(n,r):=right_ones r in (S n,r)
  | _=>(O,r) end.
Definition right_extra (l r:list Sym) : option (Extra*nat) := match l with
  | S0::S1::_=>let '(j,t):=right_ones r in
    match peel [1;1;0;0] t with
    | Some _=>Some (if Nat.odd j then R1Odd else R1Even,Nat.div j 2)
    | None=>match peel [1;0;1;0;0;0;0;0] t with
      | Some _=>Some (if Nat.odd j then R2Odd0 else R2Even0,Nat.div j 2)
      | None=>match peel [1;0;1;0;0;1;0;0] t with
        | Some _=>Some (if Nat.odd j then R2Odd1 else R2Even1,Nat.div j 2)
        | None=>match j,peel [1;0;1;1;0;0] t with
          | O,Some _=>Some (R31,O) | _,_=>None end end end end
  | _=>None end.
Definition extra (s:State) := match s with
  | (A,l,r)=>match right_extra l r with
    | Some (tag,n)=>checked_extra tag n s | None=>None end
  | _=>None end.
Lemma extra_spec s t: extra s=Some t -> denote s -->* denote t.
Proof.
  destruct s as [[q l] r]; destruct q; cbn [extra]; try discriminate.
  destruct (right_extra l r) as [[tag n]|]; try discriminate.
  apply checked_extra_spec.
Qed.

Definition primitive (s:State) : option State :=
  let '(q,l,r):=s in let '(b,r):=match r with nil=>(S0,nil) | b::r=>(b,r) end in
  match tm (q,b) with
  | None=>None
  | Some (b,R,q)=>Some (q,b::l,r)
  | Some (b,L,q)=>match l with nil=>Some (q,nil,S0::b::r) | a::l=>Some (q,l,a::b::r) end
  end.
Local Opaque tm.
Lemma primitive_spec s t: primitive s=Some t -> denote s -->* denote t.
Proof.
  destruct s as [[q l] r]; destruct r as [|b r]; unfold primitive;
    destruct (tm (q,_)) as [[[a d] q']|] eqn:E; try discriminate;
    destruct d; try destruct l as [|b' l]; intros H; injection H as <-.
  all: eapply evstep_step; [apply step_c_spec;
      cbn [step_c denote Str_app move_left move_right Streams.hd Streams.tl const];
      fold Q Sym in E; rewrite E; reflexivity|apply evstep_refl].
Qed.
Lemma primitive_halt s: primitive s=None -> halts tm (denote s).
Proof.
  destruct s as [[q l] r]; destruct r as [|b r]; unfold primitive;
    destruct (tm (q,_)) as [[[a d] q']|] eqn:E.
  all: try (destruct d; try destruct l; discriminate).
  all: intros _; apply halted_halts; exact E.
Qed.
Local Transparent tm.

Definition next (s:State) : State+unit := match accelerate s with
  | Some t=>inl t
  | None=>match overflow s with
    | Some t=>inl t
    | None=>match extra s with
      | Some t=>inl t
      | None=>match primitive s with Some t=>inl t | None=>inr tt end end end end.
Lemma next_spec s:
  match next s with inl t=>denote s -->* denote t | inr _=>halts tm (denote s) end.
Proof.
  unfold next; destruct (accelerate s) as [t|] eqn:E.
  - eapply accelerate_spec; exact E.
  - destruct (overflow s) as [t|] eqn:F.
    + eapply overflow_spec; exact F.
    + destruct (extra s) as [t|] eqn:G.
      * eapply extra_spec; exact G.
      * destruct (primitive s) as [t|] eqn:H.
        -- eapply primitive_spec; exact H.
        -- apply primitive_halt; exact H.
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
Definition initial:State := (A,nil,nil).
Definition check := check_from initial.
Lemma check_spec fuel: check fuel=true -> halts tm c0.
Proof. apply check_from_spec. Qed.
Theorem halt: halts tm c0.
Proof. apply check_spec with (fuel:=100000%N); native_check_eq. Qed.
End TM179.

Module TM177.
Definition tm := Eval compute in (TM_from_str "1RB0LC_0RC---_1RD0RE_1RE1RA_1LF1RC_1LD0LF").
Lemma renamed: Perm TM179.tm tm
  (fun q=>match q with A=>E | B=>F | C=>D | D=>C | E=>A | F=>B end).
Proof. split; intros [] []; cbn; intros; try congruence; inversion H; reflexivity. Qed.
Theorem halt: halts tm c0.
Proof.
  eapply (perm_halts _ _ _ E _ renamed).
  apply TM179.check_from_spec with (initial:=(E,nil,nil)) (fuel:=500000%N).
  native_check_eq.
Qed.
End TM177.


