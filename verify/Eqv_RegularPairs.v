(* Compact reconstructions of published PR pairs, not new class merges.
   Only literal original machines are defined; state maps belong to the
   common configuration representation.  Certificates are generated in Coq. *)
From BusyCoq Require Import Individual62 ES_v2 Helper Eqb.
Require Import List String Lia NArith PeanoNat.
Open Scope sym_scope.

Module Regular.
Local Notation "x && y" := (if x then y else false) (at level 40,left associativity).
Local Notation "x || y" := (if x then true else y) (at level 50,left associativity).
Record entry := Ent { control:Q; scanned:Sym; leftD:nat; rightD:nat }.
Definition same a b := q_eqb (control a) (control b) &&
  sym_eqb (scanned a) (scanned b) && Nat.eqb (leftD a) (leftD b) && Nat.eqb (rightD a) (rightD b).
Definition member a xs := existsb (same a) xs.
Lemma member_spec a xs: member a xs=true <-> In a xs.
Proof.
  unfold member. rewrite existsb_exists. assert (E:forall a b,same a b=true <-> a=b).
  { intros [q s l r] [q' s' l' r']; unfold same; cbn.
    rewrite !and_true_iff,!Nat.eqb_eq.
    destruct (q_eqb_spec q q'),(sym_eqb_spec s s'); cbn; intuition congruence. }
  setoid_rewrite E. split; [intros [x [H ->]]; exact H|intro H; exists a; auto].
Qed.
Definition alphabet : list Sym := [0;1].
Lemma all_symbols f: forallb f alphabet=true <-> forall b,f b=true.
Proof. rewrite forallb_forall. split; [intros H b; apply H; destruct b; cbn; auto|auto]. Qed.
Lemma all_states n f: forallb f (seq 0 n)=true <-> forall p,p<n -> f p=true.
Proof. rewrite forallb_forall. split; intros H p E; apply H; apply in_seq in E || apply in_seq; lia. Qed.
Definition successor (d:nat->Sym->nat) a w dir q b p := match dir with
| L=>Ent q b p (d (rightD a) w) | R=>Ent q b (d (leftD a) w) p end.
Definition popped a dir := match dir with L=>leftD a|R=>rightD a end.
Definition successors tm n d a := match tm (control a,scanned a) with
| None=>[] | Some(w,dir,q)=>flat_map (fun p=>flat_map (fun b=>
  if Nat.eqb (d p b) (popped a dir) then [successor d a w dir q b p] else []) alphabet) (seq 0 n) end.
Definition initial := Ent A 0 0 0.
Definition discover tm n d := fst (N.iter 20000%N (fun '(seen,todo)=>match todo with
| []=>(seen,[]) | a::todo=>if member a seen then (seen,todo)
  else (a::seen,successors tm n d a++todo) end) ([],[initial])).
Definition transition_ok tm n d xs a := match tm (control a,scanned a) with
| None=>true | Some(w,dir,q)=>forallb (fun p=>forallb (fun b=>
  negb (Nat.eqb (d p b) (popped a dir)) || member (successor d a w dir q b p) xs)
  alphabet) (seq 0 n) end.
Definition check tm n d xs := Nat.eqb (d 0%nat 0) 0%nat && (0<?n)%nat &&
  forallb (fun p=>forallb (fun b=>(d p b<?n)%nat) alphabet) (seq 0 n) &&
  member initial xs && forallb (transition_ok tm n d xs) xs.

Section Semantics.
Variable n:nat.
Variable d:nat->Sym->nat.
Hypothesis Dz:d 0%nat 0=0%nat.
Hypothesis Dn:0<n.
Hypothesis Db:forall p,p<n -> forall b,d p b<n.
Inductive accepts : nat->side->Prop :=
| accepts_blank: accepts 0%nat 0inf
| accepts_push p b r: accepts p r -> accepts (d p b) (b>>r).
Lemma accepts_bound p r: accepts p r -> p<n.
Proof. intro H; induction H; auto. Qed.
Lemma accepts_pop p r: accepts p r ->
  exists j,accepts j (Streams.tl r) /\ d j (Streams.hd r)=p.
Proof. intro H; destruct H; [exists 0%nat|exists p]; cbn; auto using accepts. Qed.
Definition Inv xs c := let '(q,(l,s,r)):=c in exists a b,
  accepts a l /\ accepts b r /\ In (Ent q s a b) xs.
Lemma preserved tm xs:
  (forall a,In a xs -> transition_ok tm n d xs a=true) ->
  forall c c',Inv xs c -> c -[tm]-> c' -> Inv xs c'.
Proof.
  intros H [q [[l s] r]] c' [a [b [Ha [Hb Hi]]]] E.
  apply step_c_spec in E. unfold step_c in E.
  specialize (H _ Hi). unfold transition_ok in H. cbn [control scanned] in H.
  destruct (tm (q,s)) as [[[w dir] q']|] eqn:F; [|discriminate].
  rewrite all_states in H. destruct dir; inversion E; subst; cbn [Inv].
  - destruct (accepts_pop _ _ Ha) as [j [Hj Eq]].
    exists j,(d b w). repeat split; auto using accepts.
    specialize (H _ (accepts_bound _ _ Hj)). rewrite all_symbols in H.
    specialize (H (Streams.hd l)). cbn [popped] in H. rewrite Eq,Nat.eqb_refl in H.
    apply member_spec,H.
  - destruct (accepts_pop _ _ Hb) as [j [Hj Eq]].
    exists (d a w),j. repeat split; auto using accepts.
    specialize (H _ (accepts_bound _ _ Hj)). rewrite all_symbols in H.
    specialize (H (Streams.hd r)). cbn [popped] in H. rewrite Eq,Nat.eqb_refl in H.
    apply member_spec,H.
Qed.
Lemma reachable tm xs: check tm n d xs=true -> forall c,c0 -[tm]->* c -> Inv xs c.
Proof.
  intro H. unfold check in H. rewrite !and_true_iff,!forallb_forall,member_spec in H.
  destruct H as [[[[_ _] _] Hi] H].
  assert (I:Inv xs c0) by (exists 0%nat,0%nat; auto using accepts).
  intros c E. gen I. induction E; intros; [assumption|].
  apply IHE. eapply preserved; eauto.
Qed.
End Semantics.

Definition of_table (xs:list(nat*nat)) p b := let row:=nth p xs (0%nat,0%nat) in
  match b with 0=>fst row|1=>snd row end.
Definition factor100 := of_table [(0,1);(2,1);(3,1);(3,4);(3,4)]%nat.
Definition factor0010 := of_table [(0,1);(2,3);(4,5);(6,3);(4,5);(2,7);(0,8);(2,7);(6,3)]%nat.
(* Check a finite near-head word without a separate label table. *)
Fixpoint prefix_ok n d (xs:list Sym) p := match xs with
| []=>true
| b::xs=>forallb (fun j=>forallb (fun c=>negb (Nat.eqb (d j c) p) ||
    (sym_eqb c b && prefix_ok n d xs j)) alphabet) (seq 0 n) end.
Lemma prefix_spec n d xs:
  d 0%nat 0=0%nat -> 0<n -> (forall p,p<n -> forall b,d p b<n) ->
  forall p t,accepts d p t -> prefix_ok n d xs p=true -> exists r,t=xs*>r.
Proof.
  intros Dz Dn Db. induction xs as [|b xs IH]; intros p t H E; [exists t; reflexivity|].
  destruct (accepts_pop d Dz _ _ H) as [j [Hj Eq]].
  cbn [prefix_ok] in E. rewrite all_states in E.
  specialize (E _ (accepts_bound n d Dn Db _ _ Hj)). rewrite all_symbols in E.
  specialize (E (Streams.hd t)). rewrite Eq,Nat.eqb_refl in E.
  apply and_true_iff in E as [E F]. destruct (sym_eqb_spec (Streams.hd t) b); [|discriminate].
  destruct (IH _ _ Hj F) as [r Hr]. exists r. destruct t; cbn in *; now subst.
Qed.
Definition word_guard q s (left:bool) n d w a :=
  if q_eqb (control a) q && sym_eqb (scanned a) s then
    prefix_ok n d w (if left then leftD a else rightD a) else true.
Definition verify_word tm n d q s left w := let xs:=discover tm n d in
  check tm n d xs && forallb (word_guard q s left n d w) xs.
Lemma reachable_word tm n d q s left w:
  verify_word tm n d q s left w=true ->
  forall l r,c0 -[tm]->* (q,(l,s,r)) -> exists t,(if left then l else r)=w*>t.
Proof.
  unfold verify_word. set (xs:=discover tm n d). intro H.
  rewrite and_true_iff in H. destruct H as [HC HG].
  pose proof HC as HD. unfold check in HD. rewrite !and_true_iff in HD.
  destruct HD as [[[[Dz Dn] Db] _] _]. apply Nat.eqb_eq in Dz. apply Nat.ltb_lt in Dn.
  rewrite all_states in Db. setoid_rewrite all_symbols in Db. setoid_rewrite Nat.ltb_lt in Db.
  intros l r HR. apply (reachable n d Dz Dn Db tm xs HC) in HR as [a [b [Ha [Hb Hi]]]].
  rewrite forallb_forall in HG. specialize (HG _ Hi). unfold word_guard in HG; cbn in HG.
  destruct (q_eqb_spec q q),(sym_eqb_spec s s); try congruence; cbn in HG.
  destruct left; [exact (prefix_spec n d w Dz Dn Db _ _ Ha HG)|
    exact (prefix_spec n d w Dz Dn Db _ _ Hb HG)].
Qed.

Definition map_config (p:Q->Q) (c:Q*tape) := (p (fst c),snd c).
Lemma common_model_from tm tm' p f:
  (forall (b:bool) c,c0 -[tm]->* c -> match f c with
   | Some c'=>map_config (if b then p else fun q=>q) c
       -[if b then tm' else tm]->+ map_config (if b then p else fun q=>q) c'
   | None=>halts (if b then tm' else tm) (map_config (if b then p else fun q=>q) c) end) ->
  halts tm c0 <-> halts tm' (map_config p c0).
Proof.
  intro H. assert (E:forall b:bool,halts (if b then tm' else tm)
    (map_config (if b then p else fun q=>q) c0) <-> iter_halts f c0).
  { intro b.
    apply (halts_iff _ _ c0 f _ (fun c=>c0 -[tm]->* c)); [|constructor].
    intros c HC. specialize (H false c HC) as H0. specialize (H b c HC).
    destruct (f c) as [c'|]; [split; [exact H|]|exact H].
    eapply evstep_trans; [exact HC|]. apply progress_evstep.
    destruct c,c'; exact H0. }
  change (halts tm (map_config (fun q=>q) c0) <-> halts tm' (map_config p c0)).
  rewrite (E false),(E true); tauto.
Qed.
Lemma common_model tm tm' p f:
  p A=A ->
  (forall (b:bool) c,c0 -[tm]->* c -> match f c with
   | Some c'=>map_config (if b then p else fun q=>q) c
       -[if b then tm' else tm]->+ map_config (if b then p else fun q=>q) c'
   | None=>halts (if b then tm' else tm) (map_config (if b then p else fun q=>q) c) end) ->
  halts tm c0 <-> halts tm' c0.
Proof.
  intros Hp H. rewrite (common_model_from tm tm' p f H).
  change (halts tm' (p A,tape0) <-> halts tm' (A,tape0)). now rewrite Hp.
Qed.
End Regular.

(* PR #8, 815-table rows 3/751. *)
Module TM99.
Definition tm := Eval compute in (TM_from_str "1RB0LC_1LA1RF_1LD1RF_1LE0LA_0RB---_0RA1RE").
Definition tm' := Eval compute in (TM_from_str "1RB0LC_1LA1RE_1LD1RE_1RE0LA_0RA1RF_0RB---").
Definition rename q := match q with E=>F|F=>E|_=>q end.
Definition f (c:Q*tape) := match c with
| (D,(l,0,r))=>Some(F,(1>>0>>Streams.tl l,Streams.hd r,Streams.tl r))
| _=>step_c tm c end.
Lemma guarded l r: c0 -[tm]->* (D,(l,0,r)) -> exists t,l=[0]*>t.
Proof. apply (Regular.reachable_word tm 5 Regular.factor100 D 0 true [0]). native_check_eq. Qed.
Lemma f_spec (b:bool) c: c0 -[tm]->* c -> match f c with
| Some c'=>Regular.map_config (if b then rename else fun q=>q) c
  -[if b then tm' else tm]->+ Regular.map_config (if b then rename else fun q=>q) c'
| None=>halts (if b then tm' else tm) (Regular.map_config (if b then rename else fun q=>q) c) end.
Proof.
  destruct c as [q [[l s] r]],q,s; intro H;
    try (apply guarded in H; destruct H as [t ->]);
    destruct b; cbn [f step_c Regular.map_config rename tm tm' move_left move_right]; esx.
Qed.
Theorem eqv: halts tm c0 <-> halts tm' c0.
Proof. apply (Regular.common_model tm tm' rename f); [reflexivity|exact f_spec]. Qed.
End TM99.

(* PR #8, rows 439/600. *)
Module TM100.
Definition tm := Eval compute in (TM_from_str "1RB1LE_1RC0RF_0LD---_1RF1LE_0LF1LC_1LD0RA").
Definition tm' := Eval compute in (TM_from_str "1RB1LC_1LC0RF_0LF1LD_0LE---_1RF1LC_1LE0RA").
Definition rename q := match q with C=>D|D=>E|E=>C|_=>q end.
Definition f (c:Q*tape) := match c with
| (B,(l,0,r))=>Some(E,(Streams.tl l,Streams.hd l,1>>0>>Streams.tl r))
| _=>step_c tm c end.
Lemma guarded l r: c0 -[tm]->* (B,(l,0,r)) -> exists t,r=[0]*>t.
Proof. apply (Regular.reachable_word tm 5 Regular.factor100 B 0 false [0]). native_check_eq. Qed.
Lemma f_spec (b:bool) c: c0 -[tm]->* c -> match f c with
| Some c'=>Regular.map_config (if b then rename else fun q=>q) c
  -[if b then tm' else tm]->+ Regular.map_config (if b then rename else fun q=>q) c'
| None=>halts (if b then tm' else tm) (Regular.map_config (if b then rename else fun q=>q) c) end.
Proof.
  destruct c as [q [[l s] r]],q,s; intro H;
    try (apply guarded in H; destruct H as [t ->]);
    destruct b; cbn [f step_c Regular.map_config rename tm tm' move_left move_right]; esx.
Qed.
Theorem eqv: halts tm c0 <-> halts tm' c0.
Proof. apply (Regular.common_model tm tm' rename f); [reflexivity|exact f_spec]. Qed.
End TM100.

(* PR #8, rows 728/772. *)
Module TM101.
Definition tm := Eval compute in (TM_from_str "1RB0RF_0RC1RD_0LD---_1LE1RA_1LA0LF_0RD0RC").
Definition tm' := Eval compute in (TM_from_str "1RB0RD_1LC1RE_1LA0LD_0RE0RF_1LC1RA_0LE---").
Definition rename q := match q with C=>F|D=>E|E=>C|F=>D|_=>q end.
Definition f (c:Q*tape) := match c with
| (B,(l,0,r))=>Some(E,(Streams.tl l,Streams.hd l,1>>0>>Streams.tl r))
| _=>step_c tm c end.
Lemma guarded l r: c0 -[tm]->* (B,(l,0,r)) -> exists t,r=[0]*>t.
Proof. apply (Regular.reachable_word tm 5 Regular.factor100 B 0 false [0]). native_check_eq. Qed.
Lemma f_spec (b:bool) c: c0 -[tm]->* c -> match f c with
| Some c'=>Regular.map_config (if b then rename else fun q=>q) c
  -[if b then tm' else tm]->+ Regular.map_config (if b then rename else fun q=>q) c'
| None=>halts (if b then tm' else tm) (Regular.map_config (if b then rename else fun q=>q) c) end.
Proof.
  destruct c as [q [[l s] r]],q,s; intro H;
    try (apply guarded in H; destruct H as [t ->]);
    destruct b; cbn [f step_c Regular.map_config rename tm tm' move_left move_right]; esx.
Qed.
Theorem eqv: halts tm c0 <-> halts tm' c0.
Proof. apply (Regular.common_model tm tm' rename f); [reflexivity|exact f_spec]. Qed.
End TM101.

(* PR #7, rows 220/723. *)
Module TM102.
Definition tm := Eval compute in (TM_from_str "1RB1RE_0LC1RF_---1LD_1LE0LD_1LA1LB_1RE0RA").
Definition tm' := Eval compute in (TM_from_str "1RB1RE_0LC1RF_---1LD_1LE0LD_1LA1LB_1RF0RA").
Definition f := step_c tm'.
Lemma guarded l r: c0 -[tm]->* (F,(l,0,r)) -> exists t,r=[1]*>t.
Proof. apply (Regular.reachable_word tm 9 Regular.factor0010 F 0 false [1]). native_check_eq. Qed.
Lemma f_spec (b:bool) c: c0 -[tm]->* c -> match f c with
| Some c'=>Regular.map_config (fun q=>q) c
  -[if b then tm' else tm]->+ Regular.map_config (fun q=>q) c'
| None=>halts (if b then tm' else tm) (Regular.map_config (fun q=>q) c) end.
Proof.
  destruct c as [q [[l s] r]],q,s; intro H;
    try (apply guarded in H; destruct H as [t ->]);
    destruct b; cbn [f step_c Regular.map_config tm tm' move_left move_right]; esx.
Qed.
Theorem eqv: halts tm c0 <-> halts tm' c0.
Proof. apply (Regular.common_model tm tm' (fun q=>q) f); [reflexivity|].
  intros []; [exact (f_spec true)|exact (f_spec false)]. Qed.
End TM102.

(* PR #8, rows 70/223: retain the common finite-halting branch. *)
Module TM103.
Definition tm := Eval compute in (TM_from_str "1RB1LF_1LC1RE_1LD1RD_1LA0LB_0RC---_1RC0LD").
Definition tm' := Eval compute in (TM_from_str "1RB1LE_0RC1RF_1LD1RD_1LA0LB_1RC0LD_0RC---").
Definition rename q := match q with E=>F|F=>E|_=>q end.
Definition f (c:Q*tape) := match c with
| (B,(l,0,r))=>match Streams.hd l with
  | 0=>None | 1=>Some(C,(0>>l,Streams.hd r,Streams.tl r)) end
| _=>step_c tm c end.
Import Regular.
Lemma db p: p<5 -> forall b,factor100 p b<5.
Proof. intros Hp b. do 5 (destruct p as [|p]; [destruct b; cbn; lia|]); lia. Qed.
Lemma zero_is_blank p t: accepts factor100 p t -> p=0%nat -> t=0inf.
Proof.
  intro H. induction H; intro E; [reflexivity|].
  assert (K:forall j b,j<5 -> factor100 j b=0%nat -> j=0%nat /\ b=0).
  { intros j x Hj F. do 5 (destruct j as [|j]; [destruct x; cbn in F; intuition discriminate|]); lia. }
  apply (K _ _ (accepts_bound 5 factor100 ltac:(lia) db _ _ H)) in E as [-> ->].
  rewrite IHaccepts by reflexivity. symmetry; apply const_unfold.
Qed.
Definition terminal_guard a := match control a,scanned a with
| B,0=>if prefix_ok 5 factor100 [1] (leftD a) then true else
  if Nat.eqb (leftD a) 0 then prefix_ok 5 factor100 [0] (rightD a) else false
| _,_=>true end.
Definition cert := discover tm 5 factor100.
Lemma checked: check tm 5 factor100 cert=true /\ forallb terminal_guard cert=true.
Proof. split; native_check_eq. Qed.
Local Opaque cert.
Lemma guarded l r: c0 -[tm]->* (B,(l,0,r)) ->
  Streams.hd l=1 \/ l=0inf /\ Streams.hd r=0.
Proof.
  intro H. apply (reachable 5 factor100 eq_refl ltac:(lia) db tm cert (proj1 checked)) in H
    as [a [b [Ha [Hb Hi]]]].
  pose proof (proj2 checked) as G. rewrite forallb_forall in G. specialize (G _ Hi).
  cbn [terminal_guard control scanned leftD rightD] in G.
  destruct (prefix_ok 5 factor100 [1] a) eqn:E.
  { left. destruct (prefix_spec 5 factor100 [1] eq_refl ltac:(lia) db _ _ Ha E) as [t ->]. reflexivity. }
  destruct (Nat.eqb_spec a 0); [subst a|discriminate].
  right. split; [exact (zero_is_blank _ _ Ha eq_refl)|].
  destruct (prefix_spec 5 factor100 [0] eq_refl ltac:(lia) db _ _ Hb G) as [t ->]. reflexivity.
Qed.
Lemma f_spec (b:bool) c: c0 -[tm]->* c -> match f c with
| Some c'=>map_config (if b then rename else fun q=>q) c
  -[if b then tm' else tm]->+ map_config (if b then rename else fun q=>q) c'
| None=>halts (if b then tm' else tm) (map_config (if b then rename else fun q=>q) c) end.
Proof.
  destruct c as [q [[l s] r]],q,s; intro H;
    try (apply guarded in H; destruct H as [H|[-> H]];
      [destruct l as [x l]|destruct r as [x r]]; cbn in H; subst x);
    destruct b; cbn [f step_c map_config rename tm tm' move_left move_right Streams.hd Streams.tl const]; esx.
Qed.
Theorem eqv: halts tm c0 <-> halts tm' c0.
Proof. apply (common_model tm tm' rename f); [reflexivity|exact f_spec]. Qed.
End TM103.

(* PR #10, rows 408/326; the state map moves A, so prove initialization. *)
Module TM104.
Definition tm := Eval compute in (TM_from_str "1RB0RE_0LC---_1RE1LD_0LE1LB_1LC0RF_1RA1LD").
Definition tm' := Eval compute in (TM_from_str "1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---").
Definition rename q := match q with A=>E|B=>F|C=>A|D=>C|E=>B|F=>D end.
Definition f (c:Q*tape) := match c with
| (A,(l,0,r))=>Some(D,(Streams.tl l,Streams.hd l,1>>0>>Streams.tl r))
| _=>step_c tm c end.
Lemma guarded l r: c0 -[tm]->* (A,(l,0,r)) -> exists t,r=[0]*>t.
Proof. apply (Regular.reachable_word tm 5 Regular.factor100 A 0 false [0]). native_check_eq. Qed.
Lemma f_spec (b:bool) c: c0 -[tm]->* c -> match f c with
| Some c'=>Regular.map_config (if b then rename else fun q=>q) c
  -[if b then tm' else tm]->+ Regular.map_config (if b then rename else fun q=>q) c'
| None=>halts (if b then tm' else tm) (Regular.map_config (if b then rename else fun q=>q) c) end.
Proof.
  destruct c as [q [[l s] r]],q,s; intro H;
    try (apply guarded in H; destruct H as [t ->]);
    destruct b; cbn [f step_c Regular.map_config rename tm tm' move_left move_right]; esx.
Qed.
Definition meet := Eval vm_compute in
  match multistep_c tm' 3242 c0 with Some c=>c|None=>c0 end.
Lemma init: c0 -[tm']->* meet.
Proof. eapply without_counter, multistep_c_spec with (n:=3242). native_check_eq. Qed.
Lemma reinit: Regular.map_config rename c0 -[tm']->* meet.
Proof. eapply without_counter, multistep_c_spec with (n:=2235). vm_compute; simpl_tape; reflexivity. Qed.
Theorem eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite (Regular.common_model_from tm tm' rename f f_spec).
  rewrite (halts_evstep_iff _ _ _ reinit),(halts_evstep_iff _ _ _ init). reflexivity.
Qed.
End TM104.

(* PR pair 464/572; only the DFA table is stored, not its closure. *)
Module TM105.
Definition tm := Eval compute in (TM_from_str "1RB0RC_1LC0RB_1RE1LD_0LB0LF_---0RA_1LB0RC").
Definition tm' := Eval compute in (TM_from_str "1RB0RC_1LC0RB_1RE1LD_0LB0LF_---0RA_1LB1LD").
Definition delta := Regular.of_table [
  (0,1);(2,3);(4,5);(6,7);(8,1);(9,10);(11,12);(13,14);
  (15,16);(0,5);(17,3);(18,19);(9,10);(20,21);(22,14);(4,1);
  (23,7);(4,12);(24,25);(26,3);(20,27);(28,29);(20,30);(11,5);
  (31,19);(13,14);(32,33);(34,14);(20,35);(36,7);(34,37);(38,21);
  (39,1);(23,40);(20,35);(34,37);(41,33);(22,14);(42,27);(43,16);
  (44,29);(45,19);(20,21);(32,16);(20,21);(46,25);(47,48);(20,21);
  (36,7)]%nat.
Definition f := step_c tm.
Lemma guarded l r: c0 -[tm]->* (F,(l,1,r)) -> exists t,l=[0;1]*>t.
Proof. apply (Regular.reachable_word tm 49 delta F 1 true [0;1]). native_check_eq. Qed.
Lemma f_spec (b:bool) c: c0 -[tm]->* c -> match f c with
| Some c'=>Regular.map_config (fun q=>q) c
  -[if b then tm' else tm]->+ Regular.map_config (fun q=>q) c'
| None=>halts (if b then tm' else tm) (Regular.map_config (fun q=>q) c) end.
Proof.
  destruct c as [q [[l s] r]],q,s; intro H;
    try (apply guarded in H; destruct H as [t ->]);
    destruct b; cbn [f step_c Regular.map_config tm tm' move_left move_right]; esx.
Qed.
Theorem eqv: halts tm c0 <-> halts tm' c0.
Proof. apply (Regular.common_model tm tm' (fun q=>q) f); [reflexivity|].
  intros []; [exact (f_spec true)|exact (f_spec false)]. Qed.
End TM105.

(* PR pair 582/637; only the DFA table is stored, not its closure. *)
Module TM106.
Definition tm := Eval compute in (TM_from_str "1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---1LC").
Definition tm' := Eval compute in (TM_from_str "1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA").
Definition delta := Regular.of_table [
  (0,1);(2,3);(4,5);(6,7);(8,9);(10,11);(12,13);(14,15);
  (16,17);(18,19);(20,21);(22,23);(24,25);(18,19);(26,27);(28,29);
  (30,17);(30,17);(31,32);(33,34);(35,36);(37,38);(39,40);(41,42);
  (16,17);(43,44);(8,25);(45,46);(26,27);(47,48);(30,17);(35,17);
  (49,50);(51,25);(52,36);(30,17);(53,54);(55,21);(56,57);(35,17);
  (45,46);(52,36);(58,59);(31,32);(33,60);(61,32);(62,63);(26,27);
  (14,15);(64,32);(65,17);(16,17);(30,17);(30,17);(30,66);(35,36);
  (52,36);(41,42);(52,36);(67,68);(30,17);(35,17);(69,70);(52,36);
  (35,17);(30,17);(52,36);(52,36);(41,42);(35,17);(71,72);(61,32);
  (62,73);(30,17)]%nat.
Definition f := step_c tm'.
Lemma guarded l r: c0 -[tm]->* (F,(l,1,r)) -> exists t,l=[0]*>t.
Proof. apply (Regular.reachable_word tm 74 delta F 1 true [0]). native_check_eq. Qed.
Lemma f_spec (b:bool) c: c0 -[tm]->* c -> match f c with
| Some c'=>Regular.map_config (fun q=>q) c
  -[if b then tm' else tm]->+ Regular.map_config (fun q=>q) c'
| None=>halts (if b then tm' else tm) (Regular.map_config (fun q=>q) c) end.
Proof.
  destruct c as [q [[l s] r]],q,s; intro H;
    try (apply guarded in H; destruct H as [t ->]);
    destruct b; cbn [f step_c Regular.map_config tm tm' move_left move_right]; esx.
Qed.
Theorem eqv: halts tm c0 <-> halts tm' c0.
Proof. apply (Regular.common_model tm tm' (fun q=>q) f); [reflexivity|].
  intros []; [exact (f_spec true)|exact (f_spec false)]. Qed.
End TM106.

(* PR pair 759/808; only the DFA table is stored, not its closure. *)
Module TM107.
Definition tm := Eval compute in (TM_from_str "1RB1LD_0RC1LE_1RD0LA_1RE0RC_1LF0LC_---1LB").
Definition tm' := Eval compute in (TM_from_str "1RB1LD_0RC1LE_1RD0LA_1RE0RF_1LF0LC_---1LB").
Definition delta := Regular.of_table [
  (0,1);(2,3);(4,5);(6,7);(8,9);(10,11);(12,13);(14,15);
  (8,9);(8,9);(8,16);(17,18);(8,9);(10,19);(20,21);(22,23);
  (8,24);(8,16);(25,26);(17,18);(27,28);(29,30);(31,32);(33,34);
  (8,9);(35,36);(25,37);(38,39);(40,9);(41,16);(42,43);(44,45);
  (29,30);(46,47);(48,49);(8,9);(10,50);(25,37);(51,52);(8,9);
  (8,9);(8,9);(53,16);(14,54);(55,56);(57,58);(59,60);(29,30);
  (61,62);(63,64);(17,18);(53,9);(8,65);(8,9);(22,23);(66,67);
  (68,69);(41,9);(51,70);(71,72);(73,74);(75,76);(29,30);(77,32);
  (78,79);(8,9);(80,81);(82,83);(41,9);(51,84);(85,86);(66,67);
  (68,69);(41,9);(51,70);(71,72);(73,83);(87,45);(88,47);(89,90);
  (91,92);(8,9);(41,9);(51,70);(93,94);(95,96);(97,98);(71,56);
  (75,60);(61,62);(99,90);(100,101);(102,103);(95,96);(97,104);(27,28);
  (68,69);(105,106);(107,108);(61,62);(109,9);(8,9);(8,9);(8,9);
  (110,111);(44,45);(68,69);(112,106);(113,114);(8,9);(115,116);(117,118);
  (119,45);(120,106);(121,122);(59,60);(68,69);(123,124);(125,126);(71,56);
  (87,45);(120,106);(121,127);(75,76);(68,69);(120,106);(128,129);(128,129);
  (130,116);(131,132);(75,60);(123,124);(133,132);(123,124)]%nat.
Definition f := step_c tm.
Lemma guarded l r: c0 -[tm]->* (D,(l,1,r)) -> exists t,r=[1]*>t.
Proof. apply (Regular.reachable_word tm 134 delta D 1 false [1]). native_check_eq. Qed.
Lemma f_spec (b:bool) c: c0 -[tm]->* c -> match f c with
| Some c'=>Regular.map_config (fun q=>q) c
  -[if b then tm' else tm]->+ Regular.map_config (fun q=>q) c'
| None=>halts (if b then tm' else tm) (Regular.map_config (fun q=>q) c) end.
Proof.
  destruct c as [q [[l s] r]],q,s; intro H;
    try (apply guarded in H; destruct H as [t ->]);
    destruct b; cbn [f step_c Regular.map_config tm tm' move_left move_right]; esx.
Qed.
Theorem eqv: halts tm c0 <-> halts tm' c0.
Proof. apply (Regular.common_model tm tm' (fun q=>q) f); [reflexivity|].
  intros []; [exact (f_spec true)|exact (f_spec false)]. Qed.
End TM107.
