(* Others 6--9: one specialized invariant-word interpreter.
   TM9 supplies the common direction and state names.  The other machines
   will be related by checked state maps, never by rewritten string tables. *)
From BusyCoq Require Import Individual62 Longitudinal ES_v3 FastRev.
Require Import ZifyNat Lia String List PeanoNat NArith.
Set Implicit Arguments.

Lemma others_rev_power (X:Type) (w:list X) n:
  rev (w^^n) = (rev w)^^n.
Proof.
  induction n; [reflexivity|].
  cbn [lpow]; rewrite rev_app_distr,IHn,<-lpow_shift; reflexivity.
Qed.

Module TM9.
Definition tm := Eval compute in (TM_from_str "1RB0LC_1RC0RC_1LD0RB_1LA1LE_0RA0LF_0LD---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

(* The stored parameter n denotes the positive exponent 1+n. *)
Definition W n a : list Sym := [0;1;1]++[0;1]^^(1+n)++[1]++[0;1]^^a.
Definition WB n a : list Sym := [0;1;1]++[0;1]^^n++[0;0;0]++[0;1]^^a.
Definition WC n a : list Sym := [1;0;0;0]++[0;1]^^(1+n)++[1;0]^^a.
Notation hB := (B,[0]).
Notation hD := (D,[0]).
Notation hC := (C,[0;0]).
Notation hE := (E,[1;1]).

Lemma B_forward n a: segRR tm hB hB (W n a) (rev (WB n a)).
Proof. unfold W,WB,segRR; intros; rewrite !rev_app_distr,!others_rev_power; esx. Qed.
Lemma B_return n a: segLL tm hD hD (rev (WB n a)) (W n a).
Proof. unfold W,WB,segLL; intros; rewrite !rev_app_distr,!others_rev_power; esx. Qed.
Lemma C_forward n a: segRR tm hC hC (W n a) (rev (WC n a)).
Proof. unfold W,WC,segRR; intros; rewrite !rev_app_distr,!others_rev_power; esx. Qed.
Lemma C_return n a: segLL tm hE hE (rev (WC n a)) (W n a).
Proof. unfold W,WC,segLL; intros; rewrite !rev_app_distr,!others_rev_power; esx. Qed.

Lemma RR_app h x1 x2 y1 y2:
  segRR tm h h x1 (rev y1) -> segRR tm h h x2 (rev y2) ->
  segRR tm h h (x1++x2) (rev (y1++y2)).
Proof.
  destruct h as [q w]; unfold segRR; intros H1 H2 l r.
  rewrite rev_app_distr, !Str_app_assoc.
  unfold to_DH_config in *.
  eapply evstep_trans; [apply H1|apply H2].
Qed.
Lemma LL_app h x1 x2 y1 y2:
  segLL tm h h (rev x1) y1 -> segLL tm h h (rev x2) y2 ->
  segLL tm h h (rev (x1++x2)) (y1++y2).
Proof.
  destruct h as [q w]; unfold segLL; intros H1 H2 l r.
  rewrite rev_app_distr, !Str_app_assoc.
  unfold to_DH_config in *.
  eapply evstep_trans; [apply H2|apply H1].
Qed.

Inductive phase := Stable | GoingB | GoingC.
Definition column := (nat*nat)%type.
Definition word p (c:column) := let '(n,a):=c in
  match p with Stable=>W n a | GoingB=>WB n a | GoingC=>WC n a end.
Definition words p (cs:list column) := flat_map (word p) cs.

Lemma Bs_forward cs:
  segRR tm hB hB (words Stable cs) (rev (words GoingB cs)).
Proof.
  induction cs as [|[n a] cs IH]; [intros l r; apply evstep_refl|].
  apply RR_app; [apply B_forward|exact IH].
Qed.
Lemma Bs_return cs:
  segLL tm hD hD (rev (words GoingB cs)) (words Stable cs).
Proof.
  induction cs as [|[n a] cs IH]; [intros l r; apply evstep_refl|].
  apply LL_app; [apply B_return|exact IH].
Qed.
Lemma Cs_forward cs:
  segRR tm hC hC (words Stable cs) (rev (words GoingC cs)).
Proof.
  induction cs as [|[n a] cs IH]; [intros l r; apply evstep_refl|].
  apply RR_app; [apply C_forward|exact IH].
Qed.
Lemma Cs_return cs:
  segLL tm hE hE (rev (words GoingC cs)) (words Stable cs).
Proof.
  induction cs as [|[n a] cs IH]; [intros l r; apply evstep_refl|].
  apply LL_app; [apply C_return|exact IH].
Qed.

(* The weight is merely a copying heuristic: correctness below never needs
   it to equal the length.  Ordinary N avoids machine-integer assumptions. *)
Record deck := Deck { front:list column; back:list column; weight:N }.
Definition deck_words x := front x ++ rev (back x).
Definition empty_deck := Deck [] [] 0%N.
Definition deck_empty x := match front x,back x with [],[]=>true | _,_=>false end.
Definition deck_flip x := Deck (back x) (front x) (weight x).
Definition deck_push c x := Deck (front x) (c::back x) (N.succ (weight x)).
Definition deck_pop x :=
  match front x with
  | c::f => Some (c,Deck f (back x) (N.pred (weight x)))
  | [] => match fast_rev (back x) with
          | []=>None
          | c::f=>Some(c,Deck f [] (N.pred (weight x))) end
  end.
Definition deck_join x y :=
  if N.leb (weight x) (weight y)
  then Deck (front x ++ fast_rev_append (back x) (front y)) (back y)
       (N.add (weight x) (weight y))
  else Deck (front x) (back y ++ fast_rev_append (front y) (back x))
       (N.add (weight x) (weight y)).

Lemma deck_empty_spec x: deck_empty x=true -> deck_words x=[].
Proof. destruct x as [[|c f] [|c' b] k]; cbn; congruence. Qed.
Lemma deck_flip_spec x: deck_words(deck_flip x)=rev(deck_words x).
Proof. destruct x as [f b k]; change (b++rev f=rev(f++rev b)); rewrite rev_app_distr,rev_involutive; reflexivity. Qed.
Lemma deck_push_spec c x: deck_words(deck_push c x)=deck_words x++[c].
Proof. destruct x; cbn[deck_push deck_words front back rev]; apply app_assoc. Qed.
Lemma deck_join_spec x y: deck_words(deck_join x y)=deck_words x++deck_words y.
Proof.
  destruct x as [f b k],y as [g c j]; unfold deck_join; cbn[front back weight].
  destruct (N.leb k j); unfold deck_words; cbn[front back]; rewrite !fast_rev_append_spec.
  - rewrite !app_assoc; reflexivity.
  - rewrite !rev_app_distr,!rev_involutive,!app_assoc; reflexivity.
Qed.
Lemma deck_pop_spec x:
  match deck_pop x with None=>deck_words x=[]
  | Some(c,y)=>deck_words x=c::deck_words y end.
Proof.
  destruct x as [[|c f] b k]; unfold deck_pop,deck_words; cbn[front back weight].
  - rewrite fast_rev_spec; destruct (rev b) as [|c f] eqn:E; unfold deck_words; cbn[front back];
      rewrite ?app_nil_r; reflexivity.
  - reflexivity.
Qed.

Definition directed_word d p c :=
  match d with R=>word p c | L=>fast_rev (word p c) end.
Lemma directed_word_nonempty d p c: directed_word d p c<>[].
Proof.
  assert (H:word p c<>[]) by (destruct p,c; discriminate).
  destruct d; cbn[directed_word]; [|exact H].
  rewrite fast_rev_spec; intro E; apply H.
  apply (f_equal (@rev Sym)) in E; now rewrite rev_involutive in E.
Qed.
Definition band_bits d p x := flat_map (directed_word d p) (deck_words x).
Inductive token := Bit (b:Sym) | Band (p:phase) (x:deck).
Definition token_bits d u := match u with Bit b=>[b] | Band p x=>band_bits d p x end.
Definition stack_bits d s := flat_map (token_bits d) s.
Definition denote d s := stack_bits d s *> 0inf.
Lemma denote_bit d b s: denote d (Bit b::s)=b >> denote d s.
Proof. reflexivity. Qed.
Lemma denote_band d p x s: denote d (Band p x::s)=band_bits d p x *> denote d s.
Proof. unfold denote,stack_bits; cbn[flat_map token_bits]; apply Str_app_assoc. Qed.

Lemma words_app p x y: words p (x++y)=words p x++words p y.
Proof. apply flat_map_app. Qed.
Lemma band_bits_join d p x y:
  band_bits d p (deck_join x y)=band_bits d p x++band_bits d p y.
Proof. unfold band_bits; rewrite deck_join_spec,flat_map_app; reflexivity. Qed.
Lemma band_bits_empty d p x: deck_empty x=true -> band_bits d p x=[].
Proof. intro H; unfold band_bits; rewrite (deck_empty_spec x H); reflexivity. Qed.
Lemma band_bits_R p x: band_bits R p x=words p (deck_words x).
Proof. reflexivity. Qed.
Lemma band_bits_flip p x:
  band_bits L p (deck_flip x)=rev (band_bits R p x).
Proof.
  unfold band_bits; rewrite deck_flip_spec.
  generalize (deck_words x); intro cs; induction cs as [|c cs IH]; [reflexivity|].
  cbn[rev]; rewrite flat_map_app; cbn[flat_map directed_word].
  rewrite fast_rev_spec,app_nil_r,IH,rev_app_distr; reflexivity.
Qed.

Definition phase_eq p q := match p,q with
  | Stable,Stable | GoingB,GoingB | GoingC,GoingC=>true | _,_=>false end.
Lemma phase_eq_spec p q: phase_eq p q=true -> p=q.
Proof. destruct p,q; cbn; congruence. Qed.
Definition put_band p x s :=
  if deck_empty x then s else
  match s with Band q y::s' =>
    if phase_eq p q then Band p (deck_join x y)::s' else Band p x::s
  | _=>Band p x::s end.
Lemma put_band_spec d p x s:
  denote d (put_band p x s)=band_bits d p x *> denote d s.
Proof.
  unfold put_band; destruct (deck_empty x) eqn:E.
  - rewrite (band_bits_empty d p x E); reflexivity.
  - destruct s as [|[b|q y] s]; try apply denote_band.
    destruct (phase_eq p q) eqn:H; [apply phase_eq_spec in H; subst q|apply denote_band].
    unfold denote,stack_bits; cbn[flat_map token_bits].
    rewrite band_bits_join,!Str_app_assoc; reflexivity.
Qed.

Definition prepend_bits bs s := map Bit bs++s.
Lemma prepend_bits_spec d bs s:
  denote d (prepend_bits bs s)=bs *> denote d s.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  change (denote d (Bit b::prepend_bits bs s)=b >> (bs *> denote d s)).
  now rewrite denote_bit,IH.
Qed.

Fixpoint pop d s : Sym*list token := match s with
  | []=>(0,[])
  | Bit b::s => (b,s)
  | Band p x::s => match deck_pop x with
    | None=>pop d s
    | Some(c,y)=>let tail:=put_band p y s in
      match directed_word d p c with
      | []=>pop d s
      | b::bs=>(b,prepend_bits bs tail) end end end.

Lemma pop_spec d s: denote d s=fst(pop d s) >> denote d (snd(pop d s)).
Proof.
  induction s as [|[b|p x] s IH]; [apply const_unfold|reflexivity|].
  pose proof (deck_pop_spec x) as E.
  cbn[pop]; destruct (deck_pop x) as [[c y]|]; cbn in E.
  - unfold denote,stack_bits at 1; cbn[flat_map token_bits]; unfold band_bits at 1.
    rewrite E; cbn[flat_map]; rewrite !Str_app_assoc.
    destruct (directed_word d p c) as [|b bs] eqn:H.
    + exfalso; exact (directed_word_nonempty d p c H).
    + change (b >> (bs *> band_bits d p y *> denote d s)=
        b >> denote d (prepend_bits bs (put_band p y s))).
      rewrite prepend_bits_spec,put_band_spec; reflexivity.
  - unfold denote,stack_bits at 1; cbn[flat_map token_bits]; unfold band_bits.
    rewrite E; cbn[flat_map Str_app]; exact IH.
Qed.

(* The look-ahead only selects where to cut the neutral (01)^a tail. *)
Definition starts_one s := match s with Bit 1::_=>true | _=>false end.
Fixpoint pairs (guard:bool) s : nat*list token :=
  match s with Bit 0::Bit 1::t =>
    if andb guard (starts_one t) then (0%nat,s)
    else let '(n,r):=pairs guard t in (S n,r)
  | _=>(0%nat,s) end.
Lemma pairs_spec guard s:
  denote R s=[0;1]^^fst(pairs guard s) *> denote R (snd(pairs guard s)).
Proof.
  revert s; fix IH 1; intro s.
  destruct s as [|[b|p x] s]; try reflexivity.
  destruct b; [|reflexivity].
  destruct s as [|[b|p x] s]; try reflexivity.
  destruct b; [reflexivity|].
  cbn[pairs]; destruct (andb guard (starts_one s)); [reflexivity|].
  specialize (IH s); destruct (pairs guard s) as [n t]; cbn[fst snd] in *.
  rewrite !denote_bit,IH; reflexivity.
Qed.

Definition parse s : option (column*list token) :=
  match s with Bit 0::Bit 1::Bit 1::Bit 0::Bit 1::s =>
    let '(n,t):=pairs false s in
    match t with Bit 1::t=>let '(a,u):=pairs true t in Some((n,a),u)
    | _=>None end
  | _=>None end.
Lemma parse_spec s c t: parse s=Some(c,t) -> denote R s=word Stable c *> denote R t.
Proof.
  unfold parse.
  do 5 (destruct s as [|[b|p x] s]; [discriminate|destruct b|discriminate]; try discriminate).
  pose proof (pairs_spec false s) as Hn.
  destruct (pairs false s) as [n u]; cbn[fst snd] in Hn.
  destruct u as [|[b|p x] u]; try discriminate; destruct b; [discriminate|].
  pose proof (pairs_spec true u) as Ha.
  destruct (pairs true u) as [a v]; cbn[fst snd] in Ha.
  intro E; injection E as <- <-.
  rewrite !denote_bit,Hn,denote_bit,Ha.
  unfold word,W; rewrite !Str_app_assoc; reflexivity.
Qed.

Fixpoint collect fuel x s := match fuel with
  | O=>put_band Stable x s
  | S fuel=>match parse s with
    | Some(c,t)=>collect fuel (deck_push c x) t
    | None=>put_band Stable x s end end.
Definition discover s := collect 128 empty_deck s.
Lemma collect_spec fuel x s:
  denote R (collect fuel x s)=band_bits R Stable x *> denote R s.
Proof.
  revert x s; induction fuel as [|fuel IH]; intros x s; cbn[collect].
  - apply put_band_spec.
  - destruct (parse s) as [[c t]|] eqn:E; [|apply put_band_spec].
    rewrite IH,(@parse_spec s c t E).
    unfold band_bits; rewrite deck_push_spec,flat_map_app.
    cbn[flat_map directed_word]; rewrite app_nil_r,Str_app_assoc; reflexivity.
Qed.
Lemma discover_spec s: denote R (discover s)=denote R s.
Proof. unfold discover; rewrite collect_spec; reflexivity. Qed.

Fixpoint strip bs d s := match bs with
  | []=>Some s
  | b::bs=>let '(c,t):=pop d s in
    if Eqb.eqb b c then strip bs d t else None end.
Lemma strip_spec bs d s t: strip bs d s=Some t -> denote d s=bs *> denote d t.
Proof.
  revert s; induction bs as [|b bs IH]; intros s E; cbn[strip] in E.
  - injection E as <-; reflexivity.
  - pose proof (pop_spec d s) as H; destruct (pop d s) as [c u]; cbn[fst snd] in H.
    destruct b,c; cbn in E; try discriminate;
      rewrite H,(IH _ E); reflexivity.
Qed.

Inductive config := Cfg (q:Q) (d:dir) (l r:list token).
Definition decode c := match c with Cfg q d l r=>
  match d with L=>denote L l <{{q}} denote R r
             | R=>denote L l {{q}}> denote R r end end.
Definition raw c := match c with
  | Cfg q L l r=>let '(b,l'):=pop L l in
    match tm(q,b) with
    | None=>None
    | Some(w,L,q')=>Some(Cfg q' L l' (Bit w::r))
    | Some(w,R,q')=>Some(Cfg q' R (Bit w::l') r) end
  | Cfg q R l r=>let '(b,r'):=pop R r in
    match tm(q,b) with
    | None=>None
    | Some(w,L,q')=>Some(Cfg q' L l (Bit w::r'))
    | Some(w,R,q')=>Some(Cfg q' R (Bit w::l) r') end end.

Definition right_macro q payload p l r :=
  match strip payload L l with
  | None=>None
  | Some l'=>match discover r with
    | Band Stable x::r'=>Some(Cfg q R
        (prepend_bits payload (put_band p (deck_flip x) l')) r')
    | _=>None end end.
Definition left_macro q payload p l r :=
  match l with
  | Band p' x::l'=>if phase_eq p p' then
    match strip payload R r with
    | None=>None
    | Some r'=>Some(Cfg q L l'
        (prepend_bits payload (put_band Stable (deck_flip x) r'))) end
    else None
  | _=>None end.
Definition macro c := match c with
  | Cfg B R l r=>right_macro B [0] GoingB l r
  | Cfg C R l r=>right_macro C [0;0] GoingC l r
  | Cfg D L l r=>left_macro D [0] GoingB l r
  | Cfg E L l r=>left_macro E [1;1] GoingC l r
  | _=>None end.
Definition advance c := match macro c with Some c'=>Some c' | None=>raw c end.

Definition then_config (o:option config) (f:config->option config) :=
  match o with None=>None | Some c=>f c end.
Fixpoint iterate_pos n c := match n with
  | xH=>advance c
  | xO n=>then_config (iterate_pos n c) (iterate_pos n)
  | xI n=>then_config (then_config (iterate_pos n c) (iterate_pos n)) advance end.
Definition iterate n c := match n with N0=>Some c | Npos n=>iterate_pos n c end.
Definition check n q := match iterate n (Cfg q R [] []) with None=>true | Some _=>false end.

Definition transfer c o := match o with
  | None=>halts tm (decode c)
  | Some c'=>halts tm (decode c') -> halts tm (decode c) end.

Lemma raw_spec c: transfer c (raw c).
Proof.
  destruct c as [q [|] l r]; unfold raw; cbn[decode].
  - pose proof (pop_spec L l) as H; destruct (pop L l) as [b l']; cbn[fst snd] in H.
    unfold transfer; cbn[decode]; rewrite H; cbn[hd tl].
    destruct (tm(q,b)) as [[[w d] q']|] eqn:E.
    + destruct d; cbn[decode]; rewrite denote_bit; intro K.
      * eapply halts_evstep; [exact K|apply progress_evstep,progress_base].
        exact (@step_left tm q q' b w (denote L l') (denote R r) E).
      * eapply halts_evstep; [exact K|apply progress_evstep,progress_base].
        exact (@step_right tm q q' b w (denote L l') (denote R r) E).
    + apply halted_halts; exact E.
  - pose proof (pop_spec R r) as H; destruct (pop R r) as [b r']; cbn[fst snd] in H.
    unfold transfer; cbn[decode]; rewrite H; cbn[hd tl].
    destruct (tm(q,b)) as [[[w d] q']|] eqn:E.
    + destruct d; cbn[decode]; rewrite denote_bit; intro K.
      * eapply halts_evstep; [exact K|apply progress_evstep,progress_base].
        exact (@step_left tm q q' b w (denote L l) (denote R r') E).
      * eapply halts_evstep; [exact K|apply progress_evstep,progress_base].
        exact (@step_right tm q q' b w (denote L l) (denote R r') E).
    + apply halted_halts; exact E.
Qed.

Lemma band_bits_L p x:
  band_bits L p x=rev (words p (deck_words (deck_flip x))).
Proof.
  replace x with (deck_flip(deck_flip x)) at 1 by (destruct x; reflexivity).
  rewrite band_bits_flip,band_bits_R; reflexivity.
Qed.
Lemma right_macro_spec q payload p l r c:
  (forall cs,segRR tm (q,payload) (q,payload) (words Stable cs) (rev(words p cs))) ->
  right_macro q payload p l r=Some c -> decode (Cfg q R l r) -->* decode c.
Proof.
  intros Rule; unfold right_macro.
  destruct (strip payload L l) as [l'|] eqn:E; [|discriminate].
  destruct (discover r) as [|[b|ph x] r'] eqn:H; try discriminate.
  destruct ph; try discriminate; intro K; injection K as <-.
  cbn[decode]; rewrite prepend_bits_spec,put_band_spec,band_bits_flip,band_bits_R.
  rewrite (@strip_spec payload L l l' E).
  pose proof (discover_spec r) as HR; rewrite H,denote_band,band_bits_R in HR.
  rewrite <-HR; apply Rule.
Qed.
Lemma left_macro_spec q payload p l r c:
  (forall cs,segLL tm (q,payload) (q,payload) (rev(words p cs)) (words Stable cs)) ->
  left_macro q payload p l r=Some c -> decode (Cfg q L l r) -->* decode c.
Proof.
  intros Rule; unfold left_macro.
  destruct l as [|[b|ph x] l']; try discriminate.
  destruct (phase_eq p ph) eqn:H; [apply phase_eq_spec in H; subst ph|discriminate].
  destruct (strip payload R r) as [r'|] eqn:E; [|discriminate].
  intro K; injection K as <-; cbn[decode].
  rewrite denote_band,prepend_bits_spec,put_band_spec,band_bits_L,band_bits_R.
  rewrite (@strip_spec payload R r r' E); apply Rule.
Qed.
Lemma macro_spec c c': macro c=Some c' -> decode c -->* decode c'.
Proof.
  destruct c as [q d l r]; destruct q,d; cbn[macro]; try discriminate; intro H.
  - eapply right_macro_spec; [apply Bs_forward|exact H].
  - eapply right_macro_spec; [apply Cs_forward|exact H].
  - eapply left_macro_spec; [apply Bs_return|exact H].
  - eapply left_macro_spec; [apply Cs_return|exact H].
Qed.
Lemma advance_spec c: transfer c (advance c).
Proof.
  unfold advance; destruct (macro c) as [c'|] eqn:E; [|apply raw_spec].
  unfold transfer; intro H; eapply halts_evstep; [exact H|apply macro_spec,E].
Qed.
Lemma bind_spec c o f:
  transfer c o -> (forall c',transfer c' (f c')) -> transfer c (then_config o f).
Proof.
  destruct o as [c'|]; cbn[then_config transfer]; auto.
  intros H K; specialize (K c'); destruct (f c'); cbn[transfer] in *; tauto.
Qed.
Lemma iterate_pos_spec n c: transfer c (iterate_pos n c).
Proof.
  revert c; induction n; intro c; cbn[iterate_pos].
  - apply bind_spec; [apply bind_spec; apply IHn|apply advance_spec].
  - apply bind_spec; apply IHn.
  - apply advance_spec.
Qed.
Lemma iterate_spec n c: transfer c (iterate n c).
Proof. destruct n; cbn[iterate transfer]; [trivial|apply iterate_pos_spec]. Qed.
Lemma check_spec n q: check n q=true -> halts tm (0inf {{q}}> 0inf).
Proof.
  pose proof (iterate_spec n (Cfg q R [] [])) as H.
  unfold check; destruct (iterate n (Cfg q R [] [])); [discriminate|].
  intro E; exact H.
Qed.

Theorem halt: halts tm c0.
Proof. apply (@check_spec 1000000000%N A). native_check_eq. Time Qed.

End TM9.

Module TM6.
(* Direct left/right mirror of the original machine; no state renaming. *)
Definition tm := Eval compute in (TM_from_str "1LB0RD_1LC1LE_1RD0LA_1RA0RA_0RC0LF_0LB---").
Definition state_map q := match q with A=>C | B=>D | C=>A | D=>B | E=>E | F=>F end.
Lemma same_table: Perm tm TM9.tm state_map.
Proof.
  split.
  - intros q b; destruct q,b; cbn; congruence.
  - intros q b w d q' H; destruct q,b; cbn in H; try discriminate;
      inversion H; subst; reflexivity.
Qed.
Lemma from_check n: TM9.check n C=true -> halts tm c0.
Proof.
  intro H; apply (@perm_halts' tm TM9.tm state_map A (0inf {{0}} 0inf) same_table).
  apply (@TM9.check_spec n C),H.
Qed.
Theorem halt: halts tm c0.
Proof. apply (from_check 1000000000%N). native_check_eq. Time Qed.
End TM6.

Module TM7.
(* Direct left/right mirror of the original machine; no state renaming. *)
Definition tm := Eval compute in (TM_from_str "1LB1LE_1RC0LD_1RD0RD_1LA0RC_0RB0LF_0LA---").
Definition state_map q := match q with A=>D | B=>A | C=>B | D=>C | E=>E | F=>F end.
Lemma same_table: Perm tm TM9.tm state_map.
Proof.
  split.
  - intros q b; destruct q,b; cbn; congruence.
  - intros q b w d q' H; destruct q,b; cbn in H; try discriminate;
      inversion H; subst; reflexivity.
Qed.
Lemma from_check n: TM9.check n D=true -> halts tm c0.
Proof.
  intro H; apply (@perm_halts' tm TM9.tm state_map A (0inf {{0}} 0inf) same_table).
  apply (@TM9.check_spec n D),H.
Qed.
Theorem halt: halts tm c0.
Proof. apply (from_check 1000000000%N). native_check_eq. Time Qed.
End TM7.

Module TM8.
Definition tm := Eval compute in (TM_from_str "1RB0RB_1LC0RA_1LE1LD_0RE0LF_1RA0LB_0LC---").
Definition state_map q := match q with A=>B | B=>C | C=>D | D=>E | E=>A | F=>F end.
Lemma same_table: Perm tm TM9.tm state_map.
Proof.
  split.
  - intros q b; destruct q,b; cbn; congruence.
  - intros q b w d q' H; destruct q,b; cbn in H; try discriminate;
      inversion H; subst; reflexivity.
Qed.
Lemma from_check n: TM9.check n B=true -> halts tm c0.
Proof.
  intro H; apply (@perm_halts' tm TM9.tm state_map A (0inf {{0}} 0inf) same_table).
  apply (@TM9.check_spec n B),H.
Qed.
Theorem halt: halts tm c0.
Proof. apply (from_check 1000000000%N). native_check_eq. Time Qed.
End TM8.

Print Assumptions TM6.halt.
Print Assumptions TM7.halt.
Print Assumptions TM8.halt.
Print Assumptions TM9.halt.
